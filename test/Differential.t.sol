// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "./ref/TinyDiamond.sol";
import "./ref/LibTinyDiamond.sol";
import "./TestFacets.sol";
import "./VerityDeploy.sol";

/// @dev Facet exercising what the routing table and fallback must forward faithfully.
contract ProbeFacet {
    /// returndata whose length is not a multiple of 32
    function oddReturn() external pure {
        assembly {
            mstore(0, 0x0102030405000000000000000000000000000000000000000000000000000000)
            return(0, 5)
        }
    }

    /// revert payload whose length is not a multiple of 32
    function oddRevert() external pure {
        assembly {
            mstore(0, 0xdeadbeefaa000000000000000000000000000000000000000000000000000000)
            revert(0, 5)
        }
    }

    function valueAndSender() external payable returns (uint256, address) {
        return (msg.value, msg.sender);
    }

    /// writes the diamond's storage at an ordinary slot and at the admin slot
    function scribble(uint256 v) external {
        assembly {
            sstore(0, v)
            sstore(0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103, v)
        }
    }

    /// the diamond calling itself: `onlyAdmin` admits `address(this)`
    function selfCut(bytes4 selector, address target) external {
        ITinyDiamond(address(this)).sharpCut(selector, target);
    }
}

/// Runs the same operations on the Solidity reference and on the Verity diamond and requires
/// identical outcomes: success flag, returndata or revert payload, logs, and every routing slot.
contract DifferentialTest is Test {
    bytes32 constant S = 0x0abc81caac83e1656ee495fd84f3fd0c2020c41999d182a4a81694a75a694700;
    bytes32 constant ADMIN_SLOT = 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103;

    TinyDiamond ref;
    TinyDiamond ver;
    bytes4[] sels;
    address[] targets;
    address[] callers;

    function setUp() public {
        vm.recordLogs();
        ref = new TinyDiamond();
        Vm.Log[] memory refLogs = vm.getRecordedLogs();
        ver = VerityDeploy.tinyDiamond();
        Vm.Log[] memory verLogs = vm.getRecordedLogs();
        _sameConstructorLog(refLogs, verLogs);

        ProbeFacet probe = new ProbeFacet();
        TestFacet1 f1 = new TestFacet1();
        TestFacet3 f3 = new TestFacet3();
        RevertFacet rf = new RevertFacet();

        sels.push(TestFacet1.function1.selector);
        sels.push(TestFacet1.function2.selector);
        sels.push(ProbeFacet.oddReturn.selector);
        sels.push(ProbeFacet.oddRevert.selector);
        sels.push(ProbeFacet.valueAndSender.selector);
        sels.push(ProbeFacet.scribble.selector);
        sels.push(ProbeFacet.selfCut.selector);
        sels.push(RevertFacet.revertingFunction.selector);
        sels.push(bytes4(0x00000000));
        sels.push(bytes4(0xffffffff));
        for (uint256 i = 10; i < 20; ++i) sels.push(bytes4(keccak256(abi.encode(i))));
        sels.push(ITinyDiamond.sharpCut.selector); // built-in: immutable
        sels.push(TinyDiamond.admin.selector); // built-in: immutable

        targets.push(address(0));
        targets.push(address(probe));
        targets.push(address(f1));
        targets.push(address(f3));
        targets.push(address(rf));
        targets.push(address(0xBEEF)); // no code: delegatecall succeeds with empty returndata

        callers.push(address(this)); // admin
        callers.push(address(0x1234));
        callers.push(address(0x5678));
    }

    function _sameConstructorLog(Vm.Log[] memory a, Vm.Log[] memory b) internal view {
        assertEq(a.length, 1, "reference constructor logs");
        assertEq(b.length, 1, "verity constructor logs");
        assertEq(a[0].topics, b[0].topics, "constructor topics");
        // the facet of the built-in selectors is the diamond itself
        (IDiamond.FacetCut[] memory ca, address ia, bytes memory da) =
            abi.decode(a[0].data, (IDiamond.FacetCut[], address, bytes));
        (IDiamond.FacetCut[] memory cb, address ib, bytes memory db) =
            abi.decode(b[0].data, (IDiamond.FacetCut[], address, bytes));
        assertEq(ca.length, 1);
        assertEq(cb.length, 1);
        assertEq(ca[0].facetAddress, address(ref));
        assertEq(cb[0].facetAddress, address(ver));
        assertEq(uint8(ca[0].action), uint8(cb[0].action));
        assertEq(abi.encode(ca[0].functionSelectors), abi.encode(cb[0].functionSelectors));
        assertEq(ia, ib);
        assertEq(da, db);
        // byte-exact encoding once the own address is substituted
        cb[0].facetAddress = address(ref);
        assertEq(a[0].data, abi.encode(cb, ib, db), "constructor payload");
    }

    /// One operation on both diamonds; requires identical results and logs.
    function _both(address caller, uint256 value, bytes memory data) internal {
        vm.deal(caller, caller.balance + 2 * value);

        vm.recordLogs();
        vm.prank(caller);
        (bool okR, bytes memory outR) = address(ref).call{value: value}(data);
        Vm.Log[] memory logR = vm.getRecordedLogs();

        vm.prank(caller);
        (bool okV, bytes memory outV) = address(ver).call{value: value}(data);
        Vm.Log[] memory logV = vm.getRecordedLogs();

        assertEq(okV, okR, "success flag");
        assertEq(outV, outR, "returndata / revert payload");
        assertEq(logV.length, logR.length, "log count");
        for (uint256 i; i < logR.length; ++i) {
            assertEq(logV[i].topics, logR[i].topics, "log topics");
            assertEq(logV[i].data, logR[i].data, "log data");
            assertEq(logR[i].emitter, address(ref));
            assertEq(logV[i].emitter, address(ver));
        }
        assertEq(address(ver).balance, address(ref).balance, "balance");
    }

    function _sameStorage() internal view {
        assertEq(vm.load(address(ver), ADMIN_SLOT), vm.load(address(ref), ADMIN_SLOT), "admin");
        assertEq(vm.load(address(ver), bytes32(0)), vm.load(address(ref), bytes32(0)), "slot 0");
        bytes32 lenSlot = bytes32(uint256(S) + 1);
        uint256 n = uint256(vm.load(address(ref), lenSlot));
        assertEq(vm.load(address(ver), lenSlot), bytes32(n), "selector count");
        uint256 data = uint256(keccak256(abi.encode(lenSlot)));
        // the used words, plus the next ones that must stay zero
        for (uint256 j; j < (n + 7) / 8 + 3; ++j) {
            assertEq(vm.load(address(ver), bytes32(data + j)), vm.load(address(ref), bytes32(data + j)), "selector word");
        }
        for (uint256 i; i < sels.length; ++i) {
            bytes32 f = keccak256(abi.encode(sels[i], S));
            assertEq(vm.load(address(ver), f), vm.load(address(ref), f), "facetOf");
            bytes32 r = keccak256(abi.encode(sels[i], bytes32(uint256(S) + 2)));
            assertEq(vm.load(address(ver), r), vm.load(address(ref), r), "restriction");
        }
    }

    function _op(uint256 seed) internal {
        uint256 kind = seed % 8;
        bytes4 sel = sels[(seed >> 8) % sels.length];
        address target = targets[(seed >> 16) % targets.length];
        address caller = callers[(seed >> 24) % callers.length];
        if (kind == 0 || kind == 1) {
            _both(caller, 0, abi.encodeCall(ITinyDiamond.sharpCut, (sel, target)));
        } else if (kind == 2) {
            address who = (seed >> 32) % 2 == 0 ? address(0) : callers[(seed >> 40) % callers.length];
            _both(caller, 0, abi.encodeCall(ITinyDiamond.restrict, (sel, who)));
        } else if (kind == 3) {
            // a routed call: arguments for the probe functions, value for the payable ones
            bytes memory args = abi.encode(seed >> 64, uint256(uint160(target)));
            if (sel == ProbeFacet.selfCut.selector || sel == ITinyDiamond.sharpCut.selector) {
                // well-formed (bytes4, address) arguments; dirty ones: test_DirtyArgumentsRevertLikeSolc
                args = abi.encode(sels[(seed >> 48) % sels.length], target);
            }
            _both(caller, (seed >> 56) % 3, bytes.concat(sel, args));
        } else if (kind == 4) {
            // views
            uint256 v = (seed >> 32) % 4;
            if (v == 0) _both(caller, 0, abi.encodeCall(TinyDiamond.getTarget, (sel)));
            if (v == 1) _both(caller, 0, abi.encodeCall(TinyDiamond.selectorToFacet, (sel)));
            if (v == 2) _both(caller, 0, abi.encodeCall(TinyDiamond.selectorRestriction, (sel)));
            if (v == 3) _both(caller, 0, abi.encodeCall(TinyDiamond.admin, ()));
        } else if (kind == 5) {
            // receive, and calldata shorter than a selector
            uint256 len = (seed >> 32) % 4;
            bytes memory short = new bytes(len);
            for (uint256 i; i < len; ++i) short[i] = bytes1(uint8(seed >> (40 + 8 * i)));
            _both(caller, (seed >> 64) % 3, short);
        } else if (kind == 6) {
            // a view called with value: views are not payable
            _both(caller, 1, abi.encodeCall(TinyDiamond.admin, ()));
        } else {
            // a malformed call to a built-in: calldata too short for its arguments
            _both(caller, 0, abi.encodePacked(ITinyDiamond.sharpCut.selector, uint64(seed)));
        }
        _sameStorage();
    }

    function testFuzz_SameBehaviour(uint256[24] calldata seeds) public {
        for (uint256 i; i < seeds.length; ++i) {
            _op(seeds[i]);
        }
    }

    /// Fills more than one packed word, then removes from the middle (swap-and-pop across words).
    function testFuzz_ManySelectors(uint256 seed) public {
        for (uint256 i; i < 20; ++i) {
            _both(address(this), 0, abi.encodeCall(ITinyDiamond.sharpCut, (sels[i % 20], targets[1 + i % 5])));
            _sameStorage();
        }
        for (uint256 k; k < 20; ++k) {
            bytes4 sel = sels[uint256(keccak256(abi.encode(seed, k))) % 20];
            _both(address(this), 0, abi.encodeCall(ITinyDiamond.sharpCut, (sel, address(0))));
            _sameStorage();
        }
    }

    /// A facet calling `sharpCut` on the diamond: `onlyAdmin` admits the diamond itself.
    function test_SelfCallIsAdmin() public {
        address probe = targets[1];
        _both(address(this), 0, abi.encodeCall(ITinyDiamond.sharpCut, (ProbeFacet.selfCut.selector, probe)));
        bytes4 fresh = sels[12];
        _both(address(0x1234), 0, abi.encodeCall(ProbeFacet.selfCut, (fresh, probe)));
        _sameStorage();
        assertEq(ver.getTarget(fresh), probe);
    }

    /// A dirty `address` or `bytes4` argument (high or low bits set beyond its width) reverts with
    /// empty data in both, as solc's ABI decoder does (Verity validates scalar head words since
    /// lfglabs-dev/verity#2798; before, it masked them and routed the call).
    function test_DirtyArgumentsRevertLikeSolc() public {
        bytes memory dirtyTarget = abi.encodePacked(
            ITinyDiamond.sharpCut.selector, bytes32(bytes4(0x11223344)), bytes32(type(uint256).max));
        _bothRevertEmpty(dirtyTarget);
        assertEq(ver.getTarget(0x11223344), address(0));

        bytes memory dirtySelector = abi.encodePacked(
            ITinyDiamond.sharpCut.selector, bytes32(uint256(0x1122334455) << 216), bytes32(uint256(1)));
        _bothRevertEmpty(dirtySelector);
        assertEq(ver.getTarget(0x11223344), address(0));
    }

    function _bothRevertEmpty(bytes memory data) internal {
        (bool okR, bytes memory outR) = address(ref).call(data);
        (bool okV, bytes memory outV) = address(ver).call(data);
        assertFalse(okR);
        assertFalse(okV);
        assertEq(outR.length, 0);
        assertEq(outV.length, 0);
    }
}
