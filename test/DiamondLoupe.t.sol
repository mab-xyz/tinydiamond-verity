// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "./ref/TinyDiamond.sol";
import "./ref/LibTinyDiamond.sol";
import "./ref/DiamondLoupeFacet.sol";
import "./TestFacets.sol";
import "./VerityDeploy.sol";

/// @dev A facet written the ordinary way: its state variables land at slots 0, 1, 2, 3 of the diamond.
contract SequentialStateFacet {
    uint256 a;
    uint256 b;
    uint256 c;
    uint256 d;

    function clobber() external {
        a = type(uint256).max;
        b = type(uint256).max;
        c = type(uint256).max;
        d = type(uint256).max;
    }
}

contract DiamondLoupeTest is Test, IDiamond {
    TinyDiamond diamond;
    DiamondLoupeFacet loupeFacet;
    IDiamondLoupe loupe;

    // Model of the routed (non built-in) selectors, mirrors what the diamond must hold
    bytes4[] tracked;
    mapping(bytes4 => address) expected;
    address[] candidateFacets;

    address constant A = address(0xA);
    address constant B = address(0xB);
    address constant C = address(0xC);

    function setUp() public {
        diamond = VerityDeploy.tinyDiamond();
        loupeFacet = new DiamondLoupeFacet();
        loupe = IDiamondLoupe(address(diamond));
        bytes4[] memory ls = _loupeSelectors();
        for (uint256 i; i < ls.length; ++i) {
            _cutAndModel(ls[i], address(loupeFacet));
        }
        candidateFacets.push(address(0));
        candidateFacets.push(address(diamond));
        candidateFacets.push(address(loupeFacet));
        candidateFacets.push(A);
        candidateFacets.push(B);
        candidateFacets.push(C);
    }

    // ============ helpers ============

    function _loupeSelectors() internal pure returns (bytes4[] memory s) {
        s = new bytes4[](5);
        s[0] = IDiamondLoupe.facets.selector;
        s[1] = IDiamondLoupe.facetFunctionSelectors.selector;
        s[2] = IDiamondLoupe.facetAddresses.selector;
        s[3] = IDiamondLoupe.facetAddress.selector;
        s[4] = IERC165.supportsInterface.selector;
    }

    function _builtins() internal pure returns (bytes4[] memory s) {
        s = new bytes4[](6);
        s[0] = bytes4(keccak256("sharpCut(bytes4,address)"));
        s[1] = bytes4(keccak256("restrict(bytes4,address)"));
        s[2] = bytes4(keccak256("admin()"));
        s[3] = bytes4(keccak256("getTarget(bytes4)"));
        s[4] = bytes4(keccak256("selectorToFacet(bytes4)"));
        s[5] = bytes4(keccak256("selectorRestriction(bytes4)"));
    }

    function _track(bytes4 s) internal {
        for (uint256 i; i < tracked.length; ++i) {
            if (tracked[i] == s) return;
        }
        tracked.push(s);
    }

    function _cutAndModel(bytes4 s, address target) internal {
        _track(s);
        diamond.sharpCut(s, target);
        expected[s] = target;
    }

    function _contains(bytes4[] memory arr, bytes4 s) internal pure returns (uint256 n) {
        for (uint256 i; i < arr.length; ++i) {
            if (arr[i] == s) ++n;
        }
    }

    /// @dev Expected DiamondCut action for a cut, or 3 for "no event"
    function _expectedAction(address oldT, address newT) internal pure returns (uint8) {
        if (oldT == newT) return 3;
        if (oldT == address(0)) return uint8(FacetCutAction.Add);
        if (newT == address(0)) return uint8(FacetCutAction.Remove);
        return uint8(FacetCutAction.Replace);
    }

    /// @dev Performs a cut and checks the emitted event against the model
    function _cutChecked(bytes4 s, address target) internal {
        _track(s);
        address oldT = expected[s];
        vm.recordLogs();
        diamond.sharpCut(s, target);
        Vm.Log[] memory logs = vm.getRecordedLogs();
        uint8 action = _expectedAction(oldT, target);
        if (action == 3) {
            assertEq(logs.length, 0, "no-op cut must be silent");
        } else {
            assertEq(logs.length, 1, "one DiamondCut per change");
            assertEq(logs[0].topics[0], DiamondCut.selector, "event is DiamondCut");
            (FacetCut[] memory cut, address init, bytes memory cd) = abi.decode(logs[0].data, (FacetCut[], address, bytes));
            assertEq(cut.length, 1);
            assertEq(cut[0].facetAddress, target, "facet address (0 for Remove)");
            assertEq(uint8(cut[0].action), action, "action");
            assertEq(cut[0].functionSelectors.length, 1);
            assertEq(cut[0].functionSelectors[0], s);
            assertEq(init, address(0));
            assertEq(cd.length, 0);
        }
        expected[s] = target;
    }

    /// @dev Checks every observable view of the routing table against the model
    function _checkInvariants() internal view {
        bytes4[] memory builtins = _builtins();

        // 1. point lookups
        for (uint256 i; i < tracked.length; ++i) {
            bytes4 s = tracked[i];
            assertEq(diamond.selectorToFacet(s), expected[s], "selectorToFacet");
            assertEq(diamond.getTarget(s), expected[s], "getTarget");
            assertEq(loupe.facetAddress(s), expected[s], "facetAddress");
        }
        for (uint256 i; i < builtins.length; ++i) {
            assertEq(loupe.facetAddress(builtins[i]), address(diamond), "builtin facetAddress");
        }

        // 2. raw V3 storage: dense array, positions are index + 1
        bytes32 base = LibTinyDiamond.STORAGE_SLOT;
        uint256 len = uint256(vm.load(address(diamond), bytes32(uint256(base) + 1)));
        uint256 live;
        for (uint256 i; i < tracked.length; ++i) {
            if (expected[tracked[i]] != address(0)) ++live;
        }
        assertEq(len, live, "selectors.length == live selectors");
        bytes32 dataSlot = keccak256(abi.encode(uint256(base) + 1));
        for (uint256 i; i < len; ++i) {
            bytes32 word = vm.load(address(diamond), bytes32(uint256(dataSlot) + i / 8));
            bytes4 s = bytes4(uint32(uint256(word) >> (32 * (i % 8))));
            bytes32 entry = vm.load(address(diamond), keccak256(abi.encode(s, base)));
            assertEq(address(uint160(uint256(entry))), expected[s], "stored facet");
            assertEq(uint256(entry) >> 160, i + 1, "stored position");
        }

        // 3. facets(): diamond first with builtins, every live selector exactly once, no empty/zero/duplicate facet
        IDiamondLoupe.Facet[] memory fs = loupe.facets();
        assertEq(fs[0].facetAddress, address(diamond), "diamond first");
        for (uint256 i; i < builtins.length; ++i) {
            assertEq(fs[0].functionSelectors[i], builtins[i], "builtins first");
        }
        uint256 total;
        for (uint256 j; j < fs.length; ++j) {
            assertTrue(fs[j].facetAddress != address(0), "no zero facet");
            assertTrue(fs[j].functionSelectors.length > 0, "no empty facet");
            for (uint256 k; k < j; ++k) {
                assertTrue(fs[k].facetAddress != fs[j].facetAddress, "no duplicate facet");
            }
            for (uint256 i; i < fs[j].functionSelectors.length; ++i) {
                bytes4 s = fs[j].functionSelectors[i];
                if (j == 0 && i < builtins.length) continue;
                assertEq(expected[s], fs[j].facetAddress, "selector grouped under its facet");
                ++total;
            }
        }
        assertEq(total, live, "every live selector listed once");

        // 4. facetFunctionSelectors(f) == model, for every candidate facet
        for (uint256 c; c < candidateFacets.length; ++c) {
            address f = candidateFacets[c];
            bytes4[] memory got = loupe.facetFunctionSelectors(f);
            uint256 want = f == address(diamond) ? builtins.length : 0;
            for (uint256 i; i < tracked.length; ++i) {
                if (f != address(0) && expected[tracked[i]] == f) {
                    ++want;
                    assertEq(_contains(got, tracked[i]), 1, "selector listed once for its facet");
                }
            }
            assertEq(got.length, want, "facetFunctionSelectors length");
        }

        // 5. facetAddresses() == facets() addresses, in order
        address[] memory addrs = loupe.facetAddresses();
        assertEq(addrs.length, fs.length, "facetAddresses length");
        for (uint256 j; j < fs.length; ++j) {
            assertEq(addrs[j], fs[j].facetAddress, "facetAddresses order");
        }
    }

    // ============ unit tests ============

    function test_Constructor_EmitsBuiltinsAsAdded() public {
        vm.recordLogs();
        TinyDiamond d = VerityDeploy.tinyDiamond();
        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].emitter, address(d));
        assertEq(logs[0].topics[0], DiamondCut.selector);
        (FacetCut[] memory cut,,) = abi.decode(logs[0].data, (FacetCut[], address, bytes));
        assertEq(cut.length, 1);
        assertEq(cut[0].facetAddress, address(d));
        assertEq(uint8(cut[0].action), uint8(FacetCutAction.Add));
        bytes4[] memory builtins = _builtins();
        assertEq(cut[0].functionSelectors.length, builtins.length);
        for (uint256 i; i < builtins.length; ++i) {
            assertEq(cut[0].functionSelectors[i], builtins[i]);
        }
    }

    function test_Builtins_SharpCutReverts() public {
        bytes4[] memory builtins = _builtins();
        for (uint256 i; i < builtins.length; ++i) {
            vm.expectRevert("TinyDiamond: immutable function");
            diamond.sharpCut(builtins[i], A);
            vm.expectRevert("TinyDiamond: immutable function");
            diamond.sharpCut(builtins[i], address(0));
        }
    }

    function test_Builtins_RestrictReverts() public {
        bytes4[] memory builtins = _builtins();
        for (uint256 i; i < builtins.length; ++i) {
            vm.expectRevert("TinyDiamond: immutable function");
            diamond.restrict(builtins[i], A);
        }
    }

    function test_Builtins_NonAdminStillGetsAdminError() public {
        vm.prank(address(0x1234));
        vm.expectRevert("TinyDiamond: caller is not admin");
        diamond.sharpCut(_builtins()[0], A);
    }

    function test_Loupe_FreshDiamond() public view {
        IDiamondLoupe.Facet[] memory fs = loupe.facets();
        assertEq(fs.length, 2);
        assertEq(fs[0].facetAddress, address(diamond));
        assertEq(fs[0].functionSelectors.length, 6);
        assertEq(fs[1].facetAddress, address(loupeFacet));
        assertEq(fs[1].functionSelectors.length, 5);
        _checkInvariants();
    }

    function test_Loupe_UnknownSelectorAndZeroFacet() public view {
        assertEq(loupe.facetAddress(bytes4(0xdeadbeef)), address(0));
        assertEq(loupe.facetFunctionSelectors(address(0)).length, 0);
        assertEq(loupe.facetFunctionSelectors(address(0xdead)).length, 0);
    }

    function test_SupportsInterface() public view {
        IERC165 d = IERC165(address(diamond));
        assertTrue(d.supportsInterface(0x01ffc9a7), "ERC-165");
        assertTrue(d.supportsInterface(0x48e2b093), "IDiamondLoupe (literal from EIP-2535 reference)");
        assertEq(
            type(IDiamondLoupe).interfaceId,
            IDiamondLoupe.facets.selector ^ IDiamondLoupe.facetFunctionSelectors.selector
                ^ IDiamondLoupe.facetAddresses.selector ^ IDiamondLoupe.facetAddress.selector
        );
        assertFalse(d.supportsInterface(0xffffffff), "ERC-165 invalid id");
        assertFalse(d.supportsInterface(0x00000000));
    }

    function test_Events_AddReplaceRemoveAndNoOps() public {
        bytes4 s = bytes4(0x11111111);
        _cutChecked(s, address(0)); // 0 -> 0: silent
        _cutChecked(s, A); // Add
        _cutChecked(s, A); // A -> A: silent
        _cutChecked(s, B); // Replace
        _cutChecked(s, address(0)); // Remove
        _checkInvariants();
    }

    function test_SwapAndPop_RemoveFirstMiddleLast() public {
        for (uint32 i = 1; i <= 6; ++i) {
            _cutChecked(bytes4(i), i % 2 == 0 ? A : B);
        }
        // array is [5 loupe selectors, 1, 2, 3, 4, 5, 6]
        _checkInvariants();
        _cutChecked(IDiamondLoupe.facets.selector, address(0)); // index 0
        _cutChecked(IDiamondLoupe.facets.selector, address(loupeFacet)); // re-added at the end
        _checkInvariants();
        _cutChecked(bytes4(uint32(3)), address(0)); // middle
        _checkInvariants();
        _cutChecked(IDiamondLoupe.facets.selector, address(0)); // last
        _cutChecked(IDiamondLoupe.facets.selector, address(loupeFacet));
        _checkInvariants();
        // remove everything, including the loupe's own selectors, then the array is empty
        for (uint256 i; i < tracked.length; ++i) {
            if (expected[tracked[i]] != address(0)) _cutChecked(tracked[i], address(0));
        }
        assertEq(uint256(vm.load(address(diamond), bytes32(uint256(LibTinyDiamond.STORAGE_SLOT) + 1))), 0);
        vm.expectRevert("TinyDiamond: selector not found");
        loupe.facets();
    }

    function test_RemoveAndReAdd_NoGrowth() public {
        bytes4 s = bytes4(0x22222222);
        for (uint256 i; i < 20; ++i) {
            _cutChecked(s, A);
            _cutChecked(s, address(0));
        }
        _cutChecked(s, A);
        _checkInvariants();
        assertEq(uint256(vm.load(address(diamond), bytes32(uint256(LibTinyDiamond.STORAGE_SLOT) + 1))), 6);
    }

    function test_Storage_ERC7201Slot() public pure {
        bytes32 slot = keccak256(abi.encode(uint256(keccak256("tinydiamond.storage")) - 1)) & ~bytes32(uint256(0xff));
        assertEq(slot, LibTinyDiamond.STORAGE_SLOT);
    }

    /// @dev Known-negative for the storage-collision hazard: a facet with ordinary state variables
    /// writes slots 0..3 of the diamond and must not affect routing or the loupe.
    function test_Storage_SequentialFacetStateDoesNotCorruptRouting() public {
        SequentialStateFacet f = new SequentialStateFacet();
        _cutChecked(SequentialStateFacet.clobber.selector, address(f));
        candidateFacets.push(address(f));
        _cutChecked(bytes4(0x33333333), A);
        SequentialStateFacet(address(diamond)).clobber();
        assertEq(uint256(vm.load(address(diamond), bytes32(uint256(2)))), type(uint256).max, "slot 2 was written");
        _checkInvariants();
    }

    function test_Loupe_ReportsFacetPointingAtDiamondItselfUnderDiamond() public {
        // Degenerate but allowed: routing a selector to the diamond's own address
        _cutChecked(bytes4(0x44444444), address(diamond));
        _checkInvariants();
        IDiamondLoupe.Facet[] memory fs = loupe.facets();
        assertEq(fs[0].functionSelectors.length, 7);
    }

    // ============ exhaustive bounded sequences ============

    bytes4[3] alphabet = [bytes4(0xaaaaaaa1), bytes4(0xaaaaaaa2), bytes4(0xaaaaaaa3)];
    /// @dev External entry points: each call gets a fresh memory frame, so 7k checks don't hit MemoryOOG
    function checkInvariantsExt() external view {
        _checkInvariants();
    }

    function cutCheckedExt(bytes4 s, address target) external {
        require(msg.sender == address(this));
        _cutChecked(s, target);
    }

    /// @return explored number of states checked (counted in memory: storage is rolled back by revertToState)
    function _explore(uint256 depth) internal returns (uint256 explored) {
        this.checkInvariantsExt();
        explored = 1;
        if (depth == 0) return explored;
        address[3] memory targets = [address(0), A, B];
        for (uint256 si; si < 3; ++si) {
            for (uint256 ti; ti < 3; ++ti) {
                uint256 snap = vm.snapshotState();
                this.cutCheckedExt(alphabet[si], targets[ti]);
                explored += _explore(depth - 1);
                vm.revertToState(snap);
            }
        }
    }

    /// @dev Every sequence of up to 4 cuts over 3 selectors x {0, A, B} (9^4 = 6561 leaves),
    /// with every view and the raw storage checked after every cut, and every event checked.
    function test_Exhaustive_AllSequencesUpTo4() public {
        for (uint256 i; i < 3; ++i) {
            _track(alphabet[i]);
        }
        assertEq(_explore(4), 1 + 9 + 81 + 729 + 6561);
    }

    // ============ long random sequences ============

    function testFuzz_RandomSequences(uint256 seed) public {
        address[4] memory targets = [address(0), A, B, C];
        for (uint256 i; i < 64; ++i) {
            seed = uint256(keccak256(abi.encode(seed)));
            bytes4 s = bytes4(uint32(0xbbbbbb00 + (seed % 8)));
            _cutChecked(s, targets[(seed >> 8) % 4]);
            _checkInvariants();
        }
    }

    // ============ fallback cost ============

    function test_Fallback_StillOneRoutingSlotRead() public {
        TestFacet1 f = new TestFacet1();
        diamond.sharpCut(TestFacet1.function2.selector, address(f));
        vm.record();
        TestFacet1(address(diamond)).function2();
        (bytes32[] memory reads,) = vm.accesses(address(diamond));
        // routing entry + restriction entry, nothing else
        assertEq(reads.length, 2);
    }
}
