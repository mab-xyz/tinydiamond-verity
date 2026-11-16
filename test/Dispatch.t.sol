// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "./ref/TinyDiamond.sol";
import "./VerityDeploy.sol";

/// @dev Returns what the diamond's fallback handed it: caller, value and the full calldata.
contract EchoFacet {
    fallback() external payable {
        bytes memory r = abi.encode(msg.sender, msg.value, msg.data);
        assembly {
            return(add(r, 32), mload(r))
        }
    }
}

/// @dev Reverts with everything after the selector as revert data (any length).
contract RevertEchoFacet {
    fallback() external payable {
        bytes memory d = msg.data[4:];
        assembly {
            revert(add(d, 32), mload(d))
        }
    }
}

/// Fallback dispatch properties 11–14 on the Verity bytecode, fuzzed.
contract DispatchTest is Test {
    TinyDiamond diamond;
    address echo;
    address revertEcho;

    function setUp() public {
        diamond = VerityDeploy.tinyDiamond();
        echo = address(new EchoFacet());
        revertEcho = address(new RevertEchoFacet());
    }

    /// The six built-ins, from their signatures (independent of the code under test).
    function isBuiltin(bytes4 sel) internal pure returns (bool) {
        return sel == bytes4(keccak256("sharpCut(bytes4,address)")) || sel == bytes4(keccak256("restrict(bytes4,address)"))
            || sel == bytes4(keccak256("admin()")) || sel == bytes4(keccak256("getTarget(bytes4)"))
            || sel == bytes4(keccak256("selectorToFacet(bytes4)"))
            || sel == bytes4(keccak256("selectorRestriction(bytes4)"));
    }

    /// 11. A routed call the restriction allows reaches the facet with exactly the original
    /// calldata, sender and value, and returns the facet's result.
    function testFuzz_RoutedCallForwardsExactly(bytes4 sel, bytes calldata tail, uint96 value, address caller, bool restricted)
        public
    {
        vm.assume(!isBuiltin(sel));
        vm.assume(caller != address(0));
        diamond.sharpCut(sel, echo);
        if (restricted) diamond.restrict(sel, caller);
        bytes memory data = bytes.concat(sel, tail);
        vm.deal(caller, value);
        vm.prank(caller);
        (bool ok, bytes memory out) = address(diamond).call{value: value}(data);
        assertTrue(ok, "routed call succeeds");
        assertEq(out, abi.encode(caller, uint256(value), data), "facet saw exact sender, value, calldata; result returned");
        assertEq(address(diamond).balance, value, "value stays in the diamond");
    }

    /// 12. When the facet reverts, the diamond reverts with exactly the same revert data.
    function testFuzz_RevertDataForwardedExactly(bytes4 sel, bytes calldata tail) public {
        vm.assume(!isBuiltin(sel));
        diamond.sharpCut(sel, revertEcho);
        (bool ok, bytes memory out) = address(diamond).call(bytes.concat(sel, tail));
        assertFalse(ok, "reverts");
        assertEq(out, tail, "same revert data, byte for byte");
    }

    /// 13. A routed call from anyone other than the restricted caller reverts.
    function testFuzz_RestrictedCallerOnly(bytes4 sel, address allowed, address other) public {
        vm.assume(!isBuiltin(sel));
        vm.assume(allowed != address(0) && other != allowed);
        diamond.sharpCut(sel, echo);
        diamond.restrict(sel, allowed);
        vm.prank(other);
        (bool ok, bytes memory out) = address(diamond).call(abi.encodePacked(sel));
        assertFalse(ok);
        assertEq(out, abi.encodeWithSignature("Error(string)", "TinyDiamond: caller is not allowed"));
    }

    /// 14. A call to any unrouted, non-built-in selector reverts with "selector not found".
    function testFuzz_UnroutedSelectorNotFound(bytes4 sel, bytes calldata tail, address caller) public {
        vm.assume(!isBuiltin(sel));
        vm.prank(caller);
        (bool ok, bytes memory out) = address(diamond).call(bytes.concat(sel, tail));
        assertFalse(ok);
        assertEq(out, abi.encodeWithSignature("Error(string)", "TinyDiamond: selector not found"));
    }
}
