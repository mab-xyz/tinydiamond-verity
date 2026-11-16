// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "./ref/TinyDiamond.sol";
import "./ref/LibTinyDiamond.sol";
import "./ref/DiamondLoupeFacet.sol";
import "./ref/DiamondCutFacet.sol";
import "./TestFacets.sol";
import "./VerityDeploy.sol";

contract DiamondCutTest is Test, IDiamond {
    TinyDiamond diamond; // upgraded with diamondCut
    TinyDiamond twin; // same changes with sharpCut, for differential testing
    DiamondLoupeFacet loupeFacet;
    DiamondCutFacet cutFacet;
    TestFacet1 facet1;
    TestFacet2 facet2;

    address constant A = address(0xA);
    address constant B = address(0xB);
    address constant C = address(0xC);
    address constant USER = address(0x1234);

    event Initialized(string message, uint256 value); // DiamondInit's

    function setUp() public {
        loupeFacet = new DiamondLoupeFacet();
        cutFacet = new DiamondCutFacet();
        facet1 = new TestFacet1();
        facet2 = new TestFacet2();
        diamond = _newDiamond();
        twin = _newDiamond();
    }

    function _newDiamond() internal returns (TinyDiamond d) {
        d = VerityDeploy.tinyDiamond();
        d.sharpCut(IDiamondLoupe.facets.selector, address(loupeFacet));
        d.sharpCut(IDiamondLoupe.facetFunctionSelectors.selector, address(loupeFacet));
        d.sharpCut(IDiamondLoupe.facetAddresses.selector, address(loupeFacet));
        d.sharpCut(IDiamondLoupe.facetAddress.selector, address(loupeFacet));
        d.sharpCut(IERC165.supportsInterface.selector, address(loupeFacet));
        d.sharpCut(IDiamondCut.diamondCut.selector, address(cutFacet));
    }

    function _one(address facet, FacetCutAction action, bytes4 s) internal pure returns (FacetCut[] memory c) {
        bytes4[] memory sels = new bytes4[](1);
        sels[0] = s;
        c = new FacetCut[](1);
        c[0] = FacetCut(facet, action, sels);
    }

    function _cut(FacetCut[] memory c) internal {
        IDiamondCut(address(diamond)).diamondCut(c, address(0), "");
    }

    // ============ semantics ============

    function test_Selector() public pure {
        assertEq(IDiamondCut.diamondCut.selector, bytes4(0x1f931c1c));
    }

    function test_Batch_AddReplaceRemoveAcrossFacets() public {
        bytes4[] memory f1 = new bytes4[](2);
        f1[0] = TestFacet1.function1.selector;
        f1[1] = TestFacet1.function2.selector;
        bytes4[] memory f2 = new bytes4[](1);
        f2[0] = TestFacet2.function4.selector;
        FacetCut[] memory c = new FacetCut[](2);
        c[0] = FacetCut(address(facet1), FacetCutAction.Add, f1);
        c[1] = FacetCut(address(facet2), FacetCutAction.Add, f2);
        _cut(c);

        assertEq(TestFacet1(address(diamond)).function1(), "function1");
        assertEq(TestFacet1(address(diamond)).function2(), 42);
        assertEq(TestFacet2(address(diamond)).function4(21), 42);

        // replace + remove in one batch
        TestFacet3 facet3 = new TestFacet3();
        bytes4[] memory r = new bytes4[](1);
        r[0] = TestFacet1.function1.selector;
        bytes4[] memory rm = new bytes4[](2);
        rm[0] = TestFacet1.function2.selector;
        rm[1] = TestFacet2.function4.selector;
        c[0] = FacetCut(address(facet3), FacetCutAction.Replace, r);
        c[1] = FacetCut(address(0), FacetCutAction.Remove, rm);
        _cut(c);

        assertEq(TestFacet1(address(diamond)).function1(), "facet3/function1");
        assertEq(diamond.getTarget(TestFacet1.function2.selector), address(0));
        assertEq(diamond.getTarget(TestFacet2.function4.selector), address(0));
        vm.expectRevert("TinyDiamond: selector not found");
        TestFacet2(address(diamond)).function4(1);
    }

    function test_EmptyBatch_EmitsAndDoesNothing() public {
        vm.recordLogs();
        _cut(new FacetCut[](0));
        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics[0], DiamondCut.selector);
    }

    function test_Event_OneDiamondCutWithTheWholeBatch() public {
        bytes4[] memory f1 = new bytes4[](2);
        f1[0] = bytes4(0x11111111);
        f1[1] = bytes4(0x22222222);
        FacetCut[] memory c = new FacetCut[](2);
        c[0] = FacetCut(A, FacetCutAction.Add, f1);
        c[1] = FacetCut(B, FacetCutAction.Add, _one(B, FacetCutAction.Add, 0x33333333)[0].functionSelectors);
        DiamondInit init = new DiamondInit();
        bytes memory data = abi.encodeCall(DiamondInit.init, ("hi", 7));

        vm.expectEmit(true, true, true, true, address(diamond));
        emit DiamondCut(c, address(init), data);
        vm.expectEmit(true, true, true, true, address(diamond)); // _init ran by delegatecall in the diamond
        emit Initialized("hi", 7);
        vm.recordLogs();
        IDiamondCut(address(diamond)).diamondCut(c, address(init), data);
        assertEq(vm.getRecordedLogs().length, 2, "exactly one DiamondCut, then the init's event");
    }

    // ============ EIP-2535 reverts ============

    function test_Add_ExistingReverts() public {
        _cut(_one(A, FacetCutAction.Add, 0x11111111));
        vm.expectRevert("DiamondCut: function already exists");
        _cut(_one(B, FacetCutAction.Add, 0x11111111));
        vm.expectRevert("DiamondCut: function already exists");
        _cut(_one(A, FacetCutAction.Add, 0x11111111));
    }

    function test_Add_DuplicateInSameBatchReverts() public {
        bytes4[] memory s = new bytes4[](2);
        s[0] = 0x11111111;
        s[1] = 0x11111111;
        FacetCut[] memory c = new FacetCut[](1);
        c[0] = FacetCut(A, FacetCutAction.Add, s);
        vm.expectRevert("DiamondCut: function already exists");
        _cut(c);
    }

    function test_Replace_UnsetReverts() public {
        vm.expectRevert("DiamondCut: function does not exist");
        _cut(_one(A, FacetCutAction.Replace, 0x11111111));
    }

    function test_Replace_SameFacetReverts() public {
        _cut(_one(A, FacetCutAction.Add, 0x11111111));
        vm.expectRevert("DiamondCut: function already on this facet");
        _cut(_one(A, FacetCutAction.Replace, 0x11111111));
    }

    function test_Remove_UnsetReverts() public {
        vm.expectRevert("DiamondCut: function does not exist");
        _cut(_one(address(0), FacetCutAction.Remove, 0x11111111));
    }

    function test_Remove_NonZeroFacetReverts() public {
        _cut(_one(A, FacetCutAction.Add, 0x11111111));
        vm.expectRevert("DiamondCut: remove facet must be address(0)");
        _cut(_one(A, FacetCutAction.Remove, 0x11111111));
    }

    function test_AddReplace_ZeroFacetReverts() public {
        vm.expectRevert("DiamondCut: facet is address(0)");
        _cut(_one(address(0), FacetCutAction.Add, 0x11111111));
        _cut(_one(A, FacetCutAction.Add, 0x11111111));
        vm.expectRevert("DiamondCut: facet is address(0)");
        _cut(_one(address(0), FacetCutAction.Replace, 0x11111111));
    }

    function test_InvalidActionReverts() public {
        bytes memory c = abi.encodeWithSelector(
            IDiamondCut.diamondCut.selector, _one(A, FacetCutAction.Add, 0x11111111), address(0), ""
        );
        // action is the 2nd word of the first FacetCut tuple: patch Add (0) into 3
        bytes32 word;
        uint256 found;
        for (uint256 off = 4; off + 32 <= c.length; off += 32) {
            assembly {
                word := mload(add(add(c, 32), off))
            }
            if (word == bytes32(uint256(uint160(A)))) {
                assembly {
                    mstore(add(add(c, 64), off), 3)
                }
                ++found;
                break;
            }
        }
        assertEq(found, 1);
        (bool ok,) = address(diamond).call(c);
        assertFalse(ok, "out-of-range enum must revert");
        assertEq(diamond.getTarget(0x11111111), address(0));
    }

    function test_ImmutableFunctionsReverts() public {
        bytes4[] memory builtins = new bytes4[](6);
        builtins[0] = bytes4(keccak256("sharpCut(bytes4,address)"));
        builtins[1] = bytes4(keccak256("restrict(bytes4,address)"));
        builtins[2] = bytes4(keccak256("admin()"));
        builtins[3] = bytes4(keccak256("getTarget(bytes4)"));
        builtins[4] = bytes4(keccak256("selectorToFacet(bytes4)"));
        builtins[5] = bytes4(keccak256("selectorRestriction(bytes4)"));
        for (uint256 i; i < builtins.length; ++i) {
            vm.expectRevert("TinyDiamond: immutable function");
            _cut(_one(A, FacetCutAction.Add, builtins[i]));
        }
    }

    function test_Atomic_BadEntryRevertsWholeBatch() public {
        FacetCut[] memory c = new FacetCut[](2);
        c[0] = _one(A, FacetCutAction.Add, 0x11111111)[0];
        c[1] = _one(B, FacetCutAction.Replace, 0x22222222)[0]; // unset: invalid
        vm.expectRevert("DiamondCut: function does not exist");
        _cut(c);
        assertEq(diamond.getTarget(0x11111111), address(0), "first entry rolled back");
    }

    // ============ access control ============

    function test_NonAdminReverts() public {
        vm.prank(USER);
        vm.expectRevert("TinyDiamond: caller is not admin");
        _cut(_one(A, FacetCutAction.Add, 0x11111111));
    }

    function test_FollowsAdminSlot() public {
        // a new admin written to the EIP-1967 slot (as a facet could) is honoured, the old one is not
        vm.store(address(diamond), LibTinyDiamond.ADMIN_SLOT, bytes32(uint256(uint160(USER))));
        assertEq(diamond.admin(), USER, "library slot is TinyDiamond's admin slot");
        vm.expectRevert("TinyDiamond: caller is not admin");
        _cut(_one(A, FacetCutAction.Add, 0x11111111));
        vm.prank(USER);
        _cut(_one(A, FacetCutAction.Add, 0x11111111));
        assertEq(diamond.getTarget(0x11111111), A);
    }

    function test_RestrictStillApplies() public {
        diamond.restrict(IDiamondCut.diamondCut.selector, USER);
        vm.expectRevert("TinyDiamond: caller is not allowed");
        _cut(_one(A, FacetCutAction.Add, 0x11111111));
    }

    function test_DirectCallOnFacetIsHarmless() public {
        // called on the facet itself (not through a diamond), admin is the facet's empty slot
        vm.expectRevert("TinyDiamond: caller is not admin");
        cutFacet.diamondCut(_one(A, FacetCutAction.Add, 0x11111111), address(0), "");
    }

    // ============ _init ============

    function test_Init_ZeroSkipsCalldata() public {
        vm.recordLogs();
        IDiamondCut(address(diamond)).diamondCut(_one(A, FacetCutAction.Add, 0x11111111), address(0), hex"deadbeef");
        assertEq(vm.getRecordedLogs().length, 1);
        assertEq(diamond.getTarget(0x11111111), A);
    }

    function test_Init_RevertBubblesAndRollsBack() public {
        RevertInit init = new RevertInit();
        vm.expectRevert(RevertInit.InitializationFailed.selector);
        IDiamondCut(address(diamond)).diamondCut(
            _one(A, FacetCutAction.Add, 0x11111111), address(init), abi.encodeCall(RevertInit.init, ())
        );
        assertEq(diamond.getTarget(0x11111111), address(0), "cut rolled back");
    }

    function test_Init_EmptyRevertGetsMessage() public {
        vm.expectRevert("DiamondCut: _init reverted");
        // TestFacet1 has no fallback: an unknown selector reverts without data
        IDiamondCut(address(diamond)).diamondCut(new FacetCut[](0), address(facet1), hex"deadbeef");
    }

    function test_Init_NoCodeReverts() public {
        vm.expectRevert("DiamondCut: _init has no code");
        IDiamondCut(address(diamond)).diamondCut(new FacetCut[](0), address(0xbeef), "");
    }

    // ============ ERC-165 ============

    function test_SupportsInterface_FollowsRouting() public {
        IERC165 d = IERC165(address(diamond));
        assertTrue(d.supportsInterface(0x1f931c1c), "IDiamondCut while routed");
        diamond.sharpCut(IDiamondCut.diamondCut.selector, address(0));
        assertFalse(d.supportsInterface(0x1f931c1c), "not after removal");
        assertTrue(d.supportsInterface(0x48e2b093), "loupe unaffected");
    }

    // ============ differential: diamondCut batch == same sharpCut sequence ============

    mapping(bytes4 => address) model;

    function testFuzz_Differential(uint256 seed) public {
        address[3] memory facets = [A, B, C];
        for (uint256 round; round < 4; ++round) {
            uint256 n = 1 + seed % 4;
            FacetCut[] memory batch = new FacetCut[](n);
            for (uint256 k; k < n; ++k) {
                seed = uint256(keccak256(abi.encode(seed)));
                FacetCutAction action = FacetCutAction(seed % 3);
                address facet = action == FacetCutAction.Remove ? address(0) : facets[(seed >> 8) % 3];
                bytes4[] memory sels = new bytes4[](3);
                uint256 m;
                for (uint256 t; t < 3; ++t) {
                    bytes4 s = bytes4(uint32(0xcccccc00 + ((seed >> (16 + 8 * t)) % 8)));
                    address old = model[s];
                    bool valid = action == FacetCutAction.Add
                        ? old == address(0)
                        : action == FacetCutAction.Replace ? old != address(0) && old != facet : old != address(0);
                    if (!valid) continue;
                    sels[m++] = s;
                    model[s] = facet;
                    twin.sharpCut(s, facet);
                }
                assembly {
                    mstore(sels, m)
                }
                batch[k] = FacetCut(facet, action, sels);
            }
            IDiamondCut(address(diamond)).diamondCut(batch, address(0), "");
        }

        IDiamondLoupe.Facet[] memory got = IDiamondLoupe(address(diamond)).facets();
        IDiamondLoupe.Facet[] memory want = IDiamondLoupe(address(twin)).facets();
        assertEq(got.length, want.length, "same number of facets");
        assertEq(got[0].facetAddress, address(diamond));
        assertEq(want[0].facetAddress, address(twin));
        for (uint256 j; j < got.length; ++j) {
            if (j > 0) assertEq(got[j].facetAddress, want[j].facetAddress, "same facet order");
            assertEq(got[j].functionSelectors.length, want[j].functionSelectors.length);
            for (uint256 i; i < got[j].functionSelectors.length; ++i) {
                assertEq(got[j].functionSelectors[i], want[j].functionSelectors[i], "same selector order");
            }
        }
        for (uint32 s = 0xcccccc00; s < 0xcccccc08; ++s) {
            assertEq(diamond.getTarget(bytes4(s)), model[bytes4(s)]);
        }
    }
}
