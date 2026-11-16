// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {LibTinyDiamond} from "./LibTinyDiamond.sol";

/// @notice EIP-2535 loupe: the functions that look at a diamond.
interface IDiamondLoupe {
    struct Facet {
        address facetAddress;
        bytes4[] functionSelectors;
    }

    function facets() external view returns (Facet[] memory facets_);
    function facetFunctionSelectors(address _facet) external view returns (bytes4[] memory facetFunctionSelectors_);
    function facetAddresses() external view returns (address[] memory facetAddresses_);
    function facetAddress(bytes4 _functionSelector) external view returns (address facetAddress_);
}

interface IERC165 {
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

/**
 * @title DiamondLoupeFacet
 * @notice Optional introspection facet for TinyDiamond. Deploy once, then route its five selectors
 * (the four loupe functions and `supportsInterface`) with `sharpCut`. It only reads the diamond's
 * ERC-7201 routing state; the diamond's built-in functions are reported with the diamond's own
 * address as facet, as EIP-2535 requires for immutable functions.
 */
contract DiamondLoupeFacet is IDiamondLoupe, IERC165 {
    function facets() external view returns (Facet[] memory facets_) {
        LibTinyDiamond.Layout storage l = LibTinyDiamond.layout();
        bytes4[] memory builtins = LibTinyDiamond.builtinSelectors();
        uint256 n = l.selectors.length;

        // Worst case: one facet per routed selector, plus the diamond itself
        address[] memory addrs = new address[](n + 1);
        bytes4[][] memory sels = new bytes4[][](n + 1);
        uint256[] memory counts = new uint256[](n + 1);

        addrs[0] = address(this);
        sels[0] = new bytes4[](n + builtins.length);
        for (uint256 i; i < builtins.length; ++i) {
            sels[0][i] = builtins[i];
        }
        counts[0] = builtins.length;
        uint256 numFacets = 1;

        for (uint256 i; i < n; ++i) {
            bytes4 selector = l.selectors[i];
            address facet = l.facetOf[selector].facet;
            uint256 j;
            while (j < numFacets && addrs[j] != facet) ++j;
            if (j == numFacets) {
                addrs[j] = facet;
                sels[j] = new bytes4[](n);
                ++numFacets;
            }
            sels[j][counts[j]++] = selector;
        }

        facets_ = new Facet[](numFacets);
        for (uint256 j; j < numFacets; ++j) {
            bytes4[] memory s = sels[j];
            uint256 c = counts[j];
            assembly {
                mstore(s, c) // shrink to the used length
            }
            facets_[j] = Facet(addrs[j], s);
        }
    }

    function facetFunctionSelectors(address _facet) external view returns (bytes4[] memory facetFunctionSelectors_) {
        if (_facet == address(0)) return facetFunctionSelectors_;
        LibTinyDiamond.Layout storage l = LibTinyDiamond.layout();
        bytes4[] memory builtins = LibTinyDiamond.builtinSelectors();
        uint256 n = l.selectors.length;
        uint256 c;
        if (_facet == address(this)) {
            facetFunctionSelectors_ = new bytes4[](n + builtins.length);
            for (; c < builtins.length; ++c) {
                facetFunctionSelectors_[c] = builtins[c];
            }
        } else {
            facetFunctionSelectors_ = new bytes4[](n);
        }
        for (uint256 i; i < n; ++i) {
            bytes4 selector = l.selectors[i];
            if (l.facetOf[selector].facet == _facet) facetFunctionSelectors_[c++] = selector;
        }
        assembly {
            mstore(facetFunctionSelectors_, c)
        }
    }

    function facetAddresses() external view returns (address[] memory facetAddresses_) {
        LibTinyDiamond.Layout storage l = LibTinyDiamond.layout();
        uint256 n = l.selectors.length;
        facetAddresses_ = new address[](n + 1);
        facetAddresses_[0] = address(this);
        uint256 c = 1;
        for (uint256 i; i < n; ++i) {
            address facet = l.facetOf[l.selectors[i]].facet;
            uint256 j;
            while (j < c && facetAddresses_[j] != facet) ++j;
            if (j == c) facetAddresses_[c++] = facet;
        }
        assembly {
            mstore(facetAddresses_, c)
        }
    }

    function facetAddress(bytes4 _functionSelector) external view returns (address facetAddress_) {
        if (LibTinyDiamond.isBuiltin(_functionSelector)) return address(this);
        return LibTinyDiamond.layout().facetOf[_functionSelector].facet;
    }

    /// @notice ERC-165, IDiamondLoupe, and IDiamondCut (its id is `diamondCut.selector`) while that function is routed
    function supportsInterface(bytes4 interfaceId) external view returns (bool) {
        if (interfaceId == type(IERC165).interfaceId || interfaceId == type(IDiamondLoupe).interfaceId) return true;
        return interfaceId == DIAMOND_CUT_SELECTOR
            && LibTinyDiamond.layout().facetOf[DIAMOND_CUT_SELECTOR].facet != address(0);
    }

    // bytes4(keccak256("diamondCut((address,uint8,bytes4[])[],address,bytes)"))
    bytes4 private constant DIAMOND_CUT_SELECTOR = 0x1f931c1c;
}
