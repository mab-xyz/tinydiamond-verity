// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IDiamond, LibTinyDiamond} from "./LibTinyDiamond.sol";

/// @notice EIP-2535 `IDiamondCut`: the standard batch upgrade function.
interface IDiamondCut is IDiamond {
    /// @notice Add/replace/remove any number of functions and optionally execute
    ///         a function with delegatecall
    /// @param _diamondCut Contains the facet addresses and function selectors
    /// @param _init The address of the contract or facet to execute _calldata
    /// @param _calldata A function call, including function selector and arguments
    ///                  _calldata is executed with delegatecall on _init
    function diamondCut(FacetCut[] calldata _diamondCut, address _init, bytes calldata _calldata) external;
}

/**
 * @title DiamondCutFacet
 * @notice Optional facet giving TinyDiamond the standard `diamondCut`. Deploy once, then route it:
 * `diamond.sharpCut(IDiamondCut.diamondCut.selector, address(cutFacet))`.
 * Only the diamond's admin (EIP-1967 admin slot) or the diamond itself may call it.
 * The whole batch is applied atomically, recorded in one `DiamondCut` event, then `_init` runs.
 */
contract DiamondCutFacet is IDiamondCut {
    function diamondCut(FacetCut[] calldata _diamondCut, address _init, bytes calldata _calldata) external {
        require(
            msg.sender == LibTinyDiamond.admin() || msg.sender == address(this), "TinyDiamond: caller is not admin"
        );
        LibTinyDiamond.Layout storage l = LibTinyDiamond.layout();

        for (uint256 i; i < _diamondCut.length; ++i) {
            FacetCut calldata c = _diamondCut[i];
            address facet = c.facetAddress;
            if (c.action == FacetCutAction.Remove) {
                require(facet == address(0), "DiamondCut: remove facet must be address(0)");
            } else {
                require(facet != address(0), "DiamondCut: facet is address(0)");
            }
            for (uint256 j; j < c.functionSelectors.length; ++j) {
                bytes4 selector = c.functionSelectors[j];
                address old = l.facetOf[selector].facet;
                if (c.action == FacetCutAction.Add) {
                    require(old == address(0), "DiamondCut: function already exists");
                } else if (c.action == FacetCutAction.Replace) {
                    require(old != address(0), "DiamondCut: function does not exist");
                    require(old != facet, "DiamondCut: function already on this facet");
                } else {
                    require(old != address(0), "DiamondCut: function does not exist");
                }
                LibTinyDiamond.route(selector, facet);
            }
        }
        LibTinyDiamond.emitDiamondCut(_diamondCut, _init, _calldata);

        if (_init == address(0)) return;
        require(_init.code.length > 0, "DiamondCut: _init has no code");
        (bool ok, bytes memory err) = _init.delegatecall(_calldata);
        if (!ok) {
            if (err.length == 0) revert("DiamondCut: _init reverted");
            assembly {
                revert(add(err, 32), mload(err))
            }
        }
    }
}
