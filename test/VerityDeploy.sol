// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Vm} from "forge-std/Vm.sol";
import {TinyDiamond} from "./ref/TinyDiamond.sol";

/// @notice Deploys the Verity-compiled TinyDiamond from `out/TinyDiamond.bin` (scripts/build-evm.sh).
/// Internal, so the deployer (and thus the admin) is the calling test contract, as with `new TinyDiamond()`.
library VerityDeploy {
    Vm private constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function tinyDiamond() internal returns (TinyDiamond d) {
        bytes memory code = vm.parseBytes(string.concat("0x", vm.readFile("out/TinyDiamond.bin")));
        address addr;
        assembly {
            addr := create(0, add(code, 32), mload(code))
        }
        require(addr != address(0), "deploy failed: TinyDiamond");
        d = TinyDiamond(payable(addr));
    }
}
