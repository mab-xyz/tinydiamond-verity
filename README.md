# tinydiamond-verity

[TinyDiamond](https://github.com/mab-xyz/tiny-diamond) (the core: `TinyDiamond.sol` +
`LibTinyDiamond.sol`, not the optional loupe and diamondCut facets) written in
[Verity](https://github.com/mab-xyz/verity), a Lean 4 language for smart contracts, and compiled by
Verity to EVM bytecode.

- Lean proves 15 properties of the contract (access control, immutable built-ins, routing
  postconditions and frames, fallback reverts, constructor). They use no `sorry` and no axiom
  beyond Lean's standard three.
- Foundry runs the upstream test suites unchanged against the compiled bytecode. It also runs
  differential fuzzing against the Solidity reference and a mutation campaign.

## Files

| File | Content |
|---|---|
| `TinyDiamond/Contract.lean` | The contract (`verity_contract TinyDiamond`) |
| `TinyDiamondCompile.lean` | Compile driver: Yul + ABI + storage layout in `out/` |
| `TinyDiamond/Proofs.lean` | The properties below |
| `TinyDiamond/Routing.lean`, `Frame.lean`, `Packing.lean` | Frame lemmas, a small `Preserves`/`Establishes` calculus, bit lemmas of the packed routing word |
| `test/ref/` | The Solidity reference (`mab-xyz/tiny-diamond@4255439`), used as fixtures and as the differential oracle |
| `test/TinyDiamond.t.sol`, `DiamondLoupe.t.sol`, `DiamondCut.t.sol` | Upstream suites. Only the imports and the deployment (`VerityDeploy.tinyDiamond()`) are changed |
| `test/Differential.t.sol` | Verity diamond vs Solidity diamond on random operation sequences |
| `scripts/build-evm.sh`, `scripts/mutants.sh` | Build the bytecode; mutation testing |

## Same storage layout as the reference

The routing state sits at exactly the slots the Solidity reference uses:

- ERC-7201 namespace `tinydiamond.storage`, with root `S = 0x0abc…4700`:
  - slot `S`: `mapping(bytes4 => {address facet; uint96 position})`, both fields in one word;
  - slot `S+1`: `bytes4[] selectors`, eight per word, with Solidity's packing;
  - slot `S+2`: `mapping(bytes4 => address) restriction`.
- `admin` is in the EIP-1967 admin slot.

The optional reference facets (`DiamondLoupeFacet`, `DiamondCutFacet`) therefore work unchanged on
the Verity diamond: the upstream loupe and diamondCut suites pass against it.

## Properties (Lean)

Every theorem is about the *executable semantics* of the contract: the Lean functions that the
Verity compiler lowers to the bytecode in `out/`. A selector `sel` is handled as its left-aligned
word `toUint256 sel` (the Solidity mapping key). The observables are read the way the contract's
own views read them:

- `targetOf s key`: what `getTarget` and `selectorToFacet` return (`getTarget_eq`, `selectorToFacet_eq`);
- `restrictionOf s key`: what `selectorRestriction` returns (`selectorRestriction_eq`);
- `adminOf s`: what `admin()` returns (`admin_eq`).

`Authorized s` means the caller is the admin or the diamond itself, which is how a facet calls
back into it.

| Theorem | Statement |
|---|---|
| `sharpCut_reverts_of_not_authorized` | An unauthorized `sharpCut` reverts with `"TinyDiamond: caller is not admin"` and changes nothing |
| `restrict_reverts_of_not_authorized` | Same for `restrict` |
| `sharpCut_reverts_of_builtin` | `sharpCut` on one of the six built-in selectors reverts, whoever calls it |
| `restrict_reverts_of_builtin` | Same for `restrict` |
| `sharpCut_routes` | After a successful `sharpCut sel t`, `targetOf sel = t`; `t = 0` removes the route |
| `sharpCut_frame` | …and every other selector's route, every restriction and the admin are unchanged |
| `restrict_sets` | After a successful `restrict sel t`, `restrictionOf sel = t` |
| `restrict_frame` | …and every route, every other restriction and the admin are unchanged |
| `fallback_reverts_of_unrouted` | A call whose `msg.sig` has no route reverts with `"TinyDiamond: selector not found"` |
| `fallback_reverts_of_restricted` | A call to a routed selector that is restricted to another caller reverts with `"TinyDiamond: caller is not allowed"` |
| `constructor_sets_admin` | The deployer becomes the admin |

The frame theorems hold whatever state the selector array is in. Writing the packed `position`
of another selector, which swap-and-pop does, never touches a `facet` field: the bit lemma
`Packing.dec_facet_enc_position` proves this.

`lake env lean scripts/PrintAxioms.lean` lists each theorem's axioms: `propext`,
`Classical.choice` and `Quot.sound` only.

### What the proofs do not cover

- **The forwarding itself.** In Verity, `delegatecall` returns whatever an oracle (an
  `AdversaryModel`) answers, and `revertReturndata` does nothing in the proof model. So no
  theorem states that the facet's returndata or revert payload is forwarded byte for byte. The
  differential tests check this on the bytecode, including payloads whose length is not a
  multiple of 32.
- **The `DiamondCut` event payload.** The contract builds it with `mstore` and emits it with
  `rawLog`, and Verity's model records the log's offset and size but not its bytes. The
  differential tests compare the payloads byte for byte, constructor log included.
- **The packed selector array's own consistency** (it lists exactly the routed selectors,
  positions are right). This is not proved. It is tested by the upstream loupe suite (an
  exhaustive check of about 7k states) and by `testFuzz_ManySelectors`.
- **Gas.**

## Testing the compiled bytecode

```bash
scripts/build-evm.sh     # lake exe tinydiamond-compile out && solc --strict-assembly → out/TinyDiamond.bin
forge test               # 78 tests: upstream (74) + differential (4)
scripts/mutants.sh       # 21 Yul mutants, all must be KILLED
```

- **Upstream suites** (74 tests). The harness was validated first with the *reference* bytecode
  in `out/TinyDiamond.bin`, where all 74 pass.
- **Differential** (`test/Differential.t.sol`). Random sequences of `sharpCut`, `restrict`,
  routed calls, views, `receive`, short calldata, value sent to views and malformed calls run on
  the reference and on the Verity diamond. After every operation, both must agree on:
  - the success flag, the returndata or revert payload, the logs and the balance;
  - every routing slot: the admin, the selector count, the packed selector words plus three
    words past the end, `facetOf` and `restriction`.

  A probe facet covers returndata and revert payloads of odd length, `msg.value` and
  `msg.sender` inside the facet, a facet writing to the diamond's storage, and a facet calling
  `sharpCut` on the diamond itself.
- **Mutation testing** (`scripts/mutants.sh`). Each mutant edits the Yul, for example to drop the
  admin check, the restriction check, the immutability check or the swap-and-pop, to lose the
  revert payload, or to make the fallback non-payable. Each one must make a test fail. All 21
  are killed.

### Known divergence from the Solidity reference

Verity's ABI decoder *masks* a dirty `bytes4` or `address` argument (high bits set) to its width,
where solc's decoder *reverts*. So `sharpCut(0x11223344…dirty, 0xff…ff)` routes to
`address(type(uint160).max)` instead of reverting. `test_DirtyArgumentsAreMasked` pins this
behaviour. It is Verity-wide (`Compiler/CompilationModel/ParamLoading.lean`), not specific to
this contract.

## Verity gaps worked around

These workarounds are kept outside Verity so that this repository builds against the pinned fork:

- `fallback` cannot be declared `payable` and cannot carry a reentrancy disposition.
  `TinyDiamondCompile.lean` patches the compiled spec: `isPayable`, `reentrancyTrusted`.
- No statement returns the raw returndata. The contract uses the ECM
  `SolidityReturnMemory` (`return(0, returndatasize())`).
- No packed `bytes4[]` and no `bytes4` mapping key. The contract declares a `uint256[]` with
  hand-packed words, and adds a `StorageKey (BytesN 4)` instance (the left-aligned word).
- `emit` cannot encode `FacetCut[]`. The contract builds the ABI encoding with `mstore` and
  emits it with `rawLog`.
- Special entrypoints come before functions, so the fallback is written inline rather than
  calling helpers.

## Trust base

- The Lean kernel and Verity's EDSL semantics, which define what the theorems are about.
- The Verity compiler (Lean → Yul), which is not verified end to end for this contract. The
  differential and upstream tests cover this gap on the bytecode.
- `solc --strict-assembly` (Yul → EVM), version 0.8.33.
- The `local_obligations`/`unsafe` blocks in `Contract.lean`, which the Verity trust report flags:
  - raw calldata and returndata handling in the fallback;
  - event encoding in memory.

## Reproduce

```bash
git submodule update --init
lake build                               # contract + proofs (Verity pinned in lakefile.lean)
lake env lean scripts/PrintAxioms.lean
scripts/build-evm.sh && forge test
scripts/mutants.sh
```

Verity is pinned at `mab-xyz/verity@262375bd9`. Building it from scratch takes a long time; a
`.lake` with the Verity packages already built can be reused.

## License

MIT, like TinyDiamond.
