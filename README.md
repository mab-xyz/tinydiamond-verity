# tinydiamond-verity

[TinyDiamond](https://github.com/mab-xyz/tiny-diamond) (the core: `TinyDiamond.sol` +
`LibTinyDiamond.sol`, not the optional loupe and diamondCut facets) written in
[Verity](https://github.com/mab-xyz/verity), a Lean 4 language for smart contracts, and compiled by
Verity to EVM bytecode.

- Lean proves the routing table correct: access control, immutable built-ins, the exact storage
  effect of every kind of cut (add, replace, remove with swap-and-pop, no-op) on the packed
  selector list, its consistency with the mapping after any sequence of cuts, and the fallback's
  reverts. The proofs use no `sorry`, no `native_decide`/`bv_decide`, and no axiom beyond Lean's
  standard three.
- What Verity's model cannot state (the fallback forwarding calldata, sender, value, result and
  revert data byte for byte) is fuzzed on the compiled bytecode.
- Foundry runs the upstream test suites unchanged against the compiled bytecode. It also runs
  differential fuzzing against the Solidity reference and a mutation campaign.

## Files

| File | Content |
|---|---|
| `TinyDiamond/Contract.lean` | The contract (`verity_contract TinyDiamond`) |
| `TinyDiamondCompile.lean` | Compile driver: Yul + ABI + storage layout in `out/` |
| `TinyDiamond/Proofs.lean` | Access control, built-ins, routing postconditions and frames, fallback reverts |
| `TinyDiamond/Table.lean` | The selector list: exact effect of each cut, consistency, sequences of cuts |
| `TinyDiamond/Routing.lean`, `Frame.lean`, `Packing.lean`, `Lanes.lean` | Frame lemmas, a small `Preserves`/`Establishes` calculus, bit lemmas of the packed routing word and of the 32-bit selector lanes |
| `test/ref/` | The Solidity reference (`mab-xyz/tiny-diamond@4255439`), used as fixtures and as the differential oracle |
| `test/TinyDiamond.t.sol`, `DiamondLoupe.t.sol`, `DiamondCut.t.sol` | Upstream suites. Only the imports and the deployment (`VerityDeploy.tinyDiamond()`) are changed |
| `test/Differential.t.sol` | Verity diamond vs Solidity diamond on random operation sequences |
| `test/Dispatch.t.sol` | Fallback forwarding (exact calldata, sender, value, result, revert data), fuzzed |
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

### The 14 routing-table and dispatch properties

Each property of the specification maps to a theorem, or to a fuzzed test when Verity's model cannot
state it. "Consistent" is property 3 (`Table.Consistent`); `n` is the selector count; positions
are slot + 1.

Routing table:

1. After any sequence of `sharpCut`s by the admin (not only 3) from an empty table, every selector
   routes to the target of the last cut that touched it, or to nothing; `getTarget` and
   `selectorToFacet` agree. `Table.cuts_from_empty`; from any consistent table:
   `Table.cuts_sequence` (each cut provably succeeds: `Table.sharpCut_step`).
2. Those cuts change no restriction and not the admin. `Table.cuts_sequence`.
3. After those cuts the list is consistent with the mapping: every listed selector is routed and
   its position matches its slot; no selector is listed twice (`Consistent.no_duplicates`); a
   selector is routed exactly when it has a position, which points back to it.
   `Table.cuts_sequence`, from per-cut preservation `consistent_add`/`_replace`/`_remove`.
4. Cutting one selector leaves every other selector's facet and restriction unchanged.
   `Proofs.sharpCut_frame`.
5. None of the six built-ins can be routed or restricted, whatever the caller and target. The
   built-ins are an independent list of selectors written from their signatures
   (`Table.specBuiltinSelectors`). `Table.builtins_immutable`.
6. A caller who is neither the admin nor the diamond changes nothing: both `sharpCut` and
   `restrict` revert. `Proofs.*_reverts_of_not_authorized`, `Table.unauthorized_cut_noop`.

Table consistency, for any number of selectors. Each theorem assumes consistency only on the
entries the cut touches, and states every storage word that changes. Packed words shared with
neighbouring lanes are covered by the per-lane statements.

7. Add: the selector gets the facet, position `n+1` and slot `n`, and the length becomes `n+1`.
   Every other routing word, every other slot and every other storage word is unchanged.
   `Table.sharpCut_add`.
8. Replace: the facet changes. Its position, the length, the whole list and every other word are
   unchanged. `Table.sharpCut_replace`.
9. Remove: the selector's routing word is cleared and the length becomes `n-1`.
   - If it was not last, the last selector moves into its slot, keeps its facet and gets its
     position.
   - The vacated slot is cleared, and every other slot and word is unchanged.

   `Table.sharpCut_remove`.
10. No-op (target equals the current facet): nothing changes, not even an event.
    `Table.sharpCut_noop`.

Fallback dispatch:

11. A routed call that the restriction allows reaches the facet with exactly the original
    calldata, sender and value, and returns the facet's result. Tested in
    `test/Dispatch.t.sol` `testFuzz_RoutedCallForwardsExactly`; see below for why there is no
    theorem.
12. When the facet reverts, the diamond reverts with exactly the same revert data, of any length.
    Tested in `testFuzz_RevertDataForwardedExactly`.
13. A routed call from anyone other than the restricted caller reverts with "caller is not
    allowed". `Proofs.fallback_reverts_of_restricted`; fuzzed by
    `testFuzz_RestrictedCallerOnly`.
14. A call to any unrouted, non-built-in selector reverts with "selector not found".
    `Proofs.fallback_reverts_of_unrouted`; fuzzed by `testFuzz_UnroutedSelectorNotFound`.

The list lemmas use exact `Uint256` expressions of the contract's packing code:
`Lanes.lane_setLane` proves that writing lane `r` sets lane `r` and keeps the other seven.

### What the proofs do not cover

- **The forwarding itself (properties 11, 12).** Verity's model cannot state it:
  - `delegatecall` returns whatever an oracle (an `AdversaryModel`) answers;
  - `revertReturndata` does nothing in the proof model;
  - the success path returns through an ECM that the model treats as a static call.

  `test/Dispatch.t.sol` and the differential tests check forwarding on the bytecode, including
  payloads whose length is not a multiple of 32.
- **The `DiamondCut` event payload.** The contract builds it with `mstore` and emits it with
  `rawLog`, and Verity's model records the log's offset and size but not its bytes. The
  differential tests compare the payloads byte for byte, constructor log included.
- **Selector counts near `2^95`.** The list theorems assume fewer than `2^95` selectors, far
  below the `2^32` distinct selectors that can exist.
- **Gas.**

## Testing the compiled bytecode

```bash
scripts/build-evm.sh     # lake exe tinydiamond-compile out && solc --strict-assembly → out/TinyDiamond.bin
forge test               # 82 tests: upstream (74) + differential (4) + dispatch (4)
scripts/mutants.sh       # 23 Yul mutants, all must be KILLED
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
  revert payload, to truncate the forwarded calldata, to `call` the facet instead of
  `delegatecall`ing it, or to make the fallback non-payable. Each one must make a test fail. All
  23 are killed.
- **Dispatch** (`test/Dispatch.t.sol`, properties 11–14, 1024 fuzz runs each). An echo facet
  returns `abi.encode(msg.sender, msg.value, msg.data)` and a second facet reverts with arbitrary
  bytes. The diamond must forward both exactly, under random selectors, calldata, values,
  callers and restrictions.

### Dirty ABI arguments

A dirty `bytes4` or `address` argument (bits set beyond its width) reverts with empty data, as
solc's ABI decoder does: `test_DirtyArgumentsRevertLikeSolc` checks both against each other. Verity
validates scalar arguments since lfglabs-dev/verity#2798; before, it masked them, so
`sharpCut(0x11223344…dirty, 0xff…ff)` routed to `address(type(uint160).max)`.

## Verity gaps worked around

These workarounds are kept outside Verity so that this repository builds against upstream Verity:

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

Verity is pinned at upstream `lfglabs-dev/verity@45578f33a` (main); no fork feature is needed. Building it from scratch takes a long time; a
`.lake` with the Verity packages already built can be reused.

## License

MIT, like TinyDiamond.
