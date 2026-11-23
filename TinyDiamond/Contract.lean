import Contracts.Common

namespace Diamond

open Contracts
open Verity hiding pure bind contractAddress BytesN
open Verity.EVM.Uint256

/-- A `bytes4` mapping key is its left-aligned word, as in Solidity and in the compiled code. -/
instance : Contracts.StorageKey (Verity.BytesN 4) where
  toWord key := (Verity.Core.BytesN.toUint256 key).val

/-- `toUint256` of a `bytes4`: its left-aligned word, the value the compiled code holds. -/
def toUint256 (value : Verity.BytesN 4) : Uint256 := Verity.Core.BytesN.toUint256 value

/-!
# TinyDiamond

A selector-routing proxy (EIP-2535 core): the fallback looks up the facet of `msg.sig`, checks
the optional per-selector caller restriction, and `delegatecall`s the facet, forwarding its
returndata or revert payload.

Storage matches the Solidity reference (`test/ref/TinyDiamond.sol`, `LibTinyDiamond.sol`) slot
for slot, so the reference loupe and diamondCut facets work on this diamond:
- ERC-7201 namespace `tinydiamond.storage`, root `S = 0x0abc…4700`:
  - `S`: `mapping(bytes4 => {address facet; uint96 position})`, both in one word;
  - `S+1`: `bytes4[] selectors`, length at `S+1`, eight selectors per word from `keccak(S+1)`,
    selector `i` in bits `32*(i%8)` of word `i/8` (Solidity's packing);
  - `S+2`: `mapping(bytes4 => address) restriction`.
- `admin` in the EIP-1967 admin slot.

Selectors are handled as left-aligned words (`key`), the Solidity mapping-key encoding.

`selectorWords` is declared as a `uint256[]` at `S+1` so that its length word is the selector
count `n` and its data words are the packed words. Only words `0 .. ⌈n/8⌉-1` are used; `push`
and `pop` touch word `n` and `n-1`, which are then unused (zero), see `addSelector` and
`removeSelector`.
-/
verity_contract TinyDiamond where
  storage
    facetOf : MappingStruct(Bytes32,[
      facet : Address @word 0 packed(0,160),
      position : Uint256 @word 0 packed(160,96)
    ]) := slot 0x0abc81caac83e1656ee495fd84f3fd0c2020c41999d182a4a81694a75a694700
    selectorWords : Array Uint256 := slot 0x0abc81caac83e1656ee495fd84f3fd0c2020c41999d182a4a81694a75a694701
    restriction : Bytes32 → Uint256 := slot 0x0abc81caac83e1656ee495fd84f3fd0c2020c41999d182a4a81694a75a694702
    adminSlot : Address := slot 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103

  -- EIP-2535's `FacetCut`; `action` is 0 (Add), 1 (Replace) or 2 (Remove)
  struct FacetCut where
    facetAddress : Address,
    action : Uint8,
    functionSelectors : Array Bytes4

  event_defs
    event DiamondCut(diamondCut : Array FacetCut, init : Address, calldata : Bytes)

  constants
    -- built-in (immutable) selectors, left-aligned
    SEL_SHARP_CUT : Uint256 := 0xaa15ede900000000000000000000000000000000000000000000000000000000
    SEL_RESTRICT : Uint256 := 0x89bf5c0200000000000000000000000000000000000000000000000000000000
    SEL_ADMIN : Uint256 := 0xf851a44000000000000000000000000000000000000000000000000000000000
    SEL_GET_TARGET : Uint256 := 0x374e404700000000000000000000000000000000000000000000000000000000
    SEL_SELECTOR_TO_FACET : Uint256 := 0xae7473ac00000000000000000000000000000000000000000000000000000000
    SEL_SELECTOR_RESTRICTION : Uint256 := 0xff8afdb900000000000000000000000000000000000000000000000000000000
    NO_POSITION : Uint256 := 0
    -- `DiamondCut`'s `_init`: no initializer is called
    NO_INIT : Uint256 := 0
    SELECTOR_MASK : Uint256 := 0xffffffff00000000000000000000000000000000000000000000000000000000
    -- gas forwarded to the facet: all of it (EIP-150 keeps 1/64)
    ALL_GAS : Uint256 := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

  constructor () := do
    let deployer ← msgSender
    setStorageAddr adminSlot deployer
    let me ← contractAddress
    emit "DiamondCut" [[⟨me, 0, [SEL_SHARP_CUT, SEL_RESTRICT, SEL_ADMIN, SEL_GET_TARGET,
      SEL_SELECTOR_TO_FACET, SEL_SELECTOR_RESTRICTION]⟩], NO_INIT, emptyBytes]

  receive := do
    pure ()

  -- Solidity's fallback is `payable`. Its `delegatecall` runs the facet *as* the diamond, so
  -- reentrancy is not a cross-contract question here: the facet is trusted with the whole
  -- storage (README, Security).
  fallback payable reentrancy_trusted local_obligations [selector_routing_proxy := assumed "msg.sig read with calldataload; the facet runs with delegatecall on this storage and its returndata or revert payload is forwarded verbatim, as in the Solidity reference's assembly."] := do
    let key := bitAnd (calldataload 0) SELECTOR_MASK
    let target ← structMember "facetOf" key "facet"
    require (target != zeroAddress) "TinyDiamond: selector not found"
    let r ← getMappingN restriction [key]
    let sender ← msgSender
    require (r == 0 || r == addressToWord sender) "TinyDiamond: caller is not allowed"
    unsafe "forward the whole calldata to the facet" do
      calldatacopy 0 0 calldatasize
    let ok := delegatecall ALL_GAS (addressToWord target) 0 calldatasize 0 0
    if ok == 0 then
      revertReturndata
    else
      unsafe "return the facet's returndata" do
        returndataCopy 0 0 returndataSize
      ecmDo Compiler.ECM.SolidityReturnMemory.module [0, returndataSize]

  -- EIP-2535 `DiamondCut` with one FacetCut of one selector, `_init = 0`, `_calldata = ""`.
  function internal emitCut (facetWord : Uint256, action : Uint256, key : Uint256) : Unit := do
    emit "DiamondCut" [[⟨facetWord, action, [key]⟩], NO_INIT, emptyBytes]

  function internal isBuiltin (key : Uint256) : Bool := do
    return (key == SEL_SHARP_CUT || key == SEL_RESTRICT || key == SEL_ADMIN ||
      key == SEL_GET_TARGET || key == SEL_SELECTOR_TO_FACET || key == SEL_SELECTOR_RESTRICTION)

  function internal requireAdmin () : Unit := do
    let sender ← msgSender
    let adm ← getStorageAddr adminSlot
    let me ← contractAddress
    require (sender == adm || sender == me) "TinyDiamond: caller is not admin"

  -- Packed `bytes4[]`: selector `i` (as a uint32) of the array.
  function internal selectorAt (i : Uint256) : Uint256 := do
    let w ← getStorageArrayElement selectorWords (div i 8)
    return (bitAnd (shr (mul 32 (mod i 8)) w) 0xffffffff)

  -- Overwrites selector `i` with `v` (a uint32), keeping the other seven of its word.
  function internal setSelectorAt (i : Uint256, v : Uint256) : Unit := do
    let j := div i 8
    let s := mul 32 (mod i 8)
    let w ← getStorageArrayElement selectorWords j
    let cleared := sub w (bitAnd w (shl s 0xffffffff))
    setStorageArrayElement selectorWords j (bitOr cleared (shl s v))

  -- Appends `key`; returns its position (index + 1).
  function internal addSelector (key : Uint256) : Uint256 := do
    let n ← getStorageArrayLength selectorWords
    -- push writes 0 to data word n (zero already: n ≥ ⌈(n+1)/8⌉ for n ≥ 1, overwritten for n = 0)
    pushStorageArray selectorWords 0
    setSelectorAt n (shr 224 key)
    return (add n 1)

  -- Swap-and-pop removal of the selector at `position` (index + 1).
  function internal removeSelector (position : Uint256) : Unit := do
    let n ← getStorageArrayLength selectorWords
    let index := sub position 1
    let lastIndex := sub n 1
    if index != lastIndex then
      let last ← selectorAt lastIndex
      setSelectorAt index last
      setStructMember "facetOf" (shl 224 last) "position" position
    setSelectorAt lastIndex 0
    -- pop writes 0 to data word n-1 (unused: n-1 ≥ ⌈n/8⌉ for n ≥ 2, cleared above for n = 1)
    popStorageArray selectorWords

  -- `LibTinyDiamond.cut`: route `key` to `target` (0 removes it), emit `DiamondCut` if it changed.
  function internal cut (key : Uint256, target : Address) : Unit := do
    let builtin ← isBuiltin key
    require (builtin == false) "TinyDiamond: immutable function"
    let old ← structMember "facetOf" key "facet"
    if old != target then
      if old == zeroAddress then
        let position ← addSelector key
        setStructMember "facetOf" key "facet" target
        setStructMember "facetOf" key "position" position
        emitCut (addressToWord target) 0 key
      else
        if target == zeroAddress then
          let position ← structMember "facetOf" key "position"
          removeSelector position
          setStructMember "facetOf" key "facet" zeroAddress
          setStructMember "facetOf" key "position" NO_POSITION
          emitCut 0 2 key
        else
          setStructMember "facetOf" key "facet" target
          emitCut (addressToWord target) 1 key

  function sharpCut (selector : Bytes4, target : Address) : Unit := do
    requireAdmin
    cut (toUint256 selector) target

  function restrict (selector : Bytes4, target : Address) : Unit := do
    requireAdmin
    let key := toUint256 selector
    let builtin ← isBuiltin key
    require (builtin == false) "TinyDiamond: immutable function"
    setMappingN restriction [key] (addressToWord target)

  function admin () : Address := do
    let a ← getStorageAddr adminSlot
    return a

  function getTarget (selector : Bytes4) : Address := do
    let f ← structMember "facetOf" (toUint256 selector) "facet"
    return f

  function selectorToFacet (selector : Bytes4) : Address := do
    let f ← structMember "facetOf" (toUint256 selector) "facet"
    return f

  function selectorRestriction (selector : Bytes4) : Address := do
    let r ← getMappingN restriction [toUint256 selector]
    return (wordToAddress r)

end Diamond
