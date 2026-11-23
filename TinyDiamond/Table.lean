import TinyDiamond.Proofs
import TinyDiamond.Lanes

/-!
# The routing table: the selector list and its consistency with the mapping

The selector list is `storageArray (S+1)`: its length is the selector count `n`, and word `j`
packs lanes `8j .. 8j+7` (`Lanes`). This file gives the exact effect of each helper on that
list, then of each branch of `cut` (Add, Replace, Remove, No-op) on the whole table.
-/

namespace Diamond.Table

open Verity
open Contracts
open Diamond
open Diamond.Frame
open Diamond.Packing
open Diamond.Routing
open Diamond.Lanes
open Diamond.Proofs
open private storageArraySetAt storageArrayDropLast? from Verity.Core

theorem setAt_eq (ws : List Uint256) (i : Nat) (v : Uint256) :
    storageArraySetAt ws i v = if i < ws.length then some (ws.set i v) else none := by
  induction ws generalizing i with
  | nil => simp [storageArraySetAt]
  | cons h t ih =>
    cases i with
    | zero => simp [storageArraySetAt]
    | succ i =>
      simp only [storageArraySetAt, ih, List.length_cons]
      by_cases hi : i < t.length <;> simp [hi, Bind.bind, Option.bind]

theorem dropLast_eq (ws : List Uint256) :
    storageArrayDropLast? ws = if ws = [] then none else some ws.dropLast := by
  induction ws with
  | nil => simp [storageArrayDropLast?]
  | cons h t ih =>
    cases t with
    | nil => simp [storageArrayDropLast?]
    | cons h2 t2 =>
      simp only [storageArrayDropLast?] at ih ⊢
      simp [ih, Bind.bind, Option.bind]

abbrev WORDS : Nat := TinyDiamond.selectorWords.slot

/-- The selector list's storage words. -/
def words (s : ContractState) : List Uint256 := s.storageArray WORDS

/-- `s` with the selector list's words replaced by `ws`. -/
def withWords (s : ContractState) (ws : List Uint256) : ContractState :=
  { s with storageArray := fun sl => if sl == WORDS then ws else s.storageArray sl }

@[simp] theorem words_withWords (s : ContractState) (ws : List Uint256) :
    words (withWords s ws) = ws := by simp [words, withWords]

@[simp] theorem storageWords_withWords (s : ContractState) (ws : List Uint256) :
    (withWords s ws).storageWords = s.storageWords := rfl

def wordAt (ws : List Uint256) (j : Nat) : Uint256 := ws.getD j 0

/-- Selector `i` (a uint32) of a packed word list. -/
def laneAt (ws : List Uint256) (i : Nat) : Uint256 := laneU (wordAt ws (i / 8)) (i % 8)

/-- `ws` with selector `i` replaced by `v`. -/
def setLaneAt (ws : List Uint256) (i : Nat) (v : Uint256) : List Uint256 :=
  ws.set (i / 8) (setLaneU (wordAt ws (i / 8)) (i % 8) v)

theorem length_setLaneAt (ws : List Uint256) (i : Nat) (v : Uint256) :
    (setLaneAt ws i v).length = ws.length := by simp [setLaneAt]

theorem laneAt_setLaneAt (ws : List Uint256) (i j : Nat) (v : Uint256)
    (hi : i / 8 < ws.length) (hv : v.val < 2 ^ 32) :
    laneAt (setLaneAt ws i v) j = if j = i then v else laneAt ws j := by
  unfold laneAt setLaneAt wordAt
  by_cases hw : j / 8 = i / 8
  · rw [hw, List.getD_eq_getElem?_getD, List.getElem?_set_self hi, Option.getD_some,
      lane_setLane _ _ _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hv]
    by_cases hj : j = i
    · simp [hj]
    · have : i % 8 ≠ j % 8 := fun h => hj (by omega)
      simp [hj, this]
  · have hj : j ≠ i := fun h => hw (by rw [h])
    rw [if_neg hj, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hw),
      ← List.getD_eq_getElem?_getD]

theorem div8_val (i : Uint256) : (EVM.Uint256.div i 8).val = i.val / 8 := by
  have hi : i.val < 2 ^ 256 := i.isLt
  have h8 : (8 : Uint256).val = 8 := rfl
  simp only [EVM.Uint256.div, Verity.Core.Uint256.div, h8]
  simp only [show (8 : Nat) ≠ 0 from by decide, if_false, Verity.Core.Uint256.val_ofNat,
    modulus_eq]
  exact Nat.mod_eq_of_lt (by omega)

theorem shift_eq (i : Uint256) :
    EVM.Uint256.mul 32 (EVM.Uint256.mod i 8) = Verity.Core.Uint256.ofNat (32 * (i.val % 8)) := by
  apply Verity.Core.Uint256.ext
  have h8 : (8 : Uint256).val = 8 := rfl
  have h32 : (32 : Uint256).val = 32 := rfl
  simp only [EVM.Uint256.mul, EVM.Uint256.mod, Verity.Core.Uint256.mul, Verity.Core.Uint256.mod,
    h8, h32, Verity.Core.Uint256.val_ofNat, modulus_eq]
  simp only [show (8 : Nat) ≠ 0 from by decide, if_false]
  have : i.val % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [Verity.Core.Uint256.val_ofNat, modulus_eq]
  rw [Nat.mod_eq_of_lt (by omega : i.val % 8 < 2 ^ 256)]

theorem selectorAt_eq (s : ContractState) (i : Uint256) (h : i.val / 8 < (words s).length) :
    TinyDiamond.selectorAt i s = ContractResult.success (laneAt (words s) i.val) s := by
  have hg : (words s)[i.val / 8]? = some (wordAt (words s) (i.val / 8)) := by
    simp [wordAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  simp only [TinyDiamond.selectorAt, Bind.bind, Verity.bind, getStorageArrayElement,
    ContractState.readArray]
  unfold words at hg
  rw [div8_val, hg, shift_eq]
  rfl

theorem setSelectorAt_eq (s : ContractState) (i v : Uint256) (h : i.val / 8 < (words s).length) :
    TinyDiamond.setSelectorAt i v s =
      ContractResult.success () (withWords s (setLaneAt (words s) i.val v)) := by
  have hg : (words s)[i.val / 8]? = some (wordAt (words s) (i.val / 8)) := by
    simp [wordAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  simp only [TinyDiamond.setSelectorAt, Bind.bind, Verity.bind, getStorageArrayElement,
    setStorageArrayElement, ContractState.readArray]
  unfold words at hg h
  rw [div8_val, hg]
  dsimp only
  rw [setAt_eq]
  simp only [show TinyDiamond.selectorWords.slot = WORDS from rfl, if_pos h, shift_eq]
  rfl

@[simp] theorem withWords_withWords (s : ContractState) (a b : List Uint256) :
    withWords (withWords s a) b = withWords s b := by
  simp only [withWords]; congr 1; funext sl; split <;> rfl

theorem ofNat_val_of_lt (n : Nat) (h : n < 2 ^ 256) : (Verity.Core.Uint256.ofNat n).val = n := by
  simp only [Verity.Core.Uint256.val_ofNat, modulus_eq]; exact Nat.mod_eq_of_lt h

/-- `addSelector key`: appends lane `n` = `key >> 224` and returns the position `n + 1`. -/
theorem addSelector_eq (s : ContractState) (key : Uint256) (hn : (words s).length < 2 ^ 255) :
    TinyDiamond.addSelector key s =
      ContractResult.success (Verity.Core.Uint256.ofNat ((words s).length + 1))
        (withWords s (setLaneAt (words s ++ [0]) (words s).length (EVM.Uint256.shr 224 key))) := by
  have hlen : (Verity.Core.Uint256.ofNat (words s).length).val = (words s).length :=
    ofNat_val_of_lt _ (by omega)
  have hpush : pushStorageArray TinyDiamond.selectorWords (0 : Uint256) s =
      ContractResult.success () (withWords s (words s ++ [0])) := rfl
  have hset := setSelectorAt_eq (withWords s (words s ++ [0]))
    (Verity.Core.Uint256.ofNat (words s).length) (EVM.Uint256.shr 224 key)
    (by rw [hlen, words_withWords, List.length_append]; simp; omega)
  simp only [TinyDiamond.addSelector, Bind.bind, Verity.bind, getStorageArrayLength,
    ContractState.readArray]
  rw [hpush]
  dsimp only
  rw [show s.storageArray TinyDiamond.selectorWords.slot = words s from rfl, hset]
  simp only [words_withWords, withWords_withWords, hlen]
  show ContractResult.success _ _ = _
  congr 1
  apply Verity.Core.Uint256.ext
  have h1 : (1 : Uint256).val = 1 := rfl
  simp only [EVM.Uint256.add, Verity.Core.Uint256.add, hlen, h1]

theorem bind_success {α β : Type} {c : Contract α} {f : α → Contract β} {s s' : ContractState}
    {a : α} (h : c s = ContractResult.success a s') : Verity.bind c f s = f a s' := by
  simp [Verity.bind, h]

theorem bindM_success {α β : Type} {c : Contract α} {f : α → Contract β} {s s' : ContractState}
    {a : α} (h : c s = ContractResult.success a s') : (c >>= f) s = f a s' :=
  bind_success h

theorem withWords_self (s : ContractState) : withWords s (words s) = s := by
  simp only [withWords, words]
  congr 1; funext sl; by_cases h : (sl == WORDS) = true
  · simp [h]; rw [beq_iff_eq.mp h]
  · simp [h]

/-- What `setStructMember "facetOf" k "position" p` does. -/
def setPos (s : ContractState) (k p : Uint256) : ContractState :=
  s.writeMapChain FACETS [k.val] 0 (enc (s.readMapChain FACETS [k.val] 0) p 160 96)

theorem setPosition_eq (s : ContractState) (k p : Uint256) :
    TinyDiamond.setStructMember "facetOf" k "position" p s =
      ContractResult.success () (setPos s k p) := by
  simp only [TinyDiamond.setStructMember]
  rw [if_neg (by decide), if_pos (by decide), setStructMemberAt_eq]
  rfl

theorem setPos_withWords (s : ContractState) (ws : List Uint256) (k p : Uint256) :
    setPos (withWords s ws) k p = withWords (setPos s k p) ws := rfl

@[simp] theorem words_setPos (s : ContractState) (k p : Uint256) :
    words (setPos s k p) = words s := rfl

theorem sub1_val (a : Uint256) (h : 1 ≤ a.val) : (EVM.Uint256.sub a 1).val = a.val - 1 := by
  have h1 : (1 : Uint256).val = 1 := rfl
  have ha : a.val < 2 ^ 256 := a.isLt
  simp only [EVM.Uint256.sub, Verity.Core.Uint256.sub, h1, if_pos h,
    Verity.Core.Uint256.val_ofNat, modulus_eq]
  exact Nat.mod_eq_of_lt (by omega)

/-- `removeSelector p` with `1 ≤ p ≤ n`: the last selector moves to index `p - 1` (and gets
position `p`) unless it is the one removed; the last lane is cleared and the list shortened. -/
theorem removeSelector_eq (s : ContractState) (p : Uint256)
    (hp : 1 ≤ p.val) (hpn : p.val ≤ (words s).length) (hn : (words s).length < 2 ^ 255) :
    TinyDiamond.removeSelector p s =
      let ws := words s
      let last := ws.length - 1
      let moved := laneAt ws last
      if p.val - 1 = last then
        ContractResult.success () (withWords s (setLaneAt ws last 0).dropLast)
      else
        ContractResult.success ()
          (withWords (setPos s (EVM.Uint256.shl 224 moved) p)
            (setLaneAt (setLaneAt ws (p.val - 1) moved) last 0).dropLast) := by
  dsimp only
  set ws := words s with hws
  set last := ws.length - 1 with hlastdef
  set moved := laneAt ws last
  have hL : 1 ≤ ws.length := by omega
  have hlen : (Verity.Core.Uint256.ofNat ws.length).val = ws.length :=
    ofNat_val_of_lt _ (by omega)
  have hidx := sub1_val p hp
  have hlast : (EVM.Uint256.sub (Verity.Core.Uint256.ofNat ws.length) 1).val = last := by
    rw [sub1_val _ (by rw [hlen]; exact hL), hlen]
  have hpop : ∀ (t : ContractState) (vs : List Uint256), vs ≠ [] →
      popStorageArray TinyDiamond.selectorWords (withWords t vs) =
        ContractResult.success () (withWords t vs.dropLast) := by
    intro t vs hvs
    simp only [popStorageArray, ContractState.readArray, ContractState.writeArray]
    rw [show (withWords t vs).storageArray TinyDiamond.selectorWords.slot = vs by
      simp [withWords], dropLast_eq, if_neg hvs]
    simp only [withWords, show TinyDiamond.selectorWords.slot = WORDS from rfl]
    have hf : (fun sl => if (sl == WORDS) = true then vs.dropLast else
        if (sl == WORDS) = true then vs else t.storageArray sl) =
        (fun sl => if (sl == WORDS) = true then vs.dropLast else t.storageArray sl) := by
      funext sl; by_cases h : (sl == WORDS) = true <;> simp [h]
    rw [hf]
  have hne : ∀ vs : List Uint256, vs.length = ws.length → vs ≠ [] := by
    intro vs h he; subst he; simp at h; omega
  simp only [TinyDiamond.removeSelector, Bind.bind, Verity.bind, getStorageArrayLength,
    ContractState.readArray]
  rw [show s.storageArray TinyDiamond.selectorWords.slot = ws from rfl]
  have hsetLast : ∀ t : ContractState, words t = ws → ∀ vs : List Uint256,
      vs.length = ws.length →
      TinyDiamond.setSelectorAt (EVM.Uint256.sub (Verity.Core.Uint256.ofNat ws.length) 1) 0
        (withWords t vs) = ContractResult.success () (withWords t (setLaneAt vs last 0)) := by
    intro t _ vs hvs
    rw [setSelectorAt_eq _ _ _ (by rw [words_withWords, hlast, hvs]; omega), words_withWords,
      hlast, withWords_withWords]
  by_cases heq : p.val - 1 = last
  · rw [if_pos heq]
    have hcond : (EVM.Uint256.sub p 1 != EVM.Uint256.sub (Verity.Core.Uint256.ofNat ws.length) 1)
        = false := by
      have : EVM.Uint256.sub p 1 = EVM.Uint256.sub (Verity.Core.Uint256.ofNat ws.length) 1 :=
        Verity.Core.Uint256.ext (by rw [hidx, hlast, heq])
      simp [this]
    rw [hcond, if_neg (by decide), bind_success (rfl : (Pure.pure () : Contract Unit) s = _)]
    conv_lhs => rw [← withWords_self s]
    rw [bind_success (hsetLast s rfl ws rfl), hpop _ _ (hne _ (length_setLaneAt _ _ _))]
  · rw [if_neg heq]
    have hcond : (EVM.Uint256.sub p 1 != EVM.Uint256.sub (Verity.Core.Uint256.ofNat ws.length) 1)
        = true := by
      have : EVM.Uint256.sub p 1 ≠ EVM.Uint256.sub (Verity.Core.Uint256.ofNat ws.length) 1 :=
        fun h => heq (by rw [← hidx, ← hlast, h])
      simp [this]
    rw [hcond, if_pos rfl]
    have hsel := selectorAt_eq s (EVM.Uint256.sub (Verity.Core.Uint256.ofNat ws.length) 1)
      (by rw [hlast]; show last / 8 < ws.length; omega)
    rw [hlast] at hsel
    rw [bind_success hsel]
    have hset1 := setSelectorAt_eq s (EVM.Uint256.sub p 1) moved
      (by rw [hidx]; show (p.val - 1) / 8 < ws.length; omega)
    rw [hidx] at hset1
    rw [bind_success hset1, bind_success (setPosition_eq _ _ _), setPos_withWords,
      bind_success (hsetLast (setPos s (EVM.Uint256.shl 224 (laneAt (words s) last)) p)
        (by rw [words_setPos]) (setLaneAt (words s) (p.val - 1) moved) (length_setLaneAt _ _ _)),
      hpop _ _ (hne _ (by simp [length_setLaneAt, hws]))]

/-- The routing word of key `k` (facet in bits 0..159, position in bits 160..255). -/
def entry (s : ContractState) (k : Uint256) : Uint256 := s.readMapChain FACETS [k.val] 0

/-- What `setStructMember "facetOf" k "facet" t` does. -/
def setFacetSt (s : ContractState) (k : Uint256) (t : Address) : ContractState :=
  s.writeMapChain FACETS [k.val] 0 (enc (entry s k) (addressToWord t) 0 160)

theorem setFacet_eq (s : ContractState) (k : Uint256) (t : Address) :
    TinyDiamond.setStructMember "facetOf" k "facet" t s =
      ContractResult.success () (setFacetSt s k t) := by
  simp only [TinyDiamond.setStructMember]
  rw [if_pos (by decide), setStructMemberAt_eq]
  rfl

/-- Storage (words and arrays), caller and own address of two states agree. -/
def SameStorage (a b : ContractState) : Prop :=
  a.storageWords = b.storageWords ∧ a.storageArray = b.storageArray ∧
    a.sender = b.sender ∧ a.thisAddress = b.thisAddress

/-- The `DiamondCut` event `emitCut facet action key` logs: one `FacetCut` with one selector,
`_init = 0`, `_calldata = ""`. Each argument's ABI encoding, in order: the `FacetCut[]` tail (one
cut at offset `0x20`; facet, action, selectors offset `0x60`; one selector), `_init`, and the empty
`bytes` (length 0). Leaves are cleaned as solc does: the facet to 160 bits, the action to 8 bits,
the selector to its high 4 bytes. -/
def cutEvent (facet action key : Uint256) : Event where
  name := "DiamondCut"
  args := [1, 32, facet.val % 2 ^ 160, action.val % 2 ^ 8, 96, 1,
    key.val / 2 ^ 224 % 2 ^ 32 * 2 ^ 224, 0, 0].map Verity.Core.Uint256.ofNat
  indexedArgs := []

/-- `emitCut` appends `cutEvent` to the log and changes nothing else. -/
theorem emitCut_eq (f a k : Uint256) (s : ContractState) :
    TinyDiamond.emitCut f a k s =
      ContractResult.success () { s with events := s.events ++ [cutEvent f a k] } := by
  simp [TinyDiamond.emitCut, cutEvent, Contracts.emitEncoded,
    Compiler.CompilationModel.abiLitWords, Compiler.CompilationModel.abiLitEncode,
    Compiler.CompilationModel.abiLitEncodeItems, Compiler.CompilationModel.abiLitLayoutSeq,
    Compiler.CompilationModel.abiLitBaseType, Compiler.CompilationModel.abiLitLeafType?,
    Compiler.CompilationModel.abiLitNormalizeWord, Compiler.CompilationModel.isDynamicParamType,
    Compiler.CompilationModel.isDynamicParamTypeList,
    TinyDiamond.__eventParamTypes_DiamondCut, TinyDiamond.NO_INIT,
    Pure.pure, Except.pure, Bind.bind, Except.bind]
  rfl

theorem emitCut_ok (f a k : Uint256) (s : ContractState) :
    ∃ s', TinyDiamond.emitCut f a k s = ContractResult.success () s' ∧ SameStorage s' s ∧
      s'.events = s.events ++ [cutEvent f a k] :=
  ⟨_, emitCut_eq f a k s, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩

theorem isBuiltin_false (k : Uint256) (s : ContractState) (h : k ∉ builtinKeys) :
    TinyDiamond.isBuiltin k s = ContractResult.success false s := by
  simp only [builtinKeys, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [TinyDiamond.isBuiltin, Pure.pure, Verity.pure]
  simp [h1, h2, h3, h4, h5, h6]

theorem setFacetSt_withWords (s : ContractState) (ws : List Uint256) (k : Uint256) (t : Address) :
    setFacetSt (withWords s ws) k t = withWords (setFacetSt s k t) ws := rfl

theorem cut_prefix (s : ContractState) (key : Uint256) (hb : key ∉ builtinKeys)
    (k : Address → Contract Unit) :
    (do
      let builtin ← TinyDiamond.isBuiltin key
      Verity.require (builtin == false) "TinyDiamond: immutable function"
      let old ← TinyDiamond.structMember (α := Address) "facetOf" key "facet"
      k old) s = k (targetOf s key) s := by
  rw [show (Bind.bind (TinyDiamond.isBuiltin key) _ : Contract Unit) s = _ from
    bind_success (isBuiltin_false key s hb)]
  rw [show (Bind.bind (Verity.require (false == false) _) _ : Contract Unit) s = _ from
    bind_success (rfl : Verity.require (false == false) _ s = _)]
  exact bind_success (readFacet_state key s)

theorem cut_add (s : ContractState) (key : Uint256) (t : Address) (hb : key ∉ builtinKeys)
    (h0 : targetOf s key = zeroAddress) (ht : t ≠ zeroAddress)
    (hn : (words s).length < 2 ^ 255) :
    ∃ s', TinyDiamond.cut key t s = ContractResult.success () s' ∧
      SameStorage s' (withWords
        (setPos (setFacetSt s key t) key (Verity.Core.Uint256.ofNat ((words s).length + 1)))
        (setLaneAt (words s ++ [0]) (words s).length (EVM.Uint256.shr 224 key))) ∧
      s'.events = s.events ++ [cutEvent (addressToWord t) 0 key] := by
  unfold TinyDiamond.cut
  rw [cut_prefix s key hb, h0]
  have c1 : (zeroAddress != t) = true := by simpa using Ne.symm ht
  rw [if_pos c1, if_pos (by simp)]
  rw [bindM_success (addSelector_eq s key hn), bindM_success (setFacet_eq _ _ _),
    setFacetSt_withWords, bindM_success (setPosition_eq _ _ _), ← setPos_withWords]
  exact emitCut_ok _ _ _ _

/-- The state `removeSelector p` produces (see `removeSelector_eq`). -/
def removeState (s : ContractState) (p : Uint256) : ContractState :=
  let ws := words s
  let last := ws.length - 1
  let moved := laneAt ws last
  if p.val - 1 = last then withWords s (setLaneAt ws last 0).dropLast
  else withWords (setPos s (EVM.Uint256.shl 224 moved) p)
    (setLaneAt (setLaneAt ws (p.val - 1) moved) last 0).dropLast

theorem removeSelector_ok (s : ContractState) (p : Uint256)
    (hp : 1 ≤ p.val) (hpn : p.val ≤ (words s).length) (hn : (words s).length < 2 ^ 255) :
    TinyDiamond.removeSelector p s = ContractResult.success () (removeState s p) := by
  rw [removeSelector_eq s p hp hpn hn]
  unfold removeState
  dsimp only
  split <;> rfl

/-- The position stored in `key`'s routing word. -/
def posOf (s : ContractState) (key : Uint256) : Uint256 := dec (entry s key) 160 96

theorem cut_replace (s : ContractState) (key : Uint256) (t : Address) (hb : key ∉ builtinKeys)
    (h0 : targetOf s key ≠ zeroAddress) (ht : t ≠ zeroAddress) (hne : targetOf s key ≠ t) :
    ∃ s', TinyDiamond.cut key t s = ContractResult.success () s' ∧
      SameStorage s' (setFacetSt s key t) ∧
      s'.events = s.events ++ [cutEvent (addressToWord t) 1 key] := by
  unfold TinyDiamond.cut
  rw [cut_prefix s key hb]
  rw [if_pos (by simpa using hne), if_neg (by simpa using h0), if_neg (by simpa using ht)]
  rw [bindM_success (setFacet_eq _ _ _)]
  exact emitCut_ok _ _ _ _

theorem cut_remove (s : ContractState) (key : Uint256) (hb : key ∉ builtinKeys)
    (h0 : targetOf s key ≠ zeroAddress)
    (hp : 1 ≤ (posOf s key).val) (hpn : (posOf s key).val ≤ (words s).length)
    (hn : (words s).length < 2 ^ 255) :
    ∃ s', TinyDiamond.cut key zeroAddress s = ContractResult.success () s' ∧
      SameStorage s' (setPos (setFacetSt (removeState s (posOf s key)) key zeroAddress) key 0) ∧
      s'.events = s.events ++ [cutEvent 0 2 key] := by
  unfold TinyDiamond.cut
  rw [cut_prefix s key hb]
  rw [if_pos (by simpa using h0), if_neg (by simpa using h0), if_pos (by simp)]
  rw [bindM_success (readPosition_state key s)]
  rw [show dec (s.readMapChain FACETS [key.val] 0) 160 96 = posOf s key from rfl]
  rw [bindM_success (removeSelector_ok s _ hp hpn hn), bindM_success (setFacet_eq _ _ _),
    bindM_success (setPosition_eq _ _ _)]
  obtain ⟨s', h1, h2, h3⟩ := emitCut_ok 0 2 key
    (setPos (setFacetSt (removeState s (posOf s key)) key zeroAddress) key TinyDiamond.NO_POSITION)
  refine ⟨s', h1, h2, h3.trans ?_⟩
  congr 1
  unfold removeState; dsimp only; split <;> rfl

/-- Cutting a selector to its current facet changes nothing (and emits nothing). -/
theorem cut_noop (s : ContractState) (key : Uint256) (t : Address) (hb : key ∉ builtinKeys)
    (h : targetOf s key = t) :
    TinyDiamond.cut key t s = ContractResult.success () s := by
  unfold TinyDiamond.cut
  rw [cut_prefix s key hb, h, if_neg (by simp)]
  rfl

/-! ## Reading the effects back -/

theorem laneAt_lt (ws : List Uint256) (i : Nat) : (laneAt ws i).val < 2 ^ 32 := by
  unfold laneAt laneU
  simp only [Verity.Core.Uint256.and, Verity.Core.Uint256.val_ofNat, modulus_eq, Nat.land_eq]
  have h : (4294967295 : Nat) % 2 ^ 256 = 2 ^ 32 - 1 := by decide
  rw [h, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by decide))

theorem shr224_lt (k : Uint256) : (EVM.Uint256.shr 224 k).val < 2 ^ 32 := by
  have hk : k.val < 2 ^ 256 := k.isLt
  have h : (224 : Uint256).val = 224 := rfl
  simp only [EVM.Uint256.shr, Verity.Core.Uint256.shr, Verity.Core.Uint256.val_ofNat, modulus_eq, h,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem laneAt_append_zero (ws : List Uint256) (i : Nat) : laneAt (ws ++ [0]) i = laneAt ws i := by
  unfold laneAt wordAt
  congr 1
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : i / 8 < ws.length
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_eq_none (by omega : ws.length ≤ i / 8)]
    by_cases h' : i / 8 = ws.length
    · rw [h', List.getElem?_append_right (le_refl _)]; simp
    · rw [List.getElem?_eq_none (by simp; omega)]

theorem laneAt_dropLast (ws : List Uint256) (i : Nat) (h : i / 8 < ws.length - 1) :
    laneAt ws.dropLast i = laneAt ws i := by
  unfold laneAt wordAt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_dropLast, if_pos h]

theorem entry_withWords (s : ContractState) (ws : List Uint256) (k : Uint256) :
    entry (withWords s ws) k = entry s k := rfl

theorem entry_setFacetSt (s : ContractState) (k k' : Uint256) (t : Address) :
    entry (setFacetSt s k t) k' =
      if k' = k then enc (entry s k) (addressToWord t) 0 160 else entry s k' := by
  unfold setFacetSt entry
  by_cases h : k' = k
  · subst h; simp
  · have : k'.val ≠ k.val := fun e => h (Verity.Core.Uint256.ext e)
    simp [ContractState.readMapChain_writeMapChain, h, this]

theorem entry_setPos (s : ContractState) (k k' p : Uint256) :
    entry (setPos s k p) k' = if k' = k then enc (entry s k) p 160 96 else entry s k' := by
  unfold setPos entry
  by_cases h : k' = k
  · subst h; simp
  · have : k'.val ≠ k.val := fun e => h (Verity.Core.Uint256.ext e)
    simp [ContractState.readMapChain_writeMapChain, h, this]

theorem entry_of_same {a b : ContractState} (h : SameStorage a b) (k : Uint256) :
    entry a k = entry b k := by
  simp only [entry, ContractState.readMapChain, ContractState.storageMapChain, h.1]

theorem words_of_same {a b : ContractState} (h : SameStorage a b) : words a = words b := by
  simp only [words, h.2.1]

theorem targetOf_eq_entry (s : ContractState) (k : Uint256) :
    targetOf s k = wordToAddress (dec (entry s k) 0 160) := rfl

theorem target_after_facet (w : Uint256) (t : Address) :
    wordToAddress (dec (enc w (addressToWord t) 0 160) 0 160) = t := by
  apply Verity.Core.Address.ext
  have ht : t.val < 2 ^ 160 := t.isLt
  show (dec (enc w (addressToWord t) 0 160) 0 160).val % 2 ^ 160 = t.val
  rw [dec_facet_enc_facet]
  show (t.val % 2 ^ 256) % 2 ^ 160 % 2 ^ 160 = t.val
  rw [Nat.mod_eq_of_lt (by omega : t.val < 2 ^ 256), Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht]

theorem sharpCut_of_cut (s s' : ContractState) (sel : Contracts.Bytes4) (t : Address)
    (ha : Authorized s) (h : TinyDiamond.cut (toUint256 sel) t s = ContractResult.success () s') :
    (TinyDiamond.sharpCut sel t).run s = ContractResult.success () s' := by
  have hr : TinyDiamond.requireAdmin s = ContractResult.success () s := by
    rw [requireAdmin_eq, if_pos (show s.sender = adminOf s ∨ s.sender = s.thisAddress from ha)]
  simp only [TinyDiamond.sharpCut, Contract.run]
  rw [bindM_success hr, h]

/-- Storage words other than the routing words of `ks` are unchanged. -/
def OnlyEntries (ks : List Uint256) (s s' : ContractState) : Prop :=
  ∀ K, (∀ k ∈ ks, K ≠ .mapChain FACETS [k.val] 0) → s'.storageWords K = s.storageWords K

/-- Other storage arrays than the selector list are unchanged. -/
def OtherArrays (s s' : ContractState) : Prop :=
  ∀ sl, sl ≠ WORDS → s'.storageArray sl = s.storageArray sl

theorem pos_after (w p : Uint256) (h : p.val < 2 ^ 96) : (dec (enc w p 160 96) 160 96).val = p.val := by
  rw [dec_position_enc_position, Nat.mod_eq_of_lt h]

/-- **7. Add.** An authorized `sharpCut` of an unrouted, non-built-in selector to `t ≠ 0` routes it
to `t`, gives it position `n + 1` and list slot `n`, and grows the list to `n + 1`; every other
routing word, every other list slot and every other storage word is unchanged. -/
theorem sharpCut_add (s : ContractState) (sel : Contracts.Bytes4) (t : Address)
    (ha : Authorized s) (hb : toUint256 sel ∉ builtinKeys)
    (h0 : targetOf s (toUint256 sel) = zeroAddress) (ht : t ≠ zeroAddress)
    (hn : (words s).length + 1 < 2 ^ 96) :
    ∃ s', (TinyDiamond.sharpCut sel t).run s = ContractResult.success () s' ∧
      targetOf s' (toUint256 sel) = t ∧
      (posOf s' (toUint256 sel)).val = (words s).length + 1 ∧
      (words s').length = (words s).length + 1 ∧
      laneAt (words s') (words s).length = EVM.Uint256.shr 224 (toUint256 sel) ∧
      (∀ i, i ≠ (words s).length → laneAt (words s') i = laneAt (words s) i) ∧
      (∀ k, k ≠ toUint256 sel → entry s' k = entry s k) ∧
      OnlyEntries [toUint256 sel] s s' ∧ OtherArrays s s' := by
  set key := toUint256 sel
  set n := (words s).length
  obtain ⟨s', hcut, hsame, _⟩ := cut_add s key t hb h0 ht (by omega)
  refine ⟨s', sharpCut_of_cut s s' sel t ha hcut, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [targetOf_eq_entry, entry_of_same hsame, entry_withWords, entry_setPos, if_pos rfl,
      dec_facet_enc_position, entry_setFacetSt, if_pos rfl, target_after_facet]
  · unfold posOf
    rw [entry_of_same hsame, entry_withWords, entry_setPos, if_pos rfl,
      pos_after _ _ (by rw [ofNat_val_of_lt _ (by omega)]; omega), ofNat_val_of_lt _ (by omega)]
  · rw [words_of_same hsame, words_withWords, length_setLaneAt]; simp [n]
  · rw [words_of_same hsame, words_withWords,
      laneAt_setLaneAt _ _ _ _ (by simp; omega) (shr224_lt key), if_pos rfl]
  · intro i hi
    rw [words_of_same hsame, words_withWords,
      laneAt_setLaneAt _ _ _ _ (by simp; omega) (shr224_lt key), if_neg hi, laneAt_append_zero]
  · intro k hk
    rw [entry_of_same hsame, entry_withWords, entry_setPos, if_neg hk, entry_setFacetSt, if_neg hk]
  · intro K hK
    have hK' := hK key (by simp)
    rw [hsame.1]
    simp [withWords, setPos, setFacetSt, entry, hK']
  · intro sl hsl
    rw [hsame.2.1]
    simp [withWords, setPos, setFacetSt, hsl]

/-- **8. Replace.** An authorized `sharpCut` of a routed, non-built-in selector to another
`t ≠ 0` changes its facet only: its position, the whole list and every other storage word are
unchanged. -/
theorem sharpCut_replace (s : ContractState) (sel : Contracts.Bytes4) (t : Address)
    (ha : Authorized s) (hb : toUint256 sel ∉ builtinKeys)
    (h0 : targetOf s (toUint256 sel) ≠ zeroAddress) (ht : t ≠ zeroAddress)
    (hne : targetOf s (toUint256 sel) ≠ t) :
    ∃ s', (TinyDiamond.sharpCut sel t).run s = ContractResult.success () s' ∧
      targetOf s' (toUint256 sel) = t ∧ posOf s' (toUint256 sel) = posOf s (toUint256 sel) ∧
      words s' = words s ∧
      (∀ k, k ≠ toUint256 sel → entry s' k = entry s k) ∧
      OnlyEntries [toUint256 sel] s s' ∧ OtherArrays s s' := by
  set key := toUint256 sel
  obtain ⟨s', hcut, hsame, _⟩ := cut_replace s key t hb h0 ht hne
  refine ⟨s', sharpCut_of_cut s s' sel t ha hcut, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [targetOf_eq_entry, entry_of_same hsame, entry_setFacetSt, if_pos rfl, target_after_facet]
  · unfold posOf
    rw [entry_of_same hsame, entry_setFacetSt, if_pos rfl, dec_position_enc_facet]
  · rw [words_of_same hsame]; rfl
  · intro k hk
    rw [entry_of_same hsame, entry_setFacetSt, if_neg hk]
  · intro K hK
    have hK' := hK key (by simp)
    rw [hsame.1]
    simp [setFacetSt, entry, hK']
  · intro sl _
    rw [hsame.2.1]; rfl

/-- **10. No-op.** Cutting a selector to the facet it already has changes nothing at all. -/
theorem sharpCut_noop (s : ContractState) (sel : Contracts.Bytes4) (t : Address)
    (ha : Authorized s) (hb : toUint256 sel ∉ builtinKeys)
    (h : targetOf s (toUint256 sel) = t) :
    (TinyDiamond.sharpCut sel t).run s = ContractResult.success () s :=
  sharpCut_of_cut s s sel t ha (cut_noop s _ t hb h)

theorem words_setFacetSt (s : ContractState) (k : Uint256) (t : Address) :
    words (setFacetSt s k t) = words s := rfl

theorem words_removeState (s : ContractState) (p : Uint256) :
    words (removeState s p) =
      if p.val - 1 = (words s).length - 1 then (setLaneAt (words s) ((words s).length - 1) 0).dropLast
      else (setLaneAt (setLaneAt (words s) (p.val - 1) (laneAt (words s) ((words s).length - 1)))
        ((words s).length - 1) 0).dropLast := by
  unfold removeState; dsimp only; split <;> rfl

theorem laneAt_nil (i : Nat) : laneAt [] i = 0 := by
  apply Verity.Core.Uint256.ext
  simp [laneAt, laneU, wordAt, Verity.Core.Uint256.and, Verity.Core.Uint256.shr,
    Verity.Core.Uint256.val_ofNat]

/-- The key of the selector in list slot `i`. -/
def keyAt (ws : List Uint256) (i : Nat) : Uint256 := EVM.Uint256.shl 224 (laneAt ws i)

theorem entry_removeState (s : ContractState) (p k : Uint256) :
    entry (removeState s p) k =
      if p.val - 1 = (words s).length - 1 then entry s k
      else if k = keyAt (words s) ((words s).length - 1)
        then enc (entry s k) p 160 96 else entry s k := by
  unfold removeState; dsimp only
  split
  · rfl
  · rw [entry_withWords, entry_setPos]; simp only [keyAt]
    split <;> simp_all

theorem enc_clear' (w : Uint256) :
    enc (enc w (addressToWord zeroAddress) 0 160) 0 160 96 = 0 := enc_clear w

theorem laneAt_dropLast_last (ws : List Uint256) (n : Nat) (hn : ws.length = n) (h1 : 1 ≤ n) :
    laneAt (setLaneAt ws (n - 1) 0).dropLast (n - 1) = 0 := by
  by_cases h : n = 1
  · subst h
    have : (setLaneAt ws 0 0).dropLast = [] := by
      apply List.eq_nil_of_length_eq_zero; simp [length_setLaneAt, hn]
    simp only [Nat.sub_self, this, laneAt_nil]
  · rw [laneAt_dropLast _ _ (by rw [length_setLaneAt]; omega),
      laneAt_setLaneAt _ _ _ _ (by omega) (by decide), if_pos rfl]

/-- **9. Remove.** An authorized `sharpCut` of a routed, non-built-in selector to `0`, from a
state consistent on the entries it touches (the selector at position `p`, `1 ≤ p ≤ n`, and the
last selector at position `n`), clears the selector's routing word and shrinks the list to
`n - 1`. If it was not last, the last selector moves into its slot `p - 1`, keeps its facet and
gets position `p`. The vacated slot `n - 1` is cleared; every other slot, every other routing
word and every other storage word is unchanged. -/
theorem sharpCut_remove (s : ContractState) (sel : Contracts.Bytes4)
    (ha : Authorized s) (hb : toUint256 sel ∉ builtinKeys)
    (h0 : targetOf s (toUint256 sel) ≠ zeroAddress)
    (hp : 1 ≤ (posOf s (toUint256 sel)).val) (hpn : (posOf s (toUint256 sel)).val ≤ (words s).length)
    (hlast : (posOf s (keyAt (words s) ((words s).length - 1))).val = (words s).length)
    (hn : (words s).length < 2 ^ 95) :
    let key := toUint256 sel
    let n := (words s).length
    let p := (posOf s key).val
    let lk := keyAt (words s) (n - 1)
    ∃ s', (TinyDiamond.sharpCut sel zeroAddress).run s = ContractResult.success () s' ∧
      entry s' key = 0 ∧ (words s').length = n - 1 ∧
      (p ≠ n → laneAt (words s') (p - 1) = laneAt (words s) (n - 1) ∧
        targetOf s' lk = targetOf s lk ∧ (posOf s' lk).val = p) ∧
      laneAt (words s') (n - 1) = 0 ∧
      (∀ i, i < n - 1 → i ≠ p - 1 → laneAt (words s') i = laneAt (words s) i) ∧
      (∀ k, k ≠ key → k ≠ lk → entry s' k = entry s k) ∧
      OnlyEntries [key, lk] s s' ∧ OtherArrays s s' := by
  intro key n p lk
  have hp1 : 1 ≤ p := hp
  have hpn1 : p ≤ n := hpn
  have hn1 : n < 2 ^ 95 := hn
  have hpp : (posOf s key).val = p := rfl
  have hnn : (words s).length = n := rfl
  obtain ⟨s', hcut, hsame, _⟩ := cut_remove s key hb h0 hp hpn (by omega)
  have hlk : p ≠ n → lk ≠ key := by
    intro hpn' he
    apply hpn'
    show (posOf s key).val = (words s).length
    rw [← hlast]; show (posOf s key).val = (posOf s lk).val; rw [he]
  have hW : words s' = words (removeState s (posOf s key)) := by
    rw [words_of_same hsame]; rfl
  have hE : ∀ k, entry s' k = entry (setPos (setFacetSt (removeState s (posOf s key)) key
      zeroAddress) key 0) k := entry_of_same hsame
  refine ⟨s', sharpCut_of_cut s s' sel zeroAddress ha hcut, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hE, entry_setPos, if_pos rfl, entry_setFacetSt, if_pos rfl]; exact enc_clear' _
  · rw [hW, words_removeState]; split <;> simp [length_setLaneAt, n]
  · intro hne
    have hne' : p - 1 ≠ n - 1 := by omega
    have hpv : (posOf s key).val - 1 ≠ (words s).length - 1 := hne'
    refine ⟨?_, ?_, ?_⟩
    · rw [hW, words_removeState, if_neg hpv,
        laneAt_dropLast _ _ (by rw [length_setLaneAt, length_setLaneAt]; omega),
        laneAt_setLaneAt _ _ _ _ (by rw [length_setLaneAt]; omega) (by decide), if_neg hne',
        laneAt_setLaneAt _ _ _ _ (by omega) (laneAt_lt _ _), if_pos rfl]
    · rw [targetOf_eq_entry, targetOf_eq_entry, hE, entry_setPos, if_neg (hlk hne),
        entry_setFacetSt, if_neg (hlk hne), entry_removeState, if_neg hpv, if_pos rfl,
        dec_facet_enc_position]
    · unfold posOf
      rw [hE, entry_setPos, if_neg (hlk hne), entry_setFacetSt, if_neg (hlk hne),
        entry_removeState, if_neg hpv, if_pos rfl, pos_after _ _ (by omega)]
  · rw [hW, words_removeState]
    split
    · exact laneAt_dropLast_last _ _ rfl (by omega)
    · exact laneAt_dropLast_last _ _ (length_setLaneAt _ _ _) (by omega)
  · intro i hi hip
    have hin : i ≠ n - 1 := by omega
    rw [hW, words_removeState]
    split
    · rw [laneAt_dropLast _ _ (by rw [length_setLaneAt]; omega),
        laneAt_setLaneAt _ _ _ _ (by omega) (by decide), if_neg hin]
    · rw [laneAt_dropLast _ _ (by rw [length_setLaneAt, length_setLaneAt]; omega),
        laneAt_setLaneAt _ _ _ _ (by rw [length_setLaneAt]; omega) (by decide), if_neg hin,
        laneAt_setLaneAt _ _ _ _ (by omega) (laneAt_lt _ _), if_neg hip]
  · intro k hk hk'
    rw [hE, entry_setPos, if_neg hk, entry_setFacetSt, if_neg hk, entry_removeState]
    have hk'' : ¬ k = keyAt (words s) ((words s).length - 1) := hk'
    split <;> simp
  · intro K hK
    have h1 := hK key (by simp)
    have h2 : K ≠ .mapChain FACETS
        [(EVM.Uint256.shl 224 (laneAt (words s) ((words s).length - 1))).val] 0 := hK lk (by simp)
    rw [hsame.1]
    unfold removeState; dsimp only
    split <;> simp [withWords, setPos, setFacetSt, entry, h1, h2]
  · intro sl hsl
    rw [hsame.2.1]
    unfold removeState; dsimp only
    split <;> simp [withWords, setPos, setFacetSt, hsl]

/-! ## The `DiamondCut` event of each cut -/

/-- An add (property 7) logs `DiamondCut([(t, Add, [sel])], 0, "")`. -/
theorem sharpCut_add_logs (s : ContractState) (sel : Contracts.Bytes4) (t : Address)
    (ha : Authorized s) (hb : toUint256 sel ∉ builtinKeys)
    (h0 : targetOf s (toUint256 sel) = zeroAddress) (ht : t ≠ zeroAddress)
    (hn : (words s).length + 1 < 2 ^ 96) :
    ∃ s', (TinyDiamond.sharpCut sel t).run s = ContractResult.success () s' ∧
      s'.events = s.events ++ [cutEvent (addressToWord t) 0 (toUint256 sel)] := by
  obtain ⟨s', hcut, _, hev⟩ := cut_add s (toUint256 sel) t hb h0 ht (by omega)
  exact ⟨s', sharpCut_of_cut s s' sel t ha hcut, hev⟩

/-- A replace (property 8) logs `DiamondCut([(t, Replace, [sel])], 0, "")`. -/
theorem sharpCut_replace_logs (s : ContractState) (sel : Contracts.Bytes4) (t : Address)
    (ha : Authorized s) (hb : toUint256 sel ∉ builtinKeys)
    (h0 : targetOf s (toUint256 sel) ≠ zeroAddress) (ht : t ≠ zeroAddress)
    (hne : targetOf s (toUint256 sel) ≠ t) :
    ∃ s', (TinyDiamond.sharpCut sel t).run s = ContractResult.success () s' ∧
      s'.events = s.events ++ [cutEvent (addressToWord t) 1 (toUint256 sel)] := by
  obtain ⟨s', hcut, _, hev⟩ := cut_replace s (toUint256 sel) t hb h0 ht hne
  exact ⟨s', sharpCut_of_cut s s' sel t ha hcut, hev⟩

/-- A remove (property 9) logs `DiamondCut([(0, Remove, [sel])], 0, "")`. -/
theorem sharpCut_remove_logs (s : ContractState) (sel : Contracts.Bytes4)
    (ha : Authorized s) (hb : toUint256 sel ∉ builtinKeys)
    (h0 : targetOf s (toUint256 sel) ≠ zeroAddress)
    (hp : 1 ≤ (posOf s (toUint256 sel)).val) (hpn : (posOf s (toUint256 sel)).val ≤ (words s).length)
    (hn : (words s).length < 2 ^ 255) :
    ∃ s', (TinyDiamond.sharpCut sel zeroAddress).run s = ContractResult.success () s' ∧
      s'.events = s.events ++ [cutEvent 0 2 (toUint256 sel)] := by
  obtain ⟨s', hcut, _, hev⟩ := cut_remove s (toUint256 sel) hb h0 hp hpn hn
  exact ⟨s', sharpCut_of_cut s s' sel zeroAddress ha hcut, hev⟩

/-! ## 3. Consistency of the list with the mapping -/

/-- A left-aligned selector word (the low 224 bits are zero). -/
def Aligned (k : Uint256) : Prop := EVM.Uint256.shl 224 (EVM.Uint256.shr 224 k) = k

/-- Property 3: every listed selector is routed and its position is its slot + 1; a selector is
routed exactly when it has a position, and that position points back to it. -/
structure Consistent (s : ContractState) : Prop where
  listed : ∀ i, i < (words s).length →
    targetOf s (keyAt (words s) i) ≠ zeroAddress ∧ (posOf s (keyAt (words s) i)).val = i + 1
  routed_iff : ∀ k, Aligned k → (targetOf s k ≠ zeroAddress ↔ (posOf s k).val ≠ 0)
  backref : ∀ k, Aligned k → (posOf s k).val ≠ 0 →
    (posOf s k).val ≤ (words s).length ∧ keyAt (words s) ((posOf s k).val - 1) = k

/-- No selector is listed twice. -/
theorem Consistent.no_duplicates {s : ContractState} (h : Consistent s) (i j : Nat)
    (hi : i < (words s).length) (hj : j < (words s).length)
    (he : keyAt (words s) i = keyAt (words s) j) : i = j := by
  have h1 := (h.listed i hi).2
  have h2 := (h.listed j hj).2
  rw [he] at h1
  omega

theorem targetOf_of_entry {a b : ContractState} {k : Uint256} (h : entry a k = entry b k) :
    targetOf a k = targetOf b k := by
  rw [targetOf_eq_entry, targetOf_eq_entry, h]

theorem posOf_of_entry {a b : ContractState} {k : Uint256} (h : entry a k = entry b k) :
    posOf a k = posOf b k := by
  unfold posOf; rw [h]

theorem toUint256_aligned (sel : Contracts.Bytes4) : Aligned (toUint256 sel) := by
  unfold Aligned
  apply Verity.Core.Uint256.ext
  have hv : sel.val < 2 ^ 32 := sel.isLt
  have h224 : (224 : Uint256).val = 224 := rfl
  simp only [toUint256, Verity.Core.BytesN.toUint256, EVM.Uint256.shl, EVM.Uint256.shr,
    Verity.Core.Uint256.shl, Verity.Core.Uint256.shr, Verity.Core.Uint256.val_ofNat, modulus_eq,
    h224, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have e : 8 * (32 - 4) = 224 := rfl
  have hlt : sel.val * 2 ^ 224 < 2 ^ 256 :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hv (by positivity)) (by norm_num)
  rw [e, Nat.mod_eq_of_lt hlt, Nat.mul_div_cancel _ (by positivity),
    Nat.mod_eq_of_lt (by omega : sel.val < 2 ^ 256), Nat.mod_eq_of_lt hlt]

theorem keyAt_aligned (ws : List Uint256) (i : Nat) : Aligned (keyAt ws i) := by
  unfold Aligned
  apply Verity.Core.Uint256.ext
  have hv := laneAt_lt ws i
  have h224 : (224 : Uint256).val = 224 := rfl
  simp only [keyAt, EVM.Uint256.shl, EVM.Uint256.shr,
    Verity.Core.Uint256.shl, Verity.Core.Uint256.shr, Verity.Core.Uint256.val_ofNat, modulus_eq,
    h224, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hlt : (laneAt ws i).val * 2 ^ 224 < 2 ^ 256 :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hv (by positivity)) (by norm_num)
  rw [Nat.mod_eq_of_lt hlt, Nat.mul_div_cancel _ (by positivity),
    Nat.mod_eq_of_lt (by omega : (laneAt ws i).val < 2 ^ 256), Nat.mod_eq_of_lt hlt]

theorem keyAt_of_lane {ws ws' : List Uint256} {i j : Nat} (h : laneAt ws' i = laneAt ws j) :
    keyAt ws' i = keyAt ws j := by unfold keyAt; rw [h]

theorem keyAt_lane_key (ws : List Uint256) (i : Nat) (key : Uint256) (hk : Aligned key)
    (h : laneAt ws i = EVM.Uint256.shr 224 key) : keyAt ws i = key := by
  unfold keyAt; rw [h]; exact hk

/-- Add keeps the table consistent. -/
theorem consistent_add {s s' : ContractState} {key : Uint256} {t : Address}
    (hc : Consistent s) (hk : Aligned key) (h0 : targetOf s key = zeroAddress)
    (ht : t ≠ zeroAddress)
    (h1 : targetOf s' key = t) (h2 : (posOf s' key).val = (words s).length + 1)
    (h3 : (words s').length = (words s).length + 1)
    (h4 : laneAt (words s') (words s).length = EVM.Uint256.shr 224 key)
    (h5 : ∀ i, i ≠ (words s).length → laneAt (words s') i = laneAt (words s) i)
    (h6 : ∀ k, k ≠ key → entry s' k = entry s k) : Consistent s' := by
  have hkn : keyAt (words s') (words s).length = key := keyAt_lane_key _ _ _ hk h4
  have hlisted_ne : ∀ i, i < (words s).length → keyAt (words s) i ≠ key := by
    intro i hi he; have := (hc.listed i hi).1; rw [he, h0] at this; exact this rfl
  constructor
  · intro i hi
    rw [h3] at hi
    by_cases hin : i = (words s).length
    · subst hin; rw [hkn, h1, h2]; exact ⟨ht, rfl⟩
    · have hi' : i < (words s).length := by omega
      rw [keyAt_of_lane (h5 i hin), targetOf_of_entry (h6 _ (hlisted_ne i hi')),
        posOf_of_entry (h6 _ (hlisted_ne i hi'))]
      exact hc.listed i hi'
  · intro k hka
    by_cases hkk : k = key
    · subst hkk; rw [h1, h2]; exact ⟨fun _ => by omega, fun _ => ht⟩
    · rw [targetOf_of_entry (h6 k hkk), posOf_of_entry (h6 k hkk)]; exact hc.routed_iff k hka
  · intro k hka hp
    by_cases hkk : k = key
    · subst hkk; rw [h2, h3]; exact ⟨le_refl _, by simpa using hkn⟩
    · rw [posOf_of_entry (h6 k hkk)] at hp ⊢
      obtain ⟨hle, hback⟩ := hc.backref k hka hp
      refine ⟨by omega, ?_⟩
      rw [keyAt_of_lane (h5 _ (by omega)), hback]

/-- Replace keeps the table consistent. -/
theorem consistent_replace {s s' : ContractState} {key : Uint256} {t : Address}
    (hc : Consistent s) (h0 : targetOf s key ≠ zeroAddress) (ht : t ≠ zeroAddress)
    (h1 : targetOf s' key = t) (h2 : posOf s' key = posOf s key) (h3 : words s' = words s)
    (h6 : ∀ k, k ≠ key → entry s' k = entry s k) : Consistent s' := by
  have tgt : ∀ k, (targetOf s' k ≠ zeroAddress ↔ targetOf s k ≠ zeroAddress) := by
    intro k; by_cases hkk : k = key
    · subst hkk; rw [h1]; exact ⟨fun _ => h0, fun _ => ht⟩
    · rw [targetOf_of_entry (h6 k hkk)]
  have pos : ∀ k, posOf s' k = posOf s k := by
    intro k; by_cases hkk : k = key
    · subst hkk; exact h2
    · exact posOf_of_entry (h6 k hkk)
  constructor
  · intro i hi; rw [h3] at hi ⊢; rw [tgt, pos]; exact hc.listed i hi
  · intro k hka; rw [tgt, pos]; exact hc.routed_iff k hka
  · intro k hka hp; rw [pos] at hp ⊢; rw [h3]; exact hc.backref k hka hp

theorem targetOf_of_zero {s : ContractState} {k : Uint256} (h : entry s k = 0) :
    targetOf s k = zeroAddress := by
  rw [targetOf_eq_entry, h]; rfl

theorem posOf_of_zero {s : ContractState} {k : Uint256} (h : entry s k = 0) :
    (posOf s k).val = 0 := by
  unfold posOf; rw [h]; rfl

/-- Remove keeps the table consistent. -/
theorem consistent_remove {s s' : ContractState} {key : Uint256}
    (hc : Consistent s) (hk : Aligned key) (h0 : targetOf s key ≠ zeroAddress)
    (r1 : entry s' key = 0) (r2 : (words s').length = (words s).length - 1)
    (r3 : (posOf s key).val ≠ (words s).length →
      laneAt (words s') ((posOf s key).val - 1) = laneAt (words s) ((words s).length - 1) ∧
      targetOf s' (keyAt (words s) ((words s).length - 1)) =
        targetOf s (keyAt (words s) ((words s).length - 1)) ∧
      (posOf s' (keyAt (words s) ((words s).length - 1))).val = (posOf s key).val)
    (r5 : ∀ i, i < (words s).length - 1 → i ≠ (posOf s key).val - 1 →
      laneAt (words s') i = laneAt (words s) i)
    (r6 : ∀ k, k ≠ key → k ≠ keyAt (words s) ((words s).length - 1) → entry s' k = entry s k) :
    Consistent s' := by
  set n := (words s).length
  set p := (posOf s key).val
  set lk := keyAt (words s) (n - 1)
  have hp0 : p ≠ 0 := (hc.routed_iff key hk).1 h0
  obtain ⟨hpn, hkey0⟩ := hc.backref key hk hp0
  have hkey : keyAt (words s) (p - 1) = key := hkey0
  have hlk : (posOf s lk).val = n ∧ targetOf s lk ≠ zeroAddress := by
    have := hc.listed (n - 1) (by omega); exact ⟨by rw [this.2]; omega, this.1⟩
  have hlk_key : p ≠ n → lk ≠ key := fun hne he => hne (by rw [← hlk.1, he])
  have hneq : ∀ i, i < n → i ≠ p - 1 → keyAt (words s) i ≠ key := by
    intro i hi hip he
    exact hip (hc.no_duplicates i (p - 1) hi (by omega) (by rw [he, hkey]))
  have hnel : ∀ i, i < n - 1 → keyAt (words s) i ≠ lk := by
    intro i hi he
    have := hc.no_duplicates i (n - 1) (by omega) (by omega) he; omega
  constructor
  · intro i hi
    rw [r2] at hi
    by_cases hip : i = p - 1
    · have hne : p ≠ n := by omega
      obtain ⟨l1, l2, l3⟩ := r3 hne
      rw [hip, keyAt_of_lane l1, l2, l3]; exact ⟨hlk.2, by omega⟩
    · rw [keyAt_of_lane (r5 i hi hip)]
      have e := r6 _ (hneq i (by omega) hip) (hnel i hi)
      rw [targetOf_of_entry e, posOf_of_entry e]; exact hc.listed i (by omega)
  · intro k hka
    by_cases hkk : k = key
    · subst hkk; rw [targetOf_of_zero r1, posOf_of_zero r1]; simp
    · by_cases hkl : k = lk
      · have hne : p ≠ n := fun he => hkk (by rw [hkl, ← hkey, he])
        obtain ⟨_, l2, l3⟩ := r3 hne
        rw [hkl, l2, l3]; exact ⟨fun _ => hp0, fun _ => hlk.2⟩
      · have e := r6 k hkk hkl
        rw [targetOf_of_entry e, posOf_of_entry e]; exact hc.routed_iff k hka
  · intro k hka hpk
    by_cases hkk : k = key
    · subst hkk; rw [posOf_of_zero r1] at hpk; exact absurd rfl hpk
    · by_cases hkl : k = lk
      · have hne : p ≠ n := fun he => hkk (by rw [hkl, ← hkey, he])
        obtain ⟨l1, _, l3⟩ := r3 hne
        rw [hkl, l3, r2, keyAt_of_lane l1]; exact ⟨by omega, rfl⟩
      · have e := r6 k hkk hkl
        rw [posOf_of_entry e] at hpk ⊢
        obtain ⟨hle, hback⟩ := hc.backref k hka hpk
        have h1 : (posOf s k).val - 1 ≠ p - 1 := fun he => hkk (by rw [← hback, he, hkey])
        have h2 : (posOf s k).val - 1 ≠ n - 1 := fun he => hkl (by rw [← hback, he])
        refine ⟨by rw [r2]; omega, ?_⟩
        rw [keyAt_of_lane (r5 _ (by omega) h1), hback]

theorem run_det {c : Contract Unit} {s a b : ContractState}
    (ha : c.run s = ContractResult.success () a) (hb : c.run s = ContractResult.success () b) :
    a = b := by
  rw [ha] at hb; cases hb; rfl

theorem sharpCut_same_of_cut {s s' m : ContractState} {sel : Contracts.Bytes4} {t : Address}
    (ha : Authorized s) (hcut : TinyDiamond.cut (toUint256 sel) t s = ContractResult.success () s')
    (hsame : SameStorage s' m) (hm : m.sender = s.sender ∧ m.thisAddress = s.thisAddress)
    {s'' : ContractState} (hrun : (TinyDiamond.sharpCut sel t).run s = ContractResult.success () s'') :
    s''.sender = s.sender ∧ s''.thisAddress = s.thisAddress := by
  have := run_det hrun (sharpCut_of_cut s s' sel t ha hcut)
  subst this
  exact ⟨hsame.2.2.1.trans hm.1, hsame.2.2.2.trans hm.2⟩

/-- One authorized cut of a non-built-in selector from a consistent table: it succeeds, keeps
the table consistent, routes the selector to `t`, and keeps the caller and own address. -/
theorem sharpCut_step (s : ContractState) (sel : Contracts.Bytes4) (t : Address)
    (hc : Consistent s) (ha : Authorized s) (hb : toUint256 sel ∉ builtinKeys)
    (hn : (words s).length + 1 < 2 ^ 95) :
    ∃ s', (TinyDiamond.sharpCut sel t).run s = ContractResult.success () s' ∧
      Consistent s' ∧ (words s').length ≤ (words s).length + 1 ∧
      s'.sender = s.sender ∧ s'.thisAddress = s.thisAddress := by
  set key := toUint256 sel
  have hk : Aligned key := toUint256_aligned sel
  by_cases hnoop : targetOf s key = t
  · exact ⟨s, sharpCut_noop s sel t ha hb hnoop, hc, by omega, rfl, rfl⟩
  by_cases h0 : targetOf s key = zeroAddress
  · have ht : t ≠ zeroAddress := fun h => hnoop (h0.trans h.symm)
    obtain ⟨s', hrun, a1, a2, a3, a4, a5, a6, _, _⟩ := sharpCut_add s sel t ha hb h0 ht (by omega)
    obtain ⟨s2, hcut, hsame, _⟩ := cut_add s key t hb h0 ht (by omega)
    exact ⟨s', hrun, consistent_add hc hk h0 ht a1 a2 a3 a4 a5 a6, by omega,
      sharpCut_same_of_cut ha hcut hsame ⟨rfl, rfl⟩ hrun⟩
  by_cases ht : t = zeroAddress
  · subst ht
    have hp0 := (hc.routed_iff key hk).1 h0
    obtain ⟨hpn, _⟩ := hc.backref key hk hp0
    have hn1 : 1 ≤ (words s).length := le_trans (Nat.one_le_iff_ne_zero.mpr hp0) hpn
    have hlast := (hc.listed ((words s).length - 1) (by omega)).2
    have hlast' : (posOf s (keyAt (words s) ((words s).length - 1))).val = (words s).length := by
      rw [hlast]; omega
    obtain ⟨s', hrun, r1, r2, r3, _, r5, r6, _, _⟩ :=
      sharpCut_remove s sel ha hb h0 (Nat.one_le_iff_ne_zero.mpr hp0) hpn hlast' (by omega)
    obtain ⟨s2, hcut, hsame, _⟩ := cut_remove s key hb h0 (Nat.one_le_iff_ne_zero.mpr hp0) hpn
      (by omega)
    refine ⟨s', hrun, consistent_remove hc hk h0 r1 r2 r3 r5 r6, by omega, ?_⟩
    apply sharpCut_same_of_cut ha hcut hsame _ hrun
    unfold removeState; dsimp only; split <;> exact ⟨rfl, rfl⟩
  · obtain ⟨s', hrun, a1, a2, a3, a4, _, _⟩ := sharpCut_replace s sel t ha hb h0 ht hnoop
    obtain ⟨s2, hcut, hsame, _⟩ := cut_replace s key t hb h0 ht hnoop
    exact ⟨s', hrun, consistent_replace hc h0 ht a1 a2 a3 a4, by rw [a3]; omega,
      sharpCut_same_of_cut ha hcut hsame ⟨rfl, rfl⟩ hrun⟩

/-! ## 1–3. Any sequence of cuts -/

/-- One `sharpCut(sel, target)` transaction sent by `caller`. -/
structure Cut where
  caller : Address
  sel : Contracts.Bytes4
  target : Address

/-- The state after the transaction (unchanged if it reverts). -/
def runCut (s : ContractState) (c : Cut) : ContractState :=
  match (TinyDiamond.sharpCut c.sel c.target).run { s with sender := c.caller } with
  | .success _ s' => s'
  | .revert _ _ => s

/-- The target of the last cut of `k` in `cs`, or `init k` if no cut touches `k`. -/
def lastTarget (init : Uint256 → Address) (cs : List Cut) (k : Uint256) : Address :=
  cs.foldl (fun acc c => if toUint256 c.sel = k then c.target else acc) (init k)

theorem consistent_sender {s : ContractState} (a : Address) (h : Consistent s) :
    Consistent { s with sender := a } :=
  ⟨fun i hi => h.listed i hi, fun k hk => h.routed_iff k hk, fun k hk hp => h.backref k hk hp⟩

/-- **1, 2, 3.** Starting from a consistent table, after any sequence of `sharpCut` transactions
sent by the admin on non-built-in selectors: every cut succeeds; every selector routes to the
target of the last cut that touched it (or to what it routed to before, e.g. nothing from an
empty table); no restriction and not the admin changed; and the table is still consistent. -/
theorem cuts_sequence (s₀ : ContractState) (cs : List Cut) (hc : Consistent s₀)
    (hadm : ∀ c ∈ cs, c.caller = adminOf s₀) (hb : ∀ c ∈ cs, toUint256 c.sel ∉ builtinKeys)
    (hn : (words s₀).length + cs.length + 1 < 2 ^ 95) :
    let sN := cs.foldl runCut s₀
    Consistent sN ∧ (∀ k, targetOf sN k = lastTarget (targetOf s₀) cs k) ∧
      (∀ k, restrictionOf sN k = restrictionOf s₀ k) ∧ adminOf sN = adminOf s₀ ∧
      sN.thisAddress = s₀.thisAddress := by
  induction cs generalizing s₀ with
  | nil => exact ⟨hc, fun _ => rfl, fun _ => rfl, rfl, rfl⟩
  | cons c cs ih =>
    intro sN
    have ha : Authorized { s₀ with sender := c.caller } :=
      Or.inl (hadm c (List.mem_cons_self ..))
    obtain ⟨s₁, hrun, hc₁, hlen, _, hthis⟩ := sharpCut_step _ c.sel c.target
      (consistent_sender c.caller hc) ha (hb c (List.mem_cons_self ..))
      (by simp at hn; show (words s₀).length + 1 < 2 ^ 95; omega)
    have hw : words { s₀ with sender := c.caller } = words s₀ := rfl
    rw [hw] at hlen
    have hstep : runCut s₀ c = s₁ := by simp [runCut, hrun]
    have hroute := sharpCut_routes _ _ _ _ hrun
    obtain ⟨hf1, hf2, hf3⟩ := sharpCut_frame _ _ _ _ hrun
    have hadm₁ : adminOf s₁ = adminOf s₀ := hf3
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih s₁ hc₁
      (fun c' hc' => (hadm c' (List.mem_cons_of_mem _ hc')).trans hadm₁.symm)
      (fun c' hc' => hb c' (List.mem_cons_of_mem _ hc'))
      (by simp at hn; show (words s₁).length + cs.length + 1 < 2 ^ 95; omega)
    have hfold : sN = cs.foldl runCut s₁ := by simp [sN, List.foldl_cons, hstep]
    rw [hfold]
    refine ⟨i1, fun k => ?_, fun k => (i3 k).trans (hf2 k), i4.trans hadm₁, i5.trans hthis⟩
    rw [i2 k]
    simp only [lastTarget, List.foldl_cons]
    congr 1
    by_cases hk : toUint256 c.sel = k
    · rw [if_pos hk, ← hk]; exact hroute
    · rw [if_neg hk]; exact hf1 k (Ne.symm hk)

/-- An empty routing table: no listed selector and every routing word zero. -/
def EmptyTable (s : ContractState) : Prop := words s = [] ∧ ∀ k, entry s k = 0

theorem EmptyTable.consistent {s : ContractState} (h : EmptyTable s) : Consistent s where
  listed := by intro i hi; rw [h.1] at hi; simp at hi
  routed_iff := by
    intro k _; rw [targetOf_of_zero (h.2 k), posOf_of_zero (h.2 k)]; simp
  backref := by intro k _ hp; rw [posOf_of_zero (h.2 k)] at hp; exact absurd rfl hp

/-- **1.** From an empty table (e.g. right after deployment), after any sequence of admin cuts of
non-built-in selectors, every selector routes to the target of the last cut that touched it,
or to nothing; `getTarget` and `selectorToFacet` both return it. -/
theorem cuts_from_empty (s₀ : ContractState) (cs : List Cut) (he : EmptyTable s₀)
    (hadm : ∀ c ∈ cs, c.caller = adminOf s₀) (hb : ∀ c ∈ cs, toUint256 c.sel ∉ builtinKeys)
    (hn : cs.length + 1 < 2 ^ 95) (sel : Contracts.Bytes4) :
    let sN := cs.foldl runCut s₀
    TinyDiamond.getTarget sel sN =
        ContractResult.success (lastTarget (fun _ => zeroAddress) cs (toUint256 sel)) sN ∧
      TinyDiamond.selectorToFacet sel sN =
        ContractResult.success (lastTarget (fun _ => zeroAddress) cs (toUint256 sel)) sN := by
  intro sN
  obtain ⟨_, h2, _, _, _⟩ := cuts_sequence s₀ cs he.consistent hadm hb (by rw [he.1]; simpa)
  have hinit : targetOf s₀ = fun _ => zeroAddress := funext fun k => targetOf_of_zero (he.2 k)
  have ht : targetOf sN (toUint256 sel) = lastTarget (fun _ => zeroAddress) cs (toUint256 sel) := by
    rw [← hinit]; exact h2 _
  rw [getTarget_eq, selectorToFacet_eq, ht]
  exact ⟨rfl, rfl⟩

/-! ## 5. Built-ins, from an independent list -/

/-- The six built-in selectors, written from their signatures (`cast sig`), independently of
the contract's constants: `sharpCut(bytes4,address)`, `restrict(bytes4,address)`, `admin()`,
`getTarget(bytes4)`, `selectorToFacet(bytes4)`, `selectorRestriction(bytes4)`. -/
def specBuiltinSelectors : List Nat :=
  [0xaa15ede9, 0x89bf5c02, 0xf851a440, 0x374e4047, 0xae7473ac, 0xff8afdb9]

theorem specBuiltins_eq :
    specBuiltinSelectors.map (fun x => Verity.Core.Uint256.ofNat (x * 2 ^ 224)) = builtinKeys := by
  decide

/-- **5.** None of the six built-ins can be routed or restricted, whoever calls and whatever the
target. -/
theorem builtins_immutable (s : ContractState) (sel : Contracts.Bytes4) (t : Address)
    (h : sel.val ∈ specBuiltinSelectors) :
    (∃ msg, (TinyDiamond.sharpCut sel t).run s = ContractResult.revert msg s) ∧
      (∃ msg, (TinyDiamond.restrict sel t).run s = ContractResult.revert msg s) := by
  have hk : toUint256 sel ∈ builtinKeys := by
    rw [← specBuiltins_eq]
    refine List.mem_map.mpr ⟨sel.val, h, ?_⟩
    rfl
  exact ⟨sharpCut_reverts_of_builtin s sel t hk, restrict_reverts_of_builtin s sel t hk⟩

/-! ## 6. Unauthorized callers -/

/-- **6.** A transaction from someone who is neither the admin nor the diamond leaves the
state as it was (both `sharpCut` and `restrict` revert). -/
theorem unauthorized_cut_noop (s : ContractState) (c : Cut)
    (h : c.caller ≠ adminOf s ∧ c.caller ≠ s.thisAddress) : runCut s c = s := by
  have hna : ¬ Authorized { s with sender := c.caller } := fun ha => ha.elim h.1 h.2
  simp [runCut, sharpCut_reverts_of_not_authorized _ _ _ hna]

end Diamond.Table
