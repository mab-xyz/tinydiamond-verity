import TinyDiamond.Contract
import TinyDiamond.Frame
import TinyDiamond.Packing

/-!
# Frame lemmas of the routing-table helpers

`Same`: the storage words are untouched (array, memory and event steps).
`Q`: every facet, every restriction and the admin are unchanged.
-/

namespace Diamond.Routing

open Verity
open Contracts
open Diamond
open Diamond.Frame
open Diamond.Packing

abbrev FACETS : Nat := 0x0abc81caac83e1656ee495fd84f3fd0c2020c41999d182a4a81694a75a694700
abbrev RESTRICTIONS : Nat := 0x0abc81caac83e1656ee495fd84f3fd0c2020c41999d182a4a81694a75a694702
abbrev ADMIN : Nat := 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103

/-- The facet bits of the routing word of key `k` (a left-aligned selector word). -/
def facetBits (s : ContractState) (k : Nat) : Uint256 := dec (s.readMapChain FACETS [k] 0) 0 160

def restrictionWord (s : ContractState) (k : Nat) : Uint256 := s.readMapChain RESTRICTIONS [k] 0

def Same (s s' : ContractState) : Prop := s'.storageWords = s.storageWords

theorem same_preorder : Preorder Same :=
  ⟨fun _ => rfl, fun _ _ _ h₁ h₂ => h₂.trans h₁⟩

theorem getStorageArrayLength_same (a : StorageSlot (List Uint256)) :
    Preserves Same (getStorageArrayLength a) :=
  Preserves.of_state same_preorder (by intro s x s' h; cases h; rfl)

theorem getStorageArrayElement_same (a : StorageSlot (List Uint256)) (i : Uint256) :
    Preserves Same (getStorageArrayElement a i) := by
  apply Preserves.of_state same_preorder
  intro s x s' h
  unfold getStorageArrayElement at h
  split at h <;> cases h; rfl

theorem setStorageArrayElement_same (a : StorageSlot (List Uint256)) (i v : Uint256) :
    Preserves Same (setStorageArrayElement a i v) := by
  intro s x s' h
  unfold setStorageArrayElement at h
  split at h <;> cases h; rfl

theorem pushStorageArray_same (a : StorageSlot (List Uint256)) (v : Uint256) :
    Preserves Same (pushStorageArray a v) := by
  intro s x s' h; cases h; rfl

theorem popStorageArray_same (a : StorageSlot (List Uint256)) :
    Preserves Same (popStorageArray a) := by
  intro s x s' h
  unfold popStorageArray at h
  split at h <;> cases h; rfl

theorem setSelectorAt_same (i v : Uint256) : Preserves Same (TinyDiamond.setSelectorAt i v) := by
  unfold TinyDiamond.setSelectorAt
  exact Preserves.bind same_preorder (getStorageArrayElement_same _ _)
    (fun _ => setStorageArrayElement_same _ _ _)

theorem addSelector_same (k : Uint256) : Preserves Same (TinyDiamond.addSelector k) := by
  unfold TinyDiamond.addSelector
  refine Preserves.bind same_preorder (getStorageArrayLength_same _) fun n => ?_
  refine Preserves.bind same_preorder (pushStorageArray_same _ _) fun _ => ?_
  exact Preserves.bind same_preorder (setSelectorAt_same _ _)
    (fun _ => Preserves.pure same_preorder _)

/-- An `emit` only appends to the log. -/
theorem emitCut_same (f a k : Uint256) : Preserves Same (TinyDiamond.emitCut f a k) := by
  intro s x s' h; cases h; rfl

/-- Facets, restrictions and the admin are unchanged. -/
def Q (s s' : ContractState) : Prop :=
  (∀ k, facetBits s' k = facetBits s k) ∧ (∀ k, restrictionWord s' k = restrictionWord s k) ∧
    s'.storageWords (.addr ADMIN) = s.storageWords (.addr ADMIN)

theorem q_preorder : Preorder Q :=
  ⟨fun _ => ⟨fun _ => rfl, fun _ => rfl, rfl⟩,
   fun _ _ _ h₁ h₂ => ⟨fun k => (h₂.1 k).trans (h₁.1 k), fun k => (h₂.2.1 k).trans (h₁.2.1 k),
     h₂.2.2.trans h₁.2.2⟩⟩

theorem q_of_same {s s' : ContractState} (h : Same s s') : Q s s' := by
  unfold Same at h
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩ <;>
    simp [facetBits, restrictionWord, ContractState.readMapChain, ContractState.storageMapChain, h]

theorem setPosition_q (k : Uint256) (v : Uint256) :
    Preserves Q (TinyDiamond.setStructMember "facetOf" k "position" v) := by
  intro s x s' h
  simp only [TinyDiamond.setStructMember] at h
  rw [if_neg (by decide), if_pos (by decide), setStructMemberAt_eq] at h
  cases h
  refine ⟨fun k' => ?_, fun k' => ?_, ?_⟩
  · unfold facetBits
    by_cases hk : k' = StorageKey.toWord k
    · subst hk; simp [dec_facet_enc_position]
    · have hk' : k' ≠ k.val := hk
      simp [ContractState.readMapChain_writeMapChain, hk']
  · simp [restrictionWord, ContractState.readMapChain_writeMapChain]
  · simp

theorem toQ {α : Type} {c : Contract α} (h : Preserves Same c) : Preserves Q c :=
  Preserves.mono (fun _ _ => q_of_same) h

theorem selectorAt_same (i : Uint256) : Preserves Same (TinyDiamond.selectorAt i) := by
  unfold TinyDiamond.selectorAt
  exact Preserves.bind same_preorder (getStorageArrayElement_same _ _)
    (fun _ => Preserves.pure same_preorder _)

theorem removeSelector_q (p : Uint256) : Preserves Q (TinyDiamond.removeSelector p) := by
  unfold TinyDiamond.removeSelector
  refine Preserves.bind q_preorder (toQ (getStorageArrayLength_same _)) fun n => ?_
  dsimp only
  have tail : Preserves Q (do
      TinyDiamond.setSelectorAt (EVM.Uint256.sub n 1) 0
      popStorageArray TinyDiamond.selectorWords) :=
    Preserves.bind q_preorder (toQ (setSelectorAt_same _ _)) (fun _ => (toQ (popStorageArray_same _)))
  apply Preserves.ite
  · refine Preserves.bind q_preorder (toQ (selectorAt_same _)) fun last => ?_
    refine Preserves.bind q_preorder (toQ (setSelectorAt_same _ _)) fun _ => ?_
    exact Preserves.bind q_preorder (setPosition_q _ _) fun _ => tail
  · exact Preserves.bind q_preorder (Preserves.pure q_preorder _) fun _ => tail

/-- Every facet but `k`'s, every restriction and the admin are unchanged. -/
def R (k : Nat) (s s' : ContractState) : Prop :=
  (∀ k', k' ≠ k → facetBits s' k' = facetBits s k') ∧
    (∀ k', restrictionWord s' k' = restrictionWord s k') ∧
    s'.storageWords (.addr ADMIN) = s.storageWords (.addr ADMIN)

theorem r_preorder (k : Nat) : Preorder (R k) :=
  ⟨fun _ => ⟨fun _ _ => rfl, fun _ => rfl, rfl⟩,
   fun _ _ _ h₁ h₂ => ⟨fun k' hk => (h₂.1 k' hk).trans (h₁.1 k' hk),
     fun k' => (h₂.2.1 k').trans (h₁.2.1 k'), h₂.2.2.trans h₁.2.2⟩⟩

theorem toR {α : Type} (k : Nat) {c : Contract α} (h : Preserves Q c) : Preserves (R k) c :=
  Preserves.mono (fun _ _ hq => ⟨fun k' _ => hq.1 k', hq.2.1, hq.2.2⟩) h

/-- The facet of `k` is unchanged. -/
def FK (k : Nat) (s s' : ContractState) : Prop := facetBits s' k = facetBits s k

theorem fk_preorder (k : Nat) : Preorder (FK k) :=
  ⟨fun _ => rfl, fun _ _ _ h₁ h₂ => h₂.trans h₁⟩

theorem toFK {α : Type} (k : Nat) {c : Contract α} (h : Preserves Q c) : Preserves (FK k) c :=
  Preserves.mono (fun _ _ hq => hq.1 k) h

theorem readFacet_state {α : Type} [Inhabited α] [StorageWord α] (k : Uint256) (s : ContractState) :
    TinyDiamond.structMember (α := α) "facetOf" k "facet" s =
      ContractResult.success (StorageWord.fromWord (facetBits s k.val)) s := by
  simp only [TinyDiamond.structMember]
  rw [if_pos (by decide), structMemberAt_eq]
  rfl

theorem readPosition_state (k : Uint256) (s : ContractState) :
    TinyDiamond.structMember (α := Uint256) "facetOf" k "position" s =
      ContractResult.success (dec (s.readMapChain FACETS [k.val] 0) 160 96) s := by
  simp only [TinyDiamond.structMember]
  rw [if_neg (by decide), if_pos (by decide), structMemberAt_eq]
  rfl

theorem setFacet_r (k : Uint256) (t : Address) :
    Preserves (R k.val) (TinyDiamond.setStructMember "facetOf" k "facet" t) := by
  intro s x s' h
  simp only [TinyDiamond.setStructMember] at h
  rw [if_pos (by decide), setStructMemberAt_eq] at h
  cases h
  refine ⟨fun k' hk => ?_, fun k' => ?_, ?_⟩
  · have hk' : k' ≠ k.val := hk
    simp [facetBits, ContractState.readMapChain_writeMapChain, hk']
  · simp [restrictionWord, ContractState.readMapChain_writeMapChain]
  · simp

theorem setFacet_post (k : Uint256) (t : Address) :
    Establishes (fun s' => wordToAddress (facetBits s' k.val) = t)
      (TinyDiamond.setStructMember "facetOf" k "facet" t) := by
  intro s x s' h
  simp only [TinyDiamond.setStructMember] at h
  rw [if_pos (by decide), setStructMemberAt_eq] at h
  cases h
  have hk : StorageKey.toWord k = k.val := rfl
  apply Verity.Core.Address.ext
  simp only [facetBits, hk, ContractState.readMapChain_writeMapChain_same, wordToAddress,
    Verity.Core.Address.val_ofNat, dec_facet_enc_facet]
  have ht : t.val < 2 ^ 160 := t.isLt
  show (t.val % 2 ^ 256) % 2 ^ 160 % 2 ^ 160 = t.val
  rw [Nat.mod_eq_of_lt (by omega : t.val < 2 ^ 256), Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht]

theorem isBuiltin_state (k : Uint256) (s : ContractState) :
    ∃ b, TinyDiamond.isBuiltin k s = ContractResult.success b s := ⟨_, rfl⟩

theorem isBuiltin_preserves {P : ContractState → ContractState → Prop} (hP : Preorder P)
    (k : Uint256) : Preserves P (TinyDiamond.isBuiltin k) :=
  Preserves.of_state hP (by intro s b s' h; cases h; rfl)

theorem readFacet_preserves {P : ContractState → ContractState → Prop} (hP : Preorder P)
    (k : Uint256) : Preserves P (TinyDiamond.structMember (α := Address) "facetOf" k "facet") :=
  Preserves.of_state hP (by intro s b s' h; rw [readFacet_state] at h; cases h; rfl)

theorem readPosition_preserves {P : ContractState → ContractState → Prop} (hP : Preorder P)
    (k : Uint256) : Preserves P (TinyDiamond.structMember (α := Uint256) "facetOf" k "position") :=
  Preserves.of_state hP (by intro s b s' h; rw [readPosition_state] at h; cases h; rfl)

/-- `cut k t` changes no facet but `k`'s, no restriction and not the admin. -/
theorem cut_r (k : Uint256) (t : Address) : Preserves (R k.val) (TinyDiamond.cut k t) := by
  have hR := r_preorder k.val
  unfold TinyDiamond.cut
  refine Preserves.bind hR (isBuiltin_preserves hR k) fun b => ?_
  refine Preserves.bind hR (Preserves.require hR _ _) fun _ => ?_
  refine Preserves.bind hR (readFacet_preserves hR k) fun old => ?_
  refine Preserves.ite (Preserves.ite ?_ (Preserves.ite ?_ ?_)) (Preserves.pure hR _)
  · refine Preserves.bind hR (toR _ (toQ (addSelector_same k))) fun p => ?_
    refine Preserves.bind hR (setFacet_r k t) fun _ => ?_
    refine Preserves.bind hR (toR _ (setPosition_q k p)) fun _ => ?_
    exact toR _ (toQ (emitCut_same _ _ _))
  · refine Preserves.bind hR (readPosition_preserves hR k) fun p => ?_
    refine Preserves.bind hR (toR _ (removeSelector_q p)) fun _ => ?_
    refine Preserves.bind hR (setFacet_r k _) fun _ => ?_
    refine Preserves.bind hR (toR _ (setPosition_q k _)) fun _ => ?_
    exact toR _ (toQ (emitCut_same _ _ _))
  · refine Preserves.bind hR (setFacet_r k t) fun _ => ?_
    exact toR _ (toQ (emitCut_same _ _ _))

/-- After a successful `cut k t`, `k` routes to `t`. -/
theorem cut_post (k : Uint256) (t : Address) :
    Establishes (fun s' => wordToAddress (facetBits s' k.val) = t) (TinyDiamond.cut k t) := by
  have hK : ∀ s s', wordToAddress (facetBits s k.val) = t → FK k.val s s' →
      wordToAddress (facetBits s' k.val) = t := by
    intro s s' h hfk; unfold FK at hfk; rw [hfk]; exact h
  have hF := fk_preorder k.val
  unfold TinyDiamond.cut
  refine Establishes.bind_right fun b => Establishes.bind_right fun _ => ?_
  intro s a s' h
  change Verity.bind _ _ s = _ at h
  unfold Verity.bind at h
  rw [readFacet_state] at h
  simp only at h
  split at h
  · revert h
    apply Establishes.ite (G := fun s' => wordToAddress (facetBits s' k.val) = t)
    · intro _
      refine Establishes.bind_right fun p => ?_
      refine Establishes.bind_left hK (setFacet_post k t) fun _ => ?_
      exact Preserves.bind hF (toFK _ (setPosition_q k p)) fun _ => toFK _ (toQ (emitCut_same _ _ _))
    · intro _
      apply Establishes.ite
      · intro ht
        have ht' : t = zeroAddress := by simpa using ht
        subst ht'
        refine Establishes.bind_right fun p => Establishes.bind_right fun _ => ?_
        refine Establishes.bind_left hK (setFacet_post k _) fun _ => ?_
        exact Preserves.bind hF (toFK _ (setPosition_q k _)) fun _ => toFK _ (toQ (emitCut_same _ _ _))
      · intro _
        refine Establishes.bind_left hK (setFacet_post k t) fun _ => ?_
        exact toFK _ (toQ (emitCut_same _ _ _))
  · rename_i hne
    cases h
    simp only [bne_iff_ne, ne_eq, not_not] at hne
    exact hne

end Diamond.Routing
