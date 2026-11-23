import TinyDiamond.Routing

/-!
# TinyDiamond properties

Theorems about the executable semantics of `Diamond.TinyDiamond` (the Lean functions that the
Verity compiler lowers to the bytecode in `out/`). A selector is handled as its left-aligned
word `key` (`toUint256 sel`, the Solidity mapping key). The observables are read the way the
contract's own views read them (`getTarget_eq`, `selectorRestriction_eq`, `admin_eq`).
-/

namespace Diamond.Proofs

open Verity
open Contracts
open Diamond
open Diamond.Frame
open Diamond.Packing
open Diamond.Routing

/-! ## Observables -/

/-- The facet `key` routes to (`address(0)`: not routed). -/
def targetOf (s : ContractState) (key : Uint256) : Address := wordToAddress (facetBits s key.val)

/-- The only caller allowed to call `key` through the fallback (`address(0)`: anyone). -/
def restrictionOf (s : ContractState) (key : Uint256) : Address :=
  wordToAddress (restrictionWord s key.val)

def adminOf (s : ContractState) : Address := s.storageAddr ADMIN

theorem getTarget_eq (sel : Contracts.Bytes4) (s : ContractState) :
    TinyDiamond.getTarget sel s = ContractResult.success (targetOf s (toUint256 sel)) s := by
  simp only [TinyDiamond.getTarget, Bind.bind, Verity.bind, readFacet_state]
  rfl

theorem selectorToFacet_eq (sel : Contracts.Bytes4) (s : ContractState) :
    TinyDiamond.selectorToFacet sel s = ContractResult.success (targetOf s (toUint256 sel)) s := by
  simp only [TinyDiamond.selectorToFacet, Bind.bind, Verity.bind, readFacet_state]
  rfl

theorem selectorRestriction_eq (sel : Contracts.Bytes4) (s : ContractState) :
    TinyDiamond.selectorRestriction sel s =
      ContractResult.success (restrictionOf s (toUint256 sel)) s := rfl

theorem admin_eq (s : ContractState) :
    TinyDiamond.admin s = ContractResult.success (adminOf s) s := rfl

/-! ## Access control -/

/-- The admin, or the diamond itself (a facet calling back into it). -/
def Authorized (s : ContractState) : Prop := s.sender = adminOf s ∨ s.sender = s.thisAddress

theorem requireAdmin_eq (s : ContractState) :
    TinyDiamond.requireAdmin s =
      if s.sender = adminOf s ∨ s.sender = s.thisAddress then ContractResult.success () s
      else ContractResult.revert "TinyDiamond: caller is not admin" s := by
  simp only [TinyDiamond.requireAdmin, TinyDiamond.adminSlot, Bind.bind, Verity.bind, msgSender,
    getStorageAddr, Contracts.contractAddress, Verity.contractAddress, Verity.require,
    ContractState.readAddrSlot, adminOf]
  by_cases h : s.sender = s.storageAddr ADMIN ∨ s.sender = s.thisAddress <;> simp [h]

theorem requireAdmin_preserves {P : ContractState → ContractState → Prop} (hP : Preorder P) :
    Preserves P TinyDiamond.requireAdmin :=
  Preserves.of_state hP (by
    intro s a s' h
    rw [requireAdmin_eq] at h
    split at h <;> cases h; rfl)

/-- Only the admin or the diamond itself can call `sharpCut`. -/
theorem sharpCut_reverts_of_not_authorized (s : ContractState) (sel : Contracts.Bytes4)
    (t : Address) (h : ¬ Authorized s) :
    (TinyDiamond.sharpCut sel t).run s =
      ContractResult.revert "TinyDiamond: caller is not admin" s := by
  have hr : TinyDiamond.requireAdmin s =
      ContractResult.revert "TinyDiamond: caller is not admin" s := by
    rw [requireAdmin_eq, if_neg (show ¬(s.sender = adminOf s ∨ s.sender = s.thisAddress) from h)]
  simp only [TinyDiamond.sharpCut, Contract.run, Bind.bind, Verity.bind, hr]

/-- Only the admin or the diamond itself can call `restrict`. -/
theorem restrict_reverts_of_not_authorized (s : ContractState) (sel : Contracts.Bytes4)
    (t : Address) (h : ¬ Authorized s) :
    (TinyDiamond.restrict sel t).run s =
      ContractResult.revert "TinyDiamond: caller is not admin" s := by
  have hr : TinyDiamond.requireAdmin s =
      ContractResult.revert "TinyDiamond: caller is not admin" s := by
    rw [requireAdmin_eq, if_neg (show ¬(s.sender = adminOf s ∨ s.sender = s.thisAddress) from h)]
  simp only [TinyDiamond.restrict, Contract.run, Bind.bind, Verity.bind, hr]

/-! ## Built-in selectors are immutable -/

/-- The selectors compiled into the diamond (left-aligned words). -/
def builtinKeys : List Uint256 :=
  [TinyDiamond.SEL_SHARP_CUT, TinyDiamond.SEL_RESTRICT, TinyDiamond.SEL_ADMIN,
    TinyDiamond.SEL_GET_TARGET, TinyDiamond.SEL_SELECTOR_TO_FACET,
    TinyDiamond.SEL_SELECTOR_RESTRICTION]

theorem isBuiltin_of_mem (k : Uint256) (s : ContractState) (h : k ∈ builtinKeys) :
    TinyDiamond.isBuiltin k s = ContractResult.success true s := by
  simp only [builtinKeys, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;> rfl

theorem cut_reverts_of_builtin (s : ContractState) (k : Uint256) (t : Address)
    (h : k ∈ builtinKeys) :
    TinyDiamond.cut k t s = ContractResult.revert "TinyDiamond: immutable function" s := by
  simp [TinyDiamond.cut, isBuiltin_of_mem k s h, Verity.require, Bind.bind, Verity.bind]

/-- `sharpCut` cannot reroute a built-in selector, whoever calls it. -/
theorem sharpCut_reverts_of_builtin (s : ContractState) (sel : Contracts.Bytes4) (t : Address)
    (h : toUint256 sel ∈ builtinKeys) :
    ∃ msg, (TinyDiamond.sharpCut sel t).run s = ContractResult.revert msg s := by
  by_cases ha : Authorized s
  · refine ⟨"TinyDiamond: immutable function", ?_⟩
    unfold Authorized at ha
    simp [TinyDiamond.sharpCut, Contract.run, Bind.bind, Verity.bind, requireAdmin_eq, ha,
      cut_reverts_of_builtin s _ t h]
  · exact ⟨_, sharpCut_reverts_of_not_authorized s sel t ha⟩

/-- `restrict` cannot restrict a built-in selector, whoever calls it. -/
theorem restrict_reverts_of_builtin (s : ContractState) (sel : Contracts.Bytes4) (t : Address)
    (h : toUint256 sel ∈ builtinKeys) :
    ∃ msg, (TinyDiamond.restrict sel t).run s = ContractResult.revert msg s := by
  by_cases ha : Authorized s
  · refine ⟨"TinyDiamond: immutable function", ?_⟩
    unfold Authorized at ha
    simp [TinyDiamond.restrict, Contract.run, Bind.bind, Verity.bind, requireAdmin_eq, ha,
      isBuiltin_of_mem _ s h, Verity.require]
  · exact ⟨_, restrict_reverts_of_not_authorized s sel t ha⟩

/-! ## `sharpCut` -/

theorem run_success {α : Type} {c : Contract α} {s s' : ContractState} {a : α}
    (h : c.run s = ContractResult.success a s') : c s = ContractResult.success a s' := by
  unfold Contract.run at h
  split at h <;> simp_all

/-- After a successful `sharpCut sel t`, `sel` routes to `t` (`t = 0`: `sel` is removed). -/
theorem sharpCut_routes (s s' : ContractState) (sel : Contracts.Bytes4) (t : Address)
    (h : (TinyDiamond.sharpCut sel t).run s = ContractResult.success () s') :
    targetOf s' (toUint256 sel) = t := by
  have hs := run_success h
  unfold TinyDiamond.sharpCut at hs
  exact Establishes.bind_right (fun _ => cut_post (toUint256 sel) t) s () s' hs

/-- `sharpCut sel t` changes no other selector's route, no restriction and not the admin. -/
theorem sharpCut_frame (s s' : ContractState) (sel : Contracts.Bytes4) (t : Address)
    (h : (TinyDiamond.sharpCut sel t).run s = ContractResult.success () s') :
    (∀ k, k ≠ toUint256 sel → targetOf s' k = targetOf s k) ∧
      (∀ k, restrictionOf s' k = restrictionOf s k) ∧ adminOf s' = adminOf s := by
  have hs := run_success h
  unfold TinyDiamond.sharpCut at hs
  have hr := Preserves.bind (r_preorder _) (requireAdmin_preserves (r_preorder _))
    (fun _ => cut_r (toUint256 sel) t) s () s' hs
  refine ⟨fun k hk => ?_, fun k => ?_, ?_⟩
  · have hv : k.val ≠ (toUint256 sel).val := fun he => hk (Verity.Core.Uint256.ext he)
    simp only [targetOf, hr.1 k.val hv]
  · simp only [restrictionOf, hr.2.1 k.val]
  · simp only [adminOf, ContractState.storageAddr, hr.2.2]

/-! ## `restrict` -/

/-- Every route, every restriction but `k`'s, and the admin are unchanged. -/
def RR (k : Nat) (s s' : ContractState) : Prop :=
  (∀ k', facetBits s' k' = facetBits s k') ∧
    (∀ k', k' ≠ k → restrictionWord s' k' = restrictionWord s k') ∧
    s'.storageWords (.addr ADMIN) = s.storageWords (.addr ADMIN)

theorem rr_preorder (k : Nat) : Preorder (RR k) :=
  ⟨fun _ => ⟨fun _ => rfl, fun _ _ => rfl, rfl⟩,
   fun _ _ _ h₁ h₂ => ⟨fun k' => (h₂.1 k').trans (h₁.1 k'),
     fun k' hk => (h₂.2.1 k' hk).trans (h₁.2.1 k' hk), h₂.2.2.trans h₁.2.2⟩⟩

theorem setRestriction_rr (k : Uint256) (v : Uint256) :
    Preserves (RR k.val) (setMappingN TinyDiamond.restriction [{ word := StorageKey.toWord k }] v) := by
  intro s x s' h
  cases h
  refine ⟨fun k' => ?_, fun k' hk => ?_, ?_⟩
  · simp [facetBits, ContractState.readMapChain_writeMapChain, TinyDiamond.restriction,
      MappingKeyWord.words]
  · simp [restrictionWord, ContractState.readMapChain_writeMapChain, TinyDiamond.restriction,
      MappingKeyWord.words, hk]
  · simp

theorem setRestriction_post (k : Uint256) (v : Uint256) :
    Establishes (fun s' => restrictionWord s' k.val = v)
      (setMappingN TinyDiamond.restriction [{ word := StorageKey.toWord k }] v) := by
  intro s x s' h
  cases h
  simp [restrictionWord, TinyDiamond.restriction, MappingKeyWord.words]

/-- After a successful `restrict sel t`, only `t` may call `sel` through the fallback
(`t = 0`: anyone). -/
theorem restrict_sets (s s' : ContractState) (sel : Contracts.Bytes4) (t : Address)
    (h : (TinyDiamond.restrict sel t).run s = ContractResult.success () s') :
    restrictionOf s' (toUint256 sel) = t := by
  have hs := run_success h
  unfold TinyDiamond.restrict at hs
  have hw : restrictionWord s' (toUint256 sel).val = addressToWord t :=
    (Establishes.bind_right fun _ => Establishes.bind_right fun _ => Establishes.bind_right
      fun _ => setRestriction_post _ _) s () s' hs
  unfold restrictionOf
  rw [hw]
  apply Verity.Core.Address.ext
  have ht : t.val < 2 ^ 160 := t.isLt
  show (t.val % 2 ^ 256) % 2 ^ 160 = t.val
  rw [Nat.mod_eq_of_lt (by omega : t.val < 2 ^ 256), Nat.mod_eq_of_lt ht]

/-- `restrict sel t` changes no route, no other restriction and not the admin. -/
theorem restrict_frame (s s' : ContractState) (sel : Contracts.Bytes4) (t : Address)
    (h : (TinyDiamond.restrict sel t).run s = ContractResult.success () s') :
    (∀ k, targetOf s' k = targetOf s k) ∧
      (∀ k, k ≠ toUint256 sel → restrictionOf s' k = restrictionOf s k) ∧
      adminOf s' = adminOf s := by
  have hs := run_success h
  unfold TinyDiamond.restrict at hs
  have hP := rr_preorder (toUint256 sel).val
  have hr := Preserves.bind hP (requireAdmin_preserves hP) (fun _ =>
    Preserves.bind hP (isBuiltin_preserves hP _) fun _ =>
      Preserves.bind hP (Preserves.require hP _ _) fun _ => setRestriction_rr _ _) s () s' hs
  refine ⟨fun k => ?_, fun k hk => ?_, ?_⟩
  · simp only [targetOf, hr.1 k.val]
  · have hv : k.val ≠ (toUint256 sel).val := fun he => hk (Verity.Core.Uint256.ext he)
    simp only [restrictionOf, hr.2.1 k.val hv]
  · simp only [adminOf, ContractState.storageAddr, hr.2.2]

/-! ## Fallback -/

/-- `msg.sig` as the fallback reads it: the first calldata word, masked to its first 4 bytes. -/
def msgSig (s : ContractState) : Uint256 :=
  Contracts.bitAnd
    (Verity.Core.Uint256.ofNat
      (Compiler.CompilationModel.Denote.calldataloadWord s.selector s.calldata
      (Verity.Core.Uint256.val 0)))
    TinyDiamond.SELECTOR_MASK

theorem require_false (m : String) (s : ContractState) :
    Verity.require false m s = ContractResult.revert m s := rfl

/-- A call to an unrouted selector reverts ("selector not found"). -/
theorem fallback_reverts_of_unrouted (ectx : ExecutableCallContext) (s : ContractState)
    (h : targetOf s (msgSig s) = zeroAddress) :
    (TinyDiamond.__verity_fallback_registry ectx).run s =
      ContractResult.revert "TinyDiamond: selector not found" s := by
  have hc : (StorageWord.fromWord (α := Address) (facetBits s (msgSig s).val) != zeroAddress)
      = false := by
    have e : StorageWord.fromWord (α := Address) (facetBits s (msgSig s).val) =
        targetOf s (msgSig s) := rfl
    rw [e, h]; rfl
  simp only [TinyDiamond.__verity_fallback_registry, Contract.run, Bind.bind, Verity.bind,
    Contracts.calldataloadLive]
  rw [readFacet_state]
  dsimp only
  unfold msgSig at hc
  rw [hc, require_false]

theorem require_true (m : String) (s : ContractState) :
    Verity.require true m s = ContractResult.success () s := rfl

/-- A routed selector restricted to another caller reverts ("caller is not allowed"). -/
theorem fallback_reverts_of_restricted (ectx : ExecutableCallContext) (s : ContractState)
    (h₁ : targetOf s (msgSig s) ≠ zeroAddress)
    (h₂ : restrictionWord s (msgSig s).val ≠ 0)
    (h₃ : restrictionWord s (msgSig s).val ≠ addressToWord s.sender) :
    (TinyDiamond.__verity_fallback_registry ectx).run s =
      ContractResult.revert "TinyDiamond: caller is not allowed" s := by
  have hc : (StorageWord.fromWord (α := Address) (facetBits s (msgSig s).val) != zeroAddress)
      = true := by
    have e : StorageWord.fromWord (α := Address) (facetBits s (msgSig s).val) =
        targetOf s (msgSig s) := rfl
    rw [e]; simpa using h₁
  have hr : (restrictionWord s (msgSig s).val == 0 ||
      restrictionWord s (msgSig s).val == addressToWord s.sender) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨h₂, h₃⟩
  simp only [TinyDiamond.__verity_fallback_registry, Contract.run, Bind.bind, Verity.bind,
    Contracts.calldataloadLive]
  rw [readFacet_state]
  dsimp only
  have hr' : (s.readMapChain TinyDiamond.restriction.slot
      (MappingKeyWord.words [{ word := StorageKey.toWord (msgSig s) }]) 0 == 0 ||
      s.readMapChain TinyDiamond.restriction.slot
      (MappingKeyWord.words [{ word := StorageKey.toWord (msgSig s) }]) 0 ==
        addressToWord s.sender) = false := hr
  unfold msgSig at hc hr'
  rw [hc, require_true]
  dsimp only [getMappingN, msgSender]
  rw [hr', require_false]

/-! ## Constructor -/

theorem contractAddress_same : Preserves Same Contracts.contractAddress :=
  Preserves.of_state same_preorder (by intro s a s' h; cases h; rfl)

/-- The deployer becomes the admin. -/
theorem constructor_sets_admin (s s' : ContractState)
    (h : TinyDiamond.constructor.run s = ContractResult.success () s') :
    adminOf s' = s.sender := by
  have hs := run_success h
  unfold TinyDiamond.constructor at hs
  change Verity.bind msgSender _ s = _ at hs
  unfold Verity.bind at hs
  simp only [msgSender] at hs
  have hK : ∀ a b, adminOf a = s.sender → Same a b → adminOf b = s.sender := by
    intro a b ha hab; unfold Same at hab; simp only [adminOf, ContractState.storageAddr, hab]
    exact ha
  have hset : Establishes (fun st => adminOf st = s.sender)
      (setStorageAddr TinyDiamond.adminSlot s.sender) := by
    intro st x st' hst; cases hst
    simp [adminOf, TinyDiamond.adminSlot, ContractState.writeAddrSlot, ContractState.storageAddr]
  refine Establishes.bind_left hK hset (fun _ => ?_) s () s' hs
  refine Preserves.bind same_preorder contractAddress_same fun _ => ?_
  intro st x st' h; cases h; rfl

end Diamond.Proofs
