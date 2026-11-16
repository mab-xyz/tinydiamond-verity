import Contracts.Common

/-!
# Frame reasoning over `Contract` programs

`Preserves P c`: every successful run of `c` relates its pre- and post-state by `P`.
For a reflexive and transitive `P`, it composes through `bind`, `if` and the read-only
primitives, so a property of a whole function follows from properties of its steps.
-/

namespace Diamond.Frame

open Verity

def Preserves {α : Type} (P : ContractState → ContractState → Prop) (c : Contract α) : Prop :=
  ∀ s a s', c s = ContractResult.success a s' → P s s'

structure Preorder (P : ContractState → ContractState → Prop) : Prop where
  refl : ∀ s, P s s
  trans : ∀ s₁ s₂ s₃, P s₁ s₂ → P s₂ s₃ → P s₁ s₃

theorem Preserves.bind {α β : Type} {P : ContractState → ContractState → Prop} (hP : Preorder P)
    {c : Contract α} {f : α → Contract β} (hc : Preserves P c) (hf : ∀ a, Preserves P (f a)) :
    Preserves P (c >>= f) := by
  intro s b s' h
  change Verity.bind c f s = _ at h
  unfold Verity.bind at h
  rcases hcs : c s with ⟨a, s₁⟩ | ⟨msg, s₁⟩
  · rw [hcs] at h
    exact hP.trans _ _ _ (hc s a s₁ hcs) (hf a s₁ b s' h)
  · rw [hcs] at h; cases h

theorem Preserves.ite {α : Type} {P : ContractState → ContractState → Prop} {b : Prop} [Decidable b]
    {c₁ c₂ : Contract α} (h₁ : Preserves P c₁) (h₂ : Preserves P c₂) :
    Preserves P (if b then c₁ else c₂) := by
  by_cases hb : b
  · simpa [hb] using h₁
  · simpa [hb] using h₂

/-- A step that leaves the state unchanged when it succeeds. -/
theorem Preserves.of_state {α : Type} {P : ContractState → ContractState → Prop} (hP : Preorder P)
    {c : Contract α} (h : ∀ s a s', c s = ContractResult.success a s' → s' = s) :
    Preserves P c := by
  intro s a s' hs
  rw [h s a s' hs]
  exact hP.refl s

theorem Preserves.pure {α : Type} {P : ContractState → ContractState → Prop} (hP : Preorder P)
    (a : α) : Preserves P (Pure.pure a : Contract α) :=
  Preserves.of_state hP (by intro s b s' h; cases h; rfl)

theorem Preserves.require {P : ContractState → ContractState → Prop} (hP : Preorder P)
    (cond : Bool) (msg : String) : Preserves P (Verity.require cond msg) :=
  Preserves.of_state hP (by
    intro s a s' h
    unfold Verity.require at h
    split at h <;> cases h; rfl)

theorem Preserves.mono {α : Type} {P Q : ContractState → ContractState → Prop}
    (hPQ : ∀ s s', P s s' → Q s s') {c : Contract α} (h : Preserves P c) : Preserves Q c :=
  fun s a s' hs => hPQ s s' (h s a s' hs)

/-- `Establishes G c`: every successful run of `c` ends in a state satisfying `G`. -/
def Establishes {α : Type} (G : ContractState → Prop) (c : Contract α) : Prop :=
  ∀ s a s', c s = ContractResult.success a s' → G s'

theorem Establishes.bind_left {α β : Type} {G : ContractState → Prop}
    {K : ContractState → ContractState → Prop} (hK : ∀ s s', G s → K s s' → G s')
    {c : Contract α} {f : α → Contract β} (hc : Establishes G c) (hf : ∀ a, Preserves K (f a)) :
    Establishes G (c >>= f) := by
  intro s b s' h
  change Verity.bind c f s = _ at h
  unfold Verity.bind at h
  rcases hcs : c s with ⟨a, s₁⟩ | ⟨msg, s₁⟩
  · rw [hcs] at h
    exact hK _ _ (hc s a s₁ hcs) (hf a s₁ b s' h)
  · rw [hcs] at h; cases h

theorem Establishes.bind_right {α β : Type} {G : ContractState → Prop}
    {c : Contract α} {f : α → Contract β} (hf : ∀ a, Establishes G (f a)) :
    Establishes G (c >>= f) := by
  intro s b s' h
  change Verity.bind c f s = _ at h
  unfold Verity.bind at h
  rcases hcs : c s with ⟨a, s₁⟩ | ⟨msg, s₁⟩
  · rw [hcs] at h
    exact hf a s₁ b s' h
  · rw [hcs] at h; cases h

theorem Establishes.ite {α : Type} {G : ContractState → Prop} {b : Prop} [Decidable b]
    {c₁ c₂ : Contract α} (h₁ : b → Establishes G c₁) (h₂ : ¬b → Establishes G c₂) :
    Establishes G (if b then c₁ else c₂) := by
  by_cases hb : b
  · simpa [hb] using h₁ hb
  · simpa [hb] using h₂ hb

end Diamond.Frame
