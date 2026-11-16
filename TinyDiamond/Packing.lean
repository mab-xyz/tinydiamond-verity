import Contracts.Common

/-!
# The packed `facet | position` word

`facetOf[selector]` holds `{address facet; uint96 position}` in one word: the facet in bits
0..159, the position in bits 160..255. Verity reads and writes such members with private
helpers of `Contracts.Common`; `dec`/`enc` restate them (the bridge lemmas are `rfl`), and
the two lemmas below are the bit facts the routing proofs need.
-/

namespace Diamond.Packing

open Verity.Core

def mask (width : Nat) : Nat := 2 ^ width - 1

/-- `Contracts.decodePackedWord`. -/
def dec (word : Uint256) (offset width : Nat) : Uint256 :=
  Uint256.and (Uint256.shr offset word) (mask width)

/-- `Contracts.encodePackedWord`. -/
def enc (current value : Uint256) (offset width : Nat) : Uint256 :=
  let m := mask width
  let shiftedMask := Uint256.shl offset m
  let packedValue := Uint256.and value m
  let cleared := Uint256.and current (Uint256.not shiftedMask)
  Uint256.or cleared (Uint256.shl offset packedValue)

theorem structMemberAt_eq {κ α : Type} [Contracts.StorageKey κ] [Contracts.StorageWord α]
    (base off : Nat) (o w : Nat) (key : κ) (s : Verity.ContractState) :
    Contracts.structMemberAt (α := α) base off (some (o, w)) key s =
      Verity.ContractResult.success
        (Contracts.StorageWord.fromWord
          (dec (s.readMapChain base [Contracts.StorageKey.toWord key] off) o w)) s := rfl

theorem setStructMemberAt_eq {κ α : Type} [Contracts.StorageKey κ] [Contracts.StorageWord α]
    (base off : Nat) (o w : Nat) (key : κ) (v : α) (s : Verity.ContractState) :
    Contracts.setStructMemberAt base off (some (o, w)) key v s =
      Verity.ContractResult.success ()
        (s.writeMapChain base [Contracts.StorageKey.toWord key] off
          (enc (s.readMapChain base [Contracts.StorageKey.toWord key] off)
            (Contracts.StorageWord.toWord v) o w)) := rfl

private theorem modulus_eq : Uint256.modulus = 2 ^ 256 := rfl

/-- Writing the position (bits 160..255) keeps the facet (bits 0..159). -/
theorem dec_facet_enc_position (cur v : Uint256) :
    dec (enc cur v 160 96) 0 160 = dec cur 0 160 := by
  apply Uint256.ext
  simp only [dec, enc, mask, Uint256.and, Uint256.or, Uint256.not, Uint256.shl, Uint256.shr,
    Uint256.val_ofNat, Nat.land_eq, Nat.lor_eq, modulus_eq]
  have hnot : (MAX_UINT256 - (((2 ^ 96 - 1) % 2 ^ 256) <<< (160 % 2 ^ 256)) % 2 ^ 256) % 2 ^ 256
      = 2 ^ 160 - 1 := by decide
  rw [hnot]
  have h160 : (160 : Nat) % 2 ^ 256 = 160 := by decide
  have h0 : (0 : Nat) % 2 ^ 256 = 0 := by decide
  have hm96 : (2 ^ 96 - 1 : Nat) % 2 ^ 256 = 2 ^ 96 - 1 := by decide
  have hm160 : (2 ^ 160 - 1 : Nat) % 2 ^ 256 = 2 ^ 160 - 1 := by decide
  simp only [h160, h0, hm96, hm160, Nat.shiftRight_zero]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one]
  by_cases h : i < 160
  · have : i < 256 := by omega
    simp [h, this]
  · simp [h]

/-- Writing the facet (bits 0..159) and reading it back gives the low 160 bits written. -/
theorem dec_facet_enc_facet (cur v : Uint256) :
    (dec (enc cur v 0 160) 0 160).val = v.val % 2 ^ 160 := by
  simp only [dec, enc, mask, Uint256.and, Uint256.or, Uint256.not, Uint256.shl, Uint256.shr,
    Uint256.val_ofNat, Nat.land_eq, Nat.lor_eq, modulus_eq]
  have h0 : (0 : Nat) % 2 ^ 256 = 0 := by decide
  have hm160 : (2 ^ 160 - 1 : Nat) % 2 ^ 256 = 2 ^ 160 - 1 := by decide
  simp only [h0, hm160, Nat.shiftRight_zero, Nat.shiftLeft_zero]
  have hv : v.val < 2 ^ 256 := v.isLt
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_or,
    Nat.testBit_two_pow_sub_one]
  have hn : MAX_UINT256 - (2 ^ 160 - 1) = (2 ^ 96 - 1) <<< 160 := by decide
  by_cases h : i < 160
  · have : i < 256 := by omega
    rw [hn, Nat.testBit_shiftLeft]
    simp [h, this]
  · simp [h]

end Diamond.Packing
