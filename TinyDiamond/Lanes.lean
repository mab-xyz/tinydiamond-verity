import Contracts.Common
import Mathlib.Tactic

/-!
# Packed 32-bit lanes

The selector array packs eight `bytes4` per word: selector `i` is lane `i % 8` of word
`i / 8`, i.e. bits `32 * (i % 8)` .. `32 * (i % 8) + 31`. `laneU`/`setLaneU` are the exact
`Uint256` expressions of `TinyDiamond.selectorAt`/`setSelectorAt`; the lemmas are proved by
moving to `BitVec 256` and bit-blasting each of the 8 × 8 lane pairs.
-/

namespace Diamond.Lanes

open Verity.Core

def bv (a : Uint256) : BitVec 256 := BitVec.ofNat 256 a.val

theorem modulus_eq : Uint256.modulus = 2 ^ 256 := rfl

theorem bv_inj {a b : Uint256} (h : bv a = bv b) : a = b := by
  apply Uint256.ext
  have h' := congrArg BitVec.toNat h
  simp only [bv, BitVec.toNat_ofNat] at h'
  have ha : a.val < 2 ^ 256 := a.isLt
  have hb : b.val < 2 ^ 256 := b.isLt
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'

theorem toNat_bv (a : Uint256) : (bv a).toNat = a.val := by
  simp only [bv, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt a.isLt

theorem bv_and (a b : Uint256) : bv (Uint256.and a b) = bv a &&& bv b := by
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_bv, BitVec.toNat_and, Uint256.and, Uint256.val_ofNat, modulus_eq, Nat.land_eq]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left a.isLt)

theorem bv_or (a b : Uint256) : bv (Uint256.or a b) = bv a ||| bv b := by
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_bv, BitVec.toNat_or, Uint256.or, Uint256.val_ofNat, modulus_eq, Nat.lor_eq]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow a.isLt b.isLt)

theorem bv_shl (s a : Uint256) : bv (Uint256.shl s a) = bv a <<< s.val := by
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_bv, BitVec.toNat_shiftLeft, Uint256.shl, Uint256.val_ofNat, modulus_eq]

theorem bv_shr (s a : Uint256) : bv (Uint256.shr s a) = bv a >>> s.val := by
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_bv, BitVec.toNat_ushiftRight, Uint256.shr, Uint256.val_ofNat, modulus_eq]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) a.isLt)

theorem bv_sub (a b : Uint256) : bv (Uint256.sub a b) = bv a - bv b := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt
  simp only [UINT256_MODULUS] at ha hb
  simp only [toNat_bv, BitVec.toNat_sub, Uint256.sub]
  split
  · simp only [Uint256.val_ofNat, modulus_eq]; omega
  · simp only [Uint256.val_ofNat, Uint256.modulus, UINT256_MODULUS]; omega

theorem bv_ofNat (n : Nat) : bv (Uint256.ofNat n) = BitVec.ofNat 256 n := by
  apply BitVec.eq_of_toNat_eq
  simp [toNat_bv, Uint256.val_ofNat, modulus_eq]

/-- Lane `r` of `w` (`selectorAt`'s expression). -/
def laneU (w : Uint256) (r : Nat) : Uint256 :=
  Uint256.and (Uint256.shr (Uint256.ofNat (32 * r)) w) (Uint256.ofNat 4294967295)

/-- `w` with lane `r` replaced by `v` (`setSelectorAt`'s expression). -/
def setLaneU (w : Uint256) (r : Nat) (v : Uint256) : Uint256 :=
  Uint256.or (Uint256.sub w (Uint256.and w (Uint256.shl (Uint256.ofNat (32 * r))
    (Uint256.ofNat 4294967295)))) (Uint256.shl (Uint256.ofNat (32 * r)) v)

theorem sub_and_eq (x m : BitVec 256) : x - (x &&& m) = x &&& ~~~m := by
  have hd : (x &&& m) &&& (x &&& ~~~m) = 0#256 := by
    ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases x[i] <;> cases m[i] <;> rfl
  have hx : x = (x &&& m) + (x &&& ~~~m) := by
    rw [BitVec.add_eq_or_of_and_eq_zero _ _ hd]
    ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
    cases x[i] <;> cases m[i] <;> rfl
  calc x - (x &&& m) = ((x &&& m) + (x &&& ~~~m)) - (x &&& m) := by rw [← hx]
    _ = x &&& ~~~m := by rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem mask32_getElem (i : Nat) (hi : i < 256) :
    (4294967295#256)[i] = decide (i < 32) := by
  rw [show (4294967295#256) = BitVec.ofNat 256 (2 ^ 32 - 1) from rfl, ← BitVec.getLsbD_eq_getElem,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  simp [hi]

theorem mask32_getLsbD (j : Nat) : (4294967295#256).getLsbD j = (decide (j < 256) && decide (j < 32)) := by
  rw [show (4294967295#256) = BitVec.ofNat 256 (2 ^ 32 - 1) from rfl,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]

theorem high (v : BitVec 256) (hv : v.toNat < 2 ^ 32) (k : Nat) (hk : 32 ≤ k) : v.getLsbD k = false := by
  rw [BitVec.getLsbD, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hk))]

theorem lane_setLane_bv (W V : BitVec 256) (r r' : Nat) (hr : r < 8) (hr' : r' < 8) (hv : V.toNat < 2 ^ 32) :
    (((W &&& ~~~(4294967295#256 <<< (32 * r))) ||| (V <<< (32 * r))) >>> (32 * r') &&& 4294967295#256)
      = if r = r' then V else (W >>> (32 * r') &&& 4294967295#256) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hV := high V hv
  split
  · rename_i h; subst h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, mask32_getLsbD]
    by_cases h32 : i < 32
    · have : 32 * r + i < 256 := by omega
      simp [h32, hi, this]
    · simp [h32, hi]
      have := hV i (by omega)
      rwa [BitVec.getLsbD_eq_getElem hi] at this
  · rename_i h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, mask32_getLsbD]
    by_cases h32 : i < 32
    · simp only [h32, hi, decide_true, Bool.and_true]
      have hlt : 32 * r' + i < 256 := by omega
      rcases Nat.lt_or_gt_of_ne h with hrr | hrr
      · have h1 : ¬ 32 * r' + i < 32 * r := by omega
        have h2 : ¬ 32 * r' + i - 32 * r < 32 := by omega
        simp [hlt, h1, h2, hV _ (by omega : 32 ≤ 32 * r' + i - 32 * r)]
      · have h1 : 32 * r' + i < 32 * r := by omega
        simp [hlt, h1]
    · simp [h32]

/-- Writing lane `r` sets lane `r` and keeps the seven others. -/
theorem lane_setLane (w v : Uint256) (r r' : Nat) (hr : r < 8) (hr' : r' < 8)
    (hv : v.val < 2 ^ 32) :
    laneU (setLaneU w r v) r' = if r = r' then v else laneU w r' := by
  have hs : 32 * r % 2 ^ 256 = 32 * r := Nat.mod_eq_of_lt (by omega)
  have hs' : 32 * r' % 2 ^ 256 = 32 * r' := Nat.mod_eq_of_lt (by omega)
  have hb : (bv v).toNat < 2 ^ 32 := by rw [toNat_bv]; exact hv
  have key := lane_setLane_bv (bv w) (bv v) r r' hr hr' hb
  split
  · rename_i h
    apply bv_inj
    simp only [laneU, setLaneU, bv_and, bv_or, bv_shl, bv_shr, bv_sub, bv_ofNat, sub_and_eq,
      Uint256.val_ofNat, modulus_eq, hs, hs']
    rw [if_pos h] at key; exact key
  · rename_i h
    apply bv_inj
    simp only [laneU, setLaneU, bv_and, bv_or, bv_shl, bv_shr, bv_sub, bv_ofNat, sub_and_eq,
      Uint256.val_ofNat, modulus_eq, hs, hs']
    rw [if_neg h] at key; exact key

end Diamond.Lanes
