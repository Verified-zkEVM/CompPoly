/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import CompPoly.Fields.Binary.Tower.Concrete.Coordinates
public import CompPoly.Data.RingTheory.AlgebraTower.Coordinates

/-!
# Relative coordinates for concrete binary tower fields

`ConcreteBinaryTower.Coordinates.coordinates h` identifies level `j` with
`2 ^ (j - i)` coefficients in level `i`, for `h : i ≤ j`. The scalar action is induced by
the existing concrete tower embedding. Coordinate `q` is the block of `2 ^ i` bits starting
at bit `2 ^ i * q`; blocks and bits within each block retain their numeric order.

The equivalence composes `succCoordinates` through `AlgebraTower.natCoordinatesConstOfLE`.
Its inverse `pack` reconstructs the original word. The readback theorems relate the algebraic
coordinates to bitvector slicing and natural-number bit blocks. They refer to raw stored words,
which differ from field numerals in characteristic two.

The coefficient ordering follows the relative multilinear basis of [DP23], §2.3:
earlier tower generators correspond to lower index bits.

## References

* [Diamond, B. E. and Posen, J., *Succinct arguments over towers of binary fields*][DP23]
-/

public section

namespace ConcreteBinaryTower.Coordinates

open AlgebraTower

/-- Coordinates of level `j` over level `i`, ordered by increasing bit-block offset, for the
scalar action induced by the concrete tower embedding associated with `h`. -/
def coordinates {i j : ℕ} (h : i ≤ j) :
    letI := ConcreteBTFieldAlgebra h
    ConcreteBTField j ≃ₗ[ConcreteBTField i] (Fin (2 ^ (j - i)) → ConcreteBTField i) :=
  natCoordinatesConstOfLE succCoordinates h

/-- The relative equivalence is the constant-two composition of the low-first successor
coordinate equivalences, with the scalar action induced by the concrete tower embedding. -/
theorem coordinates_eq_natCoordinatesConstOfLE {i j : ℕ} (h : i ≤ j) :
    coordinates h = natCoordinatesConstOfLE succCoordinates h := by
  rfl

/-- Construct a level-`j` word from level-`i` coefficients, with coefficient `q` occupying
the block of `2 ^ i` bits starting at bit `2 ^ i * q`. -/
def pack {i j : ℕ} (h : i ≤ j) (c : Fin (2 ^ (j - i)) → ConcreteBTField i) :
    ConcreteBTField j := (coordinates h).symm c

/-- Reading the coordinates of a packed word recovers every input coefficient. -/
@[simp] theorem coordinates_pack {i j : ℕ} (h : i ≤ j)
    (c : Fin (2 ^ (j - i)) → ConcreteBTField i) : coordinates h (pack h c) = c :=
  (coordinates h).apply_symm_apply c

/-- Packing all coordinates recovers the original word. -/
@[simp] theorem pack_coordinates {i j : ℕ} (h : i ≤ j) (x : ConcreteBTField j) :
    pack h (coordinates h x) = x := (coordinates h).symm_apply_apply x

/-- At equal endpoints the single coordinate is the original word. -/
@[simp] theorem coordinates_self (i : ℕ) (h : i ≤ i) (x : ConcreteBTField i)
    (q : Fin (2 ^ (i - i))) : coordinates h x q = x :=
  natCoordinatesConstOfLE_self succCoordinates i x q

/-- Packing at equal endpoints returns the single coefficient. -/
@[simp] theorem pack_self (i : ℕ) (h : i ≤ i) (c : Fin (2 ^ (i - i)) → ConcreteBTField i) :
    pack h c = c 0 :=
  (coordinates_self i h (pack h c) 0).symm.trans (congrFun (coordinates_pack h c) 0)

/-- Coordinates preserve the canonical field addition, coefficient by coefficient. -/
theorem coordinates_add {i j : ℕ} (h : i ≤ j) (x y : ConcreteBTField j) :
    coordinates h (x + y) = coordinates h x + coordinates h y :=
  (coordinates h).map_add x y

/-- Packing preserves coefficientwise canonical field addition. -/
theorem pack_add {i j : ℕ} (h : i ≤ j)
    (c d : Fin (2 ^ (j - i)) → ConcreteBTField i) :
    pack h (c + d) = pack h c + pack h d := (coordinates h).symm.map_add c d

/-- The tower embedding's scalar action multiplies each coordinate by the lower-level scalar. -/
theorem coordinates_smul {i j : ℕ} (h : i ≤ j) (a : ConcreteBTField i)
    (x : ConcreteBTField j) (q : Fin (2 ^ (j - i))) :
    letI := ConcreteBTFieldAlgebra h
    coordinates h (a • x) q = a * coordinates h x q :=
  congrFun ((coordinates h).map_smul a x) q

/-- Scaling all coefficients commutes with packing under the tower embedding's scalar action. -/
theorem pack_smul {i j : ℕ} (h : i ≤ j) (a : ConcreteBTField i)
    (c : Fin (2 ^ (j - i)) → ConcreteBTField i) :
    letI := ConcreteBTFieldAlgebra h
    pack h (fun q => a * c q) = a • pack h c :=
  (coordinates h).symm.map_smul a c

private theorem low_eq_setWidth (k : ℕ) (x : ConcreteBTField (k + 1)) :
    (low k x).toBitVec = x.toBitVec.setWidth (2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [ConcreteBTField.toBitVec, low, split, ← BitVec.dcast_bitvec_toNat_eq,
    BitVec.extractLsb, BitVec.extractLsb', BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.add_one_sub_one, Nat.sub_zero, Nat.shiftRight_zero]
  rw [Nat.sub_add_cancel ((Nat.one_le_two_pow : 1 ≤ 2 ^ k))]

private theorem high_eq_setWidth (k : ℕ) (x : ConcreteBTField (k + 1)) :
    (high k x).toBitVec = (BitVec.ushiftRight x.toBitVec (2 ^ k)).setWidth (2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [ConcreteBTField.toBitVec, high, split, ← BitVec.dcast_bitvec_toNat_eq,
    BitVec.extractLsb, BitVec.extractLsb', BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.add_one_sub_one]
  congr 2
  have hp := (Nat.one_le_two_pow : 1 ≤ 2 ^ k)
  rw [pow_succ, mul_two]
  omega

private theorem succCoordinates_low (k : ℕ) (x : ConcreteBTField (k + 1)) :
    (succCoordinates k x 0).toBitVec = x.toBitVec.setWidth (2 ^ k) := by
  rw [succCoordinates_apply]
  exact low_eq_setWidth k x

private theorem succCoordinates_high (k : ℕ) (x : ConcreteBTField (k + 1)) :
    (succCoordinates k x 1).toBitVec =
      (BitVec.ushiftRight x.toBitVec (2 ^ k)).setWidth (2 ^ k) := by
  rw [succCoordinates_apply]
  exact high_eq_setWidth k x

private theorem slice_low {w m len offset : ℕ} (x : BitVec w)
    (h : offset + len ≤ m) :
    ((x.setWidth m) >>> offset).setWidth len = (x >>> offset).setWidth len := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have hm : offset + b < m := by omega
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hb, hm,
    decide_true, Bool.true_and]

private theorem slice_high {w m len offset : ℕ} (x : BitVec w)
    (h : offset + len ≤ m) :
    (((x >>> m).setWidth m) >>> offset).setWidth len =
      (x >>> (m + offset)).setWidth len := by
  rw [slice_low _ h]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, Nat.add_assoc]

private theorem height_bits (i n : ℕ) (x : ConcreteBTField (i + n))
    (q : Fin (AlgebraTower.coordinateSize (fun _ => 2) i n)) :
    (AlgebraTower.natCoordinates succCoordinates i n x q).toBitVec =
      (BitVec.ushiftRight x.toBitVec (2 ^ i * q.val)).setWidth (2 ^ i) := by
  induction n with
  | zero =>
      have hq : q.val = 0 := by
        have := q.isLt
        change q.val < 1 at this
        omega
      simp only [AlgebraTower.natCoordinates_zero, hq, Nat.mul_zero,
        BitVec.ushiftRight_eq, BitVec.ushiftRight_zero]
      exact (BitVec.setWidth_eq x.toBitVec).symm
  | succ n ih =>
      rw [AlgebraTower.natCoordinates_succ, ih]
      have size := AlgebraTower.coordinateSize_const 2 i n
      by_cases hq : q.val < 2 ^ n
      · have outer : q.divNat = 0 := by
          apply Fin.ext
          change q.val / AlgebraTower.coordinateSize (fun _ => 2) i n = 0
          rw [size, Nat.div_eq_of_lt hq]
        have inner : q.modNat.val = q.val := by
          change q.val % AlgebraTower.coordinateSize (fun _ => 2) i n = q.val
          rw [size, Nat.mod_eq_of_lt hq]
        rw [outer, inner, succCoordinates_low]
        change ((x.toBitVec.setWidth (2 ^ (i + n))) >>> (2 ^ i * q.val)).setWidth (2 ^ i) = _
        apply slice_low
        calc
          2 ^ i * q.val + 2 ^ i = 2 ^ i * (q.val + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ 2 ^ i * 2 ^ n := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hq)
          _ = 2 ^ (i + n) := (Nat.pow_add _ _ _).symm
      · have bound : q.val < 2 ^ n + 2 ^ n := by
          have hh := q.isLt
          change q.val < 2 * AlgebraTower.coordinateSize (fun _ => 2) i n at hh
          rw [size, two_mul] at hh
          exact hh
        have outer : q.divNat = 1 := by
          apply Fin.ext
          change q.val / AlgebraTower.coordinateSize (fun _ => 2) i n = 1
          rw [size]
          apply Nat.div_eq_of_lt_le <;> omega
        have inner : q.modNat.val = q.val - 2 ^ n := by
          change q.val % AlgebraTower.coordinateSize (fun _ => 2) i n = q.val - 2 ^ n
          rw [size, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [outer, inner, succCoordinates_high]
        change (((BitVec.ushiftRight x.toBitVec (2 ^ (i + n))).setWidth (2 ^ (i + n))) >>>
          (2 ^ i * (q.val - 2 ^ n))).setWidth (2 ^ i) = _
        have hcut : 2 ^ i * (q.val - 2 ^ n) + 2 ^ i ≤ 2 ^ (i + n) := by
          calc
            _ = 2 ^ i * (q.val - 2 ^ n + 1) := by rw [Nat.mul_add, Nat.mul_one]
            _ ≤ 2 ^ i * 2 ^ n := Nat.mul_le_mul_left _ (by omega)
            _ = 2 ^ (i + n) := (Nat.pow_add _ _ _).symm
        simp only [BitVec.ushiftRight_eq]
        rw [slice_high _ hcut]
        have offset : 2 ^ (i + n) + 2 ^ i * (q.val - 2 ^ n) = 2 ^ i * q.val := by
          rw [Nat.pow_add, ← Nat.mul_add, Nat.add_sub_of_le (by omega)]
        rw [offset]

private theorem bits_cast {i j : ℕ} (h : i = j) (x : ConcreteBTField i) :
    (cast (congrArg ConcreteBTField h) x).toBitVec = x.toBitVec.cast (congrArg (2 ^ ·) h) := by
  cases h
  rfl

/-- Coordinate `q` is the raw bit block of width `2 ^ i` starting at bit `2 ^ i * q`. -/
theorem coordinates_eq_setWidth_ushiftRight {i j : ℕ} (h : i ≤ j) (x : ConcreteBTField j)
    (q : Fin (2 ^ (j - i))) :
    coordinates h x q =
      ConcreteBTField.ofBitVec
        ((BitVec.ushiftRight x.toBitVec (2 ^ i * q.val)).setWidth (2 ^ i)) := by
  apply ConcreteBTField.toBitVec_injective
  rw [ConcreteBTField.toBitVec_ofBitVec]
  unfold coordinates
  rw [AlgebraTower.natCoordinatesConstOfLE_apply,
    AlgebraTower.natCoordinatesOfLE_apply, height_bits, bits_cast (Nat.add_sub_of_le h).symm]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.ushiftRight_eq, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_cast, Fin.val_cast]

/-- Encoding coordinate `q` returns the corresponding low-first bit block of the input word. -/
theorem toBitVec_coordinates {i j : ℕ} (h : i ≤ j) (x : ConcreteBTField j)
    (q : Fin (2 ^ (j - i))) :
    (coordinates h x q).toBitVec =
      (BitVec.ushiftRight x.toBitVec (2 ^ i * q.val)).setWidth (2 ^ i) := by
  rw [coordinates_eq_setWidth_ushiftRight, ConcreteBTField.toBitVec_ofBitVec]

/-- Reading bit `b` within coordinate `q` reads the bit at offset `2 ^ i * q + b`
in the original word. The bound keeps `b` inside the coefficient's bit width. -/
theorem getLsbD_coordinates {i j : ℕ} (h : i ≤ j) (x : ConcreteBTField j)
    (q : Fin (2 ^ (j - i))) (b : ℕ) (hb : b < 2 ^ i) :
    (coordinates h x q).toBitVec.getLsbD b = x.toBitVec.getLsbD (2 ^ i * q.val + b) := by
  rw [toBitVec_coordinates, BitVec.ushiftRight_eq]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hb,
    decide_true, Bool.true_and]

/-- The stored natural word of coordinate `q` is the block of `2 ^ i` bits starting at
bit `2 ^ i * q` in the original word. -/
theorem toNat_coordinates {i j : ℕ} (h : i ≤ j) (x : ConcreteBTField j)
    (q : Fin (2 ^ (j - i))) :
    (coordinates h x q).toNat =
      Nat.getMiddleBits (2 ^ i * q.val) (2 ^ i) x.toNat := by
  change (coordinates h x q).toBitVec.toNat =
    Nat.getMiddleBits (2 ^ i * q.val) (2 ^ i) x.toBitVec.toNat
  rw [toBitVec_coordinates, BitVec.ushiftRight_eq, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.getMiddleBits_eq_mod]

end ConcreteBinaryTower.Coordinates
