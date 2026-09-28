/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import CompPoly.Fields.Binary.Tower.Concrete.Basis
public import CompPoly.Fields.Binary.Tower.Concrete.RelativeCoordinates
import CompPoly.Data.RingTheory.AlgebraTower.Basis

/-!
# Existing multilinear basis and concrete coordinates

The representation of `ConcreteBinaryTower.multilinearBasis` agrees at each numeric index
with `ConcreteBinaryTower.Coordinates.coordinates`. Consequently, packing a unit coefficient
vector computes the existing basis vector, and packing arbitrary coefficients is their linear
combination under the concrete tower embedding.

The proof compares the existing basis's generator-product formula with the successor-vector
law in `AlgebraTower.natBasisVector_succ`. Both use low-first coordinate order: earlier tower
generators correspond to lower index bits. An auxiliary basis constructed with
`Module.Basis.ofEquivFun` is private to the identification proof.

The generator-product basis and its ordering are those of [DP23], §2.3, with the
paper's generator `X_k` represented by `Z (k + 1)`.

## References

* [Diamond, B. E. and Posen, J., *Succinct arguments over towers of binary fields*][DP23]
-/

public section

namespace ConcreteBinaryTower.Coordinates

open AlgebraTower Module

private noncomputable def coordinateBasis {i j : ℕ} (h : i ≤ j) :
    let := ConcreteBTFieldAlgebra h
    Basis (Fin (2 ^ (j - i))) (ConcreteBTField i) (ConcreteBTField j) := by
  letI := ConcreteBTFieldAlgebra h
  exact Basis.ofEquivFun (coordinates h)

private theorem coordinateBasis_repr {i j : ℕ} (h : i ≤ j) (x : ConcreteBTField j)
    (q : Fin (2 ^ (j - i))) :
    let := ConcreteBTFieldAlgebra h
    (coordinateBasis h).repr x q = coordinates h x q := rfl

private theorem pack_single_eq_coordinateBasis {i j : ℕ} (h : i ≤ j)
    (q : Fin (2 ^ (j - i))) : pack h (Pi.single q 1) = coordinateBasis h q := by
  let := ConcreteBTFieldAlgebra h
  apply (coordinateBasis h).repr.injective
  ext r
  rw [coordinateBasis_repr, congrFun (coordinates_pack h _) r, Basis.repr_self]
  simp only [Pi.single_apply, Finsupp.single_apply, eq_comm]

private theorem coordinateBasis_eq_natBasisOfLE {i j : ℕ} (h : i ≤ j) :
    let := ConcreteBTFieldAlgebra h
    coordinateBasis h = (natBasisOfLE succCoordinates h).reindex
      (finCongr (coordinateSize_const 2 i (j - i))) := by
  let := ConcreteBTFieldAlgebra h
  apply Basis.eq_ofRepr_eq_repr
  intro x q
  rw [coordinateBasis_repr, Basis.repr_reindex_apply, natBasisOfLE_repr,
    coordinates_eq_natCoordinatesConstOfLE, natCoordinatesConstOfLE_apply]
  rfl

private theorem succ_vector (k : ℕ) (q : Fin 2) :
    (succCoordinates k).symm (Pi.single q 1) = Z (k + 1) ^ q.val := by
  rw [succCoordinates_symm_apply, joinSucc_eq_map_mul_add]
  fin_cases q
  · change concreteTowerAlgebraMap k (k + 1) _ 0 * Z (k + 1) +
      concreteTowerAlgebraMap k (k + 1) _ 1 = 1
    rw [map_zero, map_one, zero_mul, zero_add]
  · change concreteTowerAlgebraMap k (k + 1) _ 1 * Z (k + 1) +
      concreteTowerAlgebraMap k (k + 1) _ 0 = Z (k + 1) ^ 1
    rw [map_one, map_zero, one_mul, add_zero, pow_one]

private theorem height_vector (i n : ℕ) (q : Fin (coordinateSize (fun _ => 2) i n)) :
    natBasisVector succCoordinates i n q =
      ∏ t : Fin n, concreteTowerAlgebraMap (i + t.val + 1) (i + n) (by omega)
        (Z (i + t.val + 1) ^ Nat.getBit t.val q.val) := by
  induction n with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      apply (natCoordinates succCoordinates i 0).injective
      ext r
      rw [natCoordinates_natBasisVector, natCoordinates_zero]
      have hr : r = q := by
        apply Fin.ext
        have hr := r.isLt
        have hq := q.isLt
        simp only [coordinateSize_zero] at hr hq
        omega
      rw [hr, Pi.single_eq_same]
  | succ n ih =>
      have hbit (t : Fin (n + 1)) : Nat.getBit t.val q.val =
          if t.val < n then Nat.getBit t.val q.modNat.val else q.divNat.val := by
        have hh := bit_revFinProdFinEquiv_symm_2_pow_succ
          (j := ⟨q.val, by exact q.isLt.trans_eq (coordinateSize_const 2 i (n + 1))⟩)
          (i := t)
        simp only [revFinProdFinEquiv_symm_apply, Fin.val_cast, leftModNat, leftDivNat] at hh
        change Nat.getBit t.val q.val =
          if t.val < n then Nat.getBit t.val (q.val % coordinateSize (fun _ => 2) i n)
          else q.val / coordinateSize (fun _ => 2) i n
        simpa only [coordinateSize_const] using hh
      have he : finProdFinEquiv (q.divNat, q.modNat) = q :=
        finProdFinEquiv.apply_symm_apply q
      conv_lhs => rw [← he, natBasisVector_succ]
      change concreteTowerAlgebraMap (i + n) (i + n + 1) _
        (natBasisVector succCoordinates i n q.modNat) *
        (succCoordinates (i + n)).symm (Pi.single q.divNat 1) = _
      rw [ih, succ_vector, map_prod, Fin.prod_univ_castSucc]
      apply congrArg₂ (· * ·)
      · apply Finset.prod_congr rfl
        intro t _
        rw [hbit]
        simp only [Fin.val_castSucc, t.isLt, ite_eq_left]
        exact congrFun (congrArg DFunLike.coe
          (concreteTowerAlgebraMap_assoc (i + n + 1) (i + n) (i + t.val + 1)
            (by omega) (by omega))).symm _
      · rw [hbit]
        simp only [Fin.val_last, lt_self_iff_false, ite_false]
        change Z (i + n + 1) ^ q.divNat.val =
          concreteTowerAlgebraMap (i + n + 1) (i + n + 1) _
            (Z (i + n + 1) ^ q.divNat.val)
        rw [concreteTowerAlgebraMap_id]
        rfl

private theorem cast_product (i n j : ℕ) (h : i + n = j) (q : ℕ) :
    cast (congrArg ConcreteBTField h)
      (∏ t : Fin n, concreteTowerAlgebraMap (i + t.val + 1) (i + n) (by omega)
        (Z (i + t.val + 1) ^ Nat.getBit t.val q)) =
      ∏ t : Fin n, concreteTowerAlgebraMap (i + t.val + 1) j (by omega)
        (Z (i + t.val + 1) ^ Nat.getBit t.val q) := by
  subst j
  rfl

private theorem pack_single_eq_product {i j : ℕ} (h : i ≤ j)
    (q : Fin (2 ^ (j - i))) :
    pack h (Pi.single q 1) =
      ∏ t : Fin (j - i), concreteTowerAlgebraMap (i + t.val + 1) j (by omega)
        (Z (i + t.val + 1) ^ Nat.getBit t.val q.val) := by
  let := ConcreteBTFieldAlgebra h
  rw [pack_single_eq_coordinateBasis, coordinateBasis_eq_natBasisOfLE, Basis.reindex_apply,
    ← natBasisVectorOfLE_eq_natBasisOfLE, natBasisVectorOfLE_eq_natBasisVector,
    height_vector, cast_product _ _ _ (Nat.add_sub_of_le h)]
  rfl

private theorem coordinateBasis_eq_multilinearBasis {i j : ℕ} (h : i ≤ j) :
    let := ConcreteBTFieldAlgebra h
    coordinateBasis h = multilinearBasis i j h := by
  let := ConcreteBTFieldAlgebra h
  apply Basis.eq_of_apply_eq
  intro q
  rw [← pack_single_eq_coordinateBasis, pack_single_eq_product, multilinearBasis_apply]
  rfl

/-- The coefficient at numeric index `q` in the multilinear basis is the executable coordinate
at the same index, for the scalar action induced by the concrete tower embedding. -/
theorem multilinearBasis_repr {i j : ℕ} (h : i ≤ j) (x : ConcreteBTField j)
    (q : Fin (2 ^ (j - i))) :
    let := ConcreteBTFieldAlgebra h
    (multilinearBasis i j h).repr x q = coordinates h x q := by
  let := ConcreteBTFieldAlgebra h
  rw [← coordinateBasis_eq_multilinearBasis, coordinateBasis_repr]

/-- The multilinear basis vector at numeric index `q` has coordinate one at `q`
and coordinate zero at every other index. -/
@[simp] theorem coordinates_multilinearBasis {i j : ℕ} (h : i ≤ j)
    (q : Fin (2 ^ (j - i))) :
    coordinates h (multilinearBasis i j h q) = Pi.single q 1 := by
  let := ConcreteBTFieldAlgebra h
  ext r
  rw [← multilinearBasis_repr, Basis.repr_self]
  simp only [Pi.single_apply, Finsupp.single_apply, eq_comm]

/-- Packing a unit coefficient vector computes the multilinear basis vector at the same
numeric index. -/
theorem pack_single_eq_multilinearBasis {i j : ℕ} (h : i ≤ j)
    (q : Fin (2 ^ (j - i))) :
    pack h (Pi.single q 1) = multilinearBasis i j h q := by
  rw [pack_single_eq_coordinateBasis, coordinateBasis_eq_multilinearBasis]

/-- Packing is the sum of the multilinear basis vectors multiplied by their
coefficients embedded from level `i` into level `j` through the concrete tower map. -/
theorem pack_eq_sum_multilinearBasis {i j : ℕ} (h : i ≤ j)
    (c : Fin (2 ^ (j - i)) → ConcreteBTField i) :
    pack h c = ∑ q, concreteTowerAlgebraMap i j h (c q) * multilinearBasis i j h q := by
  let := ConcreteBTFieldAlgebra h
  have hsum := ((multilinearBasis i j h).sum_repr (pack h c)).symm
  simpa only [multilinearBasis_repr, coordinates_pack, Algebra.smul_def,
    algebraMap_ConcreteBTFieldAlgebra_def] using hsum

end ConcreteBinaryTower.Coordinates
