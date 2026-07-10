/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin
-/
import CompPoly.Multilinear.Equiv

/-!
# Bit order and the equality kernel

This file relates CompPoly's native little-endian Boolean-cube coordinates to an explicit
big-endian coordinate convention. It defines the multilinear equality kernel and proves the
associated interpolation and uniqueness identities.
-/

open scoped BigOperators
open CompPoly

namespace CompPoly.Bits

/-- Big-endian bit decomposition of `i` into `n` bits.

The bit at index `k : Fin n` is bit `n - 1 - k` of `i`, so coordinate zero
contains the most significant bit. -/
def toBE (n i : ℕ) : Vector Bool n :=
  Vector.ofFn (fun k : Fin n ↦ i.testBit (n - 1 - k.val))

@[simp]
theorem toBE_getElem (n i : ℕ) (k : ℕ) (hk : k < n) :
    (toBE n i)[k] = i.testBit (n - 1 - k) := by
  simp [toBE]

@[simp]
theorem toBE_zero (n : ℕ) : toBE n 0 = Vector.replicate n false := by
  apply Vector.ext
  intro i hi
  simp [toBE]

/-- The first coordinate of a nonempty big-endian bit vector is its most significant bit. -/
theorem toBE_msb (n i : ℕ) (hn : 0 < n) :
    (toBE n i)[0]'(by omega) = i.testBit (n - 1) := by
  simp

end CompPoly.Bits

namespace CompPoly.Multilinear

variable {R : Type*} {n : ℕ}

/-- The multilinear equality kernel in closed product form:
`eqHat z w = ∏ j, (z[j] * w[j] + (1 - z[j]) * (1 - w[j]))`. -/
def eqHat [CommRing R] (z w : Vector R n) : R :=
  ∏ j : Fin n, (z[j] * w[j] + (1 - z[j]) * (1 - w[j]))

/-- The `R`-valued cube point in CompPoly's little-endian coordinate order. -/
def cubePointLE [Zero R] [One R] (n : ℕ) (i : Fin (2 ^ n)) : Vector R n :=
  Vector.ofFn (fun j : Fin n ↦ if (BitVec.ofFin i).getLsb j then (1 : R) else 0)

/-- `eqHat z` at a little-endian cube point equals CompPoly's
`i`-th `lagrangeBasis` entry. -/
theorem eqHat_cubePointLE [CommRing R] (z : Vector R n) (i : Fin (2 ^ n)) :
    eqHat z (cubePointLE n i) = (CMlPolynomialEval.lagrangeBasis z)[i] := by
  unfold eqHat cubePointLE CMlPolynomialEval.lagrangeBasis
  simp +decide [Vector.ofFn]
  exact Finset.prod_congr rfl fun x _ ↦ by split_ifs <;> ring

/-- The interpolation identity in CompPoly's little-endian coordinates. -/
theorem eqHat_interpolationLE [CommRing R]
    (v : CMlPolynomialEval R n) (z : Vector R n) :
    v.eval z = ∑ i : Fin (2 ^ n), eqHat z (cubePointLE n i) * v[i] := by
  have h_eval : v.eval z =
      ∑ i : Fin (2 ^ n), v.get i * (CMlPolynomialEval.lagrangeBasis z).get i := by
    rw [CMlPolynomialEval.eval, Vector.dotProduct_eq_root_dotProduct]
    rfl
  have h_lagrangeBasis : ∀ i : Fin (2 ^ n),
      (CMlPolynomialEval.lagrangeBasis z).get i = eqHat z (cubePointLE n i) :=
    fun i ↦ (eqHat_cubePointLE z i).symm
  simp_all +decide
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

private theorem match_bool_zero_one [Zero R] [One R] (b : Bool) :
    (match b with | false => (0 : R) | true => 1) = if b then 1 else 0 := by
  cases b <;> rfl

/-- The `R`-valued Boolean-cube point for index `i`, with the most
significant bit in coordinate zero. -/
def cubePoint [Zero R] [One R] (n : ℕ) (i : Fin (2 ^ n)) : Vector R n :=
  Vector.ofFn fun j : Fin n ↦
    match i.val.testBit (n - 1 - j.val) with
    | false => 0
    | true => 1

/-- Reversing CompPoly's little-endian cube point gives the big-endian cube point. -/
theorem cubePoint_eq_reverse_cubePointLE [CommRing R] (i : Fin (2 ^ n)) :
    cubePoint (R := R) n i = (cubePointLE (R := R) n i).reverse := by
  apply Vector.ext
  intro j hj
  simp [cubePoint, cubePointLE]
  exact match_bool_zero_one _

/-- The equality kernel is invariant under reversing both coordinate vectors. -/
theorem eqHat_reverse [CommRing R] (z w : Vector R n) :
    eqHat z.reverse w.reverse = eqHat z w := by
  unfold eqHat
  apply Fintype.prod_equiv Fin.revPerm
  intro j
  change z.reverse.get j * w.reverse.get j +
      (1 - z.reverse.get j) * (1 - w.reverse.get j) =
    z.get (Fin.revPerm j) * w.get (Fin.revPerm j) +
      (1 - z.get (Fin.revPerm j)) * (1 - w.get (Fin.revPerm j))
  rw [Vector.get_reverse, Vector.get_reverse]
  rfl

/-- The equality kernel factors over a concatenation of coordinate blocks. -/
theorem eqHat_append [CommRing R] {m : ℕ}
    (z₁ w₁ : Vector R n) (z₂ w₂ : Vector R m) :
    eqHat (z₁ ++ z₂) (w₁ ++ w₂) = eqHat z₁ w₁ * eqHat z₂ w₂ := by
  unfold eqHat
  rw [Fin.prod_univ_add]
  congr 1
  · exact Finset.prod_congr rfl fun i _ ↦ by simp
  · exact Finset.prod_congr rfl fun i _ ↦ by simp

/-- The big-endian equality-kernel weight is CompPoly's
little-endian weight at the reversed evaluation point. -/
theorem eqHat_cubePoint_eqLE [CommRing R] (z : Vector R n) (i : Fin (2 ^ n)) :
    eqHat z (cubePoint (R := R) n i) =
      eqHat z.reverse (cubePointLE (R := R) n i) := by
  rw [cubePoint_eq_reverse_cubePointLE (R := R)]
  calc
    eqHat z (cubePointLE n i).reverse =
        eqHat z.reverse.reverse (cubePointLE n i).reverse := by simp
    _ = eqHat z.reverse (cubePointLE n i) := eqHat_reverse _ _

/-- Multilinear-extension evaluation in big-endian coordinates. -/
def mleEval [CommRing R] (v : CMlPolynomialEval R n) (z : Vector R n) : R :=
  ∑ i : Fin (2 ^ n), eqHat z (cubePoint n i) * v[i]

/-- The big-endian MLE interpolation identity. -/
theorem eqHat_interpolation [CommRing R]
    (v : CMlPolynomialEval R n) (z : Vector R n) :
    mleEval v z = ∑ i : Fin (2 ^ n), eqHat z (cubePoint n i) * v[i] := rfl

/-- The endianness bridge from `mleEval` to CompPoly evaluation. -/
theorem mleEval_eq_eval_reverse [CommRing R]
    (v : CMlPolynomialEval R n) (z : Vector R n) :
    mleEval v z = v.eval z.reverse := by
  rw [eqHat_interpolationLE]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [eqHat_cubePoint_eqLE]

/-- On big-endian Boolean points, the equality kernel is the Kronecker delta. -/
theorem eqHat_cubePoint_delta [CommRing R] (i j : Fin (2 ^ n)) :
    eqHat (cubePoint (R := R) n i) (cubePoint n j) =
      if i = j then (1 : R) else 0 := by
  split_ifs with h
  · subst j
    simp only [eqHat, cubePoint]
    apply Finset.prod_eq_one
    intro k _
    by_cases hk : i.val.testBit (n - 1 - k.val) <;> simp [hk]
  · obtain ⟨k, hk⟩ :
        ∃ k : Fin n, i.val.testBit k.val ≠ j.val.testBit k.val := by
      contrapose! h
      refine Fin.ext (Nat.eq_of_testBit_eq fun k ↦ ?_)
      by_cases hk : k < n
      · exact h ⟨k, hk⟩
      · have hkn : n ≤ k := Nat.le_of_not_gt hk
        have hipow : i.val < 2 ^ k :=
          lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right two_pos hkn)
        have hjpow : j.val < 2 ^ k :=
          lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right two_pos hkn)
        rw [Nat.testBit_eq_false_of_lt hipow, Nat.testBit_eq_false_of_lt hjpow]
    let rk : Fin n := ⟨n - 1 - k.val, by omega⟩
    have hrk : n - 1 - rk.val = k.val := by
      simp only [rk]
      omega
    refine Finset.prod_eq_zero (Finset.mem_univ rk) ?_
    simp only [cubePoint]
    cases hi : i.val.testBit k.val <;>
      cases hj : j.val.testBit k.val <;>
      simp_all

/-- `mleEval` returns the stored value at each big-endian cube point. -/
@[simp]
theorem mleEval_cubePoint [CommRing R]
    (v : CMlPolynomialEval R n) (i : Fin (2 ^ n)) :
    mleEval v (cubePoint n i) = v[i] := by
  classical
  unfold mleEval
  rw [Finset.sum_eq_single i]
  · simp [eqHat_cubePoint_delta]
  · intro b _ hbi
    have hib : i ≠ b := fun h ↦ hbi h.symm
    simp [eqHat_cubePoint_delta, hib]
  · simp

/-- A multilinear extension is uniquely determined by its values. -/
theorem mleEval_ext [CommRing R] {v w : CMlPolynomialEval R n}
    (h : ∀ z : Vector R n, mleEval v z = mleEval w z) :
    v = w := by
  apply Vector.ext
  intro k hk
  simpa using h (cubePoint n ⟨k, hk⟩)

/-- Equality of all `mleEval` evaluations is equivalent to equality of
the underlying Boolean-hypercube tables. -/
theorem mleEval_eq_iff [CommRing R] (v w : CMlPolynomialEval R n) :
    (∀ z : Vector R n, mleEval v z = mleEval w z) ↔ v = w := by
  constructor
  · exact mleEval_ext
  · rintro rfl z
    rfl

end CompPoly.Multilinear
