/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Fields.Extension.Defs
import Mathlib.RingTheory.AdjoinRoot

/-!
# Bridging `Ext P` to `AdjoinRoot P.poly`

The computable coefficient-vector arithmetic of `CompPoly/Fields/Extension/Defs.lean` is related
to its specification `AdjoinRoot (X^d - W)` by

`toQuot x = ∑ i, algebraMap F _ (x.coeff i) * root ^ i`,

which is shown to be an injective ring homomorphism. The algebraic structure on `Ext P` is then
*transported* across `toQuot` rather than proved by hand, following
`CompPoly/Fields/Montgomery/Native32Field.lean` (`toField_injective.field`).

The load-bearing lemma is `toQuot_mul`: the wrap-around `W` factor in `Ext.mul` is exactly
`root ^ d = W`, so the double sum defining the product regroups into the product of sums.

## Main definitions and statements

* `Ext.toQuot`: the map to `AdjoinRoot P.poly`.
* `Ext.toQuot_mul`, `Ext.toQuot_add`, ...: `toQuot` is a ring homomorphism.
* `Ext.toQuot_injective`: injective for any binomial modulus; irreducibility is not needed.
* `Ext.instCommRing`: the transported `CommRing` structure.
-/

namespace CompPoly.Extension.Ext

open Polynomial AdjoinRoot

variable {F : Type*} [Field F] {P : BinomialParams F}

/-- The specification of the extension: the quotient ring `F[X] / (X^d - W)`. -/
scoped notation "Quot[" P "]" => AdjoinRoot (BinomialParams.poly P)

/-- The image of `X` in the quotient, i.e. the adjoined `d`-th root of `W`. -/
noncomputable def rt (P : BinomialParams F) : Quot[P] := AdjoinRoot.root P.poly

/-- The degree of the defining polynomial, as a `WithBot ℕ`. -/
theorem degree_poly : P.poly.degree = (P.d : WithBot ℕ) := by
  rw [BinomialParams.poly]; exact degree_X_pow_sub_C P.d_pos _

/-- The defining relation: the adjoined root raised to the `d`-th power is `W`. -/
theorem rt_pow_d : (rt P) ^ P.d = algebraMap F Quot[P] P.W := by
  have h : AdjoinRoot.mk P.poly ((X : F[X]) ^ P.d - C P.W) = 0 := by
    rw [← BinomialParams.poly]; exact AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
  rw [rt, AdjoinRoot.algebraMap_eq]
  exact h

/-- The map from coefficient vectors to the quotient ring. -/
noncomputable def toQuot (x : Ext P) : Quot[P] :=
  ∑ i : Fin P.d, algebraMap F Quot[P] (coeff x i) * (rt P) ^ (i : ℕ)

/-! ### `toQuot` is additive -/

@[simp] theorem toQuot_zero : toQuot (0 : Ext P) = 0 := by simp [toQuot]

@[simp] theorem toQuot_add (x y : Ext P) : toQuot (x + y) = toQuot x + toQuot y := by
  simp only [toQuot, coeff_add, map_add, add_mul, Finset.sum_add_distrib]

@[simp] theorem toQuot_neg (x : Ext P) : toQuot (-x) = -toQuot x := by
  simp only [toQuot, coeff_neg, map_neg, neg_mul, Finset.sum_neg_distrib]

@[simp] theorem toQuot_sub (x y : Ext P) : toQuot (x - y) = toQuot x - toQuot y := by
  simp only [toQuot, coeff_sub, map_sub, sub_mul, Finset.sum_sub_distrib]

@[simp] theorem toQuot_smul (c : F) (x : Ext P) :
    toQuot (c • x) = algebraMap F Quot[P] c * toQuot x := by
  simp only [toQuot, coeff_smul, map_mul, Finset.mul_sum, mul_assoc]

/-- Only the constant coefficient of `1` is nonzero, so `toQuot 1` collapses to `1`. -/
@[simp] theorem toQuot_one : toQuot (1 : Ext P) = 1 := by
  rw [toQuot, Finset.sum_eq_single_of_mem ⟨0, P.d_pos⟩ (Finset.mem_univ _)]
  · simp
  · intro k _ hk
    have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    simp [this]

/-! ### `toQuot` is multiplicative

This is the heart of the framework. For `i, j < d` we have `i + j ≤ 2d - 2 < 2d`, so each pair
`(i, j)` contributes to exactly one output index: `k = i + j` when `i + j < d`, and
`k = i + j - d` otherwise, where the wrap-around picks up the factor `W = root ^ d`.
-/

/--
The single-index collapse: for a fixed pair `(i, j)`, summing the multiplication kernel over all
output indices `k` recovers `c * root ^ (i + j)`.
-/
private theorem sum_kernel_collapse (i j : Fin P.d) (c : F) :
    (∑ k : Fin P.d, algebraMap F Quot[P]
        (if (i : ℕ) + (j : ℕ) = (k : ℕ) then c
         else if (i : ℕ) + (j : ℕ) = (k : ℕ) + P.d then P.W * c else 0) * (rt P) ^ (k : ℕ))
      = algebraMap F Quot[P] c * (rt P) ^ ((i : ℕ) + (j : ℕ)) := by
  by_cases hlt : (i : ℕ) + (j : ℕ) < P.d
  · -- No wrap-around: only `k = i + j` contributes.
    rw [Finset.sum_eq_single_of_mem (⟨(i : ℕ) + (j : ℕ), hlt⟩ : Fin P.d) (Finset.mem_univ _)]
    · simp
    · intro k _ hk
      have h1 : (i : ℕ) + (j : ℕ) ≠ (k : ℕ) := fun h => hk (Fin.ext h.symm)
      have h2 : (i : ℕ) + (j : ℕ) ≠ (k : ℕ) + P.d := by omega
      simp [h1, h2]
  · -- Wrap-around: only `k = i + j - d` contributes, with the factor `W = root ^ d`.
    have hge : P.d ≤ (i : ℕ) + (j : ℕ) := Nat.le_of_not_lt hlt
    have hij : (i : ℕ) + (j : ℕ) < 2 * P.d := by
      have := i.isLt; have := j.isLt; omega
    have hk0 : (i : ℕ) + (j : ℕ) - P.d < P.d := by omega
    rw [Finset.sum_eq_single_of_mem (⟨(i : ℕ) + (j : ℕ) - P.d, hk0⟩ : Fin P.d)
      (Finset.mem_univ _)]
    · have h1 : (i : ℕ) + (j : ℕ) ≠ (i : ℕ) + (j : ℕ) - P.d := by omega
      have h2 : (i : ℕ) + (j : ℕ) = ((i : ℕ) + (j : ℕ) - P.d) + P.d := by omega
      simp only [h1, if_false, if_pos h2, map_mul, ← rt_pow_d]
      -- Name the wrapped index so rewriting `i + j` cannot disturb `i + j - d`.
      obtain ⟨m, hm⟩ : ∃ m, (i : ℕ) + (j : ℕ) = m + P.d := ⟨(i : ℕ) + (j : ℕ) - P.d, h2⟩
      rw [hm, Nat.add_sub_cancel, pow_add]
      ring
    · intro k _ hk
      have hkd := k.isLt
      have h1 : (i : ℕ) + (j : ℕ) ≠ (k : ℕ) := by omega
      have h2 : (i : ℕ) + (j : ℕ) ≠ (k : ℕ) + P.d := fun h =>
        hk (Fin.ext (show (k : ℕ) = (i : ℕ) + (j : ℕ) - P.d from by omega))
      simp [h1, h2]

@[simp] theorem toQuot_mul (x y : Ext P) : toQuot (x * y) = toQuot x * toQuot y := by
  -- Expand the left-hand side into a triple sum and reorder to `∑ i, ∑ j, ∑ k`.
  have hL : toQuot (x * y)
      = ∑ i : Fin P.d, ∑ j : Fin P.d, algebraMap F Quot[P] (coeff x i * coeff y j)
          * (rt P) ^ ((i : ℕ) + (j : ℕ)) := by
    simp only [toQuot, coeff_mul, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => sum_kernel_collapse i j _
  -- The right-hand side expands to the same thing.
  rw [hL, toQuot, toQuot, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, pow_add]
  ring

@[simp] theorem toQuot_natCast (n : ℕ) : toQuot (n : Ext P) = n := by
  rw [toQuot, Finset.sum_eq_single_of_mem ⟨0, P.d_pos⟩ (Finset.mem_univ _)]
  · simp
  · intro k _ hk
    have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    simp [this]

@[simp] theorem toQuot_intCast (n : ℤ) : toQuot (n : Ext P) = n := by
  rw [toQuot, Finset.sum_eq_single_of_mem ⟨0, P.d_pos⟩ (Finset.mem_univ _)]
  · simp
  · intro k _ hk
    have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    simp [this]

/-! ### Injectivity -/

/-- `toQuot` as the class of an explicit degree-`< d` polynomial representative. -/
theorem toQuot_eq_mk (x : Ext P) :
    toQuot x = AdjoinRoot.mk P.poly (∑ i : Fin P.d, C (coeff x i) * X ^ (i : ℕ)) := by
  rw [toQuot, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq]
  rfl

/-- The representative used by `toQuot_eq_mk` has degree less than that of the modulus. -/
private theorem degree_repr_lt (x : Ext P) :
    (∑ i : Fin P.d, C (coeff x i) * X ^ (i : ℕ)).degree < P.poly.degree := by
  rw [degree_poly]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe P.d)]
  intro i _
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast i.isLt)

/-- The coefficients of the explicit representative are the vector's coefficients. -/
private theorem coeff_repr (x : Ext P) (k : Fin P.d) :
    (∑ i : Fin P.d, C (coeff x i) * X ^ (i : ℕ)).coeff (k : ℕ) = coeff x k := by
  rw [finsetSum_coeff, Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
  · simp
  · intro i _ hi
    rw [coeff_C_mul_X_pow, if_neg (fun h => hi (Fin.ext h.symm))]

theorem toQuot_injective : Function.Injective (toQuot (P := P)) := by
  intro x y h
  rw [toQuot_eq_mk, toQuot_eq_mk, ← sub_eq_zero, ← map_sub, AdjoinRoot.mk_eq_zero] at h
  -- The difference has degree `< deg P.poly`, so divisibility forces it to be zero.
  have hzero : (∑ i : Fin P.d, C (coeff x i) * X ^ (i : ℕ))
      - ∑ i : Fin P.d, C (coeff y i) * X ^ (i : ℕ) = 0 :=
    eq_zero_of_dvd_of_degree_lt h
      (lt_of_le_of_lt (degree_sub_le _ _) (max_lt (degree_repr_lt x) (degree_repr_lt y)))
  rw [sub_eq_zero] at hzero
  ext k
  rw [← coeff_repr x k, ← coeff_repr y k, hzero]

theorem toQuot_inj {x y : Ext P} : toQuot x = toQuot y ↔ x = y :=
  toQuot_injective.eq_iff

/-! ### Exponentiation

`x ^ n` on `Ext P` is `npowBinRec`, i.e. repeated squaring, so it costs `O(log n)`
multiplications. `npowBinRec_succ` needs only `Semigroup`, and associativity is already
available from `toQuot_mul` plus injectivity — so exponentiation can be handled before the full
ring structure is transported.
-/

/-- Associativity. Kept out of the instance graph as a plain theorem to avoid a `Semigroup`
diamond with the `CommRing` instance below. -/
private theorem mul_assoc' (x y z : Ext P) : x * y * z = x * (y * z) :=
  toQuot_injective (by simp only [toQuot_mul, mul_assoc])

@[simp] theorem toQuot_pow (x : Ext P) (n : ℕ) : toQuot (x ^ n) = toQuot x ^ n := by
  letI : Semigroup (Ext P) := { mul_assoc := mul_assoc' }
  induction n with
  | zero => rw [pow_def, npowBinRec_zero, toQuot_one, pow_zero]
  | succ n ih => rw [pow_def, npowBinRec_succ, toQuot_mul, ← pow_def, ih, pow_succ]

/-! ### Algebraic structure

The axioms are all discharged by pushing through the injective `toQuot`, but the instances are
built field-by-field with `where` rather than via `Function.Injective.commRing`. That transport
takes `toQuot` as *data*, which would make the resulting instance `noncomputable` and — because
`Monoid.toNatPow` then outranks `Ext.instPow` — would silently break compiled `x ^ n`. Building
by hand keeps every operation computable, matching how `CPolynomial` assembles its instances in
`CompPoly/Univariate/Basic.lean`.
-/

instance instAddCommGroup : AddCommGroup (Ext P) where
  add_assoc a b c := toQuot_injective (by simp only [toQuot_add, add_assoc])
  zero_add a := toQuot_injective (by simp only [toQuot_add, toQuot_zero, zero_add])
  add_zero a := toQuot_injective (by simp only [toQuot_add, toQuot_zero, add_zero])
  add_comm a b := toQuot_injective (by simp only [toQuot_add, add_comm])
  neg_add_cancel a :=
    toQuot_injective (by simp only [toQuot_add, toQuot_neg, toQuot_zero, neg_add_cancel])
  sub_eq_add_neg a b :=
    toQuot_injective (by simp only [toQuot_sub, toQuot_add, toQuot_neg, sub_eq_add_neg])
  -- `ℕ`- and `ℤ`-scalar multiplication use the generic recursors: unlike `npow` they are not on
  -- any hot path, and this keeps them definitionally the standard ones.
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  zsmul := zsmulRec nsmulRec
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _ := rfl

instance instCommRing : CommRing (Ext P) where
  left_distrib a b c := toQuot_injective (by simp only [toQuot_mul, toQuot_add, mul_add])
  right_distrib a b c := toQuot_injective (by simp only [toQuot_mul, toQuot_add, add_mul])
  zero_mul a := toQuot_injective (by simp only [toQuot_mul, toQuot_zero, zero_mul])
  mul_zero a := toQuot_injective (by simp only [toQuot_mul, toQuot_zero, mul_zero])
  mul_assoc := mul_assoc'
  one_mul a := toQuot_injective (by simp only [toQuot_mul, toQuot_one, one_mul])
  mul_one a := toQuot_injective (by simp only [toQuot_mul, toQuot_one, mul_one])
  mul_comm a b := toQuot_injective (by simp only [toQuot_mul, mul_comm])
  npow n x := x ^ n
  npow_zero x := toQuot_injective (by simp only [toQuot_pow, toQuot_one, pow_zero])
  npow_succ n x := toQuot_injective (by simp only [toQuot_pow, toQuot_mul, pow_succ])
  natCast n := (n : Ext P)
  natCast_zero := toQuot_injective (by simp only [toQuot_natCast, toQuot_zero, Nat.cast_zero])
  natCast_succ n :=
    toQuot_injective (by simp only [toQuot_natCast, toQuot_add, toQuot_one, Nat.cast_succ])
  intCast n := (n : Ext P)
  intCast_ofNat n :=
    toQuot_injective (by simp only [toQuot_intCast, toQuot_natCast, Int.cast_natCast])
  intCast_negSucc n :=
    toQuot_injective (by simp only [toQuot_intCast, toQuot_neg, toQuot_natCast, Int.cast_negSucc])

/-- `toQuot` packaged as a ring homomorphism. -/
noncomputable def toQuotRingHom (P : BinomialParams F) : Ext P →+* Quot[P] where
  toFun := toQuot
  map_one' := toQuot_one
  map_mul' := toQuot_mul
  map_zero' := toQuot_zero
  map_add' := toQuot_add

end CompPoly.Extension.Ext
