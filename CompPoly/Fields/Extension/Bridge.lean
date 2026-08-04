/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Extension.Defs
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Bridging `Ext P` to `AdjoinRoot P.poly`

The computable coefficient-vector arithmetic of `CompPoly/Fields/Extension/Defs.lean` is related
to its specification `AdjoinRoot f` by

`toQuot x = ∑ i, algebraMap F _ (x.coeff i) * root ^ i`,

which is shown to be an injective ring homomorphism. The ring axioms on `Ext P` are then
discharged by pushing through `toQuot` rather than proved on coordinates.

The load-bearing lemma is `toQuot_shiftReduce`: `shiftReduce` is "multiply by `X`, reduce mod
`f`", and correspondingly `toQuot (shiftReduce e) = rt * toQuot e`. Everything about
multiplication follows from it: `monomialMod k = X^k mod f` satisfies `toQuot (monomialMod k) =
rt ^ k` by a one-line induction, and `toQuot_mul` is then a direct double sum with no case
analysis on wrap-around.

## Main definitions and statements

* `Ext.toQuot`: the map to `AdjoinRoot P.poly`.
* `Ext.rt_relation`: the defining relation `rt ^ d = -∑ lowerᵢ rt ^ i`, from `AdjoinRoot.mk_self`.
* `Ext.toQuot_shiftReduce`: the multiply-by-`X` homomorphism law.
* `Ext.toQuot_mul`, `Ext.toQuot_add`, ...: `toQuot` is a ring homomorphism.
* `Ext.toQuot_injective`: injective for any monic modulus; irreducibility is not needed.
* `Ext.instCommRing`: the `CommRing` structure.
* `Ext.toQuotRingHom`: `toQuot` packaged as a `RingHom`.

Bijectivity, cardinality and the `Field` structure are in
`CompPoly/Fields/Extension/Field.lean`.
-/

@[expose] public section

namespace CompPoly.Extension.Ext

open Polynomial AdjoinRoot

variable {F : Type*} [Field F] [Fintype F] {P : ExtensionParams F}

/-- The specification of the extension: the quotient ring `F[X] / f`. -/
scoped notation "Quot[" P "]" => AdjoinRoot (ExtensionParams.poly P)

/-- The image of `X` in the quotient, i.e. the adjoined root of `f`. -/
noncomputable def rt (P : ExtensionParams F) : Quot[P] := AdjoinRoot.root P.poly

/-- The degree of the defining polynomial, as a `WithBot ℕ`. -/
theorem degree_poly : P.poly.degree = (P.d : WithBot ℕ) := P.degree_poly

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
  have hzero : (∑ i : Fin P.d, C (coeff x i) * X ^ (i : ℕ))
      - ∑ i : Fin P.d, C (coeff y i) * X ^ (i : ℕ) = 0 :=
    eq_zero_of_dvd_of_degree_lt h
      (lt_of_le_of_lt (degree_sub_le _ _) (max_lt (degree_repr_lt x) (degree_repr_lt y)))
  rw [sub_eq_zero] at hzero
  ext k
  rw [← coeff_repr x k, ← coeff_repr y k, hzero]

theorem toQuot_inj {x y : Ext P} : toQuot x = toQuot y ↔ x = y :=
  toQuot_injective.eq_iff

/-! ### The defining relation and the multiply-by-`X` homomorphism law -/

/-- `toQuot` as a sum over `Finset.range`, using the total `coeffNat`. Convenient for the shift
reindexing in `toQuot_shiftReduce`. -/
theorem toQuot_rangeForm (x : Ext P) :
    toQuot x = ∑ k ∈ Finset.range P.d, algebraMap F Quot[P] (coeffNat x k) * (rt P) ^ k := by
  rw [toQuot, ← Fin.sum_univ_eq_sum_range
    (fun k => algebraMap F Quot[P] (coeffNat x k) * (rt P) ^ k) P.d]
  exact Finset.sum_congr rfl fun i _ => by rw [coeffNat_coe]

/-- **The defining relation**, from `AdjoinRoot.mk_self`: the adjoined root `rt` satisfies
`rt ^ d + ∑ lowerᵢ · rt ^ i = 0`. -/
theorem rt_relation :
    (rt P) ^ P.d + ∑ i : Fin P.d, algebraMap F Quot[P] (P.lowerCoeff i) * (rt P) ^ (i : ℕ)
      = 0 := by
  have e1 : AdjoinRoot.mk P.poly (X ^ P.d) = (rt P) ^ P.d := by
    rw [map_pow, AdjoinRoot.mk_X]; rfl
  have e2 : ∀ i : Fin P.d, AdjoinRoot.mk P.poly (C (P.lowerCoeff i) * X ^ (i : ℕ))
      = algebraMap F Quot[P] (P.lowerCoeff i) * (rt P) ^ (i : ℕ) := by
    intro i
    rw [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq]; rfl
  have expand : AdjoinRoot.mk P.poly (X ^ P.d + ∑ i : Fin P.d, C (P.lowerCoeff i) * X ^ (i : ℕ))
      = (rt P) ^ P.d + ∑ i : Fin P.d, algebraMap F Quot[P] (P.lowerCoeff i) * (rt P) ^ (i : ℕ) := by
    rw [map_add, e1, map_sum]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => e2 i)
  rw [← expand, ← ExtensionParams.poly]
  exact AdjoinRoot.mk_self

/-- In `range` form: `∑_{m < d} lowerₘ · rt ^ m = -rt ^ d`. -/
theorem sum_lower_rangeForm :
    (∑ m ∈ Finset.range P.d, algebraMap F Quot[P] (P.lowerCoeffNat m) * (rt P) ^ m)
      = -(rt P) ^ P.d := by
  have h := rt_relation (P := P)
  rw [← Fin.sum_univ_eq_sum_range
    (fun m => algebraMap F Quot[P] (P.lowerCoeffNat m) * (rt P) ^ m) P.d]
  rw [show (∑ i : Fin P.d, algebraMap F Quot[P] (P.lowerCoeffNat (i : ℕ)) * (rt P) ^ (i : ℕ))
      = ∑ i : Fin P.d, algebraMap F Quot[P] (P.lowerCoeff i) * (rt P) ^ (i : ℕ) from
    Finset.sum_congr rfl fun i _ => by rw [P.lowerCoeffNat_coe]]
  exact eq_neg_of_add_eq_zero_right h

/-- The coefficient formula for `shiftReduce`, in `coeffNat` form. -/
theorem coeffNat_shiftReduce (e : Ext P) {m : ℕ} (h : m < P.d) :
    coeffNat (shiftReduce e) m
      = (if m = 0 then 0 else coeffNat e (m - 1)) - coeffNat e (P.d - 1) * P.lowerCoeffNat m := by
  rw [coeffNat_of_lt _ h, coeff_shiftReduce, ← P.lowerCoeffNat_coe ⟨m, h⟩]

/--
**The multiply-by-`X` homomorphism law.** `shiftReduce` is multiplication by `X` in the quotient,
so `toQuot (shiftReduce e) = rt * toQuot e`. This is the one place `rt_relation` is consumed, and
everything about multiplication reduces to it.
-/
theorem toQuot_shiftReduce (e : Ext P) : toQuot (shiftReduce e) = rt P * toQuot e := by
  have hd : P.d = (P.d - 1) + 1 := (Nat.succ_pred_eq_of_pos P.d_pos).symm
  -- The right-hand side, in range form with the exponent shifted up by one.
  have hRHS : rt P * toQuot e
      = ∑ i ∈ Finset.range P.d, algebraMap F Quot[P] (coeffNat e i) * (rt P) ^ (i + 1) := by
    rw [toQuot_rangeForm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
  -- The left-hand side, split into a shift part and a wrap part.
  have hLHS : toQuot (shiftReduce e)
      = (∑ m ∈ Finset.range P.d,
            algebraMap F Quot[P] (if m = 0 then 0 else coeffNat e (m - 1)) * (rt P) ^ m)
        - algebraMap F Quot[P] (coeffNat e (P.d - 1))
            * ∑ m ∈ Finset.range P.d, algebraMap F Quot[P] (P.lowerCoeffNat m) * (rt P) ^ m := by
    rw [toQuot_rangeForm, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [coeffNat_shiftReduce e hm, map_sub, map_mul]; ring
  -- Rewrite the shift sum by peeling index `0` (which vanishes).
  have hshift : (∑ m ∈ Finset.range P.d,
        algebraMap F Quot[P] (if m = 0 then 0 else coeffNat e (m - 1)) * (rt P) ^ m)
      = ∑ k ∈ Finset.range (P.d - 1), algebraMap F Quot[P] (coeffNat e k) * (rt P) ^ (k + 1) := by
    conv_lhs => rw [hd, Finset.sum_range_succ']
    rw [show (if (0 : ℕ) = 0 then (0 : F) else coeffNat e (0 - 1)) = 0 from if_pos rfl,
      map_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
  -- Rewrite the RHS by peeling off its top index.
  have hrhs : (∑ i ∈ Finset.range P.d, algebraMap F Quot[P] (coeffNat e i) * (rt P) ^ (i + 1))
      = (∑ k ∈ Finset.range (P.d - 1), algebraMap F Quot[P] (coeffNat e k) * (rt P) ^ (k + 1))
        + algebraMap F Quot[P] (coeffNat e (P.d - 1)) * (rt P) ^ P.d := by
    conv_lhs => rw [hd, Finset.sum_range_succ]
    rw [← hd]
  rw [hLHS, sum_lower_rangeForm, hRHS, hshift, hrhs, mul_neg, sub_neg_eq_add]

/-! ### Reduced monomials -/

@[simp] theorem monomialMod_zero : (monomialMod 0 : Ext P) = 1 := rfl

theorem monomialMod_succ (k : ℕ) :
    (monomialMod (k + 1) : Ext P) = shiftReduce (monomialMod k) := by
  rw [monomialMod, monomialMod, Function.iterate_succ_apply']

/-- `monomialMod k` really is `X^k` reduced: its image under `toQuot` is `rt ^ k`. -/
@[simp] theorem toQuot_monomialMod (k : ℕ) : toQuot (monomialMod k : Ext P) = (rt P) ^ k := by
  induction k with
  | zero => rw [monomialMod_zero, toQuot_one, pow_zero]
  | succ n ih => rw [monomialMod_succ, toQuot_shiftReduce, ih, pow_succ']

/-! ### `toQuot` is multiplicative -/

@[simp] theorem toQuot_mul (x y : Ext P) : toQuot (x * y) = toQuot x * toQuot y := by
  have hL : toQuot (x * y)
      = ∑ i : Fin P.d, ∑ j : Fin P.d,
          algebraMap F Quot[P] (coeff x i * coeff y j) * (rt P) ^ ((i : ℕ) + (j : ℕ)) := by
    rw [toQuot]
    simp only [coeff_mul, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (∑ m : Fin P.d, algebraMap F Quot[P] (coeff x i) * algebraMap F Quot[P] (coeff y j)
            * algebraMap F Quot[P] (coeff (monomialMod ((i : ℕ) + (j : ℕ))) m) * (rt P) ^ (m : ℕ))
        = algebraMap F Quot[P] (coeff x i) * algebraMap F Quot[P] (coeff y j)
            * ∑ m : Fin P.d, algebraMap F Quot[P] (coeff (monomialMod ((i : ℕ) + (j : ℕ))) m)
                * (rt P) ^ (m : ℕ) from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring]
    rw [← toQuot, toQuot_monomialMod, ← map_mul]
  rw [hL, toQuot, toQuot, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, pow_add]; ring

/-! ### Exponentiation

`x ^ n` on `Ext P` is `npowBinRec`, i.e. repeated squaring, so it costs `O(log n)`
multiplications. `npowBinRec_succ` needs only `Semigroup`, and associativity is already
available from `toQuot_mul` plus injectivity — so exponentiation can be handled before the full
ring structure is transported.
-/

/-- Associativity. Kept out of the instance graph as a plain theorem to avoid a `Semigroup`
diamond with the `CommRing` instance below. -/
theorem mul_assoc' (x y z : Ext P) : x * y * z = x * (y * z) :=
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

/-! ### The base field and the adjoined root -/

/-- `ofBase` lands on the constant coefficient, so it agrees with `algebraMap` into the quotient. -/
@[simp] theorem toQuot_ofBase (c : F) :
    toQuot (ofBase (P := P) c) = algebraMap F Quot[P] c := by
  rw [toQuot, Finset.sum_eq_single_of_mem ⟨0, P.d_pos⟩ (Finset.mem_univ _)]
  · simp
  · intro k _ hk
    have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    simp [this]

/-- `gen` is the class of `X`, i.e. the adjoined root. -/
@[simp] theorem toQuot_gen : toQuot (gen : Ext P) = rt P := by
  have h1 : (1 : ℕ) < P.d := P.two_le
  rw [toQuot, Finset.sum_eq_single_of_mem ⟨1, h1⟩ (Finset.mem_univ _)]
  · simp
  · intro k _ hk
    have : (k : ℕ) ≠ 1 := fun h => hk (Fin.ext h)
    simp [this]

/-- The base-field embedding, as a ring homomorphism. -/
def ofBaseRingHom (P : ExtensionParams F) : F →+* Ext P where
  toFun := ofBase
  map_one' := ofBase_one
  map_mul' a b := toQuot_injective (by simp only [toQuot_ofBase, toQuot_mul, map_mul])
  map_zero' := ofBase_zero
  map_add' a b := toQuot_injective (by simp only [toQuot_ofBase, toQuot_add, map_add])

@[simp] theorem ofBaseRingHom_apply (c : F) : ofBaseRingHom P c = ofBase c := rfl

/-- The extension is an `F`-algebra. -/
instance instAlgebra : Algebra F (Ext P) where
  algebraMap := ofBaseRingHom P
  commutes' _ _ := mul_comm _ _
  smul_def' c x :=
    toQuot_injective (by simp only [toQuot_smul, toQuot_mul, ofBaseRingHom_apply, toQuot_ofBase])

@[simp] theorem algebraMap_eq_ofBase (c : F) : algebraMap F (Ext P) c = ofBase c := rfl

theorem toQuot_sum {ι : Type*} (s : Finset ι) (f : ι → Ext P) :
    toQuot (∑ i ∈ s, f i) = ∑ i ∈ s, toQuot (f i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, toQuot_add, ih]

/-- **The defining relation** at the level of `Ext`: `gen ^ d` equals the reduced monomial
`monomialMod d`. -/
theorem gen_pow_d : (gen : Ext P) ^ P.d = monomialMod P.d :=
  toQuot_injective (by rw [toQuot_pow, toQuot_gen, toQuot_monomialMod])

/-- `gen` is a root of the defining polynomial, in the form Mathlib's `aeval` expects. -/
theorem aeval_gen_poly : aeval (gen : Ext P) P.poly = 0 := by
  have hexp : aeval (gen : Ext P) P.poly
      = gen ^ P.d + ∑ i : Fin P.d, ofBase (P.lowerCoeff i) * gen ^ (i : ℕ) := by
    rw [ExtensionParams.poly, map_add, map_pow, aeval_X, map_sum]
    refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, map_pow, aeval_X, aeval_C, algebraMap_eq_ofBase]
  rw [hexp]
  apply toQuot_injective
  rw [toQuot_zero, toQuot_add, toQuot_pow, toQuot_gen, toQuot_sum,
    show (∑ i : Fin P.d, toQuot (ofBase (P.lowerCoeff i) * gen ^ (i : ℕ)))
        = ∑ i : Fin P.d, algebraMap F Quot[P] (P.lowerCoeff i) * (rt P) ^ (i : ℕ) from
      Finset.sum_congr rfl fun i _ => by
        rw [toQuot_mul, toQuot_ofBase, toQuot_pow, toQuot_gen]]
  exact rt_relation

/-- `toQuot` packaged as a ring homomorphism. -/
noncomputable def toQuotRingHom (P : ExtensionParams F) : Ext P →+* Quot[P] where
  toFun := toQuot
  map_one' := toQuot_one
  map_mul' := toQuot_mul
  map_zero' := toQuot_zero
  map_add' := toQuot_add

/-! ### Binomial compatibility

For a binomial modulus `X^d - W`, the general defining relation `rt ^ d = -∑ lowerᵢ rt ^ i`
collapses (the only nonzero lower coefficient is `lower₀ = -W`) to `rt ^ d = W`, recovering the
`gen ^ d = ofBase W` law the degree-4 extensions rely on.
-/

/-- The collapsed defining relation for a binomial modulus: `rt ^ d = W`. -/
theorem rt_pow_d_binomial (P : BinomialParams F) :
    (rt P.toExtensionParams) ^ P.d = algebraMap F Quot[P.toExtensionParams] P.W := by
  have hsum : (∑ i : Fin P.toExtensionParams.d,
        algebraMap F Quot[P.toExtensionParams] (P.toExtensionParams.lowerCoeff i)
          * (rt P.toExtensionParams) ^ (i : ℕ))
      = -algebraMap F Quot[P.toExtensionParams] P.W := by
    rw [Finset.sum_eq_single_of_mem (⟨0, P.d_pos⟩ : Fin P.toExtensionParams.d) (Finset.mem_univ _)]
    · rw [BinomialParams.toExtensionParams_lowerCoeff]; simp
    · intro i _ hi
      have hi0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
      rw [BinomialParams.toExtensionParams_lowerCoeff, if_neg hi0, map_zero, zero_mul]
  have h := rt_relation (P := P.toExtensionParams)
  rw [hsum, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h

/-- **The binomial defining relation** at the level of `Ext`: `gen ^ d = ofBase W`. -/
theorem gen_pow_d_binomial (P : BinomialParams F) :
    (gen : Ext P.toExtensionParams) ^ P.d = ofBase P.W :=
  toQuot_injective (by rw [toQuot_pow, toQuot_gen, toQuot_ofBase, rt_pow_d_binomial])

end CompPoly.Extension.Ext
