/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.Shoup.Basic
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Frobenius Divisors with One Root are Linear

This file contains the field-theoretic bridge used by the Shoup trace splitter:
a nonzero divisor of `X^q - X` over `GF(q)` with exactly one field root is a
represented nonconstant linear factor.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/--
A nonzero divisor of `X^q - X` with exactly one field root is represented as a
linear factor.
-/
theorem isRepresentedLinearFactor_of_dvd_frobenius_unique_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : SmallPrimeTraceContext F) {factor : CPolynomial F} {a : F}
    (hfactorNe : factor ≠ 0)
    (hdvd : factor.toPoly ∣ ((Polynomial.X : Polynomial F) ^ ctx.q - Polynomial.X))
    (hroot : CPolynomial.eval a factor = 0)
    (hunique : ∀ b, CPolynomial.eval b factor = 0 → b = a) :
    isRepresentedLinearFactor factor = true := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  letI : Finite F := ctx.finite
  letI : Fintype F := Fintype.ofFinite F
  have hqcard : ctx.q = Fintype.card F := by
    rw [← ctx.card_eq, Nat.card_eq_fintype_card]
  have hfactorPolyNe : factor.toPoly ≠ 0 :=
    (CPolynomial.toPoly_eq_zero_iff factor).not.mpr hfactorNe
  have hfrobNe : ((Polynomial.X : Polynomial F) ^ ctx.q - Polynomial.X) ≠ 0 := by
    rw [hqcard]
    exact FiniteField.X_pow_card_sub_X_ne_zero F Fintype.one_lt_card
  have hsplitFrob : Polynomial.Splits
      ((Polynomial.X : Polynomial F) ^ ctx.q - Polynomial.X) := by
    rw [hqcard]
    rw [Polynomial.splits_iff_card_roots]
    rw [FiniteField.roots_X_pow_card_sub_X]
    rw [← Finset.card_def, Finset.card_univ]
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
  have hsplitFactor : Polynomial.Splits factor.toPoly :=
    hsplitFrob.of_dvd hfrobNe hdvd
  have hrootsLe : factor.toPoly.roots ≤
      (((Polynomial.X : Polynomial F) ^ ctx.q - Polynomial.X).roots) :=
    Polynomial.roots.le_of_dvd hfrobNe hdvd
  have hfrobRoots : (((Polynomial.X : Polynomial F) ^ ctx.q - Polynomial.X).roots) =
      (Finset.univ : Finset F).val := by
    rw [hqcard]
    exact FiniteField.roots_X_pow_card_sub_X F
  have hfrobNodup :
      (((Polynomial.X : Polynomial F) ^ ctx.q - Polynomial.X).roots).Nodup := by
    rw [hfrobRoots]
    exact Finset.nodup _
  have hfactorRootsNodup : factor.toPoly.roots.Nodup :=
    Multiset.nodup_of_le hrootsLe hfrobNodup
  have haMem : a ∈ factor.toPoly.roots := by
    rw [Polynomial.mem_roots hfactorPolyNe]
    simpa [Polynomial.IsRoot, CPolynomial.eval_toPoly] using hroot
  have htoFinset : factor.toPoly.roots.toFinset = {a} := by
    ext b
    constructor
    · intro hb
      rw [Finset.mem_singleton]
      apply hunique b
      have hbroot : b ∈ factor.toPoly.roots := by
        simpa using (Multiset.mem_toFinset.mp hb)
      rw [Polynomial.mem_roots hfactorPolyNe] at hbroot
      simpa [Polynomial.IsRoot, CPolynomial.eval_toPoly] using hbroot
    · intro hb
      rw [Finset.mem_singleton] at hb
      subst b
      exact Multiset.mem_toFinset.mpr haMem
  have hrootsCard : factor.toPoly.roots.card = 1 := by
    have hcardFin : factor.toPoly.roots.toFinset.card = factor.toPoly.roots.card :=
      Multiset.toFinset_card_of_nodup hfactorRootsNodup
    rw [← hcardFin, htoFinset]
    simp
  have hnatPoly : factor.toPoly.natDegree = 1 := by
    simpa [hrootsCard] using hsplitFactor.natDegree_eq_card_roots
  have hnat : factor.natDegree = 1 := by
    rw [CPolynomial.natDegree_toPoly]
    exact hnatPoly
  have hsize : factor.val.size ≤ 2 := by
    cases hs : factor.val.size with
    | zero =>
        have hzero : factor = 0 := by
          apply CPolynomial.ext
          exact Array.eq_empty_of_size_eq_zero hs
        exact (hfactorNe hzero).elim
    | succ n =>
        have hn : n = 1 := by
          have hnatVal : factor.natDegree = n := by
            simp [CPolynomial.natDegree, hs]
          omega
        omega
  have hcoeff : factor.coeff 1 ≠ 0 := by
    have hlead := CPolynomial.leadingCoeff_ne_zero hfactorNe
    rw [CPolynomial.leadingCoeff_eq_coeff_natDegree, hnat] at hlead
    exact hlead
  unfold isRepresentedLinearFactor
  simp [hsize]
  simpa [CPolynomial.coeff, CPolynomial.Raw.coeff] using hcoeff

end FiniteField

end Roots

end CPolynomial

end CompPoly
