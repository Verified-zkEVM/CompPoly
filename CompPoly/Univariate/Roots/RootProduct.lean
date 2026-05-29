/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Raw.Modular
import CompPoly.Univariate.Roots.Context

/-!
# Finite-Field Root Products

Executable construction of `gcd(p, X^q - X)` as
`gcd(p, (X^q mod p) - (X mod p))`, so large finite fields never materialize the
dense polynomial `X^q - X`.
-/

namespace CompPoly

namespace CPolynomial

namespace Raw

namespace Roots

namespace FiniteField

/-- Raw squarefree product of the linear factors of `p` whose roots lie in the field. -/
def finiteFieldRootProductWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : CPolynomial.Roots.FiniteField.OddFiniteFieldContext F)
    (p : CPolynomial.Raw F) : CPolynomial.Raw F :=
  if p.trim == 0 then
    0
  else
    let pMonic := CPolynomial.Raw.monicNormalize p
    CPolynomial.Raw.gcdMonic pMonic (CPolynomial.Raw.xPowSubXModWith M D ctx.q pMonic)

/-- Raw squarefree product using the default raw backends. -/
def finiteFieldRootProduct {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (ctx : CPolynomial.Roots.FiniteField.OddFiniteFieldContext F)
    (p : CPolynomial.Raw F) : CPolynomial.Raw F :=
  finiteFieldRootProductWith CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive ctx p

end FiniteField

end Roots

end Raw

namespace Roots

namespace FiniteField

/-- The squarefree product of the linear factors of `p` whose roots lie in the field. -/
def finiteFieldRootProductWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : OddFiniteFieldContext F) (p : CPolynomial F) : CPolynomial F :=
  CPolynomial.ofArray (CPolynomial.Raw.Roots.FiniteField.finiteFieldRootProductWith M D ctx p.val)

/-- The squarefree product of the linear factors of `p` using the default raw backends. -/
def finiteFieldRootProduct {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (ctx : OddFiniteFieldContext F) (p : CPolynomial F) : CPolynomial F :=
  finiteFieldRootProductWith CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive ctx p

private theorem raw_monicNormalize_ne_zero_of_trim_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial.Raw F} (hp : p.trim ≠ (0 : CPolynomial.Raw F)) :
    CPolynomial.Raw.monicNormalize p ≠ 0 := by
  unfold CPolynomial.Raw.monicNormalize
  by_cases hzero : p.trim == (0 : CPolynomial.Raw F)
  · have hzeroEq : p.trim = 0 := by
      simpa using hzero
    exact (hp hzeroEq).elim
  · have hpzeroNe : ¬p.trim = (#[] : CPolynomial.Raw F) := by
      intro hpzero
      exact hzero (by simp [hpzero])
    rw [if_neg hzero]
    intro hsmul
    have hsize_smul :
        (CPolynomial.Raw.smul (p.trim.leadingCoeff)⁻¹ p.trim).size = p.trim.size := by
      simp [CPolynomial.Raw.smul]
    change CPolynomial.Raw.smul (p.trim.leadingCoeff)⁻¹ p.trim = 0 at hsmul
    rw [hsmul] at hsize_smul
    have hsize : p.trim.size = 0 := by
      simpa using hsize_smul.symm
    have hpempty : p.trim = (#[] : CPolynomial.Raw F) := by
      apply Array.eq_empty_of_size_eq_zero
      exact hsize
    exact hp (by simpa using hpempty)

private theorem raw_monicNormalize_trim {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p : CPolynomial.Raw F) :
    (CPolynomial.Raw.monicNormalize p).trim = CPolynomial.Raw.monicNormalize p := by
  unfold CPolynomial.Raw.monicNormalize
  let q := p.trim
  by_cases hzero : q == (0 : CPolynomial.Raw F)
  · have hzeroEq : q = 0 := by
      simpa using hzero
    have hpzeroEq : p.trim = (#[] : CPolynomial.Raw F) := by
      simpa [q] using hzeroEq
    simp [hpzeroEq, CPolynomial.Raw.Trim.canonical_empty]
  · have hzeroNe : q ≠ (0 : CPolynomial.Raw F) := by
      intro hq
      exact hzero (by simp [hq])
    have hpzeroNe : ¬p.trim = (#[] : CPolynomial.Raw F) := by
      intro hp
      exact hzeroNe (by simpa [q] using hp)
    simp [hpzeroNe]
    change (CPolynomial.Raw.mk
        (Array.map (fun r => (p.trim).leadingCoeff⁻¹ * r) p.trim)).trim =
      CPolynomial.Raw.mk (Array.map (fun r => (p.trim).leadingCoeff⁻¹ * r) p.trim)
    apply CPolynomial.Raw.Trim.non_zero_map (fun r => q.leadingCoeff⁻¹ * r)
    · intro r hr
      apply mul_eq_zero.mp at hr
      rcases hr with hinv | hr
      · have hlead0 : q.leadingCoeff = 0 := by
          exact inv_eq_zero.mp hinv
        have hcanon : q.trim = q := by
          simpa [q] using CPolynomial.Raw.Trim.trim_twice p
        have hcrit := (CPolynomial.Raw.Trim.trim_eq_iff_size_eq_zero_or_getLastD_ne_zero
          (p := q)).mp hcanon
        rcases hcrit with hsize | hlast
        · have hqempty : q = (#[] : CPolynomial.Raw F) := by
            apply Array.eq_empty_of_size_eq_zero
            exact hsize
          exact False.elim (hzero (by simp [hqempty]))
        · unfold CPolynomial.Raw.leadingCoeff at hlead0
          rw [hcanon] at hlead0
          exact (hlast hlead0).elim
      · exact hr
    · simpa [q] using CPolynomial.Raw.Trim.trim_twice p

private theorem raw_gcdMonicWithFuel_trim_ne_zero_of_left {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] :
    ∀ fuel (p q : CPolynomial.Raw F), p.trim ≠ (0 : CPolynomial.Raw F) →
      (CPolynomial.Raw.gcdMonicWithFuel fuel p q).trim ≠ 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro p q hp
      unfold CPolynomial.Raw.gcdMonicWithFuel
      rw [raw_monicNormalize_trim]
      exact raw_monicNormalize_ne_zero_of_trim_ne_zero hp
  | succ fuel ih =>
      intro p q hp
      rw [CPolynomial.Raw.gcdMonicWithFuel]
      by_cases hqzero : q.trim == (0 : CPolynomial.Raw F)
      · rw [if_pos hqzero]
        rw [raw_monicNormalize_trim]
        apply raw_monicNormalize_ne_zero_of_trim_ne_zero
        simpa [CPolynomial.Raw.Trim.trim_twice] using hp
      · have hqzeroNe : ¬q.trim = (0 : CPolynomial.Raw F) := by
          intro hqtrim0
          exact hqzero (by simp [hqtrim0])
        rw [if_neg hqzero]
        apply ih
        intro hqtrim0
        rw [CPolynomial.Raw.Trim.trim_twice q] at hqtrim0
        exact hqzeroNe hqtrim0

/-- Monic normalization preserves nonzeroness. -/
theorem monicNormalize_ne_zero_of_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} (hp : p ≠ 0) :
    CPolynomial.monicNormalize p ≠ 0 := by
  intro hzero
  unfold CPolynomial.monicNormalize at hzero
  have hval := congrArg Subtype.val hzero
  simp [CPolynomial.ofArray] at hval
  have hpraw : p.val.trim ≠ (0 : CPolynomial.Raw F) := by
    intro hpraw0
    apply hp
    apply CPolynomial.ext
    rw [CPolynomial.trim_eq] at hpraw0
    simpa using hpraw0
  rw [raw_monicNormalize_trim] at hval
  exact raw_monicNormalize_ne_zero_of_trim_ne_zero hpraw hval

/-- The monic gcd of a nonzero left operand is nonzero. -/
theorem gcdMonic_ne_zero_of_left {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    {p q : CPolynomial F} (hp : p ≠ 0) :
    CPolynomial.gcdMonic p q ≠ 0 := by
  intro hzero
  unfold CPolynomial.gcdMonic at hzero
  have hval := congrArg Subtype.val hzero
  simp [CPolynomial.ofArray] at hval
  have hpraw : p.val.trim ≠ (0 : CPolynomial.Raw F) := by
    intro hpraw0
    apply hp
    apply CPolynomial.ext
    rw [CPolynomial.trim_eq] at hpraw0
    simpa using hpraw0
  unfold CPolynomial.Raw.gcdMonic at hval
  exact raw_gcdMonicWithFuel_trim_ne_zero_of_left _ p.val q.val hpraw hval

/-- The finite-field root product of a nonzero polynomial is nonzero. -/
theorem finiteFieldRootProductWith_ne_zero_of_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : OddFiniteFieldContext F) {p : CPolynomial F}
    (hp : p ≠ 0) :
    finiteFieldRootProductWith M D ctx p ≠ 0 := by
  intro hzeroProduct
  unfold finiteFieldRootProductWith at hzeroProduct
  have hval := congrArg Subtype.val hzeroProduct
  simp [CPolynomial.ofArray] at hval
  have hpraw : p.val.trim ≠ (0 : CPolynomial.Raw F) := by
    intro hpraw0
    apply hp
    apply CPolynomial.ext
    rw [CPolynomial.trim_eq] at hpraw0
    simpa using hpraw0
  unfold CPolynomial.Raw.Roots.FiniteField.finiteFieldRootProductWith at hval
  by_cases hpempty : p.val = (#[] : CPolynomial.Raw F)
  · apply hp
    apply CPolynomial.ext
    simpa using hpempty
  · simp [hpempty, CPolynomial.trim_eq] at hval
    unfold CPolynomial.Raw.gcdMonic at hval
    exact raw_gcdMonicWithFuel_trim_ne_zero_of_left
      _ (CPolynomial.Raw.monicNormalize p.val)
      (CPolynomial.Raw.xPowSubXModWith M D ctx.q (CPolynomial.Raw.monicNormalize p.val))
      (by
        rw [raw_monicNormalize_trim]
        exact raw_monicNormalize_ne_zero_of_trim_ne_zero hpraw) hval

end FiniteField

end Roots

end CPolynomial

end CompPoly
