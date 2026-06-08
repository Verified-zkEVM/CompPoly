/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Raw.Modular
import CompPoly.Univariate.EuclideanAlgorithm
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
    (ctx : CPolynomial.Roots.FiniteField.FiniteFieldContext F)
    (p : CPolynomial.Raw F) : CPolynomial.Raw F :=
  if p.trim == 0 then
    0
  else
    let pMonic := CPolynomial.Raw.monicNormalize p
    CPolynomial.Raw.gcdMonic pMonic (CPolynomial.Raw.xPowSubXModWith M D ctx.q pMonic)

/-- Raw squarefree product using the default raw backends. -/
def finiteFieldRootProduct {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (ctx : CPolynomial.Roots.FiniteField.FiniteFieldContext F)
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
    (ctx : FiniteFieldContext F) (p : CPolynomial F) : CPolynomial F :=
  CPolynomial.ofArray (CPolynomial.Raw.Roots.FiniteField.finiteFieldRootProductWith M D ctx p.val)

/-- The squarefree product of the linear factors of `p` using the default raw backends. -/
def finiteFieldRootProduct {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (ctx : FiniteFieldContext F) (p : CPolynomial F) : CPolynomial F :=
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
        (Array.map (fun r ↦ (p.trim).leadingCoeff⁻¹ * r) p.trim)).trim =
      CPolynomial.Raw.mk (Array.map (fun r ↦ (p.trim).leadingCoeff⁻¹ * r) p.trim)
    apply CPolynomial.Raw.Trim.non_zero_map (fun r ↦ q.leadingCoeff⁻¹ * r)
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

private theorem raw_xPowSubXModWith_trim {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (modulus : CPolynomial.Raw F) :
    (CPolynomial.Raw.xPowSubXModWith M D q modulus).trim =
      CPolynomial.Raw.xPowSubXModWith M D q modulus := by
  unfold CPolynomial.Raw.xPowSubXModWith
  exact CPolynomial.Raw.Trim.trim_twice _

/-- The finite-field root product agrees with the normalized Mathlib gcd of the
monic input and its represented Frobenius witness. -/
theorem finiteFieldRootProductWith_toPoly_eq_normalize_gcd {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) {p : CPolynomial F}
    (hp : p ≠ 0) :
    let pMonic := CPolynomial.monicNormalize p
    (finiteFieldRootProductWith M D ctx p).toPoly =
      normalize (EuclideanDomain.gcd pMonic.toPoly
        (CPolynomial.ofArray
          (CPolynomial.Raw.xPowSubXModWith M D ctx.q pMonic.val)).toPoly) := by
  dsimp
  unfold finiteFieldRootProductWith
  unfold CPolynomial.Raw.Roots.FiniteField.finiteFieldRootProductWith
  have hpraw : p.val.trim ≠ (0 : CPolynomial.Raw F) := by
    intro hpraw0
    apply hp
    apply CPolynomial.ext
    rw [CPolynomial.trim_eq] at hpraw0
    simpa using hpraw0
  have hpzero : ¬(p.val.trim == (0 : CPolynomial.Raw F)) := by
    intro hzero
    exact hpraw (LawfulBEq.eq_of_beq hzero)
  rw [if_neg hpzero]
  have hpMonicVal :
      (CPolynomial.monicNormalize p).val = CPolynomial.Raw.monicNormalize p.val := by
    unfold CPolynomial.monicNormalize CPolynomial.ofArray
    change (CPolynomial.Raw.monicNormalize p.val).trim =
      CPolynomial.Raw.monicNormalize p.val
    exact raw_monicNormalize_trim p.val
  rw [← hpMonicVal]
  let witnessRaw :=
    CPolynomial.Raw.xPowSubXModWith M D ctx.q (CPolynomial.monicNormalize p).val
  have hwitnessTrim : witnessRaw.trim = witnessRaw := by
    dsimp [witnessRaw]
    exact raw_xPowSubXModWith_trim M D ctx.q (CPolynomial.monicNormalize p).val
  simpa [CPolynomial.gcdMonic, CPolynomial.ofArray, witnessRaw, hwitnessTrim] using
    CPolynomial.gcdMonic_toPoly_eq_normalize_gcd
      (CPolynomial.monicNormalize p) (CPolynomial.ofArray witnessRaw)

private theorem raw_monicNormalize_trim_arg {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p : CPolynomial.Raw F) :
    CPolynomial.Raw.monicNormalize p.trim = CPolynomial.Raw.monicNormalize p := by
  unfold CPolynomial.Raw.monicNormalize
  rw [CPolynomial.Raw.Trim.trim_twice]

private theorem raw_monicNormalize_toPoly_eq_normalize {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (p : CPolynomial.Raw F) :
    (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize p)).toPoly =
      normalize (CPolynomial.ofArray p).toPoly := by
  have h := CPolynomial.monicNormalize_toPoly_eq_normalize (CPolynomial.ofArray p)
  unfold CPolynomial.monicNormalize at h
  unfold CPolynomial.ofArray at h
  rw [raw_monicNormalize_trim_arg] at h
  exact h

private theorem raw_monicNormalize_toPoly_monic {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    {p : CPolynomial.Raw F} (hp : p.trim ≠ 0) :
    (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize p)).toPoly.Monic := by
  rw [raw_monicNormalize_toPoly_eq_normalize]
  have hpC : CPolynomial.ofArray p ≠ 0 := by
    intro h
    have hval := congrArg Subtype.val h
    unfold CPolynomial.ofArray at hval
    exact hp (by simpa using hval)
  have hpPoly : (CPolynomial.ofArray p).toPoly ≠ 0 :=
    (CPolynomial.toPoly_eq_zero_iff (CPolynomial.ofArray p)).not.mpr hpC
  exact Polynomial.monic_normalize hpPoly

private theorem raw_modContext_toPoly_eq_modByMonic {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (D : CPolynomial.Raw.ModContext F) {p q : CPolynomial.Raw F}
    (hpTrim : p.trim = p) (hqTrim : q.trim = q)
    (hqMonic : (CPolynomial.ofArray q).monic) :
    (CPolynomial.ofArray (D.modByMonic p q)).toPoly =
      (CPolynomial.ofArray p).toPoly %ₘ (CPolynomial.ofArray q).toPoly := by
  rw [D.modByMonic_eq_modByMonic p q hpTrim hqTrim]
  have hpval : (CPolynomial.ofArray p).val = p := by
    unfold CPolynomial.ofArray
    exact hpTrim
  have hqval : (CPolynomial.ofArray q).val = q := by
    unfold CPolynomial.ofArray
    exact hqTrim
  have h := CPolynomial.modByMonic_toPoly_eq_modByMonic
    (CPolynomial.ofArray p) (CPolynomial.ofArray q) hqMonic
  simpa [CPolynomial.modByMonic, hpval, hqval, CPolynomial.ofArray_toPoly] using h

private theorem raw_mulModWith_toPoly_eq_modByMonic {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {modulus p q : CPolynomial.Raw F} (hmod : modulus.trim ≠ 0) :
    (CPolynomial.ofArray (CPolynomial.Raw.mulModWith M D modulus p q)).toPoly =
      ((CPolynomial.ofArray p).toPoly * (CPolynomial.ofArray q).toPoly) %ₘ
        (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize modulus)).toPoly := by
  unfold CPolynomial.Raw.mulModWith
  have hzero : ¬modulus.trim == (0 : CPolynomial.Raw F) := by
    intro h
    exact hmod (LawfulBEq.eq_of_beq h)
  rw [if_neg hzero]
  have hproductTrim : (M.mul p q).trim = M.mul p q := by
    rw [M.mul_eq_mul]
    exact CPolynomial.Raw.mul_is_trimmed p q
  have hqMonic : (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize modulus)).monic :=
    (CPolynomial.monic_toPoly_iff _).mpr (raw_monicNormalize_toPoly_monic hmod)
  rw [raw_modContext_toPoly_eq_modByMonic D hproductTrim
    (raw_monicNormalize_trim modulus) hqMonic]
  rw [M.mul_eq_mul, CPolynomial.ofArray_toPoly, CPolynomial.ofArray_toPoly,
    CPolynomial.Raw.toPoly_mul]
  rw [CPolynomial.ofArray_toPoly, CPolynomial.ofArray_toPoly]

private theorem polynomial_modByMonic_idem {F : Type*} [Field F]
    {p q : Polynomial F} (hq : q.Monic) :
    (p %ₘ q) %ₘ q = p %ₘ q := by
  refine Polynomial.modByMonic_eq_of_dvd_sub hq ?_
  refine ⟨-(p /ₘ q), ?_⟩
  calc
    p %ₘ q - p = p %ₘ q - (p %ₘ q + q * (p /ₘ q)) := by
      rw [Polynomial.modByMonic_add_div p]
    _ = q * -(p /ₘ q) := by
      ring

private theorem polynomial_mul_modByMonic_congr {F : Type*} [Field F]
    {a b c d m : Polynomial F}
    (ha : a %ₘ m = b %ₘ m) (hc : c %ₘ m = d %ₘ m) :
    (a * c) %ₘ m = (b * d) %ₘ m := by
  calc
    (a * c) %ₘ m = (a %ₘ m * (c %ₘ m)) %ₘ m := by
      rw [Polynomial.mul_modByMonic]
    _ = (b %ₘ m * (d %ₘ m)) %ₘ m := by
      rw [ha, hc]
    _ = (b * d) %ₘ m := by
      exact (Polynomial.mul_modByMonic b d m).symm

private theorem polynomial_pow_modByMonic_congr {F : Type*} [Field F]
    {a b m : Polynomial F} (h : a %ₘ m = b %ₘ m) :
    ∀ n, a ^ n %ₘ m = b ^ n %ₘ m := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact polynomial_mul_modByMonic_congr ih h

private theorem raw_powModBinaryAuxWith_toPoly_modByMonic {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {modulus acc current : CPolynomial.Raw F} (hmod : modulus.trim ≠ 0) :
    ∀ n,
      (CPolynomial.ofArray
        (CPolynomial.Raw.powModBinaryAuxWith M D modulus n acc current)).toPoly %ₘ
          (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize modulus)).toPoly =
        ((CPolynomial.ofArray acc).toPoly * (CPolynomial.ofArray current).toPoly ^ n) %ₘ
          (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize modulus)).toPoly := by
  intro n
  induction n using Nat.strongRecOn generalizing acc current with
  | ind n ih =>
      cases n with
      | zero =>
          rw [CPolynomial.Raw.powModBinaryAuxWith, pow_zero]
          congr 1
          ring
      | succ n =>
          rw [CPolynomial.Raw.powModBinaryAuxWith]
          let m := (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize modulus)).toPoly
          let acc' :=
            if (n + 1) % 2 == 1 then
              CPolynomial.Raw.mulModWith M D modulus acc current
            else
              acc
          let current' := CPolynomial.Raw.mulModWith M D modulus current current
          have ih' := ih ((n + 1) / 2)
            (Nat.div_lt_self (Nat.succ_pos n) (by decide))
            (acc := acc') (current := current')
          change
            (CPolynomial.ofArray
              (CPolynomial.Raw.powModBinaryAuxWith M D modulus
                ((n + 1) / 2) acc' current')).toPoly %ₘ
                m =
              ((CPolynomial.ofArray acc).toPoly *
                (CPolynomial.ofArray current).toPoly ^ (n + 1)) %ₘ m
          rw [ih']
          have hcurrent :
              (CPolynomial.ofArray current').toPoly %ₘ m =
                ((CPolynomial.ofArray current).toPoly *
                  (CPolynomial.ofArray current).toPoly) %ₘ m := by
            dsimp [current', m]
            rw [raw_mulModWith_toPoly_eq_modByMonic M D hmod]
            exact polynomial_modByMonic_idem (raw_monicNormalize_toPoly_monic hmod)
          by_cases hodd : (n + 1) % 2 == 1
          · have hacc :
                (CPolynomial.ofArray acc').toPoly %ₘ m =
                  ((CPolynomial.ofArray acc).toPoly *
                    (CPolynomial.ofArray current).toPoly) %ₘ m := by
              dsimp [acc', m]
              rw [if_pos hodd]
              rw [raw_mulModWith_toPoly_eq_modByMonic M D hmod]
              exact polynomial_modByMonic_idem (raw_monicNormalize_toPoly_monic hmod)
            have hpow :
                ((CPolynomial.ofArray current).toPoly *
                    (CPolynomial.ofArray current).toPoly) ^ ((n + 1) / 2) =
                  (CPolynomial.ofArray current).toPoly ^ n := by
              rw [mul_pow, ← pow_add]
              congr 1
              have hoddNat : (n + 1) % 2 = 1 := by
                simpa using hodd
              omega
            have hcurrentPow :
                (CPolynomial.ofArray current').toPoly ^ ((n + 1) / 2) %ₘ m =
                  (CPolynomial.ofArray current).toPoly ^ n %ₘ m := by
              have h := polynomial_pow_modByMonic_congr hcurrent ((n + 1) / 2)
              rwa [hpow] at h
            calc
              ((CPolynomial.ofArray acc').toPoly *
                  (CPolynomial.ofArray current').toPoly ^ ((n + 1) / 2)) %ₘ m =
                (((CPolynomial.ofArray acc).toPoly *
                    (CPolynomial.ofArray current).toPoly) *
                  (CPolynomial.ofArray current).toPoly ^ n) %ₘ m := by
                  exact polynomial_mul_modByMonic_congr hacc hcurrentPow
              _ = ((CPolynomial.ofArray acc).toPoly *
                    (CPolynomial.ofArray current).toPoly ^ (n + 1)) %ₘ m := by
                  rw [pow_succ]
                  ring_nf
          · have hacc :
                (CPolynomial.ofArray acc').toPoly %ₘ m =
                  (CPolynomial.ofArray acc).toPoly %ₘ m := by
              dsimp [acc']
              rw [if_neg hodd]
            have hpow :
                ((CPolynomial.ofArray current).toPoly *
                    (CPolynomial.ofArray current).toPoly) ^ ((n + 1) / 2) =
                  (CPolynomial.ofArray current).toPoly ^ (n + 1) := by
              rw [mul_pow, ← pow_add]
              congr 1
              have hoddNat : (n + 1) % 2 = 0 := by
                simpa using hodd
              omega
            have hcurrentPow :
                (CPolynomial.ofArray current').toPoly ^ ((n + 1) / 2) %ₘ m =
                  (CPolynomial.ofArray current).toPoly ^ (n + 1) %ₘ m := by
              have h := polynomial_pow_modByMonic_congr hcurrent ((n + 1) / 2)
              rwa [hpow] at h
            exact polynomial_mul_modByMonic_congr hacc hcurrentPow

private theorem raw_powModWith_X_toPoly_modByMonic {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {modulus : CPolynomial.Raw F} (hmod : modulus.trim ≠ 0) (q : Nat) :
    (CPolynomial.ofArray
        (CPolynomial.Raw.powModWith M D modulus CPolynomial.Raw.X q)).toPoly %ₘ
      (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize modulus)).toPoly =
    ((Polynomial.X : Polynomial F) ^ q) %ₘ
      (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize modulus)).toPoly := by
  unfold CPolynomial.Raw.powModWith
  have hzero : ¬modulus.trim == (0 : CPolynomial.Raw F) := by
    intro h
    exact hmod (LawfulBEq.eq_of_beq h)
  rw [if_neg hzero]
  let m := (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize modulus)).toPoly
  let oneMod := D.modByMonic (1 : CPolynomial.Raw F) (CPolynomial.Raw.monicNormalize modulus)
  change
    (CPolynomial.ofArray
      (CPolynomial.Raw.powModBinaryAuxWith M D modulus q oneMod CPolynomial.Raw.X)).toPoly %ₘ
      m =
    ((Polynomial.X : Polynomial F) ^ q) %ₘ m
  rw [raw_powModBinaryAuxWith_toPoly_modByMonic M D hmod]
  have hOneTrim : (1 : CPolynomial.Raw F).trim = 1 := by
    change CPolynomial.Raw.trim (#[] |>.push (1 : F)) = (#[] |>.push (1 : F))
    apply CPolynomial.Raw.Trim.push_trim
    simp
  have hone :
      (CPolynomial.ofArray oneMod).toPoly %ₘ m =
        (1 : Polynomial F) %ₘ m := by
    dsimp [oneMod, m]
    rw [raw_modContext_toPoly_eq_modByMonic D hOneTrim
      (raw_monicNormalize_trim modulus)
      ((CPolynomial.monic_toPoly_iff _).mpr (raw_monicNormalize_toPoly_monic hmod))]
    rw [CPolynomial.ofArray_toPoly, CPolynomial.Raw.toPoly_one]
    exact polynomial_modByMonic_idem (raw_monicNormalize_toPoly_monic hmod)
  have hX :
      (CPolynomial.ofArray CPolynomial.Raw.X).toPoly ^ q %ₘ m =
        ((Polynomial.X : Polynomial F) ^ q) %ₘ m := by
    rw [CPolynomial.ofArray_toPoly, CPolynomial.Raw.toPoly_X]
  have hmul := polynomial_mul_modByMonic_congr hone hX
  simpa [one_mul] using hmul

private theorem raw_xModWith_toPoly_modByMonic {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (D : CPolynomial.Raw.ModContext F)
    {modulus : CPolynomial.Raw F} (hmod : modulus.trim ≠ 0) :
    (CPolynomial.ofArray (CPolynomial.Raw.xModWith D modulus)).toPoly %ₘ
      (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize modulus)).toPoly =
    (Polynomial.X : Polynomial F) %ₘ
      (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize modulus)).toPoly := by
  unfold CPolynomial.Raw.xModWith
  have hzero : ¬modulus.trim == (0 : CPolynomial.Raw F) := by
    intro h
    exact hmod (LawfulBEq.eq_of_beq h)
  rw [if_neg hzero]
  let m := (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize modulus)).toPoly
  have hXTrim : (CPolynomial.Raw.X : CPolynomial.Raw F).trim = CPolynomial.Raw.X := by
    exact CPolynomial.Raw.X_canonical
  rw [raw_modContext_toPoly_eq_modByMonic D hXTrim
    (raw_monicNormalize_trim modulus)
    ((CPolynomial.monic_toPoly_iff _).mpr (raw_monicNormalize_toPoly_monic hmod))]
  rw [CPolynomial.ofArray_toPoly, CPolynomial.Raw.toPoly_X]
  exact polynomial_modByMonic_idem (raw_monicNormalize_toPoly_monic hmod)

private theorem raw_xPowSubXModWith_toPoly_modByMonic {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {modulus : CPolynomial.Raw F} (hmod : modulus.trim ≠ 0) (q : Nat) :
    (CPolynomial.ofArray
        (CPolynomial.Raw.xPowSubXModWith M D q modulus)).toPoly %ₘ
      (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize modulus)).toPoly =
    (((Polynomial.X : Polynomial F) ^ q - Polynomial.X) %ₘ
      (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize modulus)).toPoly) := by
  unfold CPolynomial.Raw.xPowSubXModWith
  rw [CPolynomial.ofArray_toPoly, CPolynomial.Raw.toPoly_sub, Polynomial.sub_modByMonic]
  rw [← CPolynomial.ofArray_toPoly
      (CPolynomial.Raw.powModWith M D modulus CPolynomial.Raw.X q),
    ← CPolynomial.ofArray_toPoly (CPolynomial.Raw.xModWith D modulus)]
  rw [raw_powModWith_X_toPoly_modByMonic M D hmod q,
    raw_xModWith_toPoly_modByMonic D hmod]
  rw [Polynomial.sub_modByMonic]

/-- The finite-field root product divides the finite-field Frobenius polynomial.

This is the modular-gcd bridge: the executable root product uses the congruent
modular witness `(X^q mod p) - (X mod p)` instead of materializing `X^q - X`.
-/
theorem finiteFieldRootProductWith_dvd_frobenius_of_context {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) {p : CPolynomial F} (_hp : p ≠ 0) :
    (finiteFieldRootProductWith M D ctx p).toPoly ∣
      ((Polynomial.X : Polynomial F) ^ ctx.q - Polynomial.X) := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  rw [finiteFieldRootProductWith_toPoly_eq_normalize_gcd M D ctx _hp]
  apply dvd_trans (normalize_associated _).dvd
  let pMonic := CPolynomial.monicNormalize p
  let witness :=
    (CPolynomial.ofArray
      (CPolynomial.Raw.xPowSubXModWith M D ctx.q pMonic.val)).toPoly
  have hgLeft : EuclideanDomain.gcd pMonic.toPoly witness ∣ pMonic.toPoly :=
    EuclideanDomain.gcd_dvd_left _ _
  have hgRight : EuclideanDomain.gcd pMonic.toPoly witness ∣ witness :=
    EuclideanDomain.gcd_dvd_right _ _
  have hpPoly : p.toPoly ≠ 0 :=
    (CPolynomial.toPoly_eq_zero_iff p).not.mpr _hp
  have hpMonicPoly : pMonic.toPoly.Monic := by
    dsimp [pMonic]
    rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
    exact Polynomial.monic_normalize hpPoly
  have hpMonicNe : pMonic ≠ 0 := by
    intro hzero
    dsimp [pMonic] at hzero
    unfold CPolynomial.monicNormalize at hzero
    have hval := congrArg Subtype.val hzero
    simp [CPolynomial.ofArray] at hval
    have hpraw : p.val.trim ≠ (0 : CPolynomial.Raw F) := by
      intro hpraw0
      apply _hp
      apply CPolynomial.ext
      rw [CPolynomial.trim_eq] at hpraw0
      simpa using hpraw0
    rw [raw_monicNormalize_trim] at hval
    exact raw_monicNormalize_ne_zero_of_trim_ne_zero hpraw hval
  have hmod : pMonic.val.trim ≠ 0 := by
    intro htrim
    apply hpMonicNe
    apply CPolynomial.ext
    rw [CPolynomial.trim_eq] at htrim
    simpa using htrim
  have hnormModulus :
      (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize pMonic.val)).toPoly =
        pMonic.toPoly := by
    rw [raw_monicNormalize_toPoly_eq_normalize]
    rw [CPolynomial.ofArray_toPoly]
    exact hpMonicPoly.normalize_eq_self
  have hwitnessMod :
      witness %ₘ pMonic.toPoly =
        (((Polynomial.X : Polynomial F) ^ ctx.q - Polynomial.X) %ₘ pMonic.toPoly) := by
    dsimp [witness]
    have h := raw_xPowSubXModWith_toPoly_modByMonic M D hmod ctx.q
    rwa [hnormModulus] at h
  have hpMonic :
      pMonic.toPoly ∣ (Polynomial.X : Polynomial F) ^ ctx.q - Polynomial.X - witness := by
    rw [← Polynomial.modByMonic_eq_zero_iff_dvd hpMonicPoly]
    rw [Polynomial.sub_modByMonic]
    rw [← hwitnessMod]
    simp
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    dvd_add (hgLeft.trans hpMonic) hgRight

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
    (ctx : FiniteFieldContext F) {p : CPolynomial F}
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
