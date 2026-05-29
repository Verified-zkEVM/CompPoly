/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.Backend
import CompPoly.Univariate.Roots.SmoothSubgroupCorrectness
import CompPoly.Univariate.ToPoly.Impl

/-!
# Finite-Field Root Correctness

Theorem statements and certified context constructors for the executable
finite-field root backend.
-/

namespace CompPoly

namespace CPolynomial

private lemma mem_eraseDups_fold {α : Type*} [BEq α] [LawfulBEq α]
    (a : α) : ∀ (xs : List α) (out : Array α),
      a ∈ List.foldl (fun out x => if x ∈ out then out else out.push x) out xs →
        a ∈ out ∨ a ∈ xs := by
  intro xs
  induction xs with
  | nil =>
      intro out h
      exact Or.inl h
  | cons x xs ih =>
      intro out h
      simp only [List.foldl_cons] at h
      by_cases hx : x ∈ out
      · have h' := ih out (by simpa [hx] using h)
        cases h' with
        | inl hout => exact Or.inl hout
        | inr hxs => exact Or.inr (by simp [hxs])
      · have h' := ih (out.push x) (by simpa [hx] using h)
        cases h' with
        | inl hout =>
            simp at hout
            cases hout with
            | inl hout => exact Or.inl hout
            | inr hax => exact Or.inr (by simp [hax])
        | inr hxs => exact Or.inr (by simp [hxs])

private lemma mem_eraseDups {α : Type*} [BEq α] [LawfulBEq α]
    {xs : Array α} {a : α} (h : a ∈ xs.eraseDups) : a ∈ xs := by
  unfold Array.eraseDups at h
  rcases xs with ⟨l⟩
  simp at h ⊢
  have hh := mem_eraseDups_fold a l #[] h
  simpa using hh

private lemma mem_eraseDups_fold_of_mem {α : Type*} [BEq α] [LawfulBEq α]
    (a : α) : ∀ (xs : List α) (out : Array α),
      a ∈ out ∨ a ∈ xs →
        a ∈ List.foldl (fun out x => if x ∈ out then out else out.push x) out xs := by
  intro xs
  induction xs with
  | nil =>
      intro out h
      simpa using h
  | cons x xs ih =>
      intro out h
      simp only [List.foldl_cons]
      by_cases hx : x ∈ out
      · simp [hx]
        apply ih out
        cases h with
        | inl hout => exact Or.inl hout
        | inr hmem =>
            simp at hmem
            cases hmem with
            | inl hax => exact Or.inl (by simpa [hax] using hx)
            | inr hxs => exact Or.inr hxs
      · simp [hx]
        apply ih (out.push x)
        cases h with
        | inl hout => exact Or.inl (by simp [hout])
        | inr hmem =>
            simp at hmem
            cases hmem with
            | inl hax => exact Or.inl (by simp [hax])
            | inr hxs => exact Or.inr hxs

private lemma mem_eraseDups_of_mem {α : Type*} [BEq α] [LawfulBEq α]
    {xs : Array α} {a : α} (h : a ∈ xs) : a ∈ xs.eraseDups := by
  unfold Array.eraseDups
  rcases xs with ⟨l⟩
  simp at h ⊢
  exact mem_eraseDups_fold_of_mem a l #[] (Or.inr h)

private theorem Raw.toPoly_smul {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (c : F) (p : CPolynomial.Raw F) :
    (CPolynomial.Raw.smul c p).toPoly = c • p.toPoly := by
  ext i
  rw [Polynomial.coeff_smul]
  rw [CPolynomial.Raw.coeff_toPoly, CPolynomial.Raw.coeff_toPoly]
  exact CPolynomial.Raw.smul_coeff c p i

private theorem Raw.eval_smul {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (c a : F) (p : CPolynomial.Raw F) :
    (CPolynomial.Raw.smul c p).eval a = c * p.eval a := by
  rw [← CPolynomial.Raw.eval_toPoly_eq_eval, Raw.toPoly_smul]
  rw [Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
    CPolynomial.Raw.eval_toPoly_eq_eval]

private theorem Raw.eval_mul {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (a : F) (p q : CPolynomial.Raw F) :
    (p * q).eval a = p.eval a * q.eval a := by
  rw [← CPolynomial.Raw.eval_toPoly_eq_eval, CPolynomial.Raw.toPoly_mul,
    Polynomial.eval_mul, CPolynomial.Raw.eval_toPoly_eq_eval,
    CPolynomial.Raw.eval_toPoly_eq_eval]

private theorem Raw.eval_C {F : Type*} [Field F] (a c : F) :
    (CPolynomial.Raw.C c).eval a = c := by
  rw [← CPolynomial.Raw.eval_toPoly_eq_eval]
  simp [CPolynomial.Raw.toPoly_C]

private theorem Raw.eval_C_smul {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (c a : F) (p : CPolynomial.Raw F) :
    (CPolynomial.Raw.C c • p).eval a = c * p.eval a := by
  rw [smul_eq_mul, Raw.eval_mul, Raw.eval_C]

private theorem Raw.eval_monicNormalize_eq_zero_of_eval_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial.Raw F} {a : F} (hp : p.eval a = 0) :
    (CPolynomial.Raw.monicNormalize p).eval a = 0 := by
  unfold CPolynomial.Raw.monicNormalize
  by_cases hzero : p.trim = (#[] : CPolynomial.Raw F)
  · simp [hzero, CPolynomial.Raw.eval, CPolynomial.Raw.eval₂]
  · simp [hzero]
    change CPolynomial.Raw.eval a (CPolynomial.Raw.smul p.trim.leadingCoeff⁻¹ p.trim) = 0
    rw [Raw.eval_smul, CPolynomial.Raw.eval_trim_eq_eval, hp]
    simp

private theorem Raw.eval_mod_eq_zero_of_left_right {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p q : CPolynomial.Raw F} {a : F}
    (hp : p.eval a = 0) (hq : q.eval a = 0) :
    (p % q).eval a = 0 := by
  change (CPolynomial.Raw.mod p q).eval a = 0
  unfold CPolynomial.Raw.mod
  have hqscaled : (CPolynomial.Raw.C (q.leadingCoeff)⁻¹ * q).eval a = 0 := by
    rw [Raw.eval_mul, Raw.eval_C, hq]
    simp
  have hmod := CPolynomial.Raw.eval_modByMonic_eq_self_of_eval_eq_zero
    (CPolynomial.Raw.C (q.leadingCoeff)⁻¹ • p)
    (CPolynomial.Raw.C (q.leadingCoeff)⁻¹ * q) hqscaled
  rw [hmod, Raw.eval_C_smul, hp]
  simp

private theorem Raw.eval_gcdMonicWithFuel_eq_zero_of_left_right {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] {a : F} :
    ∀ fuel (p q : CPolynomial.Raw F),
      p.eval a = 0 → q.eval a = 0 →
        (CPolynomial.Raw.gcdMonicWithFuel fuel p q).eval a = 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro p q hp _hq
      unfold CPolynomial.Raw.gcdMonicWithFuel
      exact Raw.eval_monicNormalize_eq_zero_of_eval_eq_zero hp
  | succ fuel ih =>
      intro p q hp hq
      unfold CPolynomial.Raw.gcdMonicWithFuel
      by_cases hqzero : q.trim = (#[] : CPolynomial.Raw F)
      · simp [hqzero]
        exact Raw.eval_monicNormalize_eq_zero_of_eval_eq_zero (by
          rw [CPolynomial.Raw.eval_trim_eq_eval]
          exact hp)
      · simp [hqzero]
        apply ih
        · rw [CPolynomial.Raw.eval_trim_eq_eval]
          exact hq
        · exact Raw.eval_mod_eq_zero_of_left_right
            (by
              rw [CPolynomial.Raw.eval_trim_eq_eval]
              exact hp)
            (by
              rw [CPolynomial.Raw.eval_trim_eq_eval]
              exact hq)

/-- Monic normalization preserves roots of nonzero polynomials. -/
theorem monicNormalize_root_iff {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} {a : F} (hp : p ≠ 0) :
    CPolynomial.eval a (monicNormalize p) = 0 ↔ CPolynomial.eval a p = 0 := by
  unfold monicNormalize CPolynomial.Raw.monicNormalize
  have hpempty : ¬ (p.val : CPolynomial.Raw F) = #[] := by
    intro h
    apply hp
    apply CPolynomial.ext
    simpa using h
  have hsize : 0 < p.val.size := by
    cases hs : p.val.size with
    | zero =>
        have hval : p.val = (#[] : CPolynomial.Raw F) :=
          Array.eq_empty_of_size_eq_zero hs
        exact (hpempty hval).elim
    | succ _ => omega
  have hgetLastD :
      (p.val : CPolynomial.Raw F).getLastD 0 =
        (p.val : CPolynomial.Raw F).getLast hsize := by
    unfold Array.getLastD Array.getLast
    simp [hsize]
  have hlc : (p.val : CPolynomial.Raw F).getLastD 0 ≠ 0 := by
    rw [hgetLastD]
    exact p.property hsize
  simp [CPolynomial.Raw.leadingCoeff, hpempty]
  change
    CPolynomial.Raw.eval a
          (((Array.getLastD (p.val : CPolynomial.Raw F) 0)⁻¹ • p.val).trim) =
        0 ↔
      CPolynomial.Raw.eval a p.val = 0
  rw [CPolynomial.Raw.eval_trim_eq_eval]
  change
    CPolynomial.Raw.eval a
          (CPolynomial.Raw.smul ((Array.getLastD (p.val : CPolynomial.Raw F) 0)⁻¹)
            p.val) =
        0 ↔
      CPolynomial.Raw.eval a p.val = 0
  rw [CPolynomial.Raw.eval_smul]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hlc)
  · intro h
    simp [h]

/-- The monic gcd contains every common root. -/
theorem gcdMonic_root_of_left_right {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    {p q : CPolynomial F} {a : F}
    (hp : CPolynomial.eval a p = 0) (hq : CPolynomial.eval a q = 0) :
    CPolynomial.eval a (gcdMonic p q) = 0 := by
  unfold gcdMonic
  change CPolynomial.Raw.eval a (CPolynomial.Raw.gcdMonic p.val q.val).trim = 0
  rw [CPolynomial.Raw.eval_trim_eq_eval]
  unfold CPolynomial.Raw.gcdMonic
  exact Raw.eval_gcdMonicWithFuel_eq_zero_of_left_right _ p.val q.val hp hq

/-- Roots extracted from a linear factor satisfy that factor. -/
theorem linearRootOfFactor?_sound {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    {factor : CPolynomial F} {a : F}
    (h : linearRootOfFactor? factor = some a) :
    CPolynomial.eval a factor = 0 := by
  rcases factor with ⟨⟨xs⟩, hcanon⟩
  cases xs with
  | nil => simp [linearRootOfFactor?] at h
  | cons x xs =>
      cases xs with
      | nil => simp [linearRootOfFactor?] at h
      | cons y xs =>
          cases xs with
          | nil =>
              simp [linearRootOfFactor?, CPolynomial.eval] at h ⊢
              rcases h with ⟨hy, ha⟩
              rw [← ha]
              field_simp [hy]
              ring
          | cons z xs => simp [linearRootOfFactor?] at h

/-- Validation makes returned candidates sound for the original polynomial. -/
theorem mem_validateRootCandidates_eval_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} {candidates : Array F} {a : F}
    (h : a ∈ (validateRootCandidates p candidates).toList) :
    CPolynomial.eval a p = 0 := by
  rw [validateRootCandidates] at h
  simp at h
  simpa [CPolynomial.eval_horner_eq_eval] using h.2

private theorem mem_rootsFromLinearFactors_eval_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} {factors : Array (CPolynomial F)} {a : F}
    (h : a ∈ (rootsFromLinearFactors p factors).toList) :
    CPolynomial.eval a p = 0 := by
  rw [rootsFromLinearFactors] at h
  have h' :
      a ∈ (validateRootCandidates p
        (List.filterMap linearRootOfFactor? factors.toList).toArray).toList := by
    have hm :
        a ∈ validateRootCandidates p
          (List.filterMap linearRootOfFactor? factors.toList).toArray :=
      mem_eraseDups (by simpa using h)
    simpa using hm
  exact mem_validateRootCandidates_eval_eq_zero h'

namespace Roots

namespace FiniteField

private theorem linearRootOfFactor?_eq_some_of_candidate {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {factor : CPolynomial F} {a : F}
    (h : IsLinearRootFactorCandidate factor a) :
    CPolynomial.linearRootOfFactor? factor = some a := by
  rw [CPolynomial.linearRootOfFactor?]
  have hcond : factor.val.size ≤ 2 ∧ factor.coeff 1 ≠ 0 := h.1
  rw [if_pos]
  · congr
    change -(factor.coeff 0) / factor.coeff 1 = a
    apply (div_eq_iff hcond.2).2
    rw [neg_eq_iff_add_eq_zero]
    rw [_root_.mul_comm a (factor.coeff 1)]
    exact h.2
  · simp [hcond]
    intro hbad
    exact hcond.2 (by simpa [CPolynomial.coeff, CPolynomial.Raw.coeff] using hbad)

private theorem mem_rootsFromLinearFactors_of_candidate {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} {factors : Array (CPolynomial F)} {factor : CPolynomial F} {a : F}
    (hmem : factor ∈ factors.toList) (hcand : IsLinearRootFactorCandidate factor a)
    (hroot : CPolynomial.eval a p = 0) :
    a ∈ (CPolynomial.rootsFromLinearFactors p factors).toList := by
  rw [CPolynomial.rootsFromLinearFactors]
  have hvalid : a ∈ CPolynomial.validateRootCandidates p
      (List.filterMap CPolynomial.linearRootOfFactor? factors.toList).toArray := by
    rw [CPolynomial.validateRootCandidates]
    simp [hroot, CPolynomial.eval_horner_eq_eval]
    exact ⟨factor, by simpa using hmem, linearRootOfFactor?_eq_some_of_candidate hcand⟩
  have herase := mem_eraseDups_of_mem hvalid
  simpa using herase

private theorem raw_eval_mulMod_naive_eq_mul {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {modulus p q : CPolynomial.Raw F} {a : F}
    (hmod : modulus.eval a = 0) :
    (CPolynomial.Raw.mulModWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.naive modulus p q).eval a =
      p.eval a * q.eval a := by
  unfold CPolynomial.Raw.mulModWith CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive
  by_cases hzero : modulus.trim = (#[] : CPolynomial.Raw F)
  · simp [hzero, CPolynomial.Raw.eval_mul]
  · simp [hzero]
    have hroot : (CPolynomial.Raw.monicNormalize modulus).eval a = 0 :=
      CPolynomial.Raw.eval_monicNormalize_eq_zero_of_eval_eq_zero hmod
    have hmodBy := CPolynomial.Raw.eval_modByMonic_eq_self_of_eval_eq_zero
      (p * q) (CPolynomial.Raw.monicNormalize modulus) hroot
    rw [hmodBy, CPolynomial.Raw.eval_mul]

private theorem raw_eval_powModBinaryAux_naive {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {modulus acc current : CPolynomial.Raw F} {a : F}
    (hmod : modulus.eval a = 0) :
    ∀ n,
      (CPolynomial.Raw.powModBinaryAuxWith CPolynomial.Raw.MulContext.naive
        CPolynomial.Raw.ModContext.naive modulus n acc current).eval a =
      acc.eval a * current.eval a ^ n := by
  intro n
  induction n using Nat.strongRecOn generalizing acc current with
  | ind n ih =>
      cases n with
      | zero =>
          simp [CPolynomial.Raw.powModBinaryAuxWith]
      | succ n =>
          rw [CPolynomial.Raw.powModBinaryAuxWith]
          have ih' := ih ((n + 1) / 2)
            (Nat.div_lt_self (Nat.succ_pos n) (by decide))
            (acc :=
              if (n + 1) % 2 == 1 then
                CPolynomial.Raw.mulModWith CPolynomial.Raw.MulContext.naive
                  CPolynomial.Raw.ModContext.naive modulus acc current
              else
                acc)
            (current :=
              CPolynomial.Raw.mulModWith CPolynomial.Raw.MulContext.naive
                CPolynomial.Raw.ModContext.naive modulus current current)
          rw [ih']
          rw [raw_eval_mulMod_naive_eq_mul hmod]
          by_cases hodd : (n + 1) % 2 == 1
          · simp [hodd, raw_eval_mulMod_naive_eq_mul hmod]
            have hoddNat : (n + 1) % 2 = 1 := by
              simpa using hodd
            have hpow :
                (Raw.eval a current * Raw.eval a current) ^ ((n + 1) / 2) =
                  Raw.eval a current ^ n := by
              rw [mul_pow, ← pow_add]
              congr 1
              omega
            simp [hpow, pow_succ]
            ring
          · simp [hodd]
            have hoddNat : (n + 1) % 2 = 0 := by
              simpa using hodd
            have hpow :
                (Raw.eval a current * Raw.eval a current) ^ ((n + 1) / 2) =
                  Raw.eval a current ^ (n + 1) := by
              rw [mul_pow, ← pow_add]
              congr 1
              omega
            simp [hpow]

private theorem raw_eval_one {F : Type*} [Field F] (a : F) :
    (1 : CPolynomial.Raw F).eval a = 1 := by
  rw [← CPolynomial.Raw.eval_toPoly_eq_eval]
  simp

private theorem raw_eval_X {F : Type*} [Field F] (a : F) :
    (CPolynomial.Raw.X : CPolynomial.Raw F).eval a = a := by
  rw [← CPolynomial.Raw.eval_toPoly_eq_eval]
  simp [CPolynomial.Raw.toPoly_X]

private theorem raw_eval_powMod_naive_X {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {modulus : CPolynomial.Raw F} {a : F} (hmod : modulus.eval a = 0) (q : Nat) :
    (CPolynomial.Raw.powModWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.naive modulus CPolynomial.Raw.X q).eval a =
      a ^ q := by
  unfold CPolynomial.Raw.powModWith
  by_cases hzero : modulus.trim = (#[] : CPolynomial.Raw F)
  · simp [hzero]
    rw [raw_eval_powModBinaryAux_naive hmod, raw_eval_one, raw_eval_X]
    simp
  · simp [hzero]
    have hroot : (CPolynomial.Raw.monicNormalize modulus).eval a = 0 :=
      CPolynomial.Raw.eval_monicNormalize_eq_zero_of_eval_eq_zero hmod
    have hmodBy := CPolynomial.Raw.eval_modByMonic_eq_self_of_eval_eq_zero
      (1 : CPolynomial.Raw F) (CPolynomial.Raw.monicNormalize modulus) hroot
    rw [raw_eval_powModBinaryAux_naive hmod]
    simp [CPolynomial.Raw.ModContext.naive, hmodBy, raw_eval_one, raw_eval_X]

private theorem raw_eval_xMod_naive {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {modulus : CPolynomial.Raw F} {a : F} (hmod : modulus.eval a = 0) :
    (CPolynomial.Raw.xModWith CPolynomial.Raw.ModContext.naive modulus).eval a = a := by
  unfold CPolynomial.Raw.xModWith CPolynomial.Raw.ModContext.naive
  by_cases hzero : modulus.trim = (#[] : CPolynomial.Raw F)
  · simp [hzero, raw_eval_X]
  · simp [hzero]
    have hroot : (CPolynomial.Raw.monicNormalize modulus).eval a = 0 :=
      CPolynomial.Raw.eval_monicNormalize_eq_zero_of_eval_eq_zero hmod
    have hmodBy := CPolynomial.Raw.eval_modByMonic_eq_self_of_eval_eq_zero
      (CPolynomial.Raw.X : CPolynomial.Raw F) (CPolynomial.Raw.monicNormalize modulus) hroot
    rw [hmodBy, raw_eval_X]

private theorem raw_eval_sub {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (a : F) (p q : CPolynomial.Raw F) :
    (p - q).eval a = p.eval a - q.eval a := by
  rw [← CPolynomial.Raw.eval_toPoly_eq_eval, CPolynomial.Raw.toPoly_sub,
    Polynomial.eval_sub, CPolynomial.Raw.eval_toPoly_eq_eval,
    CPolynomial.Raw.eval_toPoly_eq_eval]

private theorem raw_eval_xPowSubXMod_naive {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : OddFiniteFieldContext F) {modulus : CPolynomial.Raw F} {a : F}
    (hmod : modulus.eval a = 0) :
    (CPolynomial.Raw.xPowSubXModWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.naive ctx.q modulus).eval a = 0 := by
  unfold CPolynomial.Raw.xPowSubXModWith
  rw [raw_eval_sub, raw_eval_powMod_naive_X hmod, raw_eval_xMod_naive hmod,
    ctx.frobenius_fixed a]
  simp

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

private theorem raw_eval_mulModWith_eq_mul {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {modulus p q : CPolynomial.Raw F} {a : F}
    (hmod : modulus.eval a = 0) :
    (CPolynomial.Raw.mulModWith M D modulus p q).eval a =
      p.eval a * q.eval a := by
  unfold CPolynomial.Raw.mulModWith
  by_cases hzero : modulus.trim = (#[] : CPolynomial.Raw F)
  · simp [hzero, M.mul_eq_mul, CPolynomial.Raw.eval_mul]
  · simp [hzero]
    have hproductTrim : (M.mul p q).trim = M.mul p q := by
      rw [M.mul_eq_mul]
      exact CPolynomial.Raw.mul_is_trimmed p q
    rw [D.modByMonic_eq_modByMonic _ _ hproductTrim (raw_monicNormalize_trim modulus)]
    have hroot : (CPolynomial.Raw.monicNormalize modulus).eval a = 0 :=
      CPolynomial.Raw.eval_monicNormalize_eq_zero_of_eval_eq_zero hmod
    have hmodBy := CPolynomial.Raw.eval_modByMonic_eq_self_of_eval_eq_zero
      (M.mul p q) (CPolynomial.Raw.monicNormalize modulus) hroot
    rw [hmodBy, M.mul_eq_mul, CPolynomial.Raw.eval_mul]

private theorem raw_eval_powModBinaryAuxWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {modulus acc current : CPolynomial.Raw F} {a : F}
    (hmod : modulus.eval a = 0) :
    ∀ n,
      (CPolynomial.Raw.powModBinaryAuxWith M D modulus n acc current).eval a =
      acc.eval a * current.eval a ^ n := by
  intro n
  induction n using Nat.strongRecOn generalizing acc current with
  | ind n ih =>
      cases n with
      | zero =>
          simp [CPolynomial.Raw.powModBinaryAuxWith]
      | succ n =>
          rw [CPolynomial.Raw.powModBinaryAuxWith]
          have ih' := ih ((n + 1) / 2)
            (Nat.div_lt_self (Nat.succ_pos n) (by decide))
            (acc :=
              if (n + 1) % 2 == 1 then
                CPolynomial.Raw.mulModWith M D modulus acc current
              else
                acc)
            (current := CPolynomial.Raw.mulModWith M D modulus current current)
          rw [ih']
          rw [raw_eval_mulModWith_eq_mul M D hmod]
          by_cases hodd : (n + 1) % 2 == 1
          · simp [hodd, raw_eval_mulModWith_eq_mul M D hmod]
            have hoddNat : (n + 1) % 2 = 1 := by
              simpa using hodd
            have hpow :
                (Raw.eval a current * Raw.eval a current) ^ ((n + 1) / 2) =
                  Raw.eval a current ^ n := by
              rw [mul_pow, ← pow_add]
              congr 1
              omega
            simp [hpow, pow_succ]
            ring
          · simp [hodd]
            have hoddNat : (n + 1) % 2 = 0 := by
              simpa using hodd
            have hpow :
                (Raw.eval a current * Raw.eval a current) ^ ((n + 1) / 2) =
                  Raw.eval a current ^ (n + 1) := by
              rw [mul_pow, ← pow_add]
              congr 1
              omega
            simp [hpow]

private theorem raw_eval_powModWith_X {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {modulus : CPolynomial.Raw F} {a : F} (hmod : modulus.eval a = 0) (q : Nat) :
    (CPolynomial.Raw.powModWith M D modulus CPolynomial.Raw.X q).eval a =
      a ^ q := by
  unfold CPolynomial.Raw.powModWith
  by_cases hzero : modulus.trim = (#[] : CPolynomial.Raw F)
  · simp [hzero]
    rw [raw_eval_powModBinaryAuxWith M D hmod, raw_eval_one, raw_eval_X]
    simp
  · simp [hzero]
    have hroot : (CPolynomial.Raw.monicNormalize modulus).eval a = 0 :=
      CPolynomial.Raw.eval_monicNormalize_eq_zero_of_eval_eq_zero hmod
    have hmodBy := CPolynomial.Raw.eval_modByMonic_eq_self_of_eval_eq_zero
      (1 : CPolynomial.Raw F) (CPolynomial.Raw.monicNormalize modulus) hroot
    rw [raw_eval_powModBinaryAuxWith M D hmod]
    have hOneTrim : (1 : CPolynomial.Raw F).trim = 1 := by
      change CPolynomial.Raw.trim (#[] |>.push (1 : F)) = (#[] |>.push (1 : F))
      apply CPolynomial.Raw.Trim.push_trim
      simp
    rw [D.modByMonic_eq_modByMonic _ _ hOneTrim (raw_monicNormalize_trim modulus)]
    rw [hmodBy, raw_eval_one, raw_eval_X]
    simp

private theorem raw_eval_xModWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (D : CPolynomial.Raw.ModContext F)
    {modulus : CPolynomial.Raw F} {a : F} (hmod : modulus.eval a = 0) :
    (CPolynomial.Raw.xModWith D modulus).eval a = a := by
  unfold CPolynomial.Raw.xModWith
  by_cases hzero : modulus.trim = (#[] : CPolynomial.Raw F)
  · simp [hzero, raw_eval_X]
  · simp [hzero]
    have hroot : (CPolynomial.Raw.monicNormalize modulus).eval a = 0 :=
      CPolynomial.Raw.eval_monicNormalize_eq_zero_of_eval_eq_zero hmod
    have hmodBy := CPolynomial.Raw.eval_modByMonic_eq_self_of_eval_eq_zero
      (CPolynomial.Raw.X : CPolynomial.Raw F) (CPolynomial.Raw.monicNormalize modulus) hroot
    have hXTrim : (CPolynomial.Raw.X : CPolynomial.Raw F).trim = CPolynomial.Raw.X := by
      exact CPolynomial.Raw.X_canonical
    rw [D.modByMonic_eq_modByMonic _ _ hXTrim (raw_monicNormalize_trim modulus)]
    rw [hmodBy, raw_eval_X]

private theorem raw_eval_xPowSubXModWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : OddFiniteFieldContext F) {modulus : CPolynomial.Raw F} {a : F}
    (hmod : modulus.eval a = 0) :
    (CPolynomial.Raw.xPowSubXModWith M D ctx.q modulus).eval a = 0 := by
  unfold CPolynomial.Raw.xPowSubXModWith
  rw [raw_eval_sub, raw_eval_powModWith_X M D hmod, raw_eval_xModWith D hmod,
    ctx.frobenius_fixed a]
  simp

/-- Every root of `p` is a root of the finite-field root product. -/
theorem finiteFieldRootProductWith_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : OddFiniteFieldContext F) {p : CPolynomial F} {a : F}
    (hp : p ≠ 0) (hroot : CPolynomial.eval a p = 0) :
    CPolynomial.eval a (finiteFieldRootProductWith M D ctx p) = 0 := by
  unfold finiteFieldRootProductWith
  change
    CPolynomial.Raw.eval a
        (CPolynomial.Raw.Roots.FiniteField.finiteFieldRootProductWith M D
          ctx p.val).trim =
      0
  rw [CPolynomial.Raw.eval_trim_eq_eval]
  unfold CPolynomial.Raw.Roots.FiniteField.finiteFieldRootProductWith
  by_cases hpempty : p.val = (#[] : CPolynomial.Raw F)
  · have hp0 : p = 0 := by
      apply CPolynomial.ext
      simpa using hpempty
    exact (hp hp0).elim
  · simp [hpempty, CPolynomial.trim_eq]
    have hmonicRoot : (CPolynomial.Raw.monicNormalize p.val).eval a = 0 :=
      CPolynomial.Raw.eval_monicNormalize_eq_zero_of_eval_eq_zero hroot
    unfold CPolynomial.Raw.gcdMonic
    exact Raw.eval_gcdMonicWithFuel_eq_zero_of_left_right
      _ (CPolynomial.Raw.monicNormalize p.val)
      (CPolynomial.Raw.xPowSubXModWith M D ctx.q (CPolynomial.Raw.monicNormalize p.val))
      hmonicRoot (raw_eval_xPowSubXModWith M D ctx hmonicRoot)

/-- Every root of `p` is a root of the finite-field root product. -/
theorem finiteFieldRootProduct_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : OddFiniteFieldContext F) {p : CPolynomial F} {a : F}
    (hp : p ≠ 0) (hroot : CPolynomial.eval a p = 0) :
    CPolynomial.eval a (finiteFieldRootProduct ctx p) = 0 := by
  unfold finiteFieldRootProduct finiteFieldRootProductWith
  change
    CPolynomial.Raw.eval a
        (CPolynomial.Raw.Roots.FiniteField.finiteFieldRootProductWith
          CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
          ctx p.val).trim =
      0
  rw [CPolynomial.Raw.eval_trim_eq_eval]
  unfold CPolynomial.Raw.Roots.FiniteField.finiteFieldRootProductWith
  by_cases hpempty : p.val = (#[] : CPolynomial.Raw F)
  · have hp0 : p = 0 := by
      apply CPolynomial.ext
      simpa using hpempty
    exact (hp hp0).elim
  · simp [hpempty, CPolynomial.trim_eq]
    have hmonicRoot : (CPolynomial.Raw.monicNormalize p.val).eval a = 0 :=
      CPolynomial.Raw.eval_monicNormalize_eq_zero_of_eval_eq_zero hroot
    unfold CPolynomial.Raw.gcdMonic
    exact Raw.eval_gcdMonicWithFuel_eq_zero_of_left_right
      _ (CPolynomial.Raw.monicNormalize p.val)
      (CPolynomial.Raw.xPowSubXModWith CPolynomial.Raw.MulContext.naive
        CPolynomial.Raw.ModContext.naive ctx.q (CPolynomial.Raw.monicNormalize p.val))
      hmonicRoot (raw_eval_xPowSubXMod_naive ctx hmonicRoot)

private theorem raw_monicNormalize_ne_zero {F : Type*} [Field F] [BEq F] [LawfulBEq F]
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

private theorem raw_gcdMonicWithFuel_trim_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] :
    ∀ fuel (p q : CPolynomial.Raw F), p.trim ≠ (0 : CPolynomial.Raw F) →
      (CPolynomial.Raw.gcdMonicWithFuel fuel p q).trim ≠ 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro p q hp
      unfold CPolynomial.Raw.gcdMonicWithFuel
      rw [raw_monicNormalize_trim]
      exact raw_monicNormalize_ne_zero hp
  | succ fuel ih =>
      intro p q hp
      rw [CPolynomial.Raw.gcdMonicWithFuel]
      by_cases hqzero : q.trim == (0 : CPolynomial.Raw F)
      · have hqzeroEq : q.trim = (0 : CPolynomial.Raw F) := by
          simpa using hqzero
        rw [if_pos hqzero]
        rw [raw_monicNormalize_trim]
        apply raw_monicNormalize_ne_zero
        simpa [CPolynomial.Raw.Trim.trim_twice] using hp
      · have hqzeroNe : ¬q.trim = (0 : CPolynomial.Raw F) := by
          intro hqtrim0
          exact hqzero (by simp [hqtrim0])
        rw [if_neg hqzero]
        apply ih
        intro hqtrim0
        rw [CPolynomial.Raw.Trim.trim_twice q] at hqtrim0
        exact hqzeroNe hqtrim0

private theorem finiteFieldRootProductWith_ne_zero {F : Type*}
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
    exact raw_gcdMonicWithFuel_trim_ne_zero _ (CPolynomial.Raw.monicNormalize p.val)
      (CPolynomial.Raw.xPowSubXModWith M D ctx.q (CPolynomial.Raw.monicNormalize p.val))
      (by
        rw [raw_monicNormalize_trim]
        exact raw_monicNormalize_ne_zero hpraw) hval

/-- Every validated root extracted from the root product is a root of `p`. -/
theorem finiteFieldRootProduct_validated_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (_ctx : OddFiniteFieldContext F) {p : CPolynomial F}
    {candidates : Array F} {a : F}
    (h : a ∈ (CPolynomial.validateRootCandidates p candidates).toList) :
    CPolynomial.eval a p = 0 := by
  exact CPolynomial.mem_validateRootCandidates_eval_eq_zero h

/-- Returned finite-field roots are roots of the original polynomial. -/
theorem rootsInOddFiniteFieldWith_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : OddFiniteFieldContext F) (splitter : LinearFactorProductSplitter F)
    {p : CPolynomial F} {a : F}
    (h : a ∈ (rootsInOddFiniteFieldWith M D ctx splitter p).toList) :
    CPolynomial.eval a p = 0 := by
  rw [rootsInOddFiniteFieldWith] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · exact mem_rootsFromLinearFactors_eval_eq_zero h
      · exact mem_rootsFromLinearFactors_eval_eq_zero h

/-- Returned finite-field roots are roots of the original polynomial. -/
theorem rootsInOddFiniteField_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : OddFiniteFieldContext F) (splitter : LinearFactorProductSplitter F)
    {p : CPolynomial F} {a : F}
    (h : a ∈ (rootsInOddFiniteField ctx splitter p).toList) :
    CPolynomial.eval a p = 0 := by
  exact rootsInOddFiniteFieldWith_sound
    (M := CPolynomial.Raw.MulContext.naive) (D := CPolynomial.Raw.ModContext.naive)
    ctx splitter h

private theorem eq_zero_of_size_le_one_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} {a : F}
    (hsize : p.val.size ≤ 1) (hroot : CPolynomial.eval a p = 0) :
    p = 0 := by
  rcases p with ⟨⟨xs⟩, hcanon⟩
  cases xs with
  | nil =>
      rfl
  | cons x xs =>
      cases xs with
      | nil =>
          simp [CPolynomial.eval] at hroot
          have hxne := hcanon (by simp)
          simp [Array.getLast] at hxne
          exact (hxne hroot).elim
      | cons _ _ =>
          simp at hsize

private theorem linear_candidate_self_of_size_two_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} {a : F}
    (hsize : p.val.size = 2) (hcoeff : p.coeff 1 ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    IsLinearRootFactorCandidate p a := by
  rcases p with ⟨⟨xs⟩, hcanon⟩
  cases xs with
  | nil =>
      simp at hsize
  | cons x xs =>
      cases xs with
      | nil =>
          simp at hsize
      | cons y xs =>
          cases xs with
          | nil =>
              simp [IsLinearRootFactorCandidate, IsLinearFactor, CPolynomial.eval,
                CPolynomial.coeff, CPolynomial.Raw.coeff] at hroot hcoeff ⊢
              exact ⟨hcoeff, hroot⟩
          | cons _ _ =>
              simp at hsize

/-- Every root of a nonzero polynomial is returned by the finite-field backend. -/
theorem rootsInOddFiniteFieldWith_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : OddFiniteFieldContext F) (splitter : LinearFactorProductSplitter F)
    (splitterValid :
      ∀ {p : CPolynomial F}, p ≠ 0 →
        splitter.validInput ctx.q (finiteFieldRootProductWith M D ctx p))
    {p : CPolynomial F} {a : F}
    (hp : p ≠ 0) (hroot : CPolynomial.eval a p = 0) :
    a ∈ (rootsInOddFiniteFieldWith M D ctx splitter p).toList := by
  rw [rootsInOddFiniteFieldWith]
  split
  · rename_i hzero
    have hp0 : p = 0 := by
      simpa using hzero
    exact (hp hp0).elim
  · split
    · rename_i _ hsmall
      exact (hp (eq_zero_of_size_le_one_root hsmall hroot)).elim
    · split
      · rename_i _ _ hlinear
        simp at hlinear
        have hcoeff : p.coeff 1 ≠ 0 := by
          simpa [CPolynomial.coeff, CPolynomial.Raw.coeff] using hlinear.2
        exact mem_rootsFromLinearFactors_of_candidate (p := p) (factors := #[p])
          (factor := p) (by simp)
          (linear_candidate_self_of_size_two_root hlinear.1 hcoeff hroot) hroot
      · have hprodRoot : CPolynomial.eval a (finiteFieldRootProductWith M D ctx p) = 0 :=
          finiteFieldRootProductWith_complete M D ctx hp hroot
        have hprodNe : finiteFieldRootProductWith M D ctx p ≠ 0 :=
          finiteFieldRootProductWith_ne_zero M D ctx hp
        have hprodValid :
            splitter.validInput ctx.q (finiteFieldRootProductWith M D ctx p) := by
          exact splitterValid hp
        rcases splitter.complete ctx.q (finiteFieldRootProductWith M D ctx p) a
            hprodValid hprodNe hprodRoot with
          ⟨factor, hmem, hcand⟩
        exact mem_rootsFromLinearFactors_of_candidate (p := p)
          (factors := splitter.splitLinearFactors ctx.q (finiteFieldRootProductWith M D ctx p))
          (factor := factor) hmem hcand hroot

/-- Every root of a nonzero polynomial is returned by the finite-field backend. -/
theorem rootsInOddFiniteField_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : OddFiniteFieldContext F) (splitter : LinearFactorProductSplitter F)
    (splitterValid :
      ∀ {p : CPolynomial F}, p ≠ 0 →
        splitter.validInput ctx.q (finiteFieldRootProduct ctx p))
    {p : CPolynomial F} {a : F}
    (hp : p ≠ 0) (hroot : CPolynomial.eval a p = 0) :
    a ∈ (rootsInOddFiniteField ctx splitter p).toList := by
  exact rootsInOddFiniteFieldWith_complete
    (M := CPolynomial.Raw.MulContext.naive) (D := CPolynomial.Raw.ModContext.naive)
    ctx splitter (by
      intro p hp
      exact splitterValid hp) hp hroot

/-- The complete executable finite-field root pipeline is sound and complete
for nonzero inputs under the odd finite-field and splitter contracts. -/
theorem rootsInOddFiniteField_spec {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : OddFiniteFieldContext F) (splitter : LinearFactorProductSplitter F)
    (splitterValid :
      ∀ {p : CPolynomial F}, p ≠ 0 →
        splitter.validInput ctx.q (finiteFieldRootProduct ctx p))
    {p : CPolynomial F} {a : F} (hp : p ≠ 0) :
    a ∈ (rootsInOddFiniteField ctx splitter p).toList ↔
      CPolynomial.eval a p = 0 := by
  constructor
  · intro h
    exact rootsInOddFiniteField_sound ctx splitter h
  · intro h
    exact rootsInOddFiniteField_complete ctx splitter splitterValid hp h

end FiniteField

end Roots

end CPolynomial

end CompPoly
