/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.Correctness
import CompPoly.Univariate.Roots.Shoup.Basic
import CompPoly.Univariate.Roots.Shoup.FrobeniusLinear
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Correctness Surface for Shoup-Style Trace Splitting

This file states the proof obligations for the executable Shoup trace splitter.
The main completeness contract is intentionally limited to valid root products:
nonzero divisors of `X^q - X`, as produced by the finite-field root-product
construction.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Evaluation of a Shoup modular power at a root of the modulus. -/
theorem eval_shoupModularXPowerWith_eq_pow {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {modulus : CPolynomial F} {a : F}
    (hroot : CPolynomial.eval a modulus = 0) (i : Nat) :
    CPolynomial.eval a (xPowModWith M D modulus (ctx.p ^ i)) = a ^ (ctx.p ^ i) := by
  exact eval_xPowModWith_eq_pow M D hroot (ctx.p ^ i)

/-- Trace-coordinate polynomial evaluation at a root of the modulus. -/
theorem eval_traceCoordinatePolynomialWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {modulus : CPolynomial F} {a beta : F}
    (hroot : CPolynomial.eval a modulus = 0) :
    CPolynomial.eval a (traceCoordinatePolynomialWith M D ctx modulus beta) =
      ctx.traceValue (beta * a) := by
  have evalAdd :
      ∀ p q : CPolynomial F,
        CPolynomial.eval a (p + q) = CPolynomial.eval a p + CPolynomial.eval a q := by
    intro p q
    rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_add, Polynomial.eval_add,
      ← CPolynomial.eval_toPoly, ← CPolynomial.eval_toPoly]
  have evalZero : CPolynomial.eval a (0 : CPolynomial F) = 0 := by
    rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_zero, Polynomial.eval_zero]
  rw [ctx.traceValue_eq_powerSum]
  unfold traceCoordinatePolynomialWith tracePowerSum
  have hgo : ∀ (xs : List Nat) (acc : CPolynomial F) (accVal : F),
      CPolynomial.eval a acc = accVal →
        CPolynomial.eval a
            (xs.foldl
              (fun acc i ↦
                acc + CPolynomial.C (beta ^ (ctx.p ^ i)) *
                  xPowModWith M D modulus (ctx.p ^ i))
              acc) =
          xs.foldl (fun acc i ↦ acc + (beta * a) ^ (ctx.p ^ i)) accVal := by
    intro xs
    induction xs with
    | nil =>
        intro acc accVal hacc
        simpa using hacc
    | cons i is ih =>
        intro acc accVal hacc
        simp only [List.foldl_cons]
        apply ih
        rw [evalAdd, CPolynomial.eval_mul, CPolynomial.eval_C,
          eval_xPowModWith_eq_pow M D hroot, hacc]
        rw [mul_pow]
  exact hgo (List.range ctx.k) 0 0 evalZero

/-- A Shoup trace context has the advertised base characteristic. -/
private theorem smallPrimeTraceContext_charP {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (ctx : SmallPrimeTraceContext F) :
    CharP F ctx.p := by
  letI : Finite F := ctx.finite
  letI : Fintype F := Fintype.ofFinite F
  letI : Fact ctx.p.Prime := ⟨ctx.p_prime⟩
  have hcard : Fintype.card F = ctx.p ^ ctx.k := by
    rw [← Nat.card_eq_fintype_card, ctx.card_eq, ctx.q_eq]
  exact charP_of_card_eq_prime_pow hcard

/-- The trace power-sum is additive for subtraction. -/
theorem traceValue_sub {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : SmallPrimeTraceContext F) (x y : F) :
    ctx.traceValue (x - y) = ctx.traceValue x - ctx.traceValue y := by
  letI : CharP F ctx.p := smallPrimeTraceContext_charP ctx
  letI : ExpChar F ctx.p := ExpChar.prime ctx.p_prime
  rw [ctx.traceValue_eq_powerSum, ctx.traceValue_eq_powerSum, ctx.traceValue_eq_powerSum]
  unfold tracePowerSum
  have hgo : ∀ (xs : List Nat) (accx accy : F),
      xs.foldl (fun acc i ↦ acc + (x - y) ^ (ctx.p ^ i)) (accx - accy) =
        xs.foldl (fun acc i ↦ acc + x ^ (ctx.p ^ i)) accx -
          xs.foldl (fun acc i ↦ acc + y ^ (ctx.p ^ i)) accy := by
    intro xs
    induction xs with
    | nil =>
        intro accx accy
        simp
    | cons i is ih =>
        intro accx accy
        simp only [List.foldl_cons]
        have hstep : accx - accy + (x - y) ^ (ctx.p ^ i) =
            (accx + x ^ (ctx.p ^ i)) - (accy + y ^ (ctx.p ^ i)) := by
          rw [sub_pow_expChar_pow]
          ring
        rw [hstep]
        exact ih (accx + x ^ (ctx.p ^ i)) (accy + y ^ (ctx.p ^ i))
  simpa using hgo (List.range ctx.k) 0 0

/-- Trace coordinates convert equal bucket values into zero trace on differences. -/
theorem traceValue_mul_sub_eq_zero_of_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : SmallPrimeTraceContext F) {beta a b : F}
    (htrace : ctx.traceValue (beta * a) = ctx.traceValue (beta * b)) :
    ctx.traceValue (beta * (a - b)) = 0 := by
  rw [mul_sub, traceValue_sub ctx, htrace, sub_self]

/-- Matching every trace coordinate in the separating basis forces equality. -/
theorem eq_of_traceValue_eq_on_basis {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : SmallPrimeTraceContext F) {a b : F}
    (htrace : ∀ beta, beta ∈ ctx.basis.toList →
      ctx.traceValue (beta * a) = ctx.traceValue (beta * b)) :
    a = b := by
  by_contra hne
  rcases ctx.trace_separates hne with ⟨beta, hbeta, hsep⟩
  exact hsep (traceValue_mul_sub_eq_zero_of_eq ctx (htrace beta hbeta))

/-- The trace-coordinate gcd bucket preserves roots whose trace coordinate matches the bucket. -/
theorem shoup_gcdBucket_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {u : CPolynomial F} {a beta c : F}
    (hroot : CPolynomial.eval a u = 0)
    (htrace : ctx.traceValue (beta * a) = c) :
    CPolynomial.eval a
        (CPolynomial.monicNormalize
          (CPolynomial.gcdMonic u
            (traceCoordinatePolynomialWith M D ctx u beta - CPolynomial.C c))) = 0 := by
  let witness := traceCoordinatePolynomialWith M D ctx u beta - CPolynomial.C c
  have hwitnessRoot : CPolynomial.eval a witness = 0 := by
    dsimp [witness]
    rw [CPolynomial.eval_sub, eval_traceCoordinatePolynomialWith M D ctx hroot,
      CPolynomial.eval_C, htrace]
    ring
  exact monicNormalize_root_of_root (gcdMonic_root_of_left_right hroot hwitnessRoot)

/-- Roots of a trace-coordinate gcd bucket are roots of the parent in that bucket. -/
theorem shoup_gcdBucket_root_iff {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {u : CPolynomial F} {a beta c : F}
    (hu : u ≠ 0) :
    CPolynomial.eval a
        (CPolynomial.monicNormalize
          (CPolynomial.gcdMonic u
            (traceCoordinatePolynomialWith M D ctx u beta - CPolynomial.C c))) = 0 ↔
      CPolynomial.eval a u = 0 ∧ ctx.traceValue (beta * a) = c := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  let witness := traceCoordinatePolynomialWith M D ctx u beta - CPolynomial.C c
  have hgcdNe : CPolynomial.gcdMonic u witness ≠ 0 := gcdMonic_ne_zero_of_left hu
  rw [monicNormalize_root_iff hgcdNe, gcdMonic_root_iff_left_right]
  constructor
  · intro h
    rcases h with ⟨hroot, hwitness⟩
    refine ⟨hroot, ?_⟩
    dsimp [witness] at hwitness
    rw [CPolynomial.eval_sub, eval_traceCoordinatePolynomialWith M D ctx hroot,
      CPolynomial.eval_C] at hwitness
    exact sub_eq_zero.mp hwitness
  · intro h
    rcases h with ⟨hroot, htrace⟩
    refine ⟨hroot, ?_⟩
    dsimp [witness]
    rw [CPolynomial.eval_sub, eval_traceCoordinatePolynomialWith M D ctx hroot,
      CPolynomial.eval_C, htrace]
    ring

private theorem monicNormalize_toPoly_dvd_self {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (p : CPolynomial F) :
    (CPolynomial.monicNormalize p).toPoly ∣ p.toPoly := by
  rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
  exact (normalize_associated p.toPoly).dvd

private theorem gcdMonic_toPoly_dvd_left {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (p q : CPolynomial F) :
    (CPolynomial.gcdMonic p q).toPoly ∣ p.toPoly := by
  rw [CPolynomial.gcdMonic_toPoly_eq_normalize_gcd]
  exact (normalize_associated (EuclideanDomain.gcd p.toPoly q.toPoly)).dvd.trans
    (EuclideanDomain.gcd_dvd_left p.toPoly q.toPoly)

private theorem pushNontrivialChild_mem_of_ne_zero_ne_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {children : Array (CPolynomial F)} {child : CPolynomial F}
    (h0 : child ≠ 0) (h1 : child ≠ 1) :
    child ∈ (pushNontrivialChild children child).toList := by
  unfold pushNontrivialChild
  have hskip : ¬ (child == 0 || child == 1) = true := by
    intro h
    have hcases : child = 0 ∨ child = 1 := by
      simpa using h
    rcases hcases with hzero | hone
    · exact h0 hzero
    · exact h1 hone
  rw [if_neg hskip]
  simp

private theorem pushNontrivialChild_mem_of_mem {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {children : Array (CPolynomial F)} {child factor : CPolynomial F}
    (hmem : factor ∈ children.toList) :
    factor ∈ (pushNontrivialChild children child).toList := by
  unfold pushNontrivialChild
  by_cases hskip : (child == 0 || child == 1) = true
  · rw [if_pos hskip]
    exact hmem
  · rw [if_neg hskip]
    simp [hmem]

private theorem mem_pushNontrivialChild {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {children : Array (CPolynomial F)} {child factor : CPolynomial F}
    (hmem : factor ∈ (pushNontrivialChild children child).toList) :
    factor ∈ children.toList ∨ factor = child := by
  unfold pushNontrivialChild at hmem
  by_cases hskip : (child == 0 || child == 1) = true
  · rw [if_pos hskip] at hmem
    exact Or.inl hmem
  · rw [if_neg hskip] at hmem
    simp at hmem
    rcases hmem with hmem | hfactor
    · exact Or.inl (by simpa using hmem)
    · exact Or.inr hfactor

private theorem shoupRefineBaseConstants_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (beta : F) {u : CPolynomial F} {a : F}
    (hu : u ≠ 0) (hroot : CPolynomial.eval a u = 0) :
    ∀ (constants : List F) (acc : Array (CPolynomial F)),
      (∃ factor, factor ∈ acc.toList ∧ factor ≠ 0 ∧ CPolynomial.eval a factor = 0) ∨
        ctx.traceValue (beta * a) ∈ constants →
        ∃ factor,
          factor ∈
              (constants.foldl
                (fun children c ↦
                  let child := CPolynomial.monicNormalize
                    (CPolynomial.gcdMonic u
                      (traceCoordinatePolynomialWith M D ctx u beta - CPolynomial.C c))
                  pushNontrivialChild children child)
                acc).toList ∧
            factor ≠ 0 ∧
            CPolynomial.eval a factor = 0 := by
  intro constants
  induction constants with
  | nil =>
      intro acc h
      rcases h with hacc | hmem
      · exact hacc
      · simp at hmem
  | cons c cs ih =>
      intro acc h
      simp only [List.foldl_cons]
      apply ih
      rcases h with hacc | hmem
      · left
        rcases hacc with ⟨factor, hfactor, hfactorNe, hrootFactor⟩
        refine ⟨factor, pushNontrivialChild_mem_of_mem hfactor, hfactorNe, hrootFactor⟩
      · simp at hmem
        rcases hmem with htarget | htail
        · left
          subst c
          let child := CPolynomial.monicNormalize
            (CPolynomial.gcdMonic u
              (traceCoordinatePolynomialWith M D ctx u beta -
                CPolynomial.C (ctx.traceValue (beta * a))))
          have hchildRoot : CPolynomial.eval a child = 0 := by
            dsimp [child]
            exact shoup_gcdBucket_root M D ctx hroot rfl
          have hgcdNe : CPolynomial.gcdMonic u
              (traceCoordinatePolynomialWith M D ctx u beta -
                CPolynomial.C (ctx.traceValue (beta * a))) ≠ 0 :=
            gcdMonic_ne_zero_of_left hu
          have hchildNe : child ≠ 0 := monicNormalize_ne_zero_of_ne_zero hgcdNe
          have hchildNotOne : child ≠ 1 := by
            intro hone
            rw [hone] at hchildRoot
            rw [eval_one a] at hchildRoot
            exact (one_ne_zero hchildRoot).elim
          refine ⟨child, ?_, hchildNe, hchildRoot⟩
          exact pushNontrivialChild_mem_of_ne_zero_ne_one hchildNe hchildNotOne
        · right
          exact htail

private theorem shoupRefineBaseConstants_dvd {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (beta : F) {u : CPolynomial F} :
    ∀ (constants : List F) (acc : Array (CPolynomial F)),
      (∀ factor, factor ∈ acc.toList → factor.toPoly ∣ u.toPoly) →
        ∀ factor,
          factor ∈
              (constants.foldl
                (fun children c ↦
                  let child := CPolynomial.monicNormalize
                    (CPolynomial.gcdMonic u
                      (traceCoordinatePolynomialWith M D ctx u beta - CPolynomial.C c))
                  pushNontrivialChild children child)
                acc).toList →
            factor.toPoly ∣ u.toPoly := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  intro constants
  induction constants with
  | nil =>
      intro acc hacc factor hmem
      exact hacc factor hmem
  | cons c cs ih =>
      intro acc hacc factor hmem
      simp only [List.foldl_cons] at hmem
      apply ih (pushNontrivialChild acc
        (CPolynomial.monicNormalize
          (CPolynomial.gcdMonic u
            (traceCoordinatePolynomialWith M D ctx u beta - CPolynomial.C c))))
      · intro factor hfactor
        rcases mem_pushNontrivialChild hfactor with hold | hnew
        · exact hacc factor hold
        · subst factor
          exact (monicNormalize_toPoly_dvd_self
            (CPolynomial.gcdMonic u
              (traceCoordinatePolynomialWith M D ctx u beta - CPolynomial.C c))).trans
            (gcdMonic_toPoly_dvd_left u
              (traceCoordinatePolynomialWith M D ctx u beta - CPolynomial.C c))
      · exact hmem

private theorem shoupRefineFactorWith_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (beta : F) {u : CPolynomial F} {a : F}
    (hu : u ≠ 0) (hroot : CPolynomial.eval a u = 0) :
    ∃ factor,
      factor ∈ (shoupRefineFactorWith M D ctx beta u).toList ∧
        factor ≠ 0 ∧
        CPolynomial.eval a factor = 0 := by
  unfold shoupRefineFactorWith
  let u' := CPolynomial.monicNormalize u
  have hu' : u' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hu
  have hroot' : CPolynomial.eval a u' = 0 := (monicNormalize_root_iff hu).2 hroot
  by_cases hzero : (u' == 0 || u' == 1) = true
  · have hcases : u' = 0 ∨ u' = 1 := by
      simpa [u'] using hzero
    rcases hcases with h0 | h1
    · exact (hu' h0).elim
    · rw [h1] at hroot'
      rw [eval_one a] at hroot'
      exact (one_ne_zero hroot').elim
  · rw [if_neg hzero]
    by_cases hlin : isRepresentedLinearFactor u' = true
    · rw [if_pos hlin]
      refine ⟨u', ?_, hu', hroot'⟩
      simp [u']
    · rw [if_neg hlin]
      rw [← Array.foldl_toList]
      exact shoupRefineBaseConstants_root M D ctx beta hu' hroot'
        ctx.baseConstants.toList #[] (Or.inr (ctx.traceValue_mem_base (beta * a)))

private theorem shoupRefineFactorWith_dvd {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (beta : F) {u factor : CPolynomial F}
    (hmem : factor ∈ (shoupRefineFactorWith M D ctx beta u).toList) :
    factor.toPoly ∣ u.toPoly := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  unfold shoupRefineFactorWith at hmem
  let u' := CPolynomial.monicNormalize u
  by_cases hzero : (u' == 0 || u' == 1) = true
  · rw [if_pos hzero] at hmem
    simp at hmem
  · rw [if_neg hzero] at hmem
    by_cases hlin : isRepresentedLinearFactor u' = true
    · rw [if_pos hlin] at hmem
      simp at hmem
      subst factor
      exact monicNormalize_toPoly_dvd_self u
    · rw [if_neg hlin] at hmem
      rw [← Array.foldl_toList] at hmem
      have hdivU' : factor.toPoly ∣ u'.toPoly :=
        shoupRefineBaseConstants_dvd M D ctx beta ctx.baseConstants.toList #[]
          (by
            intro factor hfactor
            simp at hfactor)
          factor hmem
      exact hdivU'.trans (monicNormalize_toPoly_dvd_self u)

private theorem shoupRefineFactorsWith_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (beta : F)
    {factors : Array (CPolynomial F)} {a : F}
    (hroot :
      ∃ factor,
        factor ∈ factors.toList ∧ factor ≠ 0 ∧ CPolynomial.eval a factor = 0) :
    ∃ factor,
      factor ∈ (shoupRefineFactorsWith M D ctx beta factors).toList ∧
        factor ≠ 0 ∧
        CPolynomial.eval a factor = 0 := by
  unfold shoupRefineFactorsWith
  rcases factors with ⟨factorList⟩
  rw [← Array.foldl_toList]
  have hgo : ∀ (xs : List (CPolynomial F)) (acc : Array (CPolynomial F)),
      (∃ factor,
        factor ∈ acc.toList ∧ factor ≠ 0 ∧ CPolynomial.eval a factor = 0) ∨
        (∃ factor,
          factor ∈ xs ∧ factor ≠ 0 ∧ CPolynomial.eval a factor = 0) →
        ∃ factor,
          factor ∈
              (xs.foldl
                (fun out factor ↦ out ++ shoupRefineFactorWith M D ctx beta factor)
                acc).toList ∧
            factor ≠ 0 ∧
            CPolynomial.eval a factor = 0 := by
    intro xs
    induction xs with
    | nil =>
        intro acc h
        rcases h with hacc | htail
        · exact hacc
        · rcases htail with ⟨factor, hmem, _⟩
          simp at hmem
    | cons x xs ih =>
        intro acc h
        simp only [List.foldl_cons]
        apply ih
        rcases h with hacc | htail
        · left
          rcases hacc with ⟨factor, hmem, hne, hrootFactor⟩
          refine ⟨factor, ?_, hne, hrootFactor⟩
          simpa using Array.mem_append_left
            (shoupRefineFactorWith M D ctx beta x) (by simpa using hmem)
        · rcases htail with ⟨factor, hmem, hne, hrootFactor⟩
          simp at hmem
          rcases hmem with hhead | htail
          · subst factor
            left
            rcases shoupRefineFactorWith_root M D ctx beta hne hrootFactor with
              ⟨child, hchildMem, hchildNe, hchildRoot⟩
            refine ⟨child, ?_, hchildNe, hchildRoot⟩
            simpa using Array.mem_append_right acc (by simpa using hchildMem)
          · right
            exact ⟨factor, htail, hne, hrootFactor⟩
  exact hgo factorList #[] (Or.inr (by simpa using hroot))

private theorem shoupRefineFactorsWith_dvd {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (beta : F)
    {p factor : CPolynomial F} {factors : Array (CPolynomial F)}
    (hparents : ∀ parent, parent ∈ factors.toList → parent.toPoly ∣ p.toPoly)
    (hmem : factor ∈ (shoupRefineFactorsWith M D ctx beta factors).toList) :
    factor.toPoly ∣ p.toPoly := by
  unfold shoupRefineFactorsWith at hmem
  rcases factors with ⟨factorList⟩
  rw [← Array.foldl_toList] at hmem
  have hgo : ∀ (xs : List (CPolynomial F)) (out : Array (CPolynomial F)),
      (∀ child, child ∈ out.toList → child.toPoly ∣ p.toPoly) →
        (∀ parent, parent ∈ xs → parent.toPoly ∣ p.toPoly) →
          ∀ child,
            child ∈
                (xs.foldl
                  (fun out factor ↦ out ++ shoupRefineFactorWith M D ctx beta factor)
                  out).toList →
              child.toPoly ∣ p.toPoly := by
    intro xs
    induction xs with
    | nil =>
        intro out hout _ child hchild
        exact hout child hchild
    | cons x xs ih =>
        intro out hout hxs child hchild
        simp only [List.foldl_cons] at hchild
        apply ih (out ++ shoupRefineFactorWith M D ctx beta x)
        · intro child hmemChild
          simp at hmemChild
          rcases hmemChild with hleft | hright
          · exact hout child (by simpa using hleft)
          · exact (shoupRefineFactorWith_dvd M D ctx beta (by simpa using hright)).trans
              (hxs x (by simp))
        · intro parent hparent
          exact hxs parent (by simp [hparent])
        · exact hchild
  exact hgo factorList #[]
    (by
      intro child hchild
      simp at hchild)
    (by
      intro parent hparent
      exact hparents parent (by simpa using hparent))
    factor hmem

private theorem shoupRefineBasisWith_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) :
    ∀ (basis : List F) (factors : Array (CPolynomial F)) {a : F},
      (∃ factor,
        factor ∈ factors.toList ∧ factor ≠ 0 ∧ CPolynomial.eval a factor = 0) →
        ∃ factor,
          factor ∈
              (basis.foldl
                (fun factors beta ↦ shoupRefineFactorsWith M D ctx beta factors)
                factors).toList ∧
            factor ≠ 0 ∧
            CPolynomial.eval a factor = 0 := by
  intro basis
  induction basis with
  | nil =>
      intro factors a hroot
      exact hroot
  | cons beta rest ih =>
      intro factors a hroot
      simp only [List.foldl_cons]
      exact ih (shoupRefineFactorsWith M D ctx beta factors)
        (shoupRefineFactorsWith_root M D ctx beta hroot)

private theorem shoupRefineBasisWith_dvd {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {p : CPolynomial F} :
    ∀ (basis : List F) (factors : Array (CPolynomial F)) {factor : CPolynomial F},
      (∀ parent, parent ∈ factors.toList → parent.toPoly ∣ p.toPoly) →
        factor ∈
            (basis.foldl
              (fun factors beta ↦ shoupRefineFactorsWith M D ctx beta factors)
              factors).toList →
          factor.toPoly ∣ p.toPoly := by
  intro basis
  induction basis with
  | nil =>
      intro factors factor hparents hmem
      exact hparents factor hmem
  | cons beta rest ih =>
      intro factors factor hparents hmem
      simp only [List.foldl_cons] at hmem
      apply ih (shoupRefineFactorsWith M D ctx beta factors)
      · intro parent hparent
        exact shoupRefineFactorsWith_dvd M D ctx beta hparents hparent
      · exact hmem

private theorem representedLinearFactor_root_unique {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} {a b : F}
    (hlin : isRepresentedLinearFactor p = true)
    (ha : CPolynomial.eval a p = 0) (hb : CPolynomial.eval b p = 0) :
    b = a := by
  have ca := representedLinearFactor_candidate_of_root hlin ha
  have cb := representedLinearFactor_candidate_of_root hlin hb
  have haeq : p.coeff 1 * a = -p.coeff 0 := by
    have h := ca.2
    rw [add_eq_zero_iff_eq_neg] at h
    rw [h]
    simp
  have hbeq : p.coeff 1 * b = -p.coeff 0 := by
    have h := cb.2
    rw [add_eq_zero_iff_eq_neg] at h
    rw [h]
    simp
  have hsub : p.coeff 1 * (b - a) = 0 := by
    rw [mul_sub, hbeq, haeq, sub_self]
  have hbmina : b - a = 0 := (mul_eq_zero.mp hsub).resolve_left ca.1.2
  exact sub_eq_zero.mp hbmina

private theorem monicNormalize_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] :
    CPolynomial.monicNormalize (0 : CPolynomial F) = 0 := by
  unfold CPolynomial.monicNormalize CPolynomial.Raw.monicNormalize CPolynomial.ofArray
  apply Subtype.ext
  change
    (if ((0 : CPolynomial F).val : CPolynomial.Raw F).trim == 0 then
        (0 : CPolynomial.Raw F)
      else
        ((0 : CPolynomial F).val : CPolynomial.Raw F).trim.leadingCoeff⁻¹ •
          ((0 : CPolynomial F).val : CPolynomial.Raw F).trim).trim =
      (0 : CPolynomial.Raw F)
  rw [if_pos]
  · exact CPolynomial.Raw.zero_canonical
  · change (((0 : CPolynomial.Raw F).trim) == 0) = true
    rw [CPolynomial.Raw.zero_canonical]
    rfl

private def rootsAgreeOn {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (ctx : SmallPrimeTraceContext F) (coords : List F) (factor : CPolynomial F) :
    Prop :=
  ∀ a b : F, CPolynomial.eval a factor = 0 → CPolynomial.eval b factor = 0 →
    ∀ beta, beta ∈ coords →
      ctx.traceValue (beta * a) = ctx.traceValue (beta * b)

private theorem rootsAgreeOn_of_root_unique {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : SmallPrimeTraceContext F) (coords : List F) {factor : CPolynomial F}
    (hunique : ∀ {a b : F}, CPolynomial.eval a factor = 0 →
      CPolynomial.eval b factor = 0 → b = a) :
    rootsAgreeOn ctx coords factor := by
  intro a b hrootA hrootB beta _hbeta
  have hba : b = a := hunique hrootA hrootB
  subst b
  rfl

private theorem rootsAgreeOn_monicNormalize {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : SmallPrimeTraceContext F) (coords : List F) {u : CPolynomial F}
    (hu : u ≠ 0) (huAgree : rootsAgreeOn ctx coords u) :
  rootsAgreeOn ctx coords (CPolynomial.monicNormalize u) := by
  intro a b hrootA hrootB beta hbeta
  exact huAgree a b ((monicNormalize_root_iff hu).1 hrootA)
    ((monicNormalize_root_iff hu).1 hrootB) beta hbeta

private theorem shoupRefineBaseConstants_rootsAgreeOn {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (beta : F) {u : CPolynomial F}
    (hu : u ≠ 0) {coords : List F}
    (huAgree : rootsAgreeOn ctx coords u) :
    ∀ (constants : List F) (acc : Array (CPolynomial F)),
      (∀ factor, factor ∈ acc.toList →
        rootsAgreeOn ctx (coords ++ [beta]) factor) →
        ∀ factor,
          factor ∈
              (constants.foldl
                (fun children c ↦
                  let child := CPolynomial.monicNormalize
                    (CPolynomial.gcdMonic u
                      (traceCoordinatePolynomialWith M D ctx u beta - CPolynomial.C c))
                  pushNontrivialChild children child)
                acc).toList →
            rootsAgreeOn ctx (coords ++ [beta]) factor := by
  intro constants
  induction constants with
  | nil =>
      intro acc hacc factor hmem
      exact hacc factor hmem
  | cons c cs ih =>
      intro acc hacc factor hmem
      simp only [List.foldl_cons] at hmem
      apply ih (pushNontrivialChild acc
        (CPolynomial.monicNormalize
          (CPolynomial.gcdMonic u
            (traceCoordinatePolynomialWith M D ctx u beta - CPolynomial.C c))))
      · intro factor hfactor
        rcases mem_pushNontrivialChild hfactor with hold | hnew
        · exact hacc factor hold
        · subst factor
          intro a b hrootA hrootB gamma hgamma
          rw [List.mem_append] at hgamma
          rcases hgamma with hgamma | hgamma
          · exact huAgree
              a b
              ((shoup_gcdBucket_root_iff M D ctx hu).1 hrootA).1
              ((shoup_gcdBucket_root_iff M D ctx hu).1 hrootB).1
              gamma hgamma
          · simp at hgamma
            subst gamma
            exact (((shoup_gcdBucket_root_iff M D ctx hu).1 hrootA).2).trans
              (((shoup_gcdBucket_root_iff M D ctx hu).1 hrootB).2).symm
      · exact hmem

private theorem shoupRefineFactorWith_rootsAgreeOn {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (beta : F) {u factor : CPolynomial F}
    {coords : List F}
    (huAgree : rootsAgreeOn ctx coords u)
    (hmem : factor ∈ (shoupRefineFactorWith M D ctx beta u).toList) :
    rootsAgreeOn ctx (coords ++ [beta]) factor := by
  unfold shoupRefineFactorWith at hmem
  let u' := CPolynomial.monicNormalize u
  by_cases hzero : (u' == 0 || u' == 1) = true
  · rw [if_pos hzero] at hmem
    simp at hmem
  · rw [if_neg hzero] at hmem
    by_cases hlin : isRepresentedLinearFactor u' = true
    · rw [if_pos hlin] at hmem
      simp at hmem
      subst factor
      exact rootsAgreeOn_of_root_unique ctx (coords ++ [beta])
        (fun hrootA hrootB ↦
          representedLinearFactor_root_unique hlin hrootA hrootB)
    · rw [if_neg hlin] at hmem
      rw [← Array.foldl_toList] at hmem
      have hu' : u' ≠ 0 := by
        intro hz
        have hskip : (u' == 0 || u' == 1) = true := by
          simp [hz]
        exact hzero hskip
      have hu : u ≠ 0 := by
        intro hz
        subst u
        exact hu' (by simpa [u'] using (monicNormalize_zero : CPolynomial.monicNormalize
          (0 : CPolynomial F) = 0))
      have huAgree' : rootsAgreeOn ctx coords u' :=
        rootsAgreeOn_monicNormalize ctx coords hu huAgree
      exact shoupRefineBaseConstants_rootsAgreeOn M D ctx beta hu'
        huAgree' ctx.baseConstants.toList #[] (by
          intro factor hfactor
          simp at hfactor) factor hmem

private theorem shoupRefineFactorsWith_rootsAgreeOn {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (beta : F)
    {coords : List F} {factors : Array (CPolynomial F)} {factor : CPolynomial F}
    (hparents : ∀ parent, parent ∈ factors.toList →
      rootsAgreeOn ctx coords parent)
    (hmem : factor ∈ (shoupRefineFactorsWith M D ctx beta factors).toList) :
    rootsAgreeOn ctx (coords ++ [beta]) factor := by
  unfold shoupRefineFactorsWith at hmem
  rcases factors with ⟨factorList⟩
  rw [← Array.foldl_toList] at hmem
  have hgo : ∀ (xs : List (CPolynomial F)) (out : Array (CPolynomial F)),
      (∀ child, child ∈ out.toList →
        rootsAgreeOn ctx (coords ++ [beta]) child) →
        (∀ parent, parent ∈ xs → rootsAgreeOn ctx coords parent) →
          ∀ child,
            child ∈
                (xs.foldl
                  (fun out factor ↦ out ++ shoupRefineFactorWith M D ctx beta factor)
                  out).toList →
              rootsAgreeOn ctx (coords ++ [beta]) child := by
    intro xs
    induction xs with
    | nil =>
        intro out hout _ child hchild
        exact hout child hchild
    | cons x xs ih =>
        intro out hout hxs child hchild
        simp only [List.foldl_cons] at hchild
        apply ih (out ++ shoupRefineFactorWith M D ctx beta x)
        · intro child hmemChild
          simp at hmemChild
          rcases hmemChild with hleft | hright
          · exact hout child (by simpa using hleft)
          · exact shoupRefineFactorWith_rootsAgreeOn M D ctx beta
              (hxs x (by simp)) (by simpa using hright)
        · intro parent hparent
          exact hxs parent (by simp [hparent])
        · exact hchild
  exact hgo factorList #[]
    (by
      intro child hchild
      simp at hchild)
    (by
      intro parent hparent
      exact hparents parent (by simpa using hparent))
    factor hmem

private theorem shoupRefineBasisWith_rootsAgreeOn {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) :
    ∀ (basis coords : List F) (factors : Array (CPolynomial F)) {factor : CPolynomial F},
      (∀ parent, parent ∈ factors.toList → rootsAgreeOn ctx coords parent) →
        factor ∈
            (basis.foldl
              (fun factors beta ↦ shoupRefineFactorsWith M D ctx beta factors)
              factors).toList →
          rootsAgreeOn ctx (coords ++ basis) factor := by
  intro basis
  induction basis with
  | nil =>
      intro coords factors factor hparents hmem
      simpa using hparents factor hmem
  | cons beta rest ih =>
      intro coords factors factor hparents hmem
      simp only [List.foldl_cons] at hmem
      have hstep :
          ∀ parent, parent ∈ (shoupRefineFactorsWith M D ctx beta factors).toList →
            rootsAgreeOn ctx (coords ++ [beta]) parent := by
        intro parent hparent
        exact shoupRefineFactorsWith_rootsAgreeOn M D ctx beta hparents hparent
      have hfinal := ih (coords ++ [beta])
        (shoupRefineFactorsWith M D ctx beta factors) hstep hmem
      simpa [List.append_assoc] using hfinal

theorem shoupSplitCandidatesWith_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {p : CPolynomial F} {a : F}
    (hp : p ≠ 0) (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈ (shoupSplitCandidatesWith M D ctx p).toList ∧
        factor ≠ 0 ∧
        CPolynomial.eval a factor = 0 := by
  unfold shoupSplitCandidatesWith
  let p' := CPolynomial.monicNormalize p
  have hp' : p' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hp
  have hroot' : CPolynomial.eval a p' = 0 := (monicNormalize_root_iff hp).2 hroot
  by_cases hzero : (p' == 0 || p' == 1) = true
  · have hcases : p' = 0 ∨ p' = 1 := by
      simpa [p'] using hzero
    rcases hcases with h0 | h1
    · exact (hp' h0).elim
    · rw [h1] at hroot'
      rw [eval_one a] at hroot'
      exact (one_ne_zero hroot').elim
  · rw [if_neg hzero]
    by_cases hlin : isRepresentedLinearFactor p' = true
    · rw [if_pos hlin]
      refine ⟨p', ?_, hp', hroot'⟩
      simp [p']
    · rw [if_neg hlin]
      rw [← Array.foldl_toList]
      exact shoupRefineBasisWith_root M D ctx ctx.basis.toList #[p']
        ⟨p', by simp [p'], hp', hroot'⟩

theorem shoupSplitCandidatesWith_dvd_input {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {p factor : CPolynomial F}
    (hmem : factor ∈ (shoupSplitCandidatesWith M D ctx p).toList) :
    factor.toPoly ∣ p.toPoly := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  unfold shoupSplitCandidatesWith at hmem
  let p' := CPolynomial.monicNormalize p
  by_cases hzero : (p' == 0 || p' == 1) = true
  · rw [if_pos hzero] at hmem
    simp at hmem
  · rw [if_neg hzero] at hmem
    by_cases hlin : isRepresentedLinearFactor p' = true
    · rw [if_pos hlin] at hmem
      simp at hmem
      subst factor
      exact monicNormalize_toPoly_dvd_self p
    · rw [if_neg hlin] at hmem
      rw [← Array.foldl_toList] at hmem
      exact shoupRefineBasisWith_dvd M D ctx ctx.basis.toList #[p']
        (by
          intro parent hparent
          simp at hparent
          subst parent
          exact monicNormalize_toPoly_dvd_self p)
        hmem

private theorem representedLinearFactorsOnly_mem_of_mem {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {factors : Array (CPolynomial F)} {factor : CPolynomial F}
    (hmem : factor ∈ factors.toList)
    (hlin : isRepresentedLinearFactor factor = true) :
    factor ∈ (representedLinearFactorsOnly factors).toList := by
  unfold representedLinearFactorsOnly
  rcases factors with ⟨factorList⟩
  rw [← Array.foldl_toList]
  have hgo : ∀ (xs : List (CPolynomial F)) (out : Array (CPolynomial F)),
      factor ∈ out.toList ∨ factor ∈ xs →
        factor ∈
          (xs.foldl
            (fun out factor ↦
              if isRepresentedLinearFactor factor then out.push factor else out)
            out).toList := by
    intro xs
    induction xs with
    | nil =>
        intro out h
        rcases h with hout | hxs
        · exact hout
        · simp at hxs
    | cons x xs ih =>
        intro out h
        simp only [List.foldl_cons]
        apply ih
        rcases h with hout | hxs
        · left
          by_cases hxlin : isRepresentedLinearFactor x = true
          · rw [if_pos hxlin]
            simp [hout]
          · rw [if_neg hxlin]
            exact hout
        · simp at hxs
          rcases hxs with hx | htail
          · subst x
            left
            rw [if_pos hlin]
            simp
          · right
            exact htail
  exact hgo factorList #[] (Or.inr (by simpa using hmem))

/- The remaining algorithmic invariant: two field roots of the same final Shoup
candidate have equal trace coordinates for every basis element, hence are equal. -/
private theorem shoupSplitCandidatesWith_root_unique {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {p factor : CPolynomial F} {a b : F}
    (hmem : factor ∈ (shoupSplitCandidatesWith M D ctx p).toList)
    (hrootA : CPolynomial.eval a factor = 0)
    (hrootB : CPolynomial.eval b factor = 0) :
    b = a := by
  unfold shoupSplitCandidatesWith at hmem
  let p' := CPolynomial.monicNormalize p
  by_cases hzero : (p' == 0 || p' == 1) = true
  · rw [if_pos hzero] at hmem
    simp at hmem
  · rw [if_neg hzero] at hmem
    by_cases hlin : isRepresentedLinearFactor p' = true
    · rw [if_pos hlin] at hmem
      simp at hmem
      subst factor
      exact representedLinearFactor_root_unique hlin hrootA hrootB
    · rw [if_neg hlin] at hmem
      rw [← Array.foldl_toList] at hmem
      have hagree : rootsAgreeOn ctx ctx.basis.toList factor := by
        have hbasis := shoupRefineBasisWith_rootsAgreeOn M D ctx
          ctx.basis.toList [] #[p'] (by
            intro parent hparent
            simp at hparent
            subst parent
            intro x y hrootX hrootY beta hbeta
            simp at hbeta) hmem
        simpa using hbasis
      exact (eq_of_traceValue_eq_on_basis ctx
        (fun beta hbeta ↦ hagree a b hrootA hrootB beta hbeta)).symm

/--
Remaining Shoup linearization obligation.

The checked lemmas above show that candidates divide the valid root product and
that valid divisors of `X^q - X` with a unique field root are represented
linear. The remaining algorithmic proof is `shoupSplitCandidatesWith_root_unique`.
-/
private theorem shoupSplitCandidatesWith_valid_factor_represented {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {p factor : CPolynomial F} {a : F}
    (hvalid : shoupSplitterInput ctx p)
    (hmem : factor ∈ (shoupSplitCandidatesWith M D ctx p).toList)
    (hfactorNe : factor ≠ 0)
    (hfactorRoot : CPolynomial.eval a factor = 0) :
    isRepresentedLinearFactor factor = true := by
  exact isRepresentedLinearFactor_of_dvd_frobenius_unique_root ctx hfactorNe
    ((shoupSplitCandidatesWith_dvd_input M D ctx hmem).trans hvalid.2)
    hfactorRoot (fun b hrootB ↦
      shoupSplitCandidatesWith_root_unique M D ctx hmem hfactorRoot hrootB)

/-- The Shoup splitter is complete for valid root-product inputs. -/
theorem shoupSplitLinearFactorsWith_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {p : CPolynomial F} {a : F}
    (hvalid : shoupSplitterInput ctx p)
    (hp : p ≠ 0) (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈ (shoupSplitLinearFactorsWith M D ctx p).toList ∧
        IsLinearRootFactorCandidate factor a := by
  rcases shoupSplitCandidatesWith_root M D ctx hp hroot with
    ⟨factor, hmem, hfactorNe, hfactorRoot⟩
  have hlin : isRepresentedLinearFactor factor = true :=
    shoupSplitCandidatesWith_valid_factor_represented M D ctx hvalid hmem
      hfactorNe hfactorRoot
  refine ⟨factor, ?_, representedLinearFactor_candidate_of_root hlin hfactorRoot⟩
  unfold shoupSplitLinearFactorsWith
  exact representedLinearFactorsOnly_mem_of_mem hmem hlin

/-- Adapt the Shoup trace splitter to the generic linear-factor-product interface. -/
def shoupLinearFactorProductSplitterWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) :
    LinearFactorProductSplitter F where
  splitLinearFactors := fun _q p ↦ shoupSplitLinearFactorsWith M D ctx p
  validInput := fun _q p ↦ shoupSplitterInput ctx p
  sound := by
    intro _q p factor h
    exact shoupSplitLinearFactorsWith_sound M D ctx h
  complete := by
    intro _q p a hvalid hp hroot
    exact shoupSplitLinearFactorsWith_complete M D ctx hvalid hp hroot

/-- Shoup trace splitter using the default raw multiplication and remainder backends. -/
def shoupLinearFactorProductSplitter {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : SmallPrimeTraceContext F) :
    LinearFactorProductSplitter F :=
  shoupLinearFactorProductSplitterWith CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive ctx

/-- The Shoup splitter only emits represented linear factors. -/
theorem shoupLinearFactorProductSplitterWith_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {q : Nat} {p factor : CPolynomial F}
    (h : factor ∈
      ((shoupLinearFactorProductSplitterWith M D ctx).splitLinearFactors q p).toList) :
    IsLinearFactor factor := by
  exact (shoupLinearFactorProductSplitterWith M D ctx).sound q p factor h

/-- The Shoup splitter is complete for valid root-product inputs. -/
theorem shoupLinearFactorProductSplitterWith_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {q : Nat} {p : CPolynomial F} {a : F}
    (hvalid : (shoupLinearFactorProductSplitterWith M D ctx).validInput q p)
    (hp : p ≠ 0) (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈
          ((shoupLinearFactorProductSplitterWith M D ctx).splitLinearFactors q p).toList ∧
        IsLinearRootFactorCandidate factor a := by
  exact (shoupLinearFactorProductSplitterWith M D ctx).complete q p a hvalid hp hroot

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
theorem finiteFieldRootProductWith_dvd_frobenius {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {p : CPolynomial F} (_hp : p ≠ 0) :
    (finiteFieldRootProductWith M D ctx.toFiniteFieldContext p).toPoly ∣
      ((Polynomial.X : Polynomial F) ^ ctx.q - Polynomial.X) := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  rw [finiteFieldRootProductWith_toPoly_eq_normalize_gcd M D ctx.toFiniteFieldContext _hp]
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
  have hpMonicNe : pMonic ≠ 0 := monicNormalize_ne_zero_of_ne_zero _hp
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

/-- Finite-field root products satisfy the Shoup splitter's valid-input predicate. -/
theorem finiteFieldRootProductWith_shoupSplitterInput {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {p : CPolynomial F} (hp : p ≠ 0) :
    shoupSplitterInput ctx (finiteFieldRootProductWith M D ctx.toFiniteFieldContext p) := by
  exact ⟨finiteFieldRootProductWith_ne_zero_of_ne_zero M D ctx.toFiniteFieldContext hp,
    finiteFieldRootProductWith_dvd_frobenius M D ctx hp⟩

/-- Default-backend finite-field root products satisfy the Shoup valid-input predicate. -/
theorem finiteFieldRootProduct_shoupSplitterInput {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : SmallPrimeTraceContext F) {p : CPolynomial F} (hp : p ≠ 0) :
    shoupSplitterInput ctx (finiteFieldRootProduct ctx.toFiniteFieldContext p) := by
  exact finiteFieldRootProductWith_shoupSplitterInput
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive ctx hp

/-- Alias emphasizing the root-product precondition used by Shoup completeness. -/
theorem rootProduct_satisfies_shoupSplitterInput {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {p : CPolynomial F} (hp : p ≠ 0) :
    (shoupLinearFactorProductSplitterWith M D ctx).validInput ctx.q
      (finiteFieldRootProductWith M D ctx.toFiniteFieldContext p) := by
  exact finiteFieldRootProductWith_shoupSplitterInput M D ctx hp

end FiniteField

end Roots

end CPolynomial

end CompPoly
