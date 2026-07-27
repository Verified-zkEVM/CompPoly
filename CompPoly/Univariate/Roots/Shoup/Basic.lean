/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.RootProduct
import CompPoly.Univariate.Roots.Splitter
import CompPoly.Univariate.ToPoly.Core

/-!
# Shoup-Style Small-Characteristic Linear-Factor Splitting

Executable trace-coordinate splitter for finite-field root products over fields
presented as `GF(p^k)` with small base characteristic `p`. The splitter refines a
valid root product by `k` trace coordinates and the `p` embedded base constants;
it does not enumerate all `p^k` field elements, following the small-characteristic
Frobenius-map factoring method of von zur Gathen and Shoup [vzGS92].

## References

* [J. von zur Gathen and Victor Shoup, *Computing Frobenius maps and factoring
    polynomials*, Computational Complexity 2, 187-224, 1992][vzGS92]
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Trace power sum `z + z^p + ... + z^(p^(k-1))`. -/
def tracePowerSum {F : Type*} [Field F] (p k : Nat) (z : F) : F :=
  (List.range k).foldl (fun acc i ↦ acc + z ^ (p ^ i)) 0

/-- The list-fold trace power sum is the corresponding finite range sum. -/
theorem tracePowerSum_eq_sum_range {F : Type*} [Field F] (p k : Nat) (z : F) :
    tracePowerSum p k z = ∑ i ∈ Finset.range k, z ^ (p ^ i) := by
  unfold tracePowerSum
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ, List.foldl_append]
      simp [ih, Finset.sum_range_succ]

/--
Executable and proof data for a Shoup-style small-characteristic trace splitter.

The field-theoretic facts are carried by the context so the generic executable
splitter can stay representation-independent. Concrete fields can discharge the
trace-image and separating-basis obligations using their own basis libraries.
-/
structure SmallPrimeTraceContext (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    extends FiniteFieldContext F where
  p : Nat
  k : Nat
  p_prime : Nat.Prime p
  q_eq : q = p ^ k
  baseConstants : Array F
  baseConstants_size : baseConstants.size = p
  basis : Array F
  basis_size : basis.size = k
  traceValue : F → F
  traceValue_eq_powerSum : ∀ z, traceValue z = tracePowerSum p k z
  traceValue_mem_base : ∀ z, traceValue z ∈ baseConstants.toList
  trace_separates :
    ∀ {a b : F}, a ≠ b →
      ∃ beta, beta ∈ basis.toList ∧ traceValue (beta * (a - b)) ≠ 0

/--
Input predicate for the Shoup splitter.

Completeness is only claimed for nonzero products of distinct field-linear
factors, represented here by divisibility into `X^q - X`. This is the contract
satisfied by the finite-field root product, not by arbitrary input polynomials.
-/
def shoupSplitterInput {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (ctx : SmallPrimeTraceContext F) (p : CPolynomial F) : Prop :=
  p ≠ 0 ∧
    p.toPoly ∣ ((Polynomial.X : Polynomial F) ^ ctx.q - Polynomial.X)

/-- Modular powers `X^(p^i) mod modulus` for `0 ≤ i < k`. -/
def modularXPowersWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (modulus : CPolynomial F) (p k : Nat) : Array (CPolynomial F) :=
  Array.ofFn fun i : Fin k ↦ xPowModWith M D modulus (p ^ i.val)

/-- `Trace(beta * X) mod modulus`, using precomputed modular Frobenius powers. -/
def traceCoordinatePolynomialFromPowers {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : SmallPrimeTraceContext F) (beta : F)
    (powers : Array (CPolynomial F)) :
    CPolynomial F :=
  (List.range ctx.k).foldl
    (fun acc i ↦
      acc + CPolynomial.C (beta ^ (ctx.p ^ i)) * powers.getD i 0)
    0

/-- `Trace(beta * X) mod modulus`, built from the modular Frobenius powers. -/
def traceCoordinatePolynomialWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (modulus : CPolynomial F) (beta : F) :
    CPolynomial F :=
  (List.range ctx.k).foldl
    (fun acc i ↦
      acc + CPolynomial.C (beta ^ (ctx.p ^ i)) *
        xPowModWith M D modulus (ctx.p ^ i))
    0

private theorem traceCoordinatePolynomialFromPowers_modularXPowersWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (modulus : CPolynomial F) (beta : F) :
    traceCoordinatePolynomialFromPowers ctx beta
        (modularXPowersWith M D modulus ctx.p ctx.k) =
      traceCoordinatePolynomialWith M D ctx modulus beta := by
  unfold traceCoordinatePolynomialFromPowers traceCoordinatePolynomialWith modularXPowersWith
  have hget : ∀ i, i ∈ List.range ctx.k →
      Array.getD
          (Array.ofFn fun i : Fin ctx.k ↦ xPowModWith M D modulus (ctx.p ^ i.val))
          i 0 =
        xPowModWith M D modulus (ctx.p ^ i) := by
    intro i hi
    have hi' : i < ctx.k := List.mem_range.mp hi
    unfold Array.getD
    simp [hi']
  have hfold : ∀ (xs : List Nat) (acc : CPolynomial F),
      (∀ i, i ∈ xs →
        Array.getD
            (Array.ofFn fun i : Fin ctx.k ↦ xPowModWith M D modulus (ctx.p ^ i.val))
            i 0 =
          xPowModWith M D modulus (ctx.p ^ i)) →
      List.foldl
          (fun acc i ↦ acc + CPolynomial.C (beta ^ ctx.p ^ i) *
            Array.getD
              (Array.ofFn fun i : Fin ctx.k ↦ xPowModWith M D modulus (ctx.p ^ i.val))
              i 0)
          acc xs =
        List.foldl
          (fun acc i ↦ acc + CPolynomial.C (beta ^ ctx.p ^ i) *
            xPowModWith M D modulus (ctx.p ^ i))
          acc xs := by
    intro xs
    induction xs with
    | nil =>
        intro acc _hxs
        simp
    | cons i xs ih =>
        intro acc hxs
        simp only [List.foldl_cons]
        rw [hxs i (by simp)]
        apply ih
        intro j hj
        exact hxs j (by simp [hj])
  exact hfold (List.range ctx.k) 0 hget

/-- Drop zero/unit children and keep the remaining monic gcd child. -/
def pushNontrivialChild {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (children : Array (CPolynomial F)) (child : CPolynomial F) :
    Array (CPolynomial F) :=
  if child == 0 || child == 1 then children else children.push child

/-- Refine one current factor by one trace coordinate and all base constants. -/
def shoupRefineFactorWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (beta : F) (u : CPolynomial F) :
    Array (CPolynomial F) :=
  let u := CPolynomial.monicNormalize u
  if u == 0 || u == 1 then
    #[]
  else if isRepresentedLinearFactor u then
    #[u]
  else
    let tracePoly := traceCoordinatePolynomialWith M D ctx u beta
    ctx.baseConstants.foldl
      (fun children c ↦
        let child := CPolynomial.monicNormalize
          (CPolynomial.gcdMonic u (tracePoly - CPolynomial.C c))
        pushNontrivialChild children child)
      #[]

/-- Refine all current factors by one trace coordinate. -/
def shoupRefineFactorsWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (beta : F) (factors : Array (CPolynomial F)) :
    Array (CPolynomial F) :=
  factors.foldl
    (fun out factor ↦ out ++ shoupRefineFactorWith M D ctx beta factor)
    #[]

abbrev ShoupTracePowerCache (F : Type*) [Field F] [BEq F] [LawfulBEq F] :=
  List (CPolynomial F × Array (CPolynomial F))

private def lookupTracePowers {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (u : CPolynomial F) :
    ShoupTracePowerCache F → Option (Array (CPolynomial F))
  | [] => none
  | (v, powers) :: rest =>
      if u == v then
        some powers
      else
        lookupTracePowers u rest

private def tracePowersWithCache {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (u : CPolynomial F)
    (cache : ShoupTracePowerCache F) :
    Array (CPolynomial F) × ShoupTracePowerCache F :=
  match lookupTracePowers u cache with
  | some powers => (powers, cache)
  | none =>
      let powers := modularXPowersWith M D u ctx.p ctx.k
      (powers, (u, powers) :: cache)

private def shoupRefineFactorCachedWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (beta : F)
    (cache : ShoupTracePowerCache F) (u : CPolynomial F) :
    ShoupTracePowerCache F × Array (CPolynomial F) :=
  let u := CPolynomial.monicNormalize u
  if u == 0 || u == 1 then
    (cache, #[])
  else if isRepresentedLinearFactor u then
    (cache, #[u])
  else
    let (powers, cache) := tracePowersWithCache M D ctx u cache
    let tracePoly := traceCoordinatePolynomialFromPowers ctx beta powers
    let children :=
      ctx.baseConstants.foldl
        (fun children c ↦
          let child := CPolynomial.monicNormalize
            (CPolynomial.gcdMonic u (tracePoly - CPolynomial.C c))
          pushNontrivialChild children child)
        #[]
    (cache, children)

private def shoupRefineFactorsCachedWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (beta : F)
    (cache : ShoupTracePowerCache F) (factors : Array (CPolynomial F)) :
    ShoupTracePowerCache F × Array (CPolynomial F) :=
  factors.foldl
    (fun state factor ↦
      let (cache, out) := state
      let (cache, children) := shoupRefineFactorCachedWith M D ctx beta cache factor
      (cache, out ++ children))
    (cache, #[])

private def shoupRefineBasisCachedWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (basis : List F)
    (cache : ShoupTracePowerCache F) (factors : Array (CPolynomial F)) :
    Array (CPolynomial F) :=
  (basis.foldl
    (fun state beta ↦
      let (cache, factors) := state
      shoupRefineFactorsCachedWith M D ctx beta cache factors)
    (cache, factors)).2

private def shoupSplitCandidatesCachedWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (p : CPolynomial F) :
    Array (CPolynomial F) :=
  let p := CPolynomial.monicNormalize p
  if p == 0 || p == 1 then
    #[]
  else if isRepresentedLinearFactor p then
    #[p]
  else
    shoupRefineBasisCachedWith M D ctx ctx.basis.toList [] #[p]

/-- Final linear-only filter for the splitter interface's unconditional soundness field. -/
def representedLinearFactorsOnly {F : Type*} [Field F] [BEq F]
    (factors : Array (CPolynomial F)) : Array (CPolynomial F) :=
  factors.foldl
    (fun out factor ↦
      if isRepresentedLinearFactor factor then out.push factor else out)
    #[]

private theorem representedLinearFactorsOnly_go_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] :
    ∀ (factors : List (CPolynomial F)) (out : Array (CPolynomial F)),
      (∀ {factor : CPolynomial F}, factor ∈ out → IsLinearFactor factor) →
        ∀ {factor : CPolynomial F},
          factor ∈
              factors.foldl
                (fun out factor ↦
                  if isRepresentedLinearFactor factor then out.push factor else out)
                out →
            IsLinearFactor factor := by
  intro factors
  induction factors with
  | nil =>
      intro out hout factor h
      exact hout h
  | cons x xs ih =>
      intro out hout factor h
      simp only [List.foldl_cons] at h
      by_cases hlin : isRepresentedLinearFactor x = true
      · simp [hlin] at h
        exact ih (out.push x) (by
          intro factor hmem
          simp at hmem
          rcases hmem with hmem | hfactor
          · exact hout hmem
          · subst factor
            exact isRepresentedLinearFactor_sound hlin) h
      · simp [hlin] at h
        exact ih out hout h

/-- The final Shoup filter only keeps represented linear factors. -/
theorem representedLinearFactorsOnly_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {factors : Array (CPolynomial F)} {factor : CPolynomial F}
    (h : factor ∈ (representedLinearFactorsOnly factors).toList) :
    IsLinearFactor factor := by
  unfold representedLinearFactorsOnly at h
  rcases factors with ⟨factors⟩
  exact representedLinearFactorsOnly_go_sound factors #[] (by
    intro factor hmem
    simp at hmem) (by
      simpa using h)

private theorem mem_representedLinearFactorsOnly_foldl_of_mem_out {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] :
    ∀ (factors : List (CPolynomial F)) (out : Array (CPolynomial F))
      {factor : CPolynomial F},
      factor ∈ out →
        factor ∈
          (factors.foldl
            (fun out factor ↦
              if isRepresentedLinearFactor factor then out.push factor else out)
            out) := by
  intro factors
  induction factors with
  | nil =>
      intro out factor hmem
      exact hmem
  | cons x xs ih =>
      intro out factor hmem
      simp only [List.foldl_cons]
      by_cases hxlin : isRepresentedLinearFactor x = true
      · simp [hxlin]
        exact ih (out.push x) (by simp [hmem])
      · simp [hxlin]
        exact ih out hmem

private theorem mem_representedLinearFactorsOnly_foldl_of_mem_input {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] :
    ∀ (factors : List (CPolynomial F)) (out : Array (CPolynomial F))
      {factor : CPolynomial F},
      factor ∈ factors →
        isRepresentedLinearFactor factor = true →
          factor ∈
            (factors.foldl
              (fun out factor ↦
                if isRepresentedLinearFactor factor then out.push factor else out)
              out) := by
  intro factors
  induction factors with
  | nil =>
      intro out factor hmem _hlin
      simp at hmem
  | cons x xs ih =>
      intro out factor hmem hlin
      simp only [List.foldl_cons]
      simp at hmem
      rcases hmem with hhead | htail
      · subst factor
        simp [hlin]
        exact mem_representedLinearFactorsOnly_foldl_of_mem_out xs (out.push x) (by simp)
      · by_cases hxlin : isRepresentedLinearFactor x = true
        · simp [hxlin]
          exact ih (out.push x) htail hlin
        · simp [hxlin]
          exact ih out htail hlin

/-- The final linear-factor filter keeps represented factors that were already present. -/
theorem representedLinearFactorsOnly_mem_of_mem {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {factors : Array (CPolynomial F)} {factor : CPolynomial F}
    (hmem : factor ∈ factors.toList)
    (hlin : isRepresentedLinearFactor factor = true) :
    factor ∈ (representedLinearFactorsOnly factors).toList := by
  unfold representedLinearFactorsOnly
  rcases factors with ⟨factors⟩
  simpa using mem_representedLinearFactorsOnly_foldl_of_mem_input factors #[] hmem hlin

/-- Trace-coordinate refinement candidates before the final linear-only filter. -/
@[implemented_by shoupSplitCandidatesCachedWith]
def shoupSplitCandidatesWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (p : CPolynomial F) :
    Array (CPolynomial F) :=
  let p := CPolynomial.monicNormalize p
  if p == 0 || p == 1 then
    #[]
  else if isRepresentedLinearFactor p then
    #[p]
  else
    ctx.basis.foldl
      (fun factors beta ↦ shoupRefineFactorsWith M D ctx beta factors)
      #[p]

/-- Shoup trace-coordinate splitting, returning only represented linear factors. -/
def shoupSplitLinearFactorsWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) (p : CPolynomial F) :
    Array (CPolynomial F) :=
  representedLinearFactorsOnly (shoupSplitCandidatesWith M D ctx p)

/-- Soundness of the final Shoup linear-factor array. -/
theorem shoupSplitLinearFactorsWith_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) {p factor : CPolynomial F}
    (h : factor ∈ (shoupSplitLinearFactorsWith M D ctx p).toList) :
    IsLinearFactor factor := by
  exact representedLinearFactorsOnly_sound h

end FiniteField

end Roots

end CPolynomial

end CompPoly
