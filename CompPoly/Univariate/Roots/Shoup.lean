/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.RootProduct
import CompPoly.Univariate.Roots.SmoothSubgroup
import CompPoly.Univariate.ToPoly.Core

/-!
# Shoup-Style Small-Characteristic Linear-Factor Splitting

Executable trace-coordinate splitter for finite-field root products over fields
presented as `GF(p^k)` with small base characteristic `p`. The splitter refines a
valid root product by `k` trace coordinates and the `p` embedded base constants;
it does not enumerate all `p^k` field elements.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Trace power sum `z + z^p + ... + z^(p^(k-1))`. -/
def tracePowerSum {F : Type*} [Field F] (p k : Nat) (z : F) : F :=
  (List.range k).foldl (fun acc i ↦ acc + z ^ (p ^ i)) 0

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

/-- Trace-coordinate refinement candidates before the final linear-only filter. -/
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
