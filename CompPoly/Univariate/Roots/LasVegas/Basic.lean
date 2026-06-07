/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.Enumeration
import CompPoly.Univariate.Roots.RootProduct
import CompPoly.Univariate.Roots.Shoup.Basic

/-!
# Las Vegas Linear-Factor Splitting

Pure, bounded Las Vegas splitting for finite-field root products. The splitter
uses the odd-field Cantor-Zassenhaus branch for odd fields, the characteristic
two trace branch when supplied with compatible trace metadata, and exhaustive
enumeration after the configured probe cutoff or when no randomized branch is
available.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Lazy pure probe source for deterministic Las Vegas splitting. -/
structure ProbeFamily (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  probe : Nat → CPolynomial F → Nat → CPolynomial F

/-- A simple deterministic affine probe source derived from a natural seed. -/
def seededLinearProbeFamily {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (seed : Nat) : ProbeFamily F where
  probe q factor attempt :=
    let slope : F := (seed + 17 * attempt + factor.val.size + q + 1 : Nat)
    let constant : F := (seed + 97 * attempt + 13 * factor.val.size + 3 * q + 1 : Nat)
    CPolynomial.C slope * (CPolynomial.X : CPolynomial F) + CPolynomial.C constant

/-- Configuration for bounded Las Vegas splitting. -/
structure LasVegasConfig where
  cutoff : Nat
  tryOddRandomizedSplitting : Bool := true
  tryEvenTraceSplitting : Bool := true

/-- Root-product input predicate for the Las Vegas splitter. -/
def lasVegasSplitterInput {F : Type*} [Field F]
    (q : Nat) (p : CPolynomial F) : Prop :=
  p ≠ 0 ∧ p.toPoly ∣ ((Polynomial.X : Polynomial F) ^ q - Polynomial.X)

/-- Reduce a canonical polynomial modulo a canonical modulus with the selected raw backend. -/
def reduceModWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (D : CPolynomial.Raw.ModContext F) (modulus h : CPolynomial F) :
    CPolynomial F :=
  if modulus == 0 then
    h
  else
    CPolynomial.ofArray (D.modByMonic h.val (CPolynomial.monicNormalize modulus).val)

/-- `base^exponent mod modulus`, lifted through the selected raw arithmetic backends. -/
def powModWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (modulus base : CPolynomial F) (exponent : Nat) :
    CPolynomial F :=
  CPolynomial.ofArray (CPolynomial.Raw.powModWith M D modulus.val base.val exponent)

private def tracePowerSumPolynomialLoopWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (modulus : CPolynomial F) (p : Nat) :
    Nat → CPolynomial F → CPolynomial F → CPolynomial F
  | 0, _power, acc => acc
  | steps + 1, power, acc =>
      let acc := reduceModWith D modulus (acc + power)
      let nextPower := powModWith M D modulus power p
      tracePowerSumPolynomialLoopWith M D modulus p steps nextPower acc

/-- Polynomial-residue analogue of Shoup's trace power sum. -/
def tracePowerSumPolynomialWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (modulus : CPolynomial F) (p k : Nat) (h : CPolynomial F) :
    CPolynomial F :=
  tracePowerSumPolynomialLoopWith M D modulus p k (reduceModWith D modulus h) 0

/--
Deterministic trace-coordinate probe family cycling through the Shoup basis.

For characteristic-two contexts this produces probes `beta * X` in basis order,
which makes the Las Vegas trace branch a bounded randomized-style splitter for
fixed deterministic benchmark and adapter contexts.
-/
def traceBasisProbeFamily {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (ctx : SmallPrimeTraceContext F) :
    ProbeFamily F where
  probe _q _factor attempt :=
    let beta := ctx.basis.getD (attempt % ctx.basis.size) (1 : F)
    CPolynomial.C beta * (CPolynomial.X : CPolynomial F)

/-- Keep only nonconstant children with strictly smaller representation size than the parent. -/
def isNontrivialProperChild {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (parent child : CPolynomial F) : Bool :=
  !(child == 0) && !(child == 1) && child.val.size < parent.val.size

/-- Filter candidate children down to nonconstant, proper children. -/
def nontrivialProperChildren {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (parent : CPolynomial F) (children : Array (CPolynomial F)) :
    Array (CPolynomial F) :=
  children.filter fun child ↦ isNontrivialProperChild parent child

private def quotientAfterChild {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (parent child : CPolynomial F) : CPolynomial F :=
  if isNontrivialProperChild parent child then
    CPolynomial.monicNormalize (parent / child)
  else
    parent

/--
One odd-field Cantor-Zassenhaus degree-one split attempt.

The probe is reduced modulo `g`, then the split candidates are
`gcd(g, h)`, `gcd(g / zeroPart, h^((q - 1) / 2) - 1)`, and the remaining
quotient. The attempt succeeds only when at least two nonconstant proper
children are produced.
-/
def cantorZassenhausOddAttemptWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) (g : CPolynomial F) (attempt : Nat) :
    Option (Array (CPolynomial F)) :=
  let g := CPolynomial.monicNormalize g
  let h := reduceModWith D g (probes.probe q g attempt)
  let s := powModWith M D g h ((q - 1) / 2)
  let zeroPart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g h)
  let afterZero := quotientAfterChild g zeroPart
  let squarePart := CPolynomial.monicNormalize
    (CPolynomial.gcdMonic afterZero (s - (1 : CPolynomial F)))
  let afterSquare := quotientAfterChild afterZero squarePart
  let children := nontrivialProperChildren g #[zeroPart, squarePart, afterSquare]
  if children.size >= 2 then some children else none

/--
One characteristic-two trace split attempt.

The probe is reduced modulo `g`, then the trace power sum
`h + h^2 + ... + h^(2^(m-1))` is computed modulo `g` using the supplied Shoup
small-prime trace metadata. The attempt succeeds only when `gcd(g, Tr(h))` and
the remaining quotient are both nonconstant proper children.
-/
def cantorZassenhausEvenTraceAttemptWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) (g : CPolynomial F) (attempt : Nat) :
    Option (Array (CPolynomial F)) :=
  let g := CPolynomial.monicNormalize g
  let h := reduceModWith D g (probes.probe q g attempt)
  let tracePoly := tracePowerSumPolynomialWith M D g traceCtx.p traceCtx.k h
  let tracePart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g tracePoly)
  let complement := quotientAfterChild g tracePart
  let children := nontrivialProperChildren g #[tracePart, complement]
  if children.size >= 2 then some children else none

private def tryOddSplitAttemptsWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) (g : CPolynomial F) :
    Nat → Nat → Option (Array (CPolynomial F))
  | 0, _ => none
  | attempts + 1, offset =>
      match cantorZassenhausOddAttemptWith M D q probes g offset with
      | some children => some children
      | none => tryOddSplitAttemptsWith M D q probes g attempts (offset + 1)

private def tryEvenTraceSplitAttemptsWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) (g : CPolynomial F) :
    Nat → Nat → Option (Array (CPolynomial F))
  | 0, _ => none
  | attempts + 1, offset =>
      match cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g offset with
      | some children => some children
      | none => tryEvenTraceSplitAttemptsWith M D traceCtx q probes g attempts (offset + 1)

private def traceContextMatchesQ {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (traceCtx : SmallPrimeTraceContext F) (q : Nat) : Bool :=
  traceCtx.p == 2 && traceCtx.q == q

private def lasVegasSplitLoopWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx? : Option (SmallPrimeTraceContext F))
    (cfg : LasVegasConfig)
    (probes : ProbeFamily F) (q : Nat) :
    Nat → List (CPolynomial F) → Array (CPolynomial F) → Array (CPolynomial F)
  | 0, _stack, out => out
  | _fuel + 1, [], out => out
  | fuel + 1, g :: stack, out =>
      let g := CPolynomial.monicNormalize g
      if g == 0 || g == 1 then
        lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel stack out
      else if isRepresentedLinearFactor g then
        lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel stack (out.push g)
      else if cfg.tryOddRandomizedSplitting && q % 2 == 1 then
        match tryOddSplitAttemptsWith M D q probes g cfg.cutoff 0 with
        | some children =>
            lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel
              (children.toList ++ stack) out
        | none =>
            lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel stack
              (out ++ enumeratedLinearFactors enumeration g)
      else if cfg.tryEvenTraceSplitting && q % 2 == 0 then
        match traceCtx? with
        | some traceCtx =>
            if traceContextMatchesQ traceCtx q then
              match tryEvenTraceSplitAttemptsWith M D traceCtx q probes g cfg.cutoff 0 with
              | some children =>
                  lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel
                    (children.toList ++ stack) out
              | none =>
                  lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel stack
                    (out ++ enumeratedLinearFactors enumeration g)
            else
              lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel stack
                (out ++ enumeratedLinearFactors enumeration g)
        | none =>
            lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel stack
              (out ++ enumeratedLinearFactors enumeration g)
      else
        lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel stack
          (out ++ enumeratedLinearFactors enumeration g)

/-- Candidate linear factors from bounded Las Vegas splitting plus enumeration fallback. -/
def lasVegasSplitCandidatesWithTrace? {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx? : Option (SmallPrimeTraceContext F))
    (cfg : LasVegasConfig)
    (probes : ProbeFamily F) (q : Nat) (p : CPolynomial F) :
    Array (CPolynomial F) :=
  let p := CPolynomial.monicNormalize p
  let fuel := 2 * p.val.size + 1
  lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel [p] #[]

/-- Candidate linear factors using odd splitting only, plus enumeration fallback. -/
def lasVegasSplitCandidatesWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (cfg : LasVegasConfig)
    (probes : ProbeFamily F) (q : Nat) (p : CPolynomial F) :
    Array (CPolynomial F) :=
  lasVegasSplitCandidatesWithTrace? M D enumeration none cfg probes q p

/-- Candidate linear factors using supplied characteristic-two trace metadata when applicable. -/
def lasVegasSplitCandidatesWithTrace {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx : SmallPrimeTraceContext F)
    (cfg : LasVegasConfig) (probes : ProbeFamily F) (q : Nat) (p : CPolynomial F) :
    Array (CPolynomial F) :=
  lasVegasSplitCandidatesWithTrace? M D enumeration (some traceCtx) cfg probes q p

/-- Las Vegas splitting with optional trace metadata, returning only represented linear factors. -/
def lasVegasSplitLinearFactorsWithTrace? {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx? : Option (SmallPrimeTraceContext F))
    (cfg : LasVegasConfig)
    (probes : ProbeFamily F) (q : Nat) (p : CPolynomial F) :
    Array (CPolynomial F) :=
  representedLinearFactorsOnly
    (lasVegasSplitCandidatesWithTrace? M D enumeration traceCtx? cfg probes q p)

/-- Las Vegas splitting, returning only represented linear factors. -/
def lasVegasSplitLinearFactorsWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (cfg : LasVegasConfig)
    (probes : ProbeFamily F) (q : Nat) (p : CPolynomial F) :
    Array (CPolynomial F) :=
  lasVegasSplitLinearFactorsWithTrace? M D enumeration none cfg probes q p

/-- Las Vegas splitting using supplied characteristic-two trace metadata when applicable. -/
def lasVegasSplitLinearFactorsWithTrace {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx : SmallPrimeTraceContext F)
    (cfg : LasVegasConfig) (probes : ProbeFamily F) (q : Nat) (p : CPolynomial F) :
    Array (CPolynomial F) :=
  lasVegasSplitLinearFactorsWithTrace? M D enumeration (some traceCtx) cfg probes q p

/-- The final Las Vegas filter only keeps represented linear factors. -/
theorem lasVegasSplitLinearFactorsWith_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (cfg : LasVegasConfig)
    (probes : ProbeFamily F) (q : Nat) {p factor : CPolynomial F}
    (h : factor ∈
      (lasVegasSplitLinearFactorsWith M D enumeration cfg probes q p).toList) :
    IsLinearFactor factor := by
  exact representedLinearFactorsOnly_sound h

/-- The final Las Vegas filter with trace metadata only keeps represented linear factors. -/
theorem lasVegasSplitLinearFactorsWithTrace_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx : SmallPrimeTraceContext F)
    (cfg : LasVegasConfig) (probes : ProbeFamily F) (q : Nat) {p factor : CPolynomial F}
    (h : factor ∈
      (lasVegasSplitLinearFactorsWithTrace M D enumeration traceCtx cfg probes q p).toList) :
    IsLinearFactor factor := by
  exact representedLinearFactorsOnly_sound h

end FiniteField

end Roots

end CPolynomial

end CompPoly
