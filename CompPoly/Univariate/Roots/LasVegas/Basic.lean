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

Pure, bounded Las Vegas splitting for finite-field root products. Phase 1
implements the odd-field Cantor-Zassenhaus branch and falls back to exhaustive
enumeration for non-odd fields or after the configured probe cutoff.
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

private def lasVegasSplitLoopWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (cfg : LasVegasConfig)
    (probes : ProbeFamily F) (q : Nat) :
    Nat → List (CPolynomial F) → Array (CPolynomial F) → Array (CPolynomial F)
  | 0, _stack, out => out
  | _fuel + 1, [], out => out
  | fuel + 1, g :: stack, out =>
      let g := CPolynomial.monicNormalize g
      if g == 0 || g == 1 then
        lasVegasSplitLoopWith M D enumeration cfg probes q fuel stack out
      else if isRepresentedLinearFactor g then
        lasVegasSplitLoopWith M D enumeration cfg probes q fuel stack (out.push g)
      else if cfg.tryOddRandomizedSplitting && q % 2 == 1 then
        match tryOddSplitAttemptsWith M D q probes g cfg.cutoff 0 with
        | some children =>
            lasVegasSplitLoopWith M D enumeration cfg probes q fuel
              (children.toList ++ stack) out
        | none =>
            lasVegasSplitLoopWith M D enumeration cfg probes q fuel stack
              (out ++ enumeratedLinearFactors enumeration g)
      else
        lasVegasSplitLoopWith M D enumeration cfg probes q fuel stack
          (out ++ enumeratedLinearFactors enumeration g)

/-- Candidate linear factors from bounded Las Vegas splitting plus enumeration fallback. -/
def lasVegasSplitCandidatesWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (cfg : LasVegasConfig)
    (probes : ProbeFamily F) (q : Nat) (p : CPolynomial F) :
    Array (CPolynomial F) :=
  let p := CPolynomial.monicNormalize p
  let fuel := 2 * p.val.size + 1
  lasVegasSplitLoopWith M D enumeration cfg probes q fuel [p] #[]

/-- Las Vegas splitting, returning only represented linear factors. -/
def lasVegasSplitLinearFactorsWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (cfg : LasVegasConfig)
    (probes : ProbeFamily F) (q : Nat) (p : CPolynomial F) :
    Array (CPolynomial F) :=
  representedLinearFactorsOnly
    (lasVegasSplitCandidatesWith M D enumeration cfg probes q p)

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

end FiniteField

end Roots

end CPolynomial

end CompPoly
