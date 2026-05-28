/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.RootProduct

/-!
# Deterministic Cantor-Zassenhaus Linear-Factor Splitting

A deterministic, fuel-bounded Cantor-Zassenhaus-style splitter for squarefree
products of linear factors over odd finite fields. The implementation consumes a
fixed probe stream. The certified splitter context is built in
`CompPoly.Univariate.Roots.Correctness`.
-/

namespace CompPoly

namespace CPolynomial

namespace Raw

namespace Roots

namespace FiniteField

/-- Raw Boolean check that `factor` is a proper nonunit factor candidate of `p`. -/
def isNontrivialPolynomialFactor {F : Type*} [Field F] [BEq F]
    (factor p : CPolynomial.Raw F) : Bool :=
  !(factor == 0) && !(factor == 1) && !(factor == p)

/-- Raw monic quotient used after finding a split candidate. -/
def monicQuotient {F : Type*} [Field F] [BEq F]
    (p factor : CPolynomial.Raw F) : CPolynomial.Raw F :=
  CPolynomial.Raw.monicNormalize (p / factor)

/-- Try one deterministic split probe on raw polynomials. -/
def cantorZassenhausSplitWithProbeWith? {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (p probe : CPolynomial.Raw F) :
    Option (CPolynomial.Raw F × CPolynomial.Raw F) :=
  let zeroFactor := CPolynomial.Raw.monicNormalize (CPolynomial.Raw.gcdMonic p probe)
  if isNontrivialPolynomialFactor zeroFactor p then
    some (zeroFactor, monicQuotient p zeroFactor)
  else
    let witness :=
      CPolynomial.Raw.powModWith M D p probe ((q - 1) / 2) - (1 : CPolynomial.Raw F)
    let characterFactor := CPolynomial.Raw.monicNormalize (CPolynomial.Raw.gcdMonic p witness)
    if isNontrivialPolynomialFactor characterFactor p then
      some (characterFactor, monicQuotient p characterFactor)
    else
      none

/-- Try one deterministic split probe on raw polynomials with the default raw backends. -/
def cantorZassenhausSplitWithProbe? {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (q : Nat) (p probe : CPolynomial.Raw F) :
    Option (CPolynomial.Raw F × CPolynomial.Raw F) :=
  cantorZassenhausSplitWithProbeWith? CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive q p probe

/-- Try a deterministic stream of raw Cantor-Zassenhaus probes. -/
def cantorZassenhausSplitWith? {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : Array (CPolynomial.Raw F)) (p : CPolynomial.Raw F) :
    Option (CPolynomial.Raw F × CPolynomial.Raw F) :=
  probes.foldl
    (fun found probe =>
      match found with
      | some split => some split
      | none => cantorZassenhausSplitWithProbeWith? M D q p probe)
    none

/-- Try a deterministic stream of raw Cantor-Zassenhaus probes with the default raw backends. -/
def cantorZassenhausSplit? {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (q : Nat) (probes : Array (CPolynomial.Raw F)) (p : CPolynomial.Raw F) :
    Option (CPolynomial.Raw F × CPolynomial.Raw F) :=
  cantorZassenhausSplitWith? CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive q probes p

/-- Recursively split a raw squarefree product of linear factors. -/
def cantorZassenhausLinearFactorsWithFuelWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : Array (CPolynomial.Raw F)) :
    Nat → CPolynomial.Raw F → Array (CPolynomial.Raw F)
  | 0, p =>
      let p := CPolynomial.Raw.monicNormalize p
      if p.size ≤ 2 && !(p.coeff 1 == 0) then #[p] else #[]
  | fuel + 1, p =>
      let p := CPolynomial.Raw.monicNormalize p
      if p == 0 || p == 1 then
        #[]
      else if p.size ≤ 2 then
        if !(p.coeff 1 == 0) then #[p] else #[]
      else
        match cantorZassenhausSplitWith? M D q probes p with
        | none => #[]
        | some split =>
            cantorZassenhausLinearFactorsWithFuelWith M D q probes fuel split.1 ++
              cantorZassenhausLinearFactorsWithFuelWith M D q probes fuel split.2

/-- Recursively split a raw squarefree product of linear factors with the default raw backends. -/
def cantorZassenhausLinearFactorsWithFuel {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (q : Nat) (probes : Array (CPolynomial.Raw F)) :
    Nat → CPolynomial.Raw F → Array (CPolynomial.Raw F) :=
  cantorZassenhausLinearFactorsWithFuelWith CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive q probes

/-- A deterministic raw affine probe `X + seed`. -/
def affineProbe {F : Type*} [Field F] [BEq F] (seed : Nat) : CPolynomial.Raw F :=
  #[(seed : F), 1]

/-- A deterministic raw quadratic probe `X^2 + (seed + 1) X + seed`. -/
def quadraticProbe {F : Type*} [Field F] [BEq F] (seed : Nat) : CPolynomial.Raw F :=
  #[(seed : F), (seed + 1 : F), 1]

/-- Deterministic raw probe stream used by the default splitter. -/
def cantorZassenhausProbePolynomials {F : Type*} [Field F] [BEq F]
    (count : Nat) : Array (CPolynomial.Raw F) :=
  (List.range count).foldl
    (fun probes seed =>
      (probes.push (affineProbe seed)).push (quadraticProbe seed))
    #[]

/-- A fuel/probe budget derived from the current raw polynomial size. -/
def defaultProbeBudget {F : Type*} (p : CPolynomial.Raw F) : Nat :=
  4 * p.size + 32

/-- Default deterministic raw splitter implementation. -/
def deterministicLinearFactorsWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (p : CPolynomial.Raw F) : Array (CPolynomial.Raw F) :=
  let p := CPolynomial.Raw.monicNormalize p
  let budget := defaultProbeBudget p
  cantorZassenhausLinearFactorsWithFuelWith M D q
    (cantorZassenhausProbePolynomials budget) budget p

/-- Default deterministic raw splitter implementation with the default raw backends. -/
def deterministicLinearFactors {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (q : Nat) (p : CPolynomial.Raw F) : Array (CPolynomial.Raw F) :=
  deterministicLinearFactorsWith CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive q p

end FiniteField

end Roots

end Raw

namespace Roots

namespace FiniteField

/-- Boolean check that `factor` is a proper nonunit factor candidate of `p`. -/
def isNontrivialPolynomialFactor {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (factor p : CPolynomial F) : Bool :=
  !(factor == 0) && !(factor == 1) && !(factor == p)

/-- Monic quotient used after finding a split candidate. -/
def monicQuotient {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p factor : CPolynomial F) : CPolynomial F :=
  CPolynomial.ofArray (CPolynomial.Raw.Roots.FiniteField.monicQuotient p.val factor.val)

/-- Try one deterministic split probe.

The first gcd catches roots where the probe itself vanishes. If that is
trivial, the second gcd uses the quadratic-character exponent `(q - 1) / 2`.
-/
def cantorZassenhausSplitWithProbeWith? {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (p probe : CPolynomial F) : Option (CPolynomial F × CPolynomial F) :=
  match CPolynomial.Raw.Roots.FiniteField.cantorZassenhausSplitWithProbeWith?
      M D q p.val probe.val with
  | none => none
  | some split => some (CPolynomial.ofArray split.1, CPolynomial.ofArray split.2)

/-- Try one deterministic split probe with the default raw backends. -/
def cantorZassenhausSplitWithProbe? {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (q : Nat) (p probe : CPolynomial F) : Option (CPolynomial F × CPolynomial F) :=
  cantorZassenhausSplitWithProbeWith? CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive q p probe

/-- Try a deterministic stream of Cantor-Zassenhaus probes. -/
def cantorZassenhausSplitWith? {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : Array (CPolynomial F)) (p : CPolynomial F) :
    Option (CPolynomial F × CPolynomial F) :=
  let rawProbes := probes.map (fun probe => probe.val)
  match CPolynomial.Raw.Roots.FiniteField.cantorZassenhausSplitWith? M D q rawProbes p.val with
  | none => none
  | some split => some (CPolynomial.ofArray split.1, CPolynomial.ofArray split.2)

/-- Try a deterministic stream of Cantor-Zassenhaus probes with the default raw backends. -/
def cantorZassenhausSplit? {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (q : Nat) (probes : Array (CPolynomial F)) (p : CPolynomial F) :
    Option (CPolynomial F × CPolynomial F) :=
  cantorZassenhausSplitWith? CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive q probes p

/-- Recursively split a squarefree product of linear factors.

When fuel or probes are insufficient for a composite factor, the unresolved
factor contributes no roots. Public root extraction remains sound because all
candidate roots are validated against the original polynomial.
-/
def cantorZassenhausLinearFactorsWithFuelWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : Array (CPolynomial F)) :
    Nat → CPolynomial F → Array (CPolynomial F)
  | fuel, p =>
      let rawProbes := probes.map (fun probe => probe.val)
      (CPolynomial.Raw.Roots.FiniteField.cantorZassenhausLinearFactorsWithFuelWith
          M D q rawProbes fuel p.val).map CPolynomial.ofArray

/-- Recursively split a squarefree product of linear factors with the default raw backends. -/
def cantorZassenhausLinearFactorsWithFuel {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (q : Nat) (probes : Array (CPolynomial F)) :
    Nat → CPolynomial F → Array (CPolynomial F) :=
  cantorZassenhausLinearFactorsWithFuelWith CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive q probes

/-- A deterministic affine probe `X + seed`. -/
def affineProbe {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (seed : Nat) : CPolynomial F :=
  CPolynomial.ofArray (CPolynomial.Raw.Roots.FiniteField.affineProbe seed)

/-- A deterministic quadratic probe `X^2 + (seed + 1) X + seed`. -/
def quadraticProbe {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (seed : Nat) : CPolynomial F :=
  CPolynomial.ofArray (CPolynomial.Raw.Roots.FiniteField.quadraticProbe seed)

/-- Deterministic probe stream used by the default splitter. -/
def cantorZassenhausProbePolynomials {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (count : Nat) : Array (CPolynomial F) :=
  (CPolynomial.Raw.Roots.FiniteField.cantorZassenhausProbePolynomials count).map
    CPolynomial.ofArray

/-- A fuel/probe budget derived from the current polynomial size. -/
def defaultProbeBudget {F : Type*} [Zero F] (p : CPolynomial F) : Nat :=
  4 * p.val.size + 32

/-- Default deterministic splitter implementation. -/
def deterministicLinearFactorsWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (p : CPolynomial F) :
    Array (CPolynomial F) :=
  (CPolynomial.Raw.Roots.FiniteField.deterministicLinearFactorsWith M D q p.val).map
    CPolynomial.ofArray

/-- Default deterministic splitter implementation with the default raw backends. -/
def deterministicLinearFactors {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (q : Nat) (p : CPolynomial F) : Array (CPolynomial F) :=
  deterministicLinearFactorsWith CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive q p

end FiniteField

end Roots

end CPolynomial

end CompPoly
