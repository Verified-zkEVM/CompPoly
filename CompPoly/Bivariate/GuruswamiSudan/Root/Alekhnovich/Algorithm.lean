/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.Common
import CompPoly.Bivariate.GuruswamiSudan.Root.ShiftedSubstitution
import CompPoly.Data.Array.Lemmas

/-!
# Alekhnovich Bivariate Bounded Root Search

Executable batched `X`-adic root lifting for the Guruswami-Sudan bivariate root
phase. The public output is exactly filtered against `Q(X, p(X)) = 0` and
`degree p < k`, following Alekhnovich's lattice-based root-search approach
[Ale05].

## References

* [M. Alekhnovich, *Linear Diophantine Equations Over Polynomials and Soft
    Decoding of Reed-Solomon Codes*, IEEE Transactions on Information Theory
    51(7), 2257-2265, 2005][Ale05]
-/

namespace CompPoly

namespace GuruswamiSudan

/-- A prefix coset `prefixPoly + X^precision * g(X)`. -/
structure RootPrefix (F : Type*) [Zero F] where
  prefixPoly : CPolynomial F
  precision : Nat
deriving BEq, DecidableEq

/-- Precision requested by the Alekhnovich top-level root search.

This asks for a small margin over the exactness bound; exact filtering remains
the public soundness boundary. -/
def alekhnovichPrecisionBound {F : Type*} [Zero F] [BEq F]
    (Q : CBivariate F) (k : Nat) : Nat :=
  k + 1 +
    (List.range' 0 Q.val.size).foldl
      (fun bound y ↦ max bound ((Q.val.coeff y).natDegree + y * (k - 1)))
      0

/-- Normalized shifted residual and its stripped `X`-adic valuation. -/
structure AlekhnovichResidual (F : Type*) [Zero F] where
  valuation : Nat
  residual : CBivariate F
deriving BEq, DecidableEq

/-- Shift, truncate, strip the visible `X`-adic factor, and report the residual. -/
def shiftedResidualUpTo {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (f : CPolynomial F) (t N : Nat) :
    AlekhnovichResidual F :=
  let T := substituteYPolynomialPlusXPowerYTruncated Q f t N
  match CBivariate.xAdicOrder? T with
  | none => { valuation := N, residual := 0 }
  | some s =>
      if s < N then
        { valuation := s, residual := CBivariate.divXPower T s }
      else
        { valuation := s, residual := 0 }

/-- Compose an outer prefix with a suffix prefix returned by a residual call. -/
def composeRootPrefixes {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (outer suffix : RootPrefix F) : RootPrefix F :=
  { prefixPoly := outer.prefixPoly + shiftPolynomialByXPower suffix.prefixPoly outer.precision
    precision := outer.precision + suffix.precision }

/-- Normalize a residual by stripping an initial common `X` factor only up to the
requested precision. Returning `none` means the current equation is
unconstrained modulo the requested precision. -/
def normalizeAlekhnovichInput {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (Q : CBivariate F) (N : Nat) : Option (CBivariate F × Nat) :=
  match CBivariate.xAdicOrder? Q with
  | none => none
  | some s =>
      if s < N then
        some (CBivariate.divXPower Q s, N - s)
      else
        none

/-- Alekhnovich root prefixes with explicit fuel. -/
def alekhnovichRootPrefixesWithFuel {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) :
    Nat → CBivariate F → Nat → Array (RootPrefix F)
  | 0, _Q, _N => #[]
  | fuel + 1, Q, N =>
      if N = 0 then
        #[{ prefixPoly := 0, precision := 0 }]
      else
        match normalizeAlekhnovichInput Q N with
        | none => #[{ prefixPoly := 0, precision := 0 }]
        | some (Qnorm, Nnorm) =>
            if Nnorm = 0 then
              #[{ prefixPoly := 0, precision := 0 }]
            else if Nnorm = 1 then
              (rootsInFieldForNonzeroEquation fieldRoots
                (initialCoefficientPolynomial Qnorm)).map
                fun a ↦ { prefixPoly := CPolynomial.C a, precision := 1 }
            else
              let halfPrecision := (Nnorm + 1) / 2
              let prefixes :=
                alekhnovichRootPrefixesWithFuel fieldRoots fuel Qnorm halfPrecision
              prefixes.foldl
                (fun out rootPrefix ↦
                  let residual :=
                    shiftedResidualUpTo Qnorm rootPrefix.prefixPoly rootPrefix.precision Nnorm
                  if residual.valuation < Nnorm then
                    let suffixes :=
                      alekhnovichRootPrefixesWithFuel fieldRoots fuel
                        residual.residual (Nnorm - residual.valuation)
                    out ++ suffixes.map (fun suffix ↦ composeRootPrefixes rootPrefix suffix)
                  else
                    out.push rootPrefix)
                #[]

/-- Alekhnovich root prefixes through the requested precision. -/
def alekhnovichRootPrefixes {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) (Q : CBivariate F) (N : Nat) :
    Array (RootPrefix F) :=
  alekhnovichRootPrefixesWithFuel fieldRoots (N + 1) Q N

/-
Fuel-bounded Alekhnovich suffix completion and candidate generation.

The recursive suffix branch is the full Alekhnovich path: a low-precision
prefix is transformed into the exact shifted residual
`Q(X, f + X^t Y) / X^s`, and the remaining suffix problem is solved by the same
Alekhnovich candidate generator with one less unit of explicit fuel.
-/
mutual

/-- Finish one Alekhnovich prefix with Alekhnovich-only recursive suffix
completion. Prefixes already at precision `k` are simply truncated to the final
degree bound. -/
def finishAlekhnovichPrefixWithAlekhnovichWithFuel {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) :
    Nat → CBivariate F → Nat → RootPrefix F → Array (CPolynomial F)
  | 0, _Q, k, rootPrefix =>
      if rootPrefix.precision < k then
        #[]
      else
        #[polynomialPrefix rootPrefix.prefixPoly k]
  | fuel + 1, Q, k, rootPrefix =>
      if rootPrefix.precision < k then
        let residual := CBivariate.stripXAdicFactor
          (substituteYPolynomialPlusXPowerY Q rootPrefix.prefixPoly rootPrefix.precision)
        (alekhnovichRootCandidatesWithFuel fieldRoots fuel residual
          (k - rootPrefix.precision)).map
          fun suffix ↦
            rootPrefix.prefixPoly + shiftPolynomialByXPower suffix rootPrefix.precision
      else
        #[polynomialPrefix rootPrefix.prefixPoly k]

/-- Materialize bounded-degree candidates from Alekhnovich prefixes. -/
def alekhnovichRootCandidatesWithFuel {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) :
    Nat → CBivariate F → Nat → Array (CPolynomial F)
  | 0, Q, k =>
      if k = 0 then
        rootsYDegreeLtFromCandidates #[0] Q k
      else
        #[]
  | fuel + 1, Q, k =>
      if Q == 0 then
        #[]
      else
        let N := alekhnovichPrecisionBound Q k
        (alekhnovichRootPrefixesWithFuel fieldRoots (N + 1) Q N).foldl
          (fun out rootPrefix ↦
            out ++
              finishAlekhnovichPrefixWithAlekhnovichWithFuel fieldRoots fuel Q k
                rootPrefix)
          #[]

end

/-- Finish one Alekhnovich prefix with Alekhnovich-only suffix completion. -/
def finishAlekhnovichPrefixWithAlekhnovich {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) (Q : CBivariate F) (k : Nat)
    (rootPrefix : RootPrefix F) : Array (CPolynomial F) :=
  finishAlekhnovichPrefixWithAlekhnovichWithFuel fieldRoots (k + 1) Q k rootPrefix

/-- Materialize bounded-degree candidates from Alekhnovich prefixes. -/
def alekhnovichRootCandidates {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) (Q : CBivariate F) (k : Nat) :
    Array (CPolynomial F) :=
  alekhnovichRootCandidatesWithFuel fieldRoots (k + 1) Q k

/-- Alekhnovich bounded-degree roots, with exact final filtering and
deduplication. The zero bivariate input follows the finite-output convention
used by the Roth backend and returns no roots. -/
def alekhnovichRootsYDegreeLt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) (Q : CBivariate F) (k : Nat) :
    Array (CPolynomial F) :=
  if Q == 0 then
    #[]
  else
    (rootsYDegreeLtFromCandidates
      (alekhnovichRootCandidates fieldRoots Q k) Q k).eraseDups

end GuruswamiSudan

end CompPoly
