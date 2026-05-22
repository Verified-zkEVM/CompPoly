/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.Basic

/-!
# Many-Polynomial Evaluation

Executable evaluators for the workload with many dense univariate polynomials
and one shared evaluation point.
-/

namespace CompPoly
namespace CPolynomial
namespace ManyEval

variable {R : Type*}

/-- Maximum stored coefficient-array size across a polynomial batch. -/
def maxCoeffSize [Zero R] (polys : Array (CPolynomial R)) : Nat :=
  polys.foldl (fun acc p ↦ Nat.max acc p.size) 0

/-- Build powers `1, x, ..., x^(limit-1)` by recurrence. -/
@[inline, specialize]
def powerTableLoop [Mul R] (x : R) (limit i : Nat) (pow : R)
    (acc : Array R) : Array R :=
  if i < limit then
    powerTableLoop x limit (i + 1) (pow * x) (acc.push pow)
  else
    acc
termination_by limit - i
decreasing_by omega

/-- Build the first `limit` powers of `x`. -/
@[inline, specialize]
def powerTable [One R] [Mul R] (x : R) (limit : Nat) : Array R :=
  powerTableLoop x limit 0 1 #[]

/-- Evaluate one coefficient array against a precomputed power table. -/
@[inline, specialize]
def evalWithPowersLoop [Add R] [Mul R] (coeffs powers : Array R)
    (limit : Nat) (hcoeffs : limit ≤ coeffs.size) (hpowers : limit ≤ powers.size)
    (i : Nat) (acc : R) : R :=
  if h : i < limit then
    let coeff := coeffs[i]'(Nat.lt_of_lt_of_le h hcoeffs)
    let pow := powers[i]'(Nat.lt_of_lt_of_le h hpowers)
    evalWithPowersLoop coeffs powers limit hcoeffs hpowers (i + 1) (acc + coeff * pow)
  else
    acc
termination_by limit - i
decreasing_by omega

/-- Evaluate one coefficient array against a precomputed power table. -/
@[inline, specialize]
def evalWithPowers [Zero R] [Add R] [Mul R] (coeffs powers : Array R) : R :=
  let limit := Nat.min coeffs.size powers.size
  evalWithPowersLoop coeffs powers limit (Nat.min_le_left _ _) (Nat.min_le_right _ _) 0 0

end ManyEval

/-- Evaluate each polynomial at the shared point using independent Horner passes. -/
@[inline, specialize]
def evalManyHorner [Semiring R] (polys : Array (CPolynomial R)) (x : R) : Array R :=
  polys.map fun p ↦ p.evalHorner x

/-- Evaluate a polynomial batch against a precomputed power table. -/
@[inline, specialize]
def ManyEval.evalManyWithPowersLoop [Semiring R] (polys : Array (CPolynomial R))
    (powers : Array R) (i : Nat) (acc : Array R) : Array R :=
  if h : i < polys.size then
    let p := polys[i]'h
    ManyEval.evalManyWithPowersLoop polys powers (i + 1)
      (acc.push (ManyEval.evalWithPowers p.val powers))
  else
    acc
termination_by polys.size - i
decreasing_by omega

/--
Evaluate many polynomials at a shared point by reusing the powers of the point.

This operates on `Array (CPolynomial R)` input and uses a scalar accumulator
for each polynomial.
-/
@[inline, specialize]
def evalManySharedPowers [Semiring R] (polys : Array (CPolynomial R)) (x : R) :
    Array R :=
  ManyEval.evalManyWithPowersLoop polys
    (ManyEval.powerTable x (ManyEval.maxCoeffSize polys)) 0 #[]

end CPolynomial
end CompPoly
