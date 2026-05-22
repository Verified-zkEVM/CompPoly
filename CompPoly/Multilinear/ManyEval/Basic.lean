/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Multilinear.Basic

/-!
# Many Multilinear Evaluations

Executable evaluators for many dense hypercube-form multilinear polynomials at
one shared point.
-/

namespace CompPoly
namespace CMlPolynomialEval

variable {R : Type*} {n : Nat}

/-- Evaluate each hypercube table independently with `evalMle`. -/
@[inline, specialize]
def evalManyMleLoop [CommRing R] (polys : Array (CMlPolynomialEval R n))
    (x : Vector R n) (i : Nat) (acc : Array R) : Array R :=
  if h : i < polys.size then
    let p := polys[i]
    evalManyMleLoop polys x (i + 1) (acc.push (evalMle p x))
  else
    acc
termination_by polys.size - i
decreasing_by omega

/-- Evaluate many hypercube tables by running scalar `evalMle` for each table. -/
@[inline, specialize]
def evalManyMle [CommRing R] (polys : Array (CMlPolynomialEval R n)) (x : Vector R n) :
    Array R :=
  evalManyMleLoop polys x 0 #[]

/-- Flatten polynomial values in polynomial-major order by hypercube index. -/
def valuesByPolynomial (polys : Array (CMlPolynomialEval R n)) : Array R := Id.run do
  let mut values := #[]
  for p in polys do
    for value in p.toArray do
      values := values.push value
  return values

/-- Fold one polynomial row for one MLE layer. -/
@[inline, specialize]
def foldLayeredPolyLoop [CommRing R] (current : Array R) (width nextWidth : Nat)
    (lo hi : R) (polyIdx pairIdx : Nat) (acc : Array R) : Array R :=
  if h : pairIdx < nextWidth then
    let base := polyIdx * width + 2 * pairIdx
    let value := lo * current.getD base 0 + hi * current.getD (base + 1) 0
    foldLayeredPolyLoop current width nextWidth lo hi polyIdx (pairIdx + 1)
      (acc.push value)
  else
    acc
termination_by nextWidth - pairIdx
decreasing_by omega

/-- Fold one MLE layer across all polynomials. -/
@[inline, specialize]
def foldLayeredLayerLoop [CommRing R] (current : Array R)
    (width nextWidth polyCount : Nat) (lo hi : R) (polyIdx : Nat) (acc : Array R) :
    Array R :=
  if h : polyIdx < polyCount then
    let acc := foldLayeredPolyLoop current width nextWidth lo hi polyIdx 0 acc
    foldLayeredLayerLoop current width nextWidth polyCount lo hi (polyIdx + 1) acc
  else
    acc
termination_by polyCount - polyIdx
decreasing_by omega

/-- Fold all MLE layers over a flattened polynomial-major batch. -/
@[inline, specialize]
def evalManyMleByLayersLoop [CommRing R] :
    {m : Nat} → Vector R m → Nat → Nat → Array R → Array R
  | 0, _x, _polyCount, _width, current => current
  | _m + 1, x, polyCount, width, current =>
      let r := x.head
      let nextWidth := width / 2
      let next := foldLayeredLayerLoop current width nextWidth polyCount (1 - r) r 0 #[]
      evalManyMleByLayersLoop x.tail polyCount nextWidth next

/--
Evaluate many hypercube tables together by folding one MLE layer at a time.
-/
@[inline, specialize]
def evalManyMleByLayers [CommRing R] (polys : Array (CMlPolynomialEval R n))
    (x : Vector R n) : Array R :=
  evalManyMleByLayersLoop x polys.size (2 ^ n) (valuesByPolynomial polys)

end CMlPolynomialEval
end CompPoly
