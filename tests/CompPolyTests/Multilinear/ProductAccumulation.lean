/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Multilinear.Basic
public import CompPoly.Multilinear.Basic

/-!
# Product accumulation and coefficient evaluation regressions

An integer-pair accumulator exercises a nontrivial additive reduction. The negative controls
separately show why the product equation and preservation of addition are required.
-/

public meta section

namespace CompPolyTests.ProductAccumulation

open CompPoly

private def pairReduce : ℤ × ℤ →+ ℤ :=
  AddMonoidHom.fst ℤ ℤ + AddMonoidHom.snd ℤ ℤ

private def pairProduct (a b : ℤ) : ℤ × ℤ := (a * b + a, -a)

private theorem pairReduce_pairProduct (a b : ℤ) : pairReduce (pairProduct a b) = a * b := by
  change a * b + a + -a = a * b
  rw [add_neg_cancel_right]

example {n : ℕ} (init : ℤ × ℤ) (a b : Vector ℤ n) :
    pairReduce (Vector.accumulateProducts pairProduct init a b) =
      pairReduce init + Vector.dotProduct a b :=
  Vector.reduce_accumulateProducts pairReduce pairProduct pairReduce_pairProduct init a b

example {R : Type*} [AddMonoid R] [Mul R] {n : ℕ} (init : R) (a b : Vector R n) :
    Vector.accumulateProducts (· * ·) init a b = init + Vector.dotProduct a b :=
  Vector.accumulateProducts_mul init a b

-- Empty input preserves the complete initial accumulator, including its reduction.
#guard Vector.accumulateProducts pairProduct (8, -3) #v[] #v[] == (8, -3)
#guard pairReduce (Vector.accumulateProducts pairProduct (8, -3) #v[] #v[]) == 5

-- The two accumulator components can cancel only after reduction.
#guard Vector.accumulateProducts pairProduct 0 #v[3, 3] #v[5, -5] == (6, -6)
#guard pairReduce (Vector.accumulateProducts pairProduct 0 #v[3, 3] #v[5, -5]) == 0
#guard pairReduce (Vector.accumulateProducts pairProduct (7, -2) #v[2, 3] #v[4, 5]) == 28

private def wrongProduct (a b : ℤ) : ℤ × ℤ := (a * b + 1, 0)

-- Additive reduction alone does not admit an incorrect product constructor.
example : ¬ ∀ a b, pairReduce (wrongProduct a b) = a * b := by
  intro h
  have hzero := h 0 0
  exact (by decide : pairReduce (wrongProduct 0 0) ≠ 0 * 0) hzero

#guard pairReduce (Vector.accumulateProducts wrongProduct 0 #v[1] #v[1]) !=
  Vector.dotProduct (#v[1] : Vector ℤ 1) #v[1]

-- Preserving individual products does not suffice for a nonadditive reduction.
private def nonlinearReduce (x : ℤ × ℤ) : ℤ := x.1 * x.2
private def taggedProduct (a b : ℤ) : ℤ × ℤ := (a * b, 1)

example (a b : ℤ) : nonlinearReduce (taggedProduct a b) = a * b := mul_one _

#guard nonlinearReduce (Vector.accumulateProducts taggedProduct 0 #v[1, 1] #v[1, 1]) == 4
#guard Vector.dotProduct (#v[1, 1] : Vector ℤ 2) #v[1, 1] == 2

example {n : ℕ} (p : CMlPolynomial ℤ n) (x : Vector ℤ n) :
    CMlPolynomial.evalWithProducts pairProduct pairReduce p x = CMlPolynomial.eval p x :=
  CMlPolynomial.evalWithProducts_eq_eval pairProduct pairReduce pairReduce_pairProduct p x

-- The first point coordinate multiplies coefficient index 1, in little-endian order.
#guard CMlPolynomial.evalWithProducts pairProduct pairReduce #v[1, 2, 3, 4] #v[5, 7] == 172
#guard CMlPolynomial.evalWithProducts pairProduct pairReduce #v[1, 2, 3, 4] #v[7, 5] == 170
#guard CMlPolynomial.evalWithProducts pairProduct pairReduce #v[1, 2, 3, 4] #v[0, 1] == 4
#guard CMlPolynomial.evalWithProducts pairProduct pairReduce #v[17] #v[] == 17

end CompPolyTests.ProductAccumulation
