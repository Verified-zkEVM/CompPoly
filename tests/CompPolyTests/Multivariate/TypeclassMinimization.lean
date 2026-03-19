/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import CompPoly.Multivariate.Operations

/-!
  # Multivariate Typeclass-Minimization Tests

  Compile-time regressions for the weakened multivariate core assumptions.
  The coefficient type below intentionally has `Zero`, `One`, `Add`, `Neg`, and `Mul`,
  but no semiring or ring structure, so these examples fail if stronger assumptions
  creep back into the API.
-/

namespace CPoly

/-- Minimal coefficient type used to pin down weakened multivariate assumptions. -/
structure MinimalCoeff where
  val : Int
  deriving DecidableEq, Repr

namespace MinimalCoeff

instance : Zero MinimalCoeff where
  zero := ⟨0⟩

instance : One MinimalCoeff where
  one := ⟨1⟩

instance : Add MinimalCoeff where
  add a b := ⟨a.val + b.val⟩

instance : Neg MinimalCoeff where
  neg a := ⟨-a.val⟩

instance : Mul MinimalCoeff where
  mul a b := ⟨a.val * b.val⟩

instance : BEq MinimalCoeff where
  beq a b := decide (a = b)

instance : ReflBEq MinimalCoeff where
  rfl := by
    intro a
    change decide (a = a) = true
    simp

instance : LawfulBEq MinimalCoeff where
  eq_of_beq := by
    intro a b h
    change decide (a = b) = true at h
    exact of_decide_eq_true h

end MinimalCoeff

namespace CMvPolynomial

open MinimalCoeff

private def x0 : Fin 2 := ⟨0, by decide⟩

private def x1 : Fin 2 := ⟨1, by decide⟩

private def collapse : Fin 2 → Fin 1 := fun _ => ⟨0, by decide⟩

example : CMvPolynomial 2 MinimalCoeff :=
  X (R := MinimalCoeff) x0

example : ℕ :=
  totalDegree <| X (R := MinimalCoeff) x0

example : CMvPolynomial 1 MinimalCoeff :=
  rename (R := MinimalCoeff) collapse (X (R := MinimalCoeff) x0)

example : CMvPolynomial 2 MinimalCoeff :=
  sumToIter <|
    X (R := MinimalCoeff) x0 +
    X (R := MinimalCoeff) x1

example (p : CMvPolynomial 2 MinimalCoeff) : CMvPolynomial 2 MinimalCoeff :=
  -p

example (p q : CMvPolynomial 2 MinimalCoeff) : CMvPolynomial 2 MinimalCoeff :=
  p - q

example (p : CMvPolynomial 1 MinimalCoeff) (q : CMvPolynomial 2 MinimalCoeff) :
    CMvPolynomial 2 MinimalCoeff :=
  p + q

example (p : CMvPolynomial 1 MinimalCoeff) (q : CMvPolynomial 2 MinimalCoeff) :
    CMvPolynomial 2 MinimalCoeff :=
  p - q

example (p : CMvPolynomial 1 MinimalCoeff) (q : CMvPolynomial 2 MinimalCoeff) :
    CMvPolynomial 2 MinimalCoeff :=
  p * q

end CMvPolynomial

end CPoly
