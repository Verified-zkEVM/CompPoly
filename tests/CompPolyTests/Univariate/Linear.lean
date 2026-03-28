/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Univariate.ToPoly.Degree

/-!
  # Univariate Linear Regression Tests

  Compile-time regressions for the instance-stable bounded-degree API.
-/

namespace CompPoly
namespace CPolynomial

@[reducible] private def natBeqEq : BEq Nat := ⟨fun a b => decide (a = b)⟩

private theorem nat_lawful_beq_eq : @LawfulBEq Nat natBeqEq := by
  letI : BEq Nat := natBeqEq
  refine { rfl := ?_, eq_of_beq := ?_ }
  · intro a; erw [show natBeqEq.beq a a = decide (a = a) from rfl]; simp
  · intro a b h; erw [show natBeqEq.beq a b = decide (a = b) from rfl] at h; simpa using h

@[reducible] private def natBeqSucc : BEq Nat := ⟨fun a b => decide (a.succ = b.succ)⟩

private theorem nat_lawful_beq_succ : @LawfulBEq Nat natBeqSucc := by
  letI : BEq Nat := natBeqSucc
  refine { rfl := ?_, eq_of_beq := ?_ }
  · intro a; erw [show natBeqSucc.beq a a = decide (a.succ = a.succ) from rfl]; simp
  · intro a b h
    erw [show natBeqSucc.beq a b = decide (a.succ = b.succ) from rfl] at h
    exact Nat.succ.inj <| by simpa using h

private def leftPoly : CPolynomial Nat :=
  @CPolynomial.monomial Nat _ natBeqEq nat_lawful_beq_eq _ 1 7

private def leftDegreeLT : ↥(CPolynomial.degreeLT (R := Nat) 3) := by
  refine ⟨leftPoly, ?_⟩
  rw [CPolynomial.mem_degreeLT_iff_size_le]
  simp [leftPoly, CPolynomial.monomial, CPolynomial.Raw.monomial]

section CrossInstance

local instance : BEq Nat := natBeqSucc
local instance : LawfulBEq Nat := nat_lawful_beq_succ

/-- Reuse a `CPolynomial` built under one lawful `BEq Nat` under another, with no cast. -/
private def reusedPoly : CPolynomial Nat := leftPoly

/-- Reuse a nonzero bounded-degree subtype value under a different lawful `BEq Nat`,
with no cast. -/
private def reusedDegreeLT : ↥(CPolynomial.degreeLT (R := Nat) 3) := leftDegreeLT

example : reusedPoly.coeff 1 = 7 := by
  simpa [reusedPoly, leftPoly] using CPolynomial.coeff_monomial (R := Nat) 1 1 7

example : reusedDegreeLT.1 = reusedPoly := rfl

example : reusedDegreeLT.1 ∈ CPolynomial.degreeLT (R := Nat) 3 := reusedDegreeLT.2

example : (reusedDegreeLT + reusedDegreeLT).1.coeff 1 = 14 := by
  calc
    (reusedDegreeLT + reusedDegreeLT).1.coeff 1 =
        reusedDegreeLT.1.coeff 1 + reusedDegreeLT.1.coeff 1 := by
          simpa using CPolynomial.coeff_add reusedDegreeLT.1 reusedDegreeLT.1 1
    _ = 7 + 7 := by
      congr
    _ = 14 := by norm_num

end CrossInstance

private def intPoly : CPolynomial Int :=
  CPolynomial.monomial 1 7

private def intDegreeLT : ↥(CPolynomial.degreeLT (R := Int) 3) := by
  refine ⟨intPoly, ?_⟩
  rw [CPolynomial.mem_degreeLT_iff_size_le]
  simp [intPoly, CPolynomial.monomial, CPolynomial.Raw.monomial]

example : CPolynomial.degreeLTEquiv (R := Int) 3 intDegreeLT ⟨1, by decide⟩ = 7 := by
  simpa [CPolynomial.degreeLTEquiv, CPolynomial.degreeLTCoeffs, intDegreeLT, intPoly] using
    CPolynomial.coeff_monomial (R := Int) 1 1 7

end CPolynomial
end CompPoly
