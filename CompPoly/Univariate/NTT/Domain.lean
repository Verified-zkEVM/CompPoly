/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu
-/
import CompPoly.Univariate.Raw
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# NTT Domain

This file defines the radix-2 NTT domain parameters and basic raw-polynomial
shape helpers used by forward/inverse NTT.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT

variable {R : Type*} [Field R]

/-- Parameters for a radix-2 NTT domain of size `2 ^ logN`. -/
structure Domain (R : Type*) [Field R] where
  logN : Nat
  omega : R
  primitive : IsPrimitiveRoot omega (2 ^ logN)
  natCast_ne_zero : (((2 ^ logN : Nat) : R) ≠ 0)

namespace Domain

/-- Domain size. -/
@[simp] def n (D : Domain R) : Nat := 2 ^ D.logN

/-- Index type for vectors over the domain. -/
abbrev Idx (D : Domain R) := Fin D.n

/-- The `i`-th evaluation node `omega^i`. -/
@[inline] def node (D : Domain R) (i : D.Idx) : R := D.omega ^ (i : Nat)

/-- Inverse root of unity. -/
@[inline] def omegaInv (D : Domain R) : R := D.omega⁻¹

/-- Multiplicative inverse of the domain size in `R`. -/
@[inline] def nInv (D : Domain R) : R := ((D.n : Nat) : R)⁻¹

@[simp] lemma n_pos (D : Domain R) : 0 < D.n := by
  simp [n]

@[simp] lemma n_ne_zero (D : Domain R) : D.n ≠ 0 := by
  exact Nat.ne_of_gt D.n_pos

section RawHelpers

variable [BEq R] [LawfulBEq R]

/-- Required convolution length for multiplying `p` and `q`. -/
def requiredLength (p q : CPolynomial.Raw R) : Nat :=
  p.trim.size + q.trim.size - 1

/-- Whether domain `D` is large enough for multiplying `p` and `q`. -/
def fits (D : Domain R) (p q : CPolynomial.Raw R) : Prop :=
  requiredLength p q ≤ D.n

/-- Truncate a polynomial to at most `m` coefficients. -/
def truncate (m : Nat) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  p.extract 0 m

end RawHelpers
end Domain

end NTT
end CPolynomial
end CompPoly
