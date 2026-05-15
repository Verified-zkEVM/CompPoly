/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu, Valerii Huhnin
-/
import CompPoly.Univariate.Raw
import Mathlib.Data.Nat.Log
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

/-- The domain with the inverse root, used by inverse NTT butterflies. -/
def inverse (D : Domain R) : Domain R where
  logN := D.logN
  omega := D.omegaInv
  primitive := by
    simpa [omegaInv] using D.primitive.inv
  natCast_ne_zero := D.natCast_ne_zero

/-- Multiplicative inverse of the domain size in `R`. -/
@[inline] def nInv (D : Domain R) : R := ((D.n : Nat) : R)⁻¹

@[simp] lemma n_pos (D : Domain R) : 0 < D.n := by
  simp [n]

@[simp] lemma n_ne_zero (D : Domain R) : D.n ≠ 0 := by
  exact Nat.ne_of_gt D.n_pos

section RawHelpers

variable [BEq R]

/-- Required convolution length for multiplying `p` and `q`. -/
def requiredLength (p q : CPolynomial.Raw R) : Nat :=
  if p.trim.size = 0 ∨ q.trim.size = 0 then
    0
  else
    p.trim.size + q.trim.size - 1

theorem requiredLength_eq_zero_of_left_trim_size_zero
    (p q : CPolynomial.Raw R) (hp : p.trim.size = 0) :
    requiredLength p q = 0 := by
  simp [requiredLength, hp]

theorem requiredLength_eq_zero_of_right_trim_size_zero
    (p q : CPolynomial.Raw R) (hq : q.trim.size = 0) :
    requiredLength p q = 0 := by
  simp [requiredLength, hq]

theorem requiredLength_eq_of_trim_size_pos
    (p q : CPolynomial.Raw R) (hp : 0 < p.trim.size) (hq : 0 < q.trim.size) :
    requiredLength p q = p.trim.size + q.trim.size - 1 := by
  have hp0 : p.trim.size ≠ 0 := Nat.ne_of_gt hp
  have hq0 : q.trim.size ≠ 0 := Nat.ne_of_gt hq
  simp [requiredLength, hp0, hq0]

/-- Whether domain `D` is large enough for multiplying `p` and `q`. -/
def fits (D : Domain R) (p q : CPolynomial.Raw R) : Prop :=
  requiredLength p q ≤ D.n

/-- Truncate a polynomial to at most `m` coefficients. -/
def truncate (m : Nat) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  p.extract 0 m

end RawHelpers
end Domain

/-- The smallest radix-2 exponent that can cover a requested convolution length. -/
def bestLogN (requiredLen : Nat) : Nat :=
  Nat.clog 2 requiredLen

/-- An NTT domain bundled with proof that it covers the requested convolution length. -/
abbrev FittingDomain (R : Type*) [Field R] (requiredLen : Nat) :=
  { D : Domain R // requiredLen ≤ D.n }

/--
Generic adapter from field-specific radix-2 domain tables to a best-fitting domain lookup.

The adapter chooses `logN = Nat.clog 2 requiredLen`, then returns `none` if that exponent
is outside the supported table.
-/
def bestDomainForLength? [Field R]
    (maxLogN : Nat) (domainOfLogN : (logN : Nat) → logN ≤ maxLogN → Domain R)
    (domainOfLogN_logN : ∀ logN hlogN, (domainOfLogN logN hlogN).logN = logN)
    (requiredLen : Nat) : Option (FittingDomain R requiredLen) :=
  let logN := bestLogN requiredLen
  if hlogN : logN ≤ maxLogN then
    some ⟨domainOfLogN logN hlogN, by
      have hfit : requiredLen ≤ 2 ^ logN := by
        simpa [logN, bestLogN] using Nat.le_pow_clog (by decide : 1 < 2) requiredLen
      simpa [Domain.n, domainOfLogN_logN logN hlogN] using hfit⟩
  else
    none

end NTT
end CPolynomial
end CompPoly
