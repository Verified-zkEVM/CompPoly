/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
import CompPoly.Bivariate.Kronecker
import CompPoly.Univariate.NTT.KoalaBear

/-!
  # Kronecker test helpers

  Shared KoalaBear data used by both the Kronecker test and the benchmark: deterministic
  operand builders, the NTT domain selector, and the `kronWith` pipeline taking the
  univariate multiplication as a parameter. Built on the efficient `kroneckerPackFast` /
  `kroneckerUnpackFast`.
-/

namespace CompPoly
namespace CBivariate
namespace TestCommon

/-- KoalaBear field abbreviation. -/
abbrev F := _root_.KoalaBear.Field

/-- Best-fitting KoalaBear NTT domain for a required convolution length. -/
def bestDomainForLength? (requiredLen : Nat) :
    Option (CPolynomial.NTT.FittingDomain F requiredLen) :=
  CPolynomial.NTT.bestDomainForLength? _root_.KoalaBear.twoAdicity
    CPolynomial.NTT.KoalaBear.domainOfLogN (by intro _ _; rfl) requiredLen

/-- Wrap a raw coefficient array as a canonical polynomial. -/
def canon {α : Type} [Zero α] [BEq α] [LawfulBEq α]
    (arr : CPolynomial.Raw α) : CPolynomial α :=
  ⟨arr.trim, CPolynomial.Raw.Trim.isCanonical_trim arr⟩

/-- Deterministic univariate column in `X` of length `degX`. -/
def mkCol (degX seed : Nat) : CPolynomial F :=
  canon (Array.ofFn (fun i : Fin degX ↦
    (((i.1 + 1) * seed + i.1 * i.1 + 17 : Nat) : F)))

/-- Deterministic bivariate polynomial with `degY` columns, each of X-length `degX`. -/
def mkBiv (degY degX seed : Nat) : CBivariate F :=
  canon (Array.ofFn (fun j : Fin degY ↦ mkCol degX (seed + 7 * j.1 + 1)))

/-- Kronecker pipeline parameterised by the univariate multiplication backend.

Uses the verified efficient `kroneckerPackFast` / `kroneckerUnpackFast` (both proven equal
to the `kroneckerPack` / `kroneckerUnpack` spec; see `kroneckerUnpackFast_mul`). -/
@[inline] def kronWith (mulU : CPolynomial F → CPolynomial F → CPolynomial F)
    (D : Nat) (p q : CBivariate F) : CBivariate F :=
  kroneckerUnpackFast D (mulU (kroneckerPackFast D p) (kroneckerPackFast D q))

end TestCommon
end CBivariate
end CompPoly
