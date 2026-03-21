/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu
-/
import CompPoly.Univariate.NTT.Domain
import CompPoly.Univariate.NTT.Forward
import CompPoly.Univariate.NTT.Inverse
import CompPoly.Univariate.Raw

/-!
# Fast Multiplication via NTT (Scaffolding)

This file wires forward NTT, pointwise multiplication, and inverse NTT into a
spec/implementation pipeline for future optimized polynomial multiplication.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace FastMul

variable {R : Type*} [Field R]

/-- Pointwise multiplication in evaluation form. -/
@[inline] def pointwiseMul (D : Domain R) (a b : Array R) : Array R :=
  Array.ofFn (fun i : D.Idx => a.getD i.1 0 * b.getD i.1 0)

@[simp] theorem size_pointwiseMul (D : Domain R) (a b : Array R) :
    (pointwiseMul D a b).size = D.n := by
  simp [pointwiseMul]

section RawMul

variable [BEq R] [LawfulBEq R]

/-- Spec pipeline for NTT-based multiplication. -/
@[inline] def fastMulSpec (D : Domain R) (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  let pHat := Forward.forwardSpec D p
  let qHat := Forward.forwardSpec D q
  let cHat := pointwiseMul D pHat qHat
  let c := Inverse.inverseSpec D cHat
  (Domain.truncate (Domain.requiredLength p q) c).trim

/-- Implementation pipeline for NTT-based multiplication. -/
@[inline] def fastMulImpl (D : Domain R) (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  let pHat := Forward.forwardImpl D p
  let qHat := Forward.forwardImpl D q
  let cHat := pointwiseMul D pHat qHat
  let c := Inverse.inverseImpl D cHat
  (Domain.truncate (Domain.requiredLength p q) c).trim

theorem fastMulImpl_correct (D : Domain R) (p q : CPolynomial.Raw R) :
    fastMulImpl D p q = fastMulSpec D p q := by
  simp [fastMulImpl, fastMulSpec, Forward.forwardImpl_correct, Inverse.inverseImpl_correct]

theorem fastMulSpec_coeff (D : Domain R) (p q : CPolynomial.Raw R) (i : Nat) :
    (fastMulSpec D p q).coeff i = (p * q).coeff i := by
  sorry

theorem fastMulSpec_eq_mul (D : Domain R) (p q : CPolynomial.Raw R)
    (hfit : Domain.fits D p q) : fastMulSpec D p q = p * q := by
  sorry

theorem fastMulImpl_eq_mul (D : Domain R) (p q : CPolynomial.Raw R)
    (hfit : Domain.fits D p q) : fastMulImpl D p q = p * q := by
  sorry

/-- Optional wrapper that uses NTT only when the operands fit the domain. -/
@[inline] def mulWithFastPath (D : Domain R) (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  if Domain.requiredLength p q ≤ D.n then fastMulImpl D p q else p * q

theorem mulWithFastPath_eq_mul (D : Domain R) (p q : CPolynomial.Raw R) :
    mulWithFastPath D p q = p * q := by
  sorry

end RawMul

end FastMul
end NTT
end CPolynomial
end CompPoly
