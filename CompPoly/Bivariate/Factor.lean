/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/

import CompPoly.Bivariate.Basic
import CompPoly.Bivariate.ToPoly

/-!
# Factorisation of Computable Bivariate Polynomials

Defines `evalYPoly` (substitute Y ↦ f(X)), `isLinearYFactor` (check
divisibility by Y - f(X)), and `divByLinearY` (synthetic division in Y).
These operations support the Roth-Ruckenstein root-finding step in
Guruswami–Sudan interpolation.
-/

namespace CompPoly

namespace CBivariate

def evalYPoly [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
  (f : CPolynomial R) (Q : CBivariate R) : CPolynomial R :=
  Q.val.eval f

def isLinearYFactor [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) : Bool :=
  evalYPoly f Q == 0

theorem evalYPoly_zero [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (f : CPolynomial R) :
    evalYPoly f (0 : CBivariate R) = 0 := by
  show (0 : CBivariate R).val.eval f = 0
  have h : (0 : CBivariate R).val = (0 : CPolynomial.Raw (CPolynomial R)) := rfl
  rw [h, ← CPolynomial.Raw.eval_toPoly_eq_eval f (0 : CPolynomial.Raw (CPolynomial R)),
    CPolynomial.Raw.toPoly_zero, Polynomial.eval_zero]

theorem evalYPoly_add [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (f : CPolynomial R) (P Q : CBivariate R) :
    evalYPoly f (P + Q) = evalYPoly f P + evalYPoly f Q := by
  show (P + Q).val.eval f = P.val.eval f + Q.val.eval f
  have h : (P + Q).val = P.val + Q.val := rfl
  rw [h, ← CPolynomial.Raw.eval_toPoly_eq_eval f (P.val + Q.val),
    ← CPolynomial.Raw.eval_toPoly_eq_eval f P.val,
    ← CPolynomial.Raw.eval_toPoly_eq_eval f Q.val,
    CPolynomial.Raw.toPoly_add, Polynomial.eval_add]

theorem isLinearYFactor_iff [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) :
    isLinearYFactor Q f = true ↔ evalYPoly f Q = 0 := by
  simp [isLinearYFactor, beq_iff_eq]

theorem evalYPoly_toPoly [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f : CPolynomial R) (Q : CBivariate R) :
    (evalYPoly f Q).toPoly = (toPoly Q).eval (f.toPoly) := by
  show (Q.val.eval f).toPoly = (toPoly Q).eval (f.toPoly)
  rw [← CPolynomial.Raw.eval_toPoly_eq_eval f Q.val]
  rw [toPoly_eq_map, Polynomial.eval_map]
  change (CPolynomial.ringEquiv (R := R)).toRingHom ((CPolynomial.toPoly Q).eval f) =
    (CPolynomial.toPoly Q).eval₂ (CPolynomial.ringEquiv (R := R)).toRingHom (f.toPoly)
  rw [show Polynomial.eval f (CPolynomial.toPoly Q) =
    (CPolynomial.toPoly Q).eval₂ (RingHom.id _) f from rfl]
  rw [Polynomial.hom_eval₂, RingHom.comp_id]
  rfl

def divByLinearY [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (Q : CBivariate R) (f : CPolynomial R) : CBivariate R × CPolynomial R :=
  let n := natDegreeY Q
  if n = 0 then (0, CPolynomial.coeff Q 0)
  else
    let a : ℕ → CPolynomial R := fun j => CPolynomial.coeff Q j
    let b_init := a n
    let (b_last, coeffs) := (List.range (n - 1)).foldl
      (fun (b, acc) k =>
        let bj := a (n - 1 - k) + f * b
        (bj, acc.push bj))
      (b_init, #[b_init])
    let rem := a 0 + f * b_last
    let quotArr : CPolynomial.Raw (CPolynomial R) := coeffs.reverse
    (⟨quotArr.trim, CPolynomial.Raw.Trim.isCanonical_trim quotArr⟩, rem)

end CBivariate

end CompPoly
