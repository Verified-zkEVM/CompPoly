/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
import CompPoly.Bivariate.Factor
import CompPoly.Univariate.DivisionCorrectness

/-!
# Bridge: synthetic linear division equals general monic division

Proves that the bespoke synthetic division `divByLinearY Q f` (Horner) coincides
with general monic Euclidean division of `Q` by the linear factor `Y - f`, using
the `CommRing`-general `CPolynomial.divByMonic` / `CPolynomial.modByMonic` at the
coefficient ring `CPolynomial R` (recall `CBivariate R = CPolynomial (CPolynomial R)`).

`divByLinearY_eq_divByMonic` shows the quotient equals `(divByLinearY Q f).1` and
the remainder equals `CPolynomial.C (divByLinearY Q f).2`, so `divByLinearY` is a
verified fast path for division by `Y - f`.

The proof works in the outer polynomial ring `(CPolynomial R)[Y]` (the image of
`CPolynomial.toPoly`): it rewrites the divisor as `X - C f`
(`linearYDivisor_toPoly`), establishes the Euclidean identity by transporting
`divByLinearY_spec` across the coefficient ring-equiv
(`divByLinearY_euclid_toPoly`), and concludes via
`Polynomial.div_modByMonic_unique`.
-/

namespace CompPoly

namespace CBivariate

variable {R : Type*}

/-- The linear monic divisor `Y - f`, as a bivariate polynomial
(`CBivariate R = CPolynomial (CPolynomial R)`). -/
def linearYDivisor [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (f : CPolynomial R) : CBivariate R :=
  -- `CPolynomial.X` at this nested type is `Y`; it is defeq to `CBivariate.X`.
  (CPolynomial.X : CPolynomial (CPolynomial R)) - CPolynomial.C f

/-- `toPoly` sends the linear divisor `Y - f` to `X - C f` in `(CPolynomial R)[Y]`. -/
theorem linearYDivisor_toPoly [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f : CPolynomial R) :
    CPolynomial.toPoly (linearYDivisor f) = Polynomial.X - Polynomial.C f := by
  simpa [linearYDivisor, CPolynomial.X_toPoly, CPolynomial.C_toPoly] using
    (CPolynomial.toPoly_sub (p := (CPolynomial.X : CPolynomial (CPolynomial R)))
      (q := CPolynomial.C f))

/-- The linear divisor `Y - f` is monic. -/
theorem linearYDivisor_monic [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f : CPolynomial R) :
    CPolynomial.monic (linearYDivisor f) = true := by
  have hpoly := linearYDivisor_toPoly (R := R) f
  have hmonic : (CPolynomial.toPoly (linearYDivisor f)).Monic := by
    rw [hpoly]
    exact Polynomial.monic_X_sub_C f
  exact (CPolynomial.monic_toPoly_iff (linearYDivisor f)).2 hmonic

/-- Euclidean identity for `divByLinearY` in the outer ring `(CPolynomial R)[Y]`:
`C rem + (Y - f) * quot = Q` after `toPoly`. Transports `divByLinearY_spec`
across the coefficient ring-equiv. -/
theorem divByLinearY_euclid_toPoly
    [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) :
    (CPolynomial.C (divByLinearY Q f).2).toPoly
        + CPolynomial.toPoly (linearYDivisor f) * CPolynomial.toPoly ((divByLinearY Q f).1)
      = CPolynomial.toPoly Q := by
  let e := (CPolynomial.ringEquiv (R := R)).toRingHom
  apply Polynomial.map_injective e (CPolynomial.ringEquiv (R := R)).injective
  rw [Polynomial.map_add, Polynomial.map_mul, CPolynomial.C_toPoly,
    linearYDivisor_toPoly (R := R) f]
  simp only [Polynomial.map_C, Polynomial.map_sub, Polynomial.map_X]
  simpa [e, CBivariate.toPoly_eq_map, mul_comm, add_comm, add_left_comm, add_assoc] using
    (divByLinearY_spec Q f).symm

/-- The bespoke synthetic division `divByLinearY` agrees with general monic
division by `Y - f`: the quotient matches `divByMonic`, and the constant-in-`Y`
remainder `C (divByLinearY Q f).2` matches `modByMonic`. -/
theorem divByLinearY_eq_divByMonic [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) :
    CPolynomial.divByMonic Q (linearYDivisor f) = (divByLinearY Q f).1
      ∧ CPolynomial.modByMonic Q (linearYDivisor f)
          = CPolynomial.C (divByLinearY Q f).2 := by
  let g := linearYDivisor f
  let q := (divByLinearY Q f).1
  let r := (divByLinearY Q f).2
  have hg : CPolynomial.monic g := by
    simpa [g] using linearYDivisor_monic (R := R) f
  have hg_toPoly : (CPolynomial.toPoly g).Monic :=
    (CPolynomial.monic_toPoly_iff g).1 hg
  have he : (CPolynomial.C r).toPoly + CPolynomial.toPoly g * CPolynomial.toPoly q
      = CPolynomial.toPoly Q := by
    simpa [g, q, r] using divByLinearY_euclid_toPoly (R := R) Q f
  have hdeg : ((CPolynomial.C r).toPoly).degree < (CPolynomial.toPoly g).degree := by
    rw [CPolynomial.C_toPoly, linearYDivisor_toPoly (R := R) f]
    by_cases hr : r = 0 <;> simp [hr, Polynomial.degree_X_sub_C]
  have huniq := Polynomial.div_modByMonic_unique
      (f := CPolynomial.toPoly Q) (g := CPolynomial.toPoly g)
      (q := CPolynomial.toPoly q) (r := (CPolynomial.C r).toPoly)
      hg_toPoly ⟨he, hdeg⟩
  have hdiv : CPolynomial.toPoly (CPolynomial.divByMonic Q g) = CPolynomial.toPoly q := by
    rw [CPolynomial.divByMonic_toPoly_eq_divByMonic Q g hg]
    exact huniq.1
  have hmod : CPolynomial.toPoly (CPolynomial.modByMonic Q g)
      = CPolynomial.toPoly (CPolynomial.C r) := by
    rw [CPolynomial.modByMonic_toPoly_eq_modByMonic Q g hg]
    exact huniq.2
  constructor
  · apply CPolynomial.eq_iff_coeff.2
    intro i
    have hi := congrArg (fun p : Polynomial (CPolynomial R) => p.coeff i) hdiv
    simpa only [CPolynomial.coeff_toPoly, g, q] using hi
  · apply CPolynomial.eq_iff_coeff.2
    intro i
    have hi := congrArg (fun p : Polynomial (CPolynomial R) => p.coeff i) hmod
    simpa only [CPolynomial.coeff_toPoly, g, r] using hi

end CBivariate

end CompPoly
