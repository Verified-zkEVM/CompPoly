import CompPoly.Univariate.Quotient

open CompPoly
open CompPoly.CPolynomial
open Trim

theorem CompPoly.CPolynomial.QuotientCPolynomial.add_mul_equiv_proof {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p q r : CPolynomial R) :
    Trim.equiv ((p + q) * r) (p * r + q * r) := by
  unfold Trim.equiv
  intro i
  rw [coeff_add]
  rw [mul_coeff, mul_coeff, mul_coeff]
  let f : ℕ → R := fun j => p.coeff j * r.coeff (i - j)
  let g : ℕ → R := fun j => q.coeff j * r.coeff (i - j)
  have hfun :
      (fun acc j => acc + (p + q).coeff j * r.coeff (i - j)) =
        (fun acc j => acc + (f j + g j)) := by
    funext acc j
    rw [coeff_add]
    simp [f, g, add_mul, add_assoc, add_left_comm, add_comm]
  rw [hfun]
  simpa [f, g] using
    (QuotientCPolynomial.range_foldl_add_distrib_proof (f := f) (g := g) (n := i + 1))

theorem CompPoly.CPolynomial.QuotientCPolynomial.right_distrib_proof {R : Type*} [Ring R] [BEq R] [LawfulBEq R] :
    ∀ (a b c : QuotientCPolynomial R), (a + b) * c = a * c + b * c := by
  intro a b c
  refine Quotient.inductionOn₃ a b c ?_
  intro p q r
  apply Quotient.sound
  simpa using CompPoly.CPolynomial.QuotientCPolynomial.add_mul_equiv_proof p q r


