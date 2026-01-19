import CompPoly.Multivariate.MvPolyEquiv

/-!
# simp/grind lemmas for `CPoly.CMvPolynomial.eval`

These lemmas are meant to support proof automation (simp/grind normalization)
when reasoning about polynomial evaluation (e.g. Horner correctness proofs).
-/

namespace CPoly

open CMvPolynomial

section

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
variable (vals : Fin n → R)

@[simp]
lemma eval_add (p q : CMvPolynomial n R) :
    (p + q).eval vals = p.eval vals + q.eval vals := by
  -- rewrite both sides via Mathlib `MvPolynomial` using the equivalence
  have hpq : (p + q).eval vals = (fromCMvPolynomial (p + q)).eval vals := by
    simpa using (eval_equiv (p := p + q) (vals := vals))
  have hp : (fromCMvPolynomial p).eval vals = p.eval vals := by
    simpa using (eval_equiv (p := p) (vals := vals)).symm
  have hq : (fromCMvPolynomial q).eval vals = q.eval vals := by
    simpa using (eval_equiv (p := q) (vals := vals)).symm

  calc
    (p + q).eval vals
        = (fromCMvPolynomial (p + q)).eval vals := hpq
    _   = (fromCMvPolynomial p + fromCMvPolynomial q).eval vals := by
          simp [map_add]
    _   = (fromCMvPolynomial p).eval vals + (fromCMvPolynomial q).eval vals := by
          -- Mathlib lemma
          simpa using (MvPolynomial.eval_add (p := fromCMvPolynomial p)
                                            (q := fromCMvPolynomial q)
                                            (x := vals))
    _   = p.eval vals + q.eval vals := by
          simp [hp, hq]

@[simp]
lemma eval_mul (p q : CMvPolynomial n R) :
    (p * q).eval vals = p.eval vals * q.eval vals := by
  have hpq : (p * q).eval vals = (fromCMvPolynomial (p * q)).eval vals := by
    simpa using (eval_equiv (p := p * q) (vals := vals))
  have hp : (fromCMvPolynomial p).eval vals = p.eval vals := by
    simpa using (eval_equiv (p := p) (vals := vals)).symm
  have hq : (fromCMvPolynomial q).eval vals = q.eval vals := by
    simpa using (eval_equiv (p := q) (vals := vals)).symm

  calc
    (p * q).eval vals
        = (fromCMvPolynomial (p * q)).eval vals := hpq
    _   = (fromCMvPolynomial p * fromCMvPolynomial q).eval vals := by
          simp [map_mul]
    _   = (fromCMvPolynomial p).eval vals * (fromCMvPolynomial q).eval vals := by
          -- Mathlib lemma
          simpa using (MvPolynomial.eval_mul (p := fromCMvPolynomial p)
                                            (q := fromCMvPolynomial q)
                                            (x := vals))
    _   = p.eval vals * q.eval vals := by
          simp [hp, hq]

end

attribute [grind =] eval_add eval_mul

end CPoly
