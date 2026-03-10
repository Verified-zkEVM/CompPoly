 /-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Desmond Coles
 -/
import CompPoly.Univariate.Raw.Ops

namespace CompPoly

namespace CPolynomial.Raw

variable {R : Type*}

section Division

variable [Ring R] [BEq R]

/-- Division with remainder by a monic polynomial using polynomial long division. -/
def divModByMonicAux [Field R] (p : CPolynomial.Raw R) (q : CPolynomial.Raw R) :
    CPolynomial.Raw R × CPolynomial.Raw R :=
  go p.size p q
where
  go : Nat → CPolynomial.Raw R → CPolynomial.Raw R → CPolynomial.Raw R × CPolynomial.Raw R
  | 0, p, _ => ⟨0, p⟩
  | n+1, p, q =>
      if p.size < q.size then
        ⟨0, p⟩
      else
        let k := p.size - q.size
        let q' := C p.leadingCoeff * (q * X.pow k)
        let p' := (p - q').trim
        let (e, f) := go n p' q
        ⟨e + C p.leadingCoeff * X^k, f⟩

/-- Division of `p : CPolynomial.Raw R` by a monic `q : CPolynomial.Raw R`. -/
def divByMonic [Field R] (p : CPolynomial.Raw R) (q : CPolynomial.Raw R) :
    CPolynomial.Raw R :=
  (divModByMonicAux p q).1

/-- Modulus of `p : CPolynomial.Raw R` by a monic `q : CPolynomial.Raw R`. -/
def modByMonic [Field R] (p : CPolynomial.Raw R) (q : CPolynomial.Raw R) :
    CPolynomial.Raw R :=
  (divModByMonicAux p q).2

/-- Division of two `CPolynomial.Raw`s. -/
def div [Field R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (C (q.leadingCoeff)⁻¹ • p).divByMonic (C (q.leadingCoeff)⁻¹ * q)

/-- Modulus of two `CPolynomial.Raw`s. -/
def mod [Field R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (C (q.leadingCoeff)⁻¹ • p).modByMonic (C (q.leadingCoeff)⁻¹ * q)

instance [Field R] : Div (CPolynomial.Raw R) := ⟨div⟩
instance [Field R] : Mod (CPolynomial.Raw R) := ⟨mod⟩

end Division

end CPolynomial.Raw

end CompPoly
