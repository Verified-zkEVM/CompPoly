/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Desmond Coles, Valerii Huhnin
-/
import CompPoly.Univariate.Raw.Ops

/-!
# Raw Univariate Polynomial Division

Division algorithms for raw computable univariate polynomials.
-/

namespace CompPoly

namespace CPolynomial.Raw

variable {R : Type*}

section Division

variable [BEq R]

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

/-- Subtract `scale * q * X^shift` from `p` without using general polynomial multiplication. -/
@[inline, specialize]
def subScaledShift [Field R] (p q : CPolynomial.Raw R) (scale : R) (shift : Nat) :
    CPolynomial.Raw R :=
  let coeffs := Array.ofFn (n := p.size) fun j : Fin p.size ↦
    let i := j.val - shift
    let subtractCoeff := if shift ≤ j.val ∧ i < q.size then scale * q.coeff i else 0
    p.coeff j.val - subtractCoeff
  (CPolynomial.Raw.mk coeffs).trim

/-- Remainder-only long division by a monic polynomial.

Unlike `modByMonic`, this does not compute the quotient and avoids the general
polynomial multiplications used by each cancellation step. It is intended as an
executable implementation for the canonical `modByMonic` specification.
-/
@[inline, specialize]
def modByMonicRemainderOnly [Field R] (p : CPolynomial.Raw R) (q : CPolynomial.Raw R) :
    CPolynomial.Raw R :=
  go p.size p q
where
  go : Nat → CPolynomial.Raw R → CPolynomial.Raw R → CPolynomial.Raw R
  | 0, p, _ => p
  | n + 1, p, q =>
      if p.size < q.size then
        p
      else
        let k := p.size - q.size
        let p' := subScaledShift p q p.leadingCoeff k
        go n p' q

/-- Inverse modulo `X^k`, using Newton iteration and the supplied low-product backend. -/
@[inline, specialize]
def inverseModX [Field R] [LawfulBEq R] (M : MulLowContext R) (k : Nat)
    (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  if k = 0 then
    #[]
  else
    go (k + 1) 1 (C (p.coeff 0)⁻¹)
where
  go : Nat → Nat → CPolynomial.Raw R → CPolynomial.Raw R
  | 0, _, g => truncate k g
  | fuel + 1, n, g =>
      if k ≤ n then
        truncate k g
      else
        let next := Nat.min k (2 * n)
        let fg := M.mulLow next p g
        let correction := C (2 : R) - fg
        let g' := M.mulLow next g correction
        go fuel next g'

/--
Remainder by a monic polynomial through reversal and truncated products.

For canonical monic inputs this computes the quotient from the reversed divisor
inverse modulo `X^k`, then subtracts only the low coefficients needed for the
remainder. Inputs outside that executable contract fall back to the
remainder-only implementation.
-/
@[inline, specialize]
def modByMonicByReversal [Field R] [LawfulBEq R] (M : MulLowContext R)
    (p : CPolynomial.Raw R) (q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  if p.trim == p && q.trim == q && q.leadingCoeff == 1 then
    if p.size < q.size then
      p
    else
      let k := p.size - q.size + 1
      let remainderLen := q.size - 1
      let revP := reverse p.size p
      let revQ := reverse q.size q
      let invRevQ := inverseModX M k revQ
      let quotientRev := M.mulLow k revP invRevQ
      let quotient := reverse k quotientRev
      let productLow := M.mulLow remainderLen q quotient
      truncate remainderLen p - productLow
  else
    modByMonicRemainderOnly p q

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
