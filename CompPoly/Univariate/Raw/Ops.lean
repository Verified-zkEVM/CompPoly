/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Desmond Coles
-/
import CompPoly.Univariate.Raw.Core

/-!
# Raw Univariate Polynomial Operations

Operations and evaluation lemmas for raw computable univariate polynomials.
-/

namespace CompPoly

namespace CPolynomial.Raw

variable {R : Type*}
variable {Q : Type*}

section Operations

section Semiring

variable [Semiring R] [BEq R]
variable [Semiring Q]

variable {S : Type*}

/-- Evaluates a `CPolynomial.Raw` at `x : S` using a ring homomorphism `f : R →+* S`.

  Computes `f(a₀) + f(a₁) * x + f(a₂) * x² + ...` where `aᵢ` are the coefficients.

  TODO: define an efficient version of this with caching -/
def eval₂ [Semiring S] (f : R →+* S) (x : S) (p : CPolynomial.Raw R) : S :=
  p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + f a * x ^ i) 0

/-- Evaluates a `CPolynomial.Raw` at a given value -/
@[inline, specialize]
def eval (x : R) (p : CPolynomial.Raw R) : R :=
  p.eval₂ (RingHom.id R) x

/-- Raw addition: pointwise sum of coefficient arrays (padded to equal length).

  The result may have trailing zeros and should be trimmed for canonical form. -/
@[inline, specialize]
def addRaw (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  let ⟨p', q'⟩ := Array.matchSize p q 0
  .mk (Array.zipWith (· + ·) p' q' )

/-- Addition of two `CPolynomial.Raw`s, with result trimmed. -/
@[inline, specialize]
def add (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  addRaw p q |> trim

section SMulDefs

/-- Scalar multiplication: multiplies each coefficient by `r`. -/
@[inline, specialize]
def smul (r : R) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  .mk (Array.map (fun a => r * a) p)

/-- Raw scalar multiplication by a natural number (may have trailing zeros). -/
@[inline, specialize]
def nsmulRaw (n : ℕ) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  .mk (Array.map (fun a => n * a) p)

/-- Scalar multiplication of `CPolynomial.Raw` by a natural number, with result trimmed. -/
@[inline, specialize]
def nsmul (n : ℕ) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  nsmulRaw n p |> trim

end SMulDefs

section MulPowXDefs

/-- Multiplication by `X^i`: shifts coefficients right by `i` positions (prepends `i` zeros). -/
@[inline, specialize]
def mulPowX (i : Nat) (p : CPolynomial.Raw R) : CPolynomial.Raw R := .mk (Array.replicate i 0 ++ p)

/-- Multiplication of a `CPolynomial.Raw` by `X`, reduces to `mulPowX 1`. -/
@[inline, specialize]
def mulX (p : CPolynomial.Raw R) : CPolynomial.Raw R := p.mulPowX 1

end MulPowXDefs

/-- Multiplication using the naive `O(n²)` algorithm: `Σᵢ (aᵢ * q) * X^i`. -/
@[inline, specialize]
def mul (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc.add <| (smul a q).mulPowX i) (mk #[])

/-- Exponentiation of a `CPolynomial.Raw` by a natural number `n` via repeated multiplication. -/
@[inline, specialize]
def pow (p : CPolynomial.Raw R) (n : Nat) : CPolynomial.Raw R := (mul p)^[n] (C 1)

instance : Zero (CPolynomial.Raw R) := ⟨#[]⟩
instance : One (CPolynomial.Raw R) := ⟨C 1⟩
instance : Add (CPolynomial.Raw R) := ⟨add⟩
instance : SMul R (CPolynomial.Raw R) := ⟨smul⟩
instance : SMul ℕ (CPolynomial.Raw R) := ⟨nsmul⟩
instance : Mul (CPolynomial.Raw R) := ⟨mul⟩
instance : Pow (CPolynomial.Raw R) Nat := ⟨pow⟩
instance : NatCast (CPolynomial.Raw R) := ⟨fun n => C (n : R)⟩

/-- Upper bound on degree: `size - 1` if non-empty, `⊥` if empty. -/
def degreeBound (p : CPolynomial.Raw R) : WithBot Nat :=
  match p.size with
  | 0 => ⊥
  | .succ n => n

/-- Convert `degreeBound` to a natural number by sending `⊥` to `0`. -/
def natDegreeBound (p : CPolynomial.Raw R) : Nat :=
  (degreeBound p).getD 0

/-- Check if a `CPolynomial.Raw` is monic, i.e. its leading coefficient is 1. -/
def monic (p : CPolynomial.Raw R) : Bool := p.leadingCoeff == 1

/-- Pseudo-division by `X`: removes the constant term and shifts remaining coefficients left. -/
def divX (p : CPolynomial.Raw R) : CPolynomial.Raw R := p.extract 1 p.size

end Semiring

section Ring

variable [Ring R] [BEq R]

/-- Negation of a `CPolynomial.Raw`. -/
@[inline, specialize]
def neg (p : CPolynomial.Raw R) : CPolynomial.Raw R := p.map (fun a => -a)

/-- Subtraction of two `CPolynomial.Raw`s. -/
@[inline, specialize]
def sub (p q : CPolynomial.Raw R) : CPolynomial.Raw R := p.add q.neg

instance : Neg (CPolynomial.Raw R) := ⟨neg⟩
instance : Sub (CPolynomial.Raw R) := ⟨sub⟩
instance : IntCast (CPolynomial.Raw R) := ⟨fun n => C (n : R)⟩

/-- Erase the coefficient at index `n`: same as `p` except `coeff n = 0`, then trimmed. -/
def erase [DecidableEq R] (n : ℕ) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  p - monomial n (p.coeff n)

end Ring

end Operations

end CPolynomial.Raw

end CompPoly
