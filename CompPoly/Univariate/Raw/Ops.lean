/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Desmond Coles,
  Natalie Klaus, Dimitris Mitsios
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

variable {S : Type*}

/-- Evaluates a `CPolynomial.Raw` at `x : S` using a ring homomorphism `f : R →+* S`.

  Computes `f(a₀) + f(a₁) * x + f(a₂) * x² + ...` where `aᵢ` are the coefficients.  -/
def eval₂ [Semiring R] [Semiring S] (f : R →+* S) (x : S) (p : CPolynomial.Raw R) : S :=
  p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + f a * x ^ i) 0

/-- Evaluates a `CPolynomial.Raw` at `x : S` using Horner's method.

  Computes `f(aₙ) + x * (f(aₙ₋₁) + x * (... + x * f(a₀)))` via a right fold. -/
@[inline, specialize]
def eval₂Horner [Semiring R] [Semiring S] (f : R →+* S) (x : S) (p : CPolynomial.Raw R) : S :=
  p.foldr (fun a acc => acc * x + f a) 0

/-- Evaluates a `CPolynomial.Raw` at a given value -/
@[inline, specialize]
def eval [Semiring R] (x : R) (p : CPolynomial.Raw R) : R :=
  p.eval₂ (RingHom.id R) x

/-- Raw addition: pointwise sum of coefficient arrays (padded to equal length).

  The result may have trailing zeros and should be trimmed for canonical form. -/
@[inline, specialize]
def addRaw [Zero R] [Add R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  let ⟨p', q'⟩ := Array.matchSize p q 0
  .mk (Array.zipWith (· + ·) p' q' )

/-- Addition of two `CPolynomial.Raw`s, with result trimmed. -/
@[inline, specialize]
def add [Zero R] [Add R] [BEq R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  addRaw p q |> trim

section SMulDefs

/-- Scalar multiplication: multiplies each coefficient by `r`. -/
@[inline, specialize]
def smul [Mul R] (r : R) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  .mk (Array.map (fun a => r * a) p)

/-- Raw scalar multiplication by a natural number (may have trailing zeros). -/
@[inline, specialize]
def nsmulRaw [Semiring R] (n : ℕ) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  .mk (Array.map (fun a => n * a) p)

/-- Scalar multiplication of `CPolynomial.Raw` by a natural number, with result trimmed. -/
@[inline, specialize]
def nsmul [Semiring R] [BEq R] (n : ℕ) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  nsmulRaw n p |> trim

end SMulDefs

section MulPowXDefs

/-- Multiplication by `X^i`: shifts coefficients right by `i` positions (prepends `i` zeros). -/
@[inline, specialize]
def mulPowX [Zero R] (i : Nat) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  .mk (Array.replicate i 0 ++ p)

/-- Multiplication of a `CPolynomial.Raw` by `X`, reduces to `mulPowX 1`. -/
@[inline, specialize]
def mulX [Zero R] (p : CPolynomial.Raw R) : CPolynomial.Raw R := p.mulPowX 1

end MulPowXDefs

/-- Multiplication using the naive `O(n²)` algorithm: `Σᵢ (aᵢ * q) * X^i`. -/
@[inline, specialize]
def mul [Semiring R] [BEq R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc.add <| (smul a q).mulPowX i) (mk #[])

/-- Exponentiation of a `CPolynomial.Raw` by a natural number `n` via repeated multiplication.
This is the specification; `powBySq` is the efficient O(log n) implementation. -/
@[inline, specialize]
def pow [Semiring R] [BEq R] (p : CPolynomial.Raw R) (n : Nat) : CPolynomial.Raw R :=
  (mul p)^[n] (C 1)

/-- Exponentiation via repeated squaring: $ O(\log n) $ multiplications
instead of $ O(n) $.

For $ n > 0 $, computes $ p ^ n $ by recursing on $ n / 2 $:
* If $ n $ is even: $ (p ^ {n/2})^2 $
* If $ n $ is odd:  $ p \cdot (p ^ {n/2})^2 $
-/
@[inline, specialize]
def powBySq [Semiring R] [BEq R] (p : CPolynomial.Raw R) : Nat → CPolynomial.Raw R
  | 0 => C 1
  | n + 1 =>
    let half := powBySq p ((n + 1) / 2)
    let sq := mul half half
    if (n + 1) % 2 = 0 then sq else mul p sq
  decreasing_by omega

instance : Zero (CPolynomial.Raw R) := ⟨#[]⟩
instance [One R] : One (CPolynomial.Raw R) := ⟨C 1⟩
instance [Zero R] [Add R] [BEq R] : Add (CPolynomial.Raw R) := ⟨add⟩
instance [Mul R] : SMul R (CPolynomial.Raw R) := ⟨smul⟩
instance [Semiring R] [BEq R] : SMul ℕ (CPolynomial.Raw R) := ⟨nsmul⟩
instance [Semiring R] [BEq R] : Mul (CPolynomial.Raw R) := ⟨mul⟩
instance [Semiring R] [BEq R] : Pow (CPolynomial.Raw R) Nat := ⟨pow⟩
instance [NatCast R] : NatCast (CPolynomial.Raw R) := ⟨fun n => C (n : R)⟩

/-- Upper bound on degree: `size - 1` if non-empty, `⊥` if empty. -/
def degreeBound (p : CPolynomial.Raw R) : WithBot Nat :=
  match p.size with
  | 0 => ⊥
  | .succ n => n

/-- Convert `degreeBound` to a natural number by sending `⊥` to `0`. -/
def natDegreeBound (p : CPolynomial.Raw R) : Nat :=
  (degreeBound p).getD 0

/-- Check if a `CPolynomial.Raw` is monic, i.e. its leading coefficient is 1. -/
def monic [Zero R] [One R] [BEq R] (p : CPolynomial.Raw R) : Bool := p.leadingCoeff == 1

/-- Pseudo-division by `X`: removes the constant term and shifts remaining coefficients left. -/
def divX (p : CPolynomial.Raw R) : CPolynomial.Raw R := p.extract 1 p.size

end Semiring

section Ring

/-- Negation of a `CPolynomial.Raw`. -/
@[inline, specialize]
def neg [Neg R] (p : CPolynomial.Raw R) : CPolynomial.Raw R := p.map (fun a => -a)

/-- Subtraction of two `CPolynomial.Raw`s. -/
@[inline, specialize]
def sub [Zero R] [Add R] [Neg R] [BEq R]
    (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  p.add q.neg

instance [Neg R] : Neg (CPolynomial.Raw R) := ⟨neg⟩
instance [Zero R] [Add R] [Neg R] [BEq R] : Sub (CPolynomial.Raw R) := ⟨sub⟩
instance [IntCast R] : IntCast (CPolynomial.Raw R) := ⟨fun n => C (n : R)⟩

/-- Erase the coefficient at index `n`: same as `p` except `coeff n = 0`, then trimmed. -/
def erase [Zero R] [Add R] [Neg R] [BEq R] [DecidableEq R]
    (n : ℕ) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  p - monomial n (p.coeff n)

end Ring

end Operations

end CPolynomial.Raw

end CompPoly
