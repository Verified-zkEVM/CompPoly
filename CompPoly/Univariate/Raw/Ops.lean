/-
Copyright (c) 2025 CompPoly. All rights reserved.
Copyright (c) 2026 ArkLib Contributors (the size lemmas of `SizeCoeffLemmas`).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Desmond Coles,
  Natalie Klaus, Dimitris Mitsios, Alexander Hicks
-/
module

import all CompPoly.Univariate.Raw.Core
public import CompPoly.Univariate.Raw.Core

/-!
# Raw Univariate Polynomial Operations

Operations and evaluation lemmas for raw computable univariate polynomials.
-/

public section

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

/-- Evaluates a `CPolynomial.Raw` at a given value using Horner's method. -/
@[inline, specialize]
def evalHorner [Semiring R] (x : R) (p : CPolynomial.Raw R) : R :=
  p.eval₂Horner (RingHom.id R) x

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

/-- Right scalar multiplication: multiplies each coefficient by `r` on the right.

  Corresponds to `p.toPoly * Polynomial.C r`, in contrast to `smul` which corresponds
  to `Polynomial.C r * p.toPoly`. The distinction matters in non-commutative semirings. -/
@[inline, specialize]
def smulRight [Mul R] (r : R) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  .mk (Array.map (fun a => a * r) p)

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

/-- Multiplication accumulator using the naive `O(n²)` algorithm: `Σᵢ (aᵢ * q) * X^i`.

  The partial sums are combined with the untrimmed `addRaw`, so the result may carry
  trailing zeros and should be trimmed for canonical form. Deferring the trim to the
  end (see `mul`) avoids an `O(size)` scan after every partial sum.

  Compiled code computes `mulRaw` with `mulRawFast` (see `mulRaw_eq_mulRawFast`). -/
@[inline, specialize]
def mulRaw [Semiring R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc.addRaw <| (smul a q).mulPowX i) (mk #[])

section SizeCoeffLemmas

/-! ### Sizes and coefficients of the raw operations

The sizes count the stored coefficients, including trailing zeros. `size_smul`, `size_mulPowX`,
`size_addRaw` and `size_mulRaw` were ported from ArkLib's raw-size adapter under Apache 2.0.
The file header records their copyright. -/

/-- Scalar multiplication preserves the stored coefficient count. -/
@[simp]
theorem size_smul [Mul R] (x : R) (p : CPolynomial.Raw R) :
    (smul x p).size = p.size := by
  simp only [smul, Array.size_map]

/-- Multiplication by `X^i` retains all of the prepended zero coefficients. -/
@[simp]
theorem size_mulPowX [Zero R] (i : Nat) (p : CPolynomial.Raw R) :
    (mulPowX i p).size = i + p.size := by
  simp only [mulPowX, Array.size_append, Array.size_replicate]

/-- Padded raw addition stores the larger input size. -/
@[simp]
theorem size_addRaw [Zero Q] [Add Q] {p q : CPolynomial.Raw Q} :
    (addRaw p q).size = max p.size q.size := by
  simp only [addRaw, Array.size_zipWith, Array.size_rightpad]
  omega

/-- Coefficient `i` of `addRaw p q` is the sum of coefficient `i` of `p` and of `q`. -/
theorem add_coeff? [AddZeroClass Q] (p q : CPolynomial.Raw Q) (i : ℕ) :
    (addRaw p q).coeff i = p.coeff i + q.coeff i := by
  by_cases hi : i < (addRaw p q).size
  · rw [coeff, ← Array.getElem_eq_getD (h := hi)]
    simp only [addRaw, mk, Array.getElem_zipWith, Array.rightpad_getElem_eq_getD]
  · rw [size_addRaw, not_lt, max_le_iff] at hi
    simp [coeff, Array.getD_eq_getD_getElem?, hi.1, hi.2]

/-- Coefficient `k` of `smul a q` shifted by `i` places: `0` below `i`, and `a * q.coeff (k - i)`
from `i` on. -/
theorem smul_mulPowX_coeff [MulZeroClass R] (a : R) (q : CPolynomial.Raw R) (i k : ℕ) :
    ((smul a q).mulPowX i).coeff k = if k < i then 0 else a * q.coeff (k - i) := by
  simp only [mulPowX, smul, mk, coeff, Array.getD_eq_getD_getElem?, Array.getElem?_append,
    Array.size_replicate, Array.getElem?_replicate, Array.getElem?_map]
  split_ifs
  · rfl
  · cases q[k - i]? <;> simp

/-- Raw multiplication retains every shifted row, including padding from an empty right array. -/
theorem size_mulRaw [Semiring R] (p q : CPolynomial.Raw R) :
    (mulRaw p q).size = if p.size = 0 then 0 else q.size + p.size - 1 := by
  unfold mulRaw
  have h := Array.foldl_induction (as := p.zipIdx)
    (motive := fun i (acc : CPolynomial.Raw R) ↦ acc.size = if i = 0 then 0 else q.size + i - 1)
    (init := mk #[]) (by rfl)
    (f := fun acc ai ↦ acc.addRaw ((smul ai.1 q).mulPowX ai.2)) ?_
  · simpa only [Array.size_zipIdx] using h
  · intro i acc ih
    have hz : (p.zipIdx)[i].2 = i.val := by
      change ((p.zipIdx)[i.val]'i.isLt).2 = i.val
      rw [Array.getElem_zipIdx]
      exact Nat.zero_add _
    simp only [size_addRaw, size_mulPowX, size_smul]
    rw [hz, ih]
    by_cases hi : i.val = 0
    · simp [hi]
    · simp [hi]
      omega

/-- Coefficient `k` of `mulRaw p q` is the convolution sum of the coefficients of `p` and `q`. -/
theorem coeff_mulRaw [Semiring R] (p q : CPolynomial.Raw R) (k : ℕ) :
    (mulRaw p q).coeff k =
      ∑ i ∈ Finset.range p.size, if k < i then 0 else p.coeff i * q.coeff (k - i) := by
  unfold mulRaw
  have h := Array.foldl_induction (as := p.zipIdx)
    (motive := fun n (acc : CPolynomial.Raw R) ↦ ∀ k, acc.coeff k =
      ∑ i ∈ Finset.range n, if k < i then 0 else p.coeff i * q.coeff (k - i))
    (init := mk #[]) (fun k ↦ by simp)
    (f := fun acc ai ↦ acc.addRaw ((smul ai.1 q).mulPowX ai.2)) ?_
  · simpa only [Array.size_zipIdx] using h k
  · intro i acc ih k
    have hz : (p.zipIdx)[i] = (p.coeff i, i.val) := by
      change (p.zipIdx)[i.val]'i.isLt = _
      rw [Array.getElem_zipIdx, zero_add, Array.getElem_eq_getD 0]
    rw [hz, add_coeff?, ih, smul_mulPowX_coeff, Finset.sum_range_succ]

end SizeCoeffLemmas

section MulRawFast

/-! ### Compiled raw multiplication

`mulRawFast` computes the same array as `mulRaw`. The `@[csimp]` lemma `mulRaw_eq_mulRawFast`
makes compiled code use it. The lemma comes before `mul` and the other definitions in this file
that use `mulRaw`, because the compiler inlines or specializes `mulRaw` into them when it compiles
them, and a later `@[csimp]` lemma does not change that code. -/

/-- Raw multiplication that computes each entry of the result as one sum.

  The result is empty when `p` is empty. Otherwise it has `q.size + p.size - 1` entries, as in
  `mulRaw`. Entry `k` is the sum of the products `p[i] * q[k - i]` over the indices `i` with
  `k + 1 - q.size ≤ i < min (k + 1) p.size`, added to `0` in increasing order of `i`. Each pair
  `(i, j)` with `i < p.size` and `j < q.size` occurs in exactly one entry, so the loop makes
  `p.size * q.size` multiplications and the same number of additions. -/
@[specialize]
def mulRawFast [inst : Semiring R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  -- Structure projections of `inst`. The default instances construct `Distrib R` and
  -- `MulZeroClass R` values. Code specialized at a carrier whose instance the compiler cannot
  -- unfold, such as `ZMod n`, would construct them in every iteration of the loop.
  letI : Zero R := inst.toAddCommMonoid.toAddMonoid.toZero
  letI : Add R := inst.toAddCommMonoid.toAddMonoid.toAdd
  letI : Mul R := inst.toMonoid.toMul
  if p.size = 0 then mk #[] else
    (q.size + p.size - 1).fold (fun k _ acc ↦
        let lo := k + 1 - q.size
        let hi := min (k + 1) p.size
        acc.push ((hi - lo).fold
          (fun t ht s ↦ s + p[lo + t]'(by omega) * q[k - (lo + t)]'(by omega)) 0))
      (Array.emptyWithCapacity (q.size + p.size - 1))

/-- A `Nat.fold` that pushes `e k` at step `k` appends `e 0, …, e (n - 1)`. -/
private theorem natFold_push {n : ℕ} (e : ℕ → R) (init : Array R) :
    n.fold (fun k _ acc ↦ acc.push (e k)) init = init ++ Array.ofFn fun k : Fin n ↦ e k := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.fold_succ, ih, Array.ofFn_succ, Array.push_append]; rfl

/-- For a nonempty `p`, `mulRawFast p q` is the array of the entry sums. -/
private theorem mulRawFast_eq_ofFn [Semiring R] {p : CPolynomial.Raw R} (q : CPolynomial.Raw R)
    (hp : p.size ≠ 0) :
    mulRawFast p q = Array.ofFn fun k : Fin (q.size + p.size - 1) ↦
      (min (k.val + 1) p.size - (k.val + 1 - q.size)).fold (fun t _ s ↦
        s + p.getD (k.val + 1 - q.size + t) 0 * q.getD (k.val - (k.val + 1 - q.size + t)) 0) 0 := by
  simp only [mulRawFast, hp, ↓reduceIte]
  rw [natFold_push, Array.emptyWithCapacity_eq, Array.empty_append]
  congr! 3 with k
  funext t ht s
  rw [Array.getElem_eq_getD 0, Array.getElem_eq_getD 0]

/-- A `Nat.fold` that adds `g t` at step `t`, from `0`, computes the sum of the `g t`. -/
private theorem natFold_add_eq_sum [AddCommMonoid R] (n : ℕ) (g : ℕ → R) :
    n.fold (fun t _ acc ↦ acc + g t) 0 = ∑ t ∈ Finset.range n, g t := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.fold_succ, ih, Finset.sum_range_succ]

/-- The convolution sum over `i < p.size` is the sum over the indices `i` whose products land in
entry `k`. -/
private theorem sum_range_eq_sum_Ico [Semiring R] (p q : CPolynomial.Raw R) (k : ℕ) :
    (∑ i ∈ Finset.range p.size, if k < i then 0 else p.coeff i * q.coeff (k - i)) =
      ∑ i ∈ Finset.Ico (k + 1 - q.size) (min (k + 1) p.size), p.coeff i * q.coeff (k - i) := by
  have hsub : Finset.Ico (k + 1 - q.size) (min (k + 1) p.size) ⊆ Finset.range p.size :=
    fun i hi ↦ by simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢; omega
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [Finset.mem_Ico] at hi
    simp [show ¬k < i by omega]
  · intro i hi hi'
    simp only [Finset.mem_Ico, Finset.mem_range, not_and_or, not_le, not_lt] at hi hi'
    split_ifs with hk
    · rfl
    · have : q.size ≤ k - i := by omega
      simp [this]

/-- `mulRawFast p q` has the size of `mulRaw p q`. -/
@[simp]
theorem size_mulRawFast [Semiring R] (p q : CPolynomial.Raw R) :
    (mulRawFast p q).size = if p.size = 0 then 0 else q.size + p.size - 1 := by
  by_cases hp : p.size = 0
  · simp [mulRawFast, hp]
  · simp [mulRawFast_eq_ofFn q hp, hp]

/-- Entry `k` of `mulRawFast p q` is the convolution sum of the coefficients of `p` and `q`. -/
@[simp]
theorem getElem_mulRawFast [Semiring R] (p q : CPolynomial.Raw R) (k : ℕ)
    (hk : k < (mulRawFast p q).size) :
    (mulRawFast p q)[k] =
      ∑ i ∈ Finset.range p.size, if k < i then 0 else p.coeff i * q.coeff (k - i) := by
  have hp : p.size ≠ 0 := by rw [size_mulRawFast] at hk; split_ifs at hk <;> omega
  simp only [mulRawFast_eq_ofFn q hp, Array.getElem_ofFn]
  rw [natFold_add_eq_sum, sum_range_eq_sum_Ico, Finset.sum_Ico_eq_sum_range]

/-- Compiled code computes `mulRaw` with `mulRawFast`. -/
@[csimp]
theorem mulRaw_eq_mulRawFast : @mulRaw = @mulRawFast := by
  funext R _ p q
  refine Array.ext (by simp only [size_mulRaw, size_mulRawFast]) fun k h _ ↦ ?_
  simp only [Array.getElem_eq_getD 0 (h := h), getElem_mulRawFast]
  exact coeff_mulRaw p q k

end MulRawFast

/-- Multiplication using the naive `O(n²)` algorithm: `Σᵢ (aᵢ * q) * X^i`.

  Trims only once, at the end of the convolution fold, rather than after every
  partial sum (`mulRaw` does the untrimmed accumulation). Compiled code computes the product with
  `mulRawFast` (see `mulRaw_eq_mulRawFast`). -/
@[inline, specialize]
def mul [Semiring R] [BEq R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (mulRaw p q).trim

/-- Exponentiation of a `CPolynomial.Raw` by a natural number `n` via repeated multiplication.
This is the specification; `powBySq` is the efficient O(log n) implementation. -/
@[inline, specialize]
def pow [Semiring R] [BEq R] (p : CPolynomial.Raw R) (n : Nat) : CPolynomial.Raw R :=
  (mul p)^[n] (C 1)

/-- Repeated-squaring core that accumulates with the untrimmed `mulRaw`, deferring
the canonicalization trim to the outer `powBySq` wrapper. The output may carry
trailing zeros and is not in canonical form.

For $ n > 0 $, computes $ p ^ n $ by recursing on $ n / 2 $:
* If $ n $ is even: $ (p ^ {n/2})^2 $
* If $ n $ is odd:  $ p \cdot (p ^ {n/2})^2 $
-/
@[inline, specialize]
def powBySqUntrimmed [Semiring R] (p : CPolynomial.Raw R) : Nat → CPolynomial.Raw R
  | 0 => C 1
  | n + 1 =>
    let half := powBySqUntrimmed p ((n + 1) / 2)
    let sq := mulRaw half half
    if (n + 1) % 2 = 0 then sq else mulRaw p sq
  decreasing_by omega

/-- Exponentiation via repeated squaring: $ O(\log n) $ multiplications
instead of $ O(n) $. Delegates to `powBySqUntrimmed` and trims only once
at the end, rather than after every squaring step.
-/
@[inline, specialize]
def powBySq [Semiring R] [BEq R] (p : CPolynomial.Raw R) (n : Nat) : CPolynomial.Raw R :=
  (powBySqUntrimmed p n).trim

instance : Zero (CPolynomial.Raw R) := ⟨#[]⟩
instance [One R] : One (CPolynomial.Raw R) := ⟨C 1⟩
instance [Zero R] [Add R] [BEq R] : Add (CPolynomial.Raw R) := ⟨add⟩
instance [Mul R] : SMul R (CPolynomial.Raw R) := ⟨smul⟩
instance [Semiring R] [BEq R] : SMul ℕ (CPolynomial.Raw R) := ⟨nsmul⟩
instance [Semiring R] [BEq R] : Mul (CPolynomial.Raw R) := ⟨mul⟩
instance [Semiring R] [BEq R] : Pow (CPolynomial.Raw R) Nat := ⟨pow⟩
instance [NatCast R] : NatCast (CPolynomial.Raw R) := ⟨fun n => C (n : R)⟩

/-- Keep only the stored coefficients with index `< k`. -/
@[inline, specialize]
def truncate [Zero R] (k : Nat) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  p.extract 0 k

/-- Return exactly the first `k` coefficients, padding missing coefficients with zero. -/
@[inline, specialize]
def takeLow [Zero R] (k : Nat) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  Array.ofFn fun i : Fin k ↦ p.coeff i

/-- Reverse the first `n` coefficients, padding missing coefficients with zero. -/
@[inline, specialize]
def reverse [Zero R] (n : Nat) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  Array.ofFn fun i : Fin n ↦ p.coeff (n - 1 - i.val)

/-- Low product computed by the coefficient convolution formula. -/
@[inline, specialize]
def mulLowConvolution [Semiring R] (k : Nat) (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  Array.ofFn fun i : Fin k ↦
    (Finset.range (i.val + 1)).sum fun j ↦ p.coeff j * q.coeff (i.val - j)

/-- Backend for computing the low `k` coefficients of a raw product. -/
structure MulLowContext (R : Type*) [Semiring R] [BEq R] [LawfulBEq R] where
  /-- Return the low `k` coefficients of `p * q`. -/
  mulLow : Nat → CPolynomial.Raw R → CPolynomial.Raw R → CPolynomial.Raw R
  /-- The backend does not return coefficients at degree `>= k`. -/
  size_le : ∀ k p q, (mulLow k p q).size ≤ k
  /-- Low coefficients agree with ordinary raw multiplication. -/
  coeff_of_lt : ∀ k p q i, i < k → (mulLow k p q).coeff i = (p * q).coeff i

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

end Ring

end Operations

end CPolynomial.Raw

end CompPoly
