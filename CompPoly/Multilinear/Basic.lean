/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/
import Mathlib.RingTheory.MvPolynomial.Basic
import CompPoly.Data.List.Lemmas
import CompPoly.Data.Vector.Basic
import CompPoly.Data.Nat.Bitwise

/-!
  # Multilinear Polynomials

  This file defines computable representations of **multilinear polynomials**.

  The first representation is by their coefficients, and the second representation is by their
  evaluations over the Boolean hypercube `{0,1}^n`. Both representations are defined as `Vector`s of
  length `2^n`, where `n` is the number of variables. We will define operations on these
  representations, and prove equivalence between them, and with the standard Mathlib definition of
  multilinear polynomials, which is the type `R⦃≤ 1⦄[X Fin n]` (notation for
  `MvPolynomial.restrictDegree (Fin n) R 1`).

  ## TODOs
  - The abstract zeta formula for `monoToLagrange`
  - A naive `O(4^n)` zeta spec `monoToLagrangeSpec` mirroring `lagrangeToMonoSpec`,
    plus equivalence `monoToLagrange = monoToLagrangeSpec`
-/

namespace CompPoly

/-- `CMlPolynomial n R` is the type of multilinear polynomials in `n` variables over a ring `R`.
  It is represented by its monomial coefficients as a `Vector` of length `2^n`.
  The indexing is **little-endian** (i.e. the least significant bit is the first bit). -/
@[reducible]
def CMlPolynomial (R : Type*) (n : ℕ) := Vector R (2 ^ n) -- coefficient of monomial basis
def CMlPolynomial.mk {R : Type*} (n : ℕ) (v : Vector R (2 ^ n)) : CMlPolynomial R n := v

/-- `CMlPolynomialEval n R` is the type of multilinear polynomials in `n` variables over a ring `R`.
  It is represented by its evaluations over the Boolean hypercube `{0,1}^n`,
  i.e. Lagrange basis coefficients.
  The indexing is **little-endian** (i.e. the least significant bit is the first bit). -/
@[reducible]
def CMlPolynomialEval (R : Type*) (n : ℕ) := Vector R (2 ^ n) -- coefficient of Lagrange basis
def CMlPolynomialEval.mk {R : Type*} (n : ℕ) (v : Vector R (2 ^ n)) : CMlPolynomialEval R n := v

variable {R : Type*} {n : ℕ}

-- Note: `finFunctionFinEquiv` maps `i : Fin (2 ^ n)` to its bit-vector in little‑endian order,
-- with bit 0 the least significant bit. For example, `6 : Fin 8` maps to `[0, 1, 1]`.
-- #check finFunctionFinEquiv

-- #check Pi.single

namespace CMlPolynomial

section CMlPolynomialInstances

instance inhabited [Inhabited R] : Inhabited (CMlPolynomial R n) := by
  simp [CMlPolynomial]; infer_instance

/-- Conform a list of coefficients to a `CMlPolynomial` with a given number of variables.
    May either pad with zeros or truncate. -/
@[inline]
def ofArray [Zero R] (coeffs : Array R) (n : ℕ) : CMlPolynomial R n :=
  .ofFn (fun i => if h : i.1 < coeffs.size then coeffs[i] else 0)
  -- ⟨((coeffs.take (2 ^ n)).rightpad (2 ^ n) 0 : Array R), by simp⟩
  -- Not sure which is better performance wise?

-- Create a zero polynomial over n variables
@[inline]
def zero [Zero R] : CMlPolynomial R n := Vector.replicate (2 ^ n) 0

lemma zero_def [Zero R] : zero = Vector.replicate (2 ^ n) 0 := rfl

/-- Add two `CMlPolynomial`s -/
@[inline]
def add [Add R] (p q : CMlPolynomial R n) : CMlPolynomial R n := Vector.zipWith (· + ·) p q

/-- Negation of a `CMlPolynomial` -/
@[inline]
def neg [Neg R] (p : CMlPolynomial R n) : CMlPolynomial R n := p.map (fun a => -a)

/-- Scalar multiplication of a `CMlPolynomial` -/
@[inline]
def smul [Mul R] (r : R) (p : CMlPolynomial R n) : CMlPolynomial R n := p.map (fun a => r * a)

/-- Scalar multiplication of a `CMlPolynomial` by a natural number -/
@[inline]
def nsmul [SMul ℕ R] (m : ℕ) (p : CMlPolynomial R n) : CMlPolynomial R n :=
  p.map (fun a => m • a)

/-- Scalar multiplication of a `CMlPolynomial` by an integer -/
@[inline]
def zsmul [SMul ℤ R] (m : ℤ) (p : CMlPolynomial R n) : CMlPolynomial R n :=
  p.map (fun a => m • a)

instance [AddCommMonoid R] : AddCommMonoid (CMlPolynomial R n) where
  add := add
  add_assoc a b c := by
    change Vector.zipWith (· + ·) (Vector.zipWith (· + ·) a b) c =
      Vector.zipWith (· + ·) a (Vector.zipWith (· + ·) b c)
    ext; simp [add_assoc]
  add_comm a b := by
    change Vector.zipWith (· + ·) a b = Vector.zipWith (· + ·) b a
    ext; simp [add_comm]
  zero := zero
  zero_add a := by
    change Vector.zipWith (· + ·) (Vector.replicate (2 ^ n) 0) a = a
    ext; simp
  add_zero a := by
    change Vector.zipWith (· + ·) a (Vector.replicate (2 ^ n) 0) = a
    ext; simp
  nsmul := nsmul
  nsmul_zero a := by
    change Vector.map (fun a ↦ 0 • a) a = Vector.replicate (2 ^ n) 0
    ext; simp
  nsmul_succ n a := by
    change a.map (fun a ↦ (n + 1) • a) = Vector.zipWith (· + ·) (Vector.map (fun a ↦ n • a) a) a
    ext i; simp; exact AddMonoid.nsmul_succ n a[i]

instance [Semiring R] : Module R (CMlPolynomial R n) where
  smul := smul
  one_smul a := by
    change Vector.map (fun a ↦ 1 * a) a = a
    ext; simp
  mul_smul r s a := by
    simp [HSMul.hSMul, smul]
  smul_zero a := by
    change Vector.map (fun a_1 ↦ a * a_1) (Vector.replicate (2 ^ n) 0) = Vector.replicate (2 ^ n) 0
    ext; simp
  smul_add r a b := by
    change Vector.map (fun a ↦ r * a) (Vector.zipWith (· + ·) a b) =
      Vector.zipWith (· + ·) (Vector.map (fun a ↦ r * a) a) (Vector.map (fun a ↦ r * a) b)
    ext; simp [left_distrib]
  add_smul r s a := by
    change Vector.map (fun a ↦ (r + s) * a) a =
      Vector.zipWith (· + ·) (Vector.map (fun a ↦ r * a) a) (Vector.map (fun a ↦ s * a) a)
    ext; simp [right_distrib]
  zero_smul a := by
    change Vector.map (fun a ↦ 0 * a) a = Vector.replicate (2 ^ n) 0
    ext; simp
end CMlPolynomialInstances

section CMlPolynomialMonomialBasisAndEvaluations

variable [CommSemiring R]
variable {S : Type*} [CommSemiring S]

/-
Monomial-basis evaluations at point `w`.

Returns the length-`2^n` vector whose index `i : Fin (2^n)` encodes a Boolean vector in
little‑endian order (bit 0 is the least significant bit). The entry at `i` is
`∏_{j < n} (if the j-th bit of i is 1 then w[j] else 1)`.
-/
def monomialBasis (w : Vector R n) : Vector R (2 ^ n) :=
  Vector.ofFn (fun i => ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1)

@[simp]
theorem monomialBasis_zero {w : Vector R 0} : monomialBasis w = #v[1] := by rfl

-- #eval monomialBasis #v[(1 : ℤ), 2, 3] (n := 3)
-- #eval Nat.digits 2 8

/-- The `i`-th element of `monomialBasis w` is the product of `w[j]` if the `j`-th bit of `i` is 1,
    and `1` if the `j`-th bit of `i` is 0. -/
theorem monomialBasis_getElem {w : Vector R n} (i : Fin (2 ^ n)) :
    (monomialBasis w)[i] = ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 := by
  rw [monomialBasis]
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]

def map {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (p : CMlPolynomial R n) : CMlPolynomial S n :=
  Vector.map f p

/-- Evaluate a `CMlPolynomial` at a point -/
def eval (p : CMlPolynomial R n) (x : Vector R n) : R :=
  Vector.dotProduct p (monomialBasis x)

def eval₂ (p : CMlPolynomial R n) (f : R →+* S) (x : Vector S n) : S := eval (map f p) x
end CMlPolynomialMonomialBasisAndEvaluations

end CMlPolynomial

namespace CMlPolynomialEval

section CMlPolynomialEvalInstances

instance inhabited [Inhabited R] : Inhabited (CMlPolynomialEval R n) := by
  simp only [CMlPolynomialEval]; infer_instance

/-- Conform a list of coefficients to a `CMlPolynomialEval` with a given number of variables.
    May either pad with zeros or truncate. -/
@[inline]
def ofArray [Zero R] (coeffs : Array R) (n : ℕ) : CMlPolynomialEval R n :=
  .ofFn (fun i => if h : i.1 < coeffs.size then coeffs[i] else 0)
  -- ⟨((coeffs.take (2 ^ n)).rightpad (2 ^ n) 0 : Array R), by simp⟩
  -- Not sure which is better performance wise?

-- Create a zero polynomial over n variables
@[inline]
def zero [Zero R] : CMlPolynomialEval R n := Vector.replicate (2 ^ n) 0

lemma zero_def [Zero R] : zero = Vector.replicate (2 ^ n) 0 := rfl

/-- Add two `CMlPolynomialEval`s -/
@[inline]
def add [Add R] (p q : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  Vector.zipWith (· + ·) p q

/-- Negation of a `CMlPolynomialEval` -/
@[inline]
def neg [Neg R] (p : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  p.map (fun a => -a)

/-- Scalar multiplication of a `CMlPolynomialEval` -/
@[inline]
def smul [Mul R] (r : R) (p : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  p.map (fun a => r * a)

/-- Scalar multiplication of a `CMlPolynomialEval` by a natural number -/
@[inline]
def nsmul [SMul ℕ R] (m : ℕ) (p : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  p.map (fun a => m • a)

/-- Scalar multiplication of a `CMlPolynomialEval` by an integer -/
@[inline]
def zsmul [SMul ℤ R] (m : ℤ) (p : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  p.map (fun a => m • a)

instance [AddCommMonoid R] : AddCommMonoid (CMlPolynomialEval R n) where
  add := add
  add_assoc a b c := by
    change Vector.zipWith (· + ·) (Vector.zipWith (· + ·) a b) c =
      Vector.zipWith (· + ·) a (Vector.zipWith (· + ·) b c)
    ext; simp [add_assoc]
  add_comm a b := by
    change Vector.zipWith (· + ·) a b = Vector.zipWith (· + ·) b a
    ext; simp [add_comm]
  zero := zero
  zero_add a := by
    change Vector.zipWith (· + ·) (Vector.replicate (2 ^ n) 0) a = a
    ext; simp
  add_zero a := by
    change Vector.zipWith (· + ·) a (Vector.replicate (2 ^ n) 0) = a
    ext; simp
  nsmul := nsmul
  nsmul_zero a := by
    change Vector.map (fun a ↦ 0 • a) a = Vector.replicate (2 ^ n) 0
    ext; simp
  nsmul_succ n a := by
    change a.map (fun a ↦ (n + 1) • a) = Vector.zipWith (· + ·) (Vector.map (fun a ↦ n • a) a) a
    ext i; simp; exact AddMonoid.nsmul_succ n a[i]

instance [Semiring R] : Module R (CMlPolynomialEval R n) where
  smul := smul
  one_smul a := by
    change Vector.map (fun a ↦ 1 * a) a = a
    ext; simp
  mul_smul r s a := by
    simp [HSMul.hSMul, smul]
  smul_zero a := by
    change Vector.map (fun a_1 ↦ a * a_1) (Vector.replicate (2 ^ n) 0) = Vector.replicate (2 ^ n) 0
    ext; simp
  smul_add r a b := by
    change Vector.map (fun a ↦ r * a) (Vector.zipWith (· + ·) a b) =
      Vector.zipWith (· + ·) (Vector.map (fun a ↦ r * a) a) (Vector.map (fun a ↦ r * a) b)
    ext; simp [left_distrib]
  add_smul r s a := by
    change Vector.map (fun a ↦ (r + s) * a) a =
      Vector.zipWith (· + ·) (Vector.map (fun a ↦ r * a) a) (Vector.map (fun a ↦ s * a) a)
    ext; simp [right_distrib]
  zero_smul a := by
    change Vector.map (fun a ↦ 0 * a) a = Vector.replicate (2 ^ n) 0
    ext; simp

end CMlPolynomialEvalInstances

section CMlPolynomialLagrangeBasisAndEvaluations

variable [CommRing R]
variable {S : Type*} [CommRing S]

/-- Lagrange (hypercube) basis at point `w`.

Returns the length-`2^n` vector `v` such that for any `x ∈ {0,1}^n`, letting
`i = ∑_{j=0}^{n-1} x_j · 2^j` (little‑endian indexing), we have
`v[i] = ∏_{j < n} (x_j · w[j] + (1 - x_j) · (1 - w[j]))`.
Equivalently, for `i : Fin (2^n)`,
`v[i] = ∏_{j < n}, (if the j-th bit of i is 1 then w[j] else 1 - w[j])`.
-/
def lagrangeBasis (w : Vector R n) : Vector R (2 ^ n) :=
  Vector.ofFn (fun i => ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 - w[j])

@[simp]
theorem lagrangeBasis_zero {w : Vector R 0} : lagrangeBasis w = #v[1] := by rfl

-- #eval lagrangeBasis #v[(1 : ℤ), 2, 3] (n := 3)
-- #eval Nat.digits 2 8

/-- The `i`-th element of `lagrangeBasis w` is the product of `w[j]` if the `j`-th bit of `i` is 1,
    and `1 - w[j]` if the `j`-th bit of `i` is 0. -/
theorem lagrangeBasis_getElem {w : Vector R n} (i : Fin (2 ^ n)) :
    (lagrangeBasis w)[i] = ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 - w[j] := by
  rw [lagrangeBasis]
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]

/-- Map a ring homomorphism over a `CMlPolynomialEval` -/
def map {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (p : CMlPolynomialEval R n) : CMlPolynomialEval S n :=
  Vector.map (fun a => f a) p

/-- Evaluate a `CMlPolynomialEval` at a point -/
def eval (p : CMlPolynomialEval R n) (x : Vector R n) : R :=
  Vector.dotProduct p (lagrangeBasis x)

/-- Evaluate a `CMlPolynomialEval` at a point using a ring homomorphism -/
def eval₂ (p : CMlPolynomialEval R n) (f : R →+* S) (x : Vector S n) : S := eval (map f p) x

/-- Evaluate the multilinear equality kernel `eq̃(w, x)`. -/
@[inline] def eqTilde (w x : Vector R n) : R :=
  eval (lagrangeBasis w) x

-- Theorems about evaluations

end CMlPolynomialLagrangeBasisAndEvaluations

end CMlPolynomialEval

namespace CMlPolynomial

-- Conversion between the coefficient (i.e. monomial) and evaluation (on the Boolean hypercube)
-- representations.

variable {R : Type*} [AddCommGroup R]

/-- **One level** of the zeta‑transform (coefficient to evaluation).

Processes the `j`-th variable by folding the "partner" index (with bit `j` cleared) into
every index that has bit `j` set. At output index `i`:
$$ (\text{monoToLagrangeLevel}\ j\ v)[i] \ =\ \begin{cases}
  v[i] + v[i - 2^j] & \text{if bit } j \text{ of } i \text{ is } 1 \\
  v[i] & \text{otherwise}
\end{cases} $$

After applying every level `0, 1, …, n-1` the resulting entry at `i` is
$\sum_{j \subseteq i} p[j]$ (bitwise subset), which is the hypercube evaluation at the
Boolean point encoded by `i`. Cost per level: $O(2^n)$ additions, so the full transform
is $O(n \cdot 2^n)$.

The `stride` is $2^j$, the distance between indices that differ only in bit `j`.
-/
@[inline] def monoToLagrangeLevel {n : ℕ} (j : Fin n) : Vector R (2 ^ n) → Vector R (2 ^ n) :=
  fun v =>
    let stride : ℕ := 2 ^ j.val    -- distance to the "partner" index
    Vector.ofFn (fun i : Fin (2 ^ n) =>
      if (BitVec.ofFin i).getLsb j then
        v[i] + v[i - stride]'(Nat.sub_lt_of_lt i.isLt)
      else
        v[i])

/-- **Full zeta transform**: coefficients → evaluations.

Applies `monoToLagrangeLevel 0, 1, …, n-1` in that order via `foldl`. The resulting entry
at each index `i : Fin (2 ^ n)` is $\sum_{j \subseteq i} p[j]$ (the classical zeta
transform on the Boolean lattice).

**Complexity:** $O(n \cdot 2^n)$ additions — this is the butterfly form. Contrast with
the naive `monoToLagrangeSpec` which is $O(4^n)$. -/
@[inline] def monoToLagrange (n : ℕ) : CMlPolynomial R n → CMlPolynomialEval R n :=
  (List.finRange n).foldl (fun acc level => monoToLagrangeLevel level acc)

/-- **One level** of the inverse zeta‑transform / Möbius transform (evaluation to
coefficient).

Processes the `j`-th variable by subtracting the partner entry (bit `j` cleared) from
every index that has bit `j` set. At output index `i`:
$$ (\text{lagrangeToMonoLevel}\ j\ v)[i] \ =\ \begin{cases}
  v[i] - v[i - 2^j] & \text{if bit } j \text{ of } i \text{ is } 1 \\
  v[i] & \text{otherwise}
\end{cases} $$

Each level is the exact inverse of `monoToLagrangeLevel j` (see
`lagrangeToMonoLevel_monoToLagrangeLevel_id`).

The `stride` is $2^j$.
-/
@[inline] def lagrangeToMonoLevel {n : ℕ} (j : Fin n) : Vector R (2 ^ n) → Vector R (2 ^ n) :=
  fun v =>
    let stride : ℕ := 2 ^ j.val  -- distance to the "partner" index
    Vector.ofFn (fun i : Fin (2 ^ n) =>
      if (BitVec.ofFin i).getLsb j then
        v[i] - v[i - stride]'(Nat.sub_lt_of_lt i.isLt)
      else
        v[i])

/-- **Full inverse / Möbius transform**: evaluations → coefficients.

Applies `lagrangeToMonoLevel (n-1), (n-2), …, 0` via `foldr`. The resulting entry at
each index `i : Fin (2 ^ n)` is the inclusion-exclusion sum
$\sum_{j \subseteq i} (-1)^{\mathrm{popCount}(i) - \mathrm{popCount}(j)} \cdot p[j]$ —
see `lagrangeToMono_eq_lagrangeToMonoSpec`.

**Complexity:** $O(n \cdot 2^n)$ additions/subtractions. Contrast with the naive
`lagrangeToMonoSpec` which is $O(4^n)$. -/
@[inline]
def lagrangeToMono (n : ℕ) :
    Vector R (2 ^ n) → Vector R (2 ^ n) :=
  (List.finRange n).foldr (fun h acc => lagrangeToMonoLevel h acc)

/-- The $O(4^n)$ inclusion-exclusion specification for the Möbius transform.

For each output index `i`, this sums over all indices `j` that are bitwise subsets of `i`
(`i &&& j = j`), with sign
$(-1)^{\mathrm{popCount}(i) - \mathrm{popCount}(j)}$:
$$ (\text{lagrangeToMonoSpec}\ p)[i]
  = \sum_{j \subseteq i} (-1)^{\mathrm{popCount}(i) - \mathrm{popCount}(j)} \cdot p[j]. $$

Provable equivalent to the fast `lagrangeToMono` — see `lagrangeToMono_eq_lagrangeToMonoSpec`.
-/
def lagrangeToMonoSpec (p : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  -- We define the output vector by specifying the value for each entry `i`.
  Vector.ofFn (fun i =>
    -- For each output entry `i`, we compute a sum over all possible input indices `j`.
    Finset.sum Finset.univ (fun j =>
      -- The sum is only over `j` that are bitwise subsets of `i`.
      if (i.val &&& j.val = j.val) then
        -- The term is added or subtracted based on the parity of the difference
        -- in the number of set bits (Hamming weight).
        if (i.val.popCount - j.val.popCount) % 2 = 0 then
          p.get j -- Add if the difference is even
        else
          -p.get j -- Subtract if the difference is odd
      else
        0 -- If j is not a subset of i, the term is zero.
    )
  )

/-- The $O(4^n)$ specification for the zeta transform (the mirror of
`lagrangeToMonoSpec`).

For each output index `i`, this sums `p[j]` over every index `j` that is a bitwise subset
of `i` (`i &&& j = j`):
$$ (\text{monoToLagrangeSpec}\ p)[i]\ =\ \sum_{j \subseteq i} p[j]. $$

Provable equivalent to the fast `monoToLagrange` — see `monoToLagrange_eq_monoToLagrangeSpec`.
-/
def monoToLagrangeSpec (p : CMlPolynomial R n) : CMlPolynomialEval R n :=
  Vector.ofFn (fun i =>
    Finset.sum Finset.univ (fun j =>
      if (i.val &&& j.val = j.val) then p.get j else 0))

-- #eval lagrangeToMono 2 #v[(78 : ℤ), 3, 4, 100]
-- #eval lagrangeToMonoSpec (n:=2) #v[(78 : ℤ), 3, 4, 100]

section MobiusEquivalence

/-! ### Fast ↔ Spec equivalence for the Möbius transform

We prove `lagrangeToMono = lagrangeToMonoSpec` by introducing an indexed family of
"partial Möbius sums" `mobiusPartial k` that interpolates between the identity (at `k = n`)
and the full spec (at `k = 0`). Each step of the fast transform
`lagrangeToMonoLevel (k - 1)` decrements the parameter by exactly one. Combined with the
base case we obtain the result by descending induction on `k`. -/

/-- Partial Möbius sum at index `i` after processing levels `[k, k + 1, …, n - 1]`.

Sums over `j : Fin (2 ^ n)` that are bitwise subsets of `i` and that agree with `i` modulo
`2 ^ k` (i.e. on all bits strictly below `k`), weighted by
`(-1) ^ (popCount i - popCount j)`.

* At `k = n` only `j = i` satisfies the constraints, so the result is `p[i]`.
* At `k = 0` the low-bits constraint is vacuous and the formula is exactly
  `lagrangeToMonoSpec`.
-/
private def mobiusPartial (k : ℕ) (p : Vector R (2 ^ n)) (i : Fin (2 ^ n)) : R :=
  ∑ j : Fin (2 ^ n),
    if (i.val &&& j.val = j.val) ∧ (i.val % 2 ^ k = j.val % 2 ^ k) then
      if (i.val.popCount - j.val.popCount) % 2 = 0 then p.get j else -p.get j
    else 0

/-- Base case: at `k = n` the modular constraint forces `j = i`, so the partial sum
collapses to `p.get i`. -/
private lemma mobiusPartial_n (p : Vector R (2 ^ n)) (i : Fin (2 ^ n)) :
    mobiusPartial n p i = p.get i := by
  unfold mobiusPartial
  rw [Finset.sum_eq_single i]
  · have h1 : i.val &&& i.val = i.val := by simp [Nat.and_self]
    simp only [h1, and_self, if_true, Nat.sub_self, Nat.zero_mod, if_true]
  · intro j _ hji
    have hji' : j.val ≠ i.val := fun h => hji (Fin.ext h)
    have hi_lt : i.val < 2 ^ n := i.isLt
    have hj_lt : j.val < 2 ^ n := j.isLt
    have : i.val % 2 ^ n ≠ j.val % 2 ^ n := by
      rw [Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt hj_lt]
      exact fun h => hji' h.symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The `k = 0` case is (definitionally) equivalent to `lagrangeToMonoSpec`. -/
private lemma mobiusPartial_zero_eq_spec (p : Vector R (2 ^ n)) (i : Fin (2 ^ n)) :
    mobiusPartial 0 p i = (lagrangeToMonoSpec p).get i := by
  unfold mobiusPartial lagrangeToMonoSpec
  simp only [pow_zero, Nat.mod_one, and_true, Vector.get_ofFn]

/-- `Nat.popCount 0 = 0`: the zero-bit count of `0` is `0`. -/
private lemma popCount_zero' :
    Nat.popCount 0 = 0 := by
  unfold Nat.popCount; simp [Nat.digits]

/-- Recursion for `Nat.popCount` on positive arguments: split off the least-significant bit. -/
private lemma popCount_pos' {m : ℕ} (hm : 0 < m) :
    Nat.popCount m =
      m % 2 + Nat.popCount (m / 2) := by
  unfold Nat.popCount
  rw [Nat.digits_def' (by norm_num : 1 < 2) hm]
  simp [List.sum_cons]

/-- `testBit` at index `k + 1` equals `testBit` at index `k` of the half. -/
private lemma testBit_succ_eq_div2 (m k : ℕ) :
    m.testBit (k + 1) = (m / 2).testBit k := by
  have h := @Nat.testBit_div_two_pow 1 m k
  rw [pow_one] at h; exact h.symm

/-- Clearing a set bit at position `k` decreases `popCount` by exactly one. -/
private lemma popCount_sub_two_pow {m k : ℕ}
    (hbit : m.testBit k = true) :
    Nat.popCount m =
      Nat.popCount (m - 2 ^ k) + 1 := by
  induction k generalizing m with
  | zero =>
    have hm_pos : 0 < m := by
      by_contra h; push Not at h
      simp only [Nat.le_zero] at h
      subst h; simp at hbit
    have hm_odd : m % 2 = 1 := by
      rw [Nat.testBit] at hbit
      simp only [Nat.shiftRight_zero,
        Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero,
        beq_iff_eq] at hbit; omega
    rw [popCount_pos' hm_pos, hm_odd, pow_zero]
    by_cases h1 : m = 1
    · subst h1; simp [popCount_zero']
    · rw [popCount_pos' (by omega : 0 < m - 1)]
      have : (m - 1) % 2 = 0 := by omega
      have : (m - 1) / 2 = m / 2 := by omega
      simp_all; ring
  | succ k ih =>
    have h2k_le := Nat.ge_two_pow_of_testBit hbit
    have hm_pos : 0 < m := by
      linarith [Nat.two_pow_pos (k + 1)]
    rw [popCount_pos' hm_pos]
    have hbd : (m / 2).testBit k = true := by
      rwa [← testBit_succ_eq_div2]
    by_cases h_eq : m = 2 ^ (k + 1)
    · subst h_eq
      rw [Nat.sub_self, popCount_zero']
      have hmod : 2 ^ (k + 1) % 2 = 0 :=
        Nat.dvd_iff_mod_eq_zero.mp
          (dvd_pow_self 2 (by omega))
      have hdiv : 2 ^ (k + 1) / 2 = 2 ^ k := by
        have := pow_succ 2 k; omega
      rw [hmod, hdiv, Nat.zero_add]
      have h := @ih (2 ^ k) Nat.testBit_two_pow_self
      rw [Nat.sub_self, popCount_zero'] at h; omega
    · rw [ih hbd, popCount_pos'
        (by omega : 0 < m - 2 ^ (k + 1))]
      have : (m - 2 ^ (k + 1)) % 2 = m % 2 := by
        have : 2 ∣ 2 ^ (k + 1) :=
          dvd_pow_self 2 (by omega); omega
      have : (m - 2 ^ (k + 1)) / 2 =
          m / 2 - 2 ^ k := by
        have := pow_succ 2 k; omega
      simp_all; ring

/-- If `n &&& m = m` (i.e. `m` is a bitwise submask of `n`) and `n` has bit `k` clear,
then so does `m`. -/
private lemma submask_testBit_false {m n k : ℕ}
    (hsub : n &&& m = m)
    (hbit : n.testBit k = false) :
    m.testBit k = false := by
  by_contra hj; simp only [Bool.not_eq_false] at hj
  have h := Nat.testBit_and n m k
  rw [hsub] at h
  simp only [hbit, Bool.false_and] at h
  exact absurd h.symm (by simp [hj])

/-- Transfer `getBit` equality to `testBit` equality. -/
private lemma testBit_eq_of_getBit_eq {m n k : ℕ}
    (h : Nat.getBit k m = Nat.getBit k n) :
    m.testBit k = n.testBit k := by
  rw [Nat.getBit_eq_testBit,
    Nat.getBit_eq_testBit] at h
  cases hm : m.testBit k <;>
    cases hn : n.testBit k <;> simp_all

/-- Clearing bit `k` in a number that has bit `k` set gives a number with bit `k` clear. -/
private lemma testBit_sub_self {m k : ℕ}
    (hbit : m.testBit k = true) :
    (m - 2 ^ k).testBit k = false := by
  rw [Nat.testBit_false_eq_getBit_eq_0]
  have hgb : Nat.getBit k m = 1 := by
    rw [Nat.testBit_true_eq_getBit_eq_1] at hbit
    exact hbit
  have h :=
    Nat.getBit_of_sub_two_pow_of_bit_1 hgb (j := k)
  simp at h; exact h

/-- Bits other than `k` are unchanged when subtracting `2 ^ k` from a number with bit `k` set. -/
private lemma testBit_sub_ne {m k l : ℕ}
    (hbit : m.testBit k = true) (hl : l ≠ k) :
    (m - 2 ^ k).testBit l = m.testBit l := by
  apply testBit_eq_of_getBit_eq
  have hgb : Nat.getBit k m = 1 := by
    rw [Nat.testBit_true_eq_getBit_eq_1] at hbit
    exact hbit
  have h :=
    Nat.getBit_of_sub_two_pow_of_bit_1 hgb (j := l)
  simp only [hl, ite_false] at h; exact h

/-- `(m / 2 ^ k) % 2 = 1` when bit `k` of `m` is set. -/
private lemma div_mod2_of_testBit_true {m k : ℕ}
    (h : m.testBit k = true) :
    (m / 2 ^ k) % 2 = 1 := by
  rw [Nat.testBit] at h
  simp only [Nat.shiftRight_eq_div_pow] at h
  simp only [Nat.one_and_eq_mod_two,
    Nat.mod_two_bne_zero, beq_iff_eq] at h; omega

/-- `(m / 2 ^ k) % 2 = 0` when bit `k` of `m` is clear. -/
private lemma div_mod2_of_testBit_false {m k : ℕ}
    (h : m.testBit k = false) :
    (m / 2 ^ k) % 2 = 0 := by
  rw [Nat.testBit] at h
  simp only [Nat.shiftRight_eq_div_pow] at h
  simp only [Nat.one_and_eq_mod_two,
    Nat.mod_two_bne_zero,
    beq_eq_false_iff_ne, ne_eq] at h; omega

/-- Decomposition for the case `(m / d) % 2 = 1`: express `m` via
`(d * 2) * q + r` with `r = d + m % d`. Useful to read `m % (d * 2)`. -/
private lemma rewrite_odd (m d : ℕ)
    (hodd : (m / d) % 2 = 1) :
    m = d * 2 * (m / d / 2) + (d + m % d) := by
  have hd := Nat.div_add_mod m d
  have : d * (m / d) =
      d * 2 * (m / d / 2) + d := by
    have hq : m / d = 2 * (m / d / 2) + 1 := by
      omega
    conv_lhs => rw [hq]; rw [Nat.mul_add, Nat.mul_one]
    show d * (2 * (m / d / 2)) + d =
      d * 2 * (m / d / 2) + d
    congr 1; ring
  linarith

/-- Decomposition for the case `(m / d) % 2 = 0`: express `m` via
`(d * 2) * q + r` with `r = m % d`. Useful to read `m % (d * 2)`. -/
private lemma rewrite_even (m d : ℕ)
    (heven : (m / d) % 2 = 0) :
    m = d * 2 * (m / d / 2) + m % d := by
  have hd := Nat.div_add_mod m d
  have : d * (m / d) = d * 2 * (m / d / 2) := by
    have hq : m / d = 2 * (m / d / 2) := by omega
    conv_lhs => rw [hq]
    show d * (2 * (m / d / 2)) =
      d * 2 * (m / d / 2)
    ring
  linarith

/-- When `(m / d) % 2 = 1`, the value of `m % (d * 2)` is `d + m % d`. -/
private lemma mod_double_of_odd_div (m d : ℕ)
    (hd : 0 < d) (hodd : (m / d) % 2 = 1) :
    m % (d * 2) = d + m % d := by
  have := Nat.mod_lt m hd
  conv_lhs => rw [rewrite_odd m d hodd]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- When `(m / d) % 2 = 0`, the value of `m % (d * 2)` is `m % d`. -/
private lemma mod_double_of_even_div (m d : ℕ)
    (hd : 0 < d) (heven : (m / d) % 2 = 0) :
    m % (d * 2) = m % d := by
  have := Nat.mod_lt m hd
  conv_lhs => rw [rewrite_even m d heven]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- If bit `k` of `m` is clear then `m % 2 ^ (k + 1) = m % 2 ^ k`. -/
private lemma mod_pow_succ_of_testBit_false
    {m k : ℕ} (hbit : m.testBit k = false) :
    m % 2 ^ (k + 1) = m % 2 ^ k := by
  rw [pow_succ]; exact mod_double_of_even_div m _
    (Nat.two_pow_pos k)
    (div_mod2_of_testBit_false hbit)

/-- If bit `k` of `m` is set then `(m - 2 ^ k) % 2 ^ (k + 1) = m % 2 ^ k`. -/
private lemma mod_pow_succ_sub_of_testBit_true
    {m k : ℕ} (hbit : m.testBit k = true) :
    (m - 2 ^ k) % 2 ^ (k + 1) = m % 2 ^ k := by
  rw [pow_succ, mod_double_of_even_div _ _
    (Nat.two_pow_pos k)
    (div_mod2_of_testBit_false (testBit_sub_self hbit))]
  have : 2 ^ k * 1 ≤ m := by
    have := Nat.ge_two_pow_of_testBit hbit; omega
  have := @Nat.sub_mul_mod m 1 (2 ^ k) this
  simp at this; exact this

/-- Lift equality modulo `2 ^ k` to equality modulo `2 ^ (k + 1)` when bit `k` agrees on
both sides (both set). -/
private lemma mod_succ_of_both_true {m n k : ℕ}
    (hm : m.testBit k = true)
    (hn : n.testBit k = true)
    (hmod : m % 2 ^ k = n % 2 ^ k) :
    m % 2 ^ (k + 1) = n % 2 ^ (k + 1) := by
  rw [pow_succ,
    mod_double_of_odd_div m _ (Nat.two_pow_pos k)
      (div_mod2_of_testBit_true hm),
    mod_double_of_odd_div n _ (Nat.two_pow_pos k)
      (div_mod2_of_testBit_true hn), hmod]

/-- When bit `k` disagrees between `m` and `n` (set vs clear), their residues modulo
`2 ^ (k + 1)` differ. -/
private lemma mod_succ_ne_of_diff {m n k : ℕ}
    (hm : m.testBit k = true)
    (hn : n.testBit k = false) :
    m % 2 ^ (k + 1) ≠ n % 2 ^ (k + 1) := by
  rw [pow_succ,
    mod_double_of_odd_div m _ (Nat.two_pow_pos k)
      (div_mod2_of_testBit_true hm),
    mod_double_of_even_div n _ (Nat.two_pow_pos k)
      (div_mod2_of_testBit_false hn)]
  have := Nat.mod_lt m (Nat.two_pow_pos k); omega

/-- If residues modulo `2 ^ k` disagree, then so do residues modulo `2 ^ (k + 1)`. -/
private lemma mod_ne_lift {m n k : ℕ}
    (h : m % 2 ^ k ≠ n % 2 ^ k) :
    m % 2 ^ (k + 1) ≠ n % 2 ^ (k + 1) := by
  intro heq; apply h
  have hdvd := Nat.pow_dvd_pow 2 (Nat.le_succ k)
  rw [← Nat.mod_mod_of_dvd m hdvd, heq,
    Nat.mod_mod_of_dvd n hdvd]

/-- If `m` has bit `k` set and `n` is a submask of `m` with bit `k` clear, then `n`
remains a submask after clearing bit `k` in `m`. -/
private lemma submask_sub_two_pow {m n k : ℕ}
    (hsub : m &&& n = n)
    (hbit_m : m.testBit k = true)
    (hbit_n : n.testBit k = false) :
    (m - 2 ^ k) &&& n = n := by
  apply Nat.eq_of_testBit_eq; intro l
  rw [Nat.testBit_and]
  have hsub_tb : (m.testBit l && n.testBit l) =
      n.testBit l := by
    have h := Nat.testBit_and m n l
    rw [hsub] at h; exact h.symm
  if hl : l = k then
    subst hl; simp [hbit_n]
  else rw [testBit_sub_ne hbit_m hl, hsub_tb]

/-- A bitwise submask has no more set bits than its supermask. -/
private lemma popCount_le_of_and_eq :
    ∀ {m n : ℕ}, m &&& n = n →
      n.popCount ≤ m.popCount := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro n h
    by_cases hn : n = 0
    · subst hn; simp [popCount_zero']
    · have hm : m > 0 := by
        by_contra h0; push Not at h0
        simp only [Nat.le_zero] at h0; subst h0
        simp at h; exact hn h.symm
      rw [popCount_pos' (by omega : 0 < n),
        popCount_pos' hm]
      have h_div :
          (m / 2) &&& (n / 2) = n / 2 := by
        have := @Nat.and_div_two_pow m n 1
        simp [pow_one] at this; rw [h] at this
        exact this.symm
      have hmod_le : n % 2 ≤ m % 2 := by
        have hmod := @Nat.and_mod_two_pow m n 1
        simp [pow_one] at hmod; rw [h] at hmod
        rw [hmod]; exact Nat.and_le_left
      have := ih (m / 2)
        (Nat.div_lt_self (by omega) (by norm_num))
        h_div
      omega

/-- Step lemma: applying `lagrangeToMonoLevel k` to the partial sum at level `k + 1`
yields the partial sum at level `k`. This is the induction step that chains the fast
transform to the inclusion-exclusion spec one bit at a time. -/
private lemma mobiusPartial_step
    {k : ℕ} (hk : k < n) (p : Vector R (2 ^ n))
    (i : Fin (2 ^ n)) :
    Vector.get
      (lagrangeToMonoLevel ⟨k, hk⟩
        (Vector.ofFn (mobiusPartial (k + 1) p)))
      i =
    mobiusPartial k p i := by
  unfold lagrangeToMonoLevel mobiusPartial
  simp only [Vector.get_eq_getElem,
    Vector.getElem_ofFn, BitVec.getLsb_eq_getElem,
    Fin.getElem_fin, BitVec.getElem_ofFin]
  if hbit : i.val.testBit k = true then
    simp only [hbit, ↓reduceIte]
    have h2k_le := Nat.ge_two_pow_of_testBit hbit
    have hi_sub_lt : i.val - 2 ^ k < 2 ^ n :=
      Nat.sub_lt_of_lt i.isLt
    have hbit' : (i.val - 2 ^ k).testBit k = false :=
      testBit_sub_self hbit
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    by_cases hjbit : j.val.testBit k = true
    · have hnsub' :
          ¬((i.val - 2 ^ k) &&& j.val = j.val) := by
        intro h
        have := submask_testBit_false h hbit'
        simp [this] at hjbit
      simp only [hnsub', false_and, ite_false, sub_zero]
      by_cases hsub : i.val &&& j.val = j.val
      · by_cases hmod :
            i.val % 2 ^ k = j.val % 2 ^ k
        · simp [hsub, mod_succ_of_both_true
            hbit hjbit hmod, hmod]
        · simp [hsub, mod_ne_lift hmod, hmod]
      · simp [hsub]
    · simp only [Bool.not_eq_true] at hjbit
      by_cases hsub : i.val &&& j.val = j.val
      · have hsub' :=
          submask_sub_two_pow hsub hbit hjbit
        have hmod_ne :=
          mod_succ_ne_of_diff hbit hjbit
        simp only [hsub, true_and, hmod_ne,
          ite_false, zero_sub, hsub', true_and]
        have hmod_iff :
            (i.val % 2 ^ k = j.val % 2 ^ k) ↔
            ((i.val - 2 ^ k) % 2 ^ (k + 1) =
              j.val % 2 ^ (k + 1)) := by
          rw [mod_pow_succ_sub_of_testBit_true hbit,
            mod_pow_succ_of_testBit_false hjbit]
        by_cases hmod :
            i.val % 2 ^ k = j.val % 2 ^ k
        · simp only [hmod, ite_true, hmod_iff.mp hmod]
          have hpc := popCount_sub_two_pow hbit
          have hpc_le := popCount_le_of_and_eq hsub'
          by_cases hpar :
            (i.val.popCount -
              j.val.popCount) % 2 = 0
          · have : ((i.val - 2 ^ k).popCount -
                j.val.popCount) % 2 = 1 := by omega
            simp only [hpar, ite_true, this]; norm_num
          · have hp1 : (i.val.popCount -
                j.val.popCount) % 2 = 1 := by omega
            have : ((i.val - 2 ^ k).popCount -
                j.val.popCount) % 2 = 0 := by omega
            simp only [hp1, this]; norm_num
        · simp only [hmod, ite_false]
          have : ¬((i.val - 2 ^ k) % 2 ^ (k + 1) =
              j.val % 2 ^ (k + 1)) :=
            fun h => hmod (hmod_iff.mpr h)
          simp [this]
      · have hnsub' :
            ¬((i.val - 2 ^ k) &&& j.val = j.val) := by
          intro h'; apply hsub
          apply Nat.eq_of_testBit_eq; intro l
          rw [Nat.testBit_and]
          have hh := Nat.testBit_and
            (i.val - 2 ^ k) j.val l
          rw [h'] at hh
          if hl : l = k then
            subst hl; simp [hjbit]
          else
            rw [testBit_sub_ne hbit hl] at hh
            exact hh.symm
        simp [hsub, hnsub']
  else
    simp only [Bool.not_eq_true] at hbit
    simp only [hbit]
    apply Finset.sum_congr rfl; intro j _
    by_cases hsub : i.val &&& j.val = j.val
    · have hjf := submask_testBit_false hsub hbit
      have hmod_eq :
          (i.val % 2 ^ (k + 1) = j.val % 2 ^ (k + 1)) ↔
          (i.val % 2 ^ k = j.val % 2 ^ k) := by
        rw [mod_pow_succ_of_testBit_false hbit,
          mod_pow_succ_of_testBit_false hjf]
      simp only [hsub, true_and]
      by_cases hmod :
          i.val % 2 ^ k = j.val % 2 ^ k
      · simp [hmod_eq.mpr hmod, hmod]
      · have : ¬(i.val % 2 ^ (k + 1) =
            j.val % 2 ^ (k + 1)) :=
          fun h => hmod (hmod_eq.mp h)
        simp [this, hmod]
    · simp [hsub]

/-- Fold lemma: applying all `n` levels of the fast Möbius transform reduces `p` to the
value `Vector.ofFn (mobiusPartial 0 p)`. Proved by descending induction on the number of
remaining levels. -/
private lemma lagrangeToMono_eq_mobiusPartial_zero
    (p : Vector R (2 ^ n)) :
    lagrangeToMono n p =
      Vector.ofFn (mobiusPartial 0 p) := by
  unfold lagrangeToMono
  suffices h : ∀ m ≤ n,
      ((List.finRange n).drop (n - m)).foldr
        (fun h acc => lagrangeToMonoLevel h acc)
        p =
      Vector.ofFn (mobiusPartial (n - m) p) by
    have := h n (le_refl n)
    simp only [Nat.sub_self, List.drop_zero] at this
    exact this
  intro m hm
  induction m with
  | zero =>
    simp only [Nat.sub_zero]
    have hdrop : (List.finRange n).drop n = [] :=
      List.drop_of_length_le (by simp)
    simp only [hdrop, List.foldr_nil]
    ext i hi; simp only [Vector.getElem_ofFn]
    exact (mobiusPartial_n p ⟨i, hi⟩).symm
  | succ m' ih =>
    have hm' : m' ≤ n := by omega
    have hk : n - (m' + 1) < n := by omega
    have hlen : n - m' - 1 <
        (List.finRange n).length := by
      simp [List.length_finRange]; omega
    have hdrop := List.drop_eq_getElem_cons hlen
      (l := List.finRange n)
    simp only [List.getElem_finRange,
      show n - m' - 1 + 1 = n - m' from by omega]
      at hdrop
    rw [show n - (m' + 1) = n - m' - 1 from by
      omega, hdrop, List.foldr_cons, ih hm']
    ext idx hidx
    simp only [Vector.getElem_ofFn]
    have hstep := mobiusPartial_step hk p
      ⟨idx, hidx⟩
    simp only [Vector.get_eq_getElem] at hstep
    have h1 : n - m' - 1 = n - (m' + 1) := by omega
    have h2 : n - m' = n - (m' + 1) + 1 := by omega
    simp only [h2] at *
    convert hstep using 2

/-- The fast Möbius transform `lagrangeToMono` is pointwise equal to the inclusion-exclusion
specification `lagrangeToMonoSpec`. Combines the fold lemma with the `k = 0` base case. -/
theorem lagrangeToMono_eq_lagrangeToMonoSpec
    {R : Type*} [AddCommGroup R] {n : ℕ}
    (p : Vector R (2 ^ n)) :
    CMlPolynomial.lagrangeToMono n p =
      CMlPolynomial.lagrangeToMonoSpec p := by
  rw [lagrangeToMono_eq_mobiusPartial_zero]
  ext i hi
  simp only [Vector.getElem_ofFn]
  exact mobiusPartial_zero_eq_spec p ⟨i, hi⟩

end MobiusEquivalence

section ZetaEquivalence

/-! ### Fast ↔ Spec equivalence for the zeta transform

Mirror of `MobiusEquivalence`: we prove `monoToLagrange = monoToLagrangeSpec` with an
indexed family `zetaPartial k` of partial subset sums. Instead of the low-bits constraint
used in the Möbius proof, here `k` counts how many leading levels have already been
applied — the constraint is that `j` must agree with `i` on bits **at or above**
position `k` (`i / 2 ^ k = j / 2 ^ k`).

* At `k = 0` only `j = i` matches, so `zetaPartial 0 p i = p[i]`.
* At `k = n` the constraint is vacuous, recovering `monoToLagrangeSpec`.

Each application of `monoToLagrangeLevel k` to `Vector.ofFn (zetaPartial k p)` increments
`k` by one. `monoToLagrange n` is a `foldl`, so applying the levels `0, 1, …, n-1`
transports us from `zetaPartial 0 = id` to `zetaPartial n = spec`. -/

/-- Partial zeta sum at index `i` after processing levels `[0, 1, …, k - 1]`.

Sums `p[j]` over `j : Fin (2 ^ n)` that are bitwise subsets of `i` and that agree with `i`
on all bits at or above position `k` (`i / 2 ^ k = j / 2 ^ k`).

* At `k = 0` only `j = i` satisfies the constraints, so the result is `p[i]`.
* At `k = n` the high-bits constraint is vacuous and the formula coincides with
  `monoToLagrangeSpec`.
-/
private def zetaPartial (k : ℕ) (p : Vector R (2 ^ n)) (i : Fin (2 ^ n)) : R :=
  ∑ j : Fin (2 ^ n),
    if (i.val &&& j.val = j.val) ∧ (i.val / 2 ^ k = j.val / 2 ^ k) then
      p.get j
    else 0

/-- Base case: at `k = 0` the high-bits constraint forces `j = i`, so the partial zeta
sum collapses to `p.get i`. -/
private lemma zetaPartial_zero (p : Vector R (2 ^ n)) (i : Fin (2 ^ n)) :
    zetaPartial 0 p i = p.get i := by
  unfold zetaPartial
  rw [Finset.sum_eq_single i]
  · have h1 : i.val &&& i.val = i.val := by simp [Nat.and_self]
    simp only [h1, pow_zero, Nat.div_one, and_self, if_true]
  · intro j _ hji
    have hji' : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp only [pow_zero, Nat.div_one]
    have : i.val ≠ j.val := fun h => hji' h.symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- At `k = n` the high-bits constraint is vacuous (both `i / 2 ^ n` and `j / 2 ^ n`
are `0`), so the partial sum equals `monoToLagrangeSpec`. -/
private lemma zetaPartial_n_eq_spec (p : Vector R (2 ^ n)) (i : Fin (2 ^ n)) :
    zetaPartial n p i = (monoToLagrangeSpec p).get i := by
  unfold zetaPartial monoToLagrangeSpec
  simp only [Vector.get_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  have hi : i.val / 2 ^ n = 0 := Nat.div_eq_of_lt i.isLt
  have hj : j.val / 2 ^ n = 0 := Nat.div_eq_of_lt j.isLt
  by_cases hsub : i.val &&& j.val = j.val
  · simp [hsub, hi, hj]
  · simp [hsub]

/-- `m / 2 ^ (k + 1) = (m / 2 ^ k) / 2`: increasing the shift exponent by one is one
extra halving. -/
private lemma div_pow_succ (m k : ℕ) :
    m / 2 ^ (k + 1) = (m / 2 ^ k) / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

/-- If bit `k` of both `m` and `n` is `0`, then equality modulo `2 ^ k` (high-bits sense,
i.e. of the quotients `/ 2 ^ k`) is equivalent to equality modulo `2 ^ (k + 1)`. -/
private lemma div_pow_succ_eq_of_both_false {m n k : ℕ}
    (hm : m.testBit k = false) (hn : n.testBit k = false) :
    m / 2 ^ k = n / 2 ^ k ↔ m / 2 ^ (k + 1) = n / 2 ^ (k + 1) := by
  have hm_even : (m / 2 ^ k) % 2 = 0 := div_mod2_of_testBit_false hm
  have hn_even : (n / 2 ^ k) % 2 = 0 := div_mod2_of_testBit_false hn
  have hm_div : m / 2 ^ (k + 1) = (m / 2 ^ k) / 2 := div_pow_succ m k
  have hn_div : n / 2 ^ (k + 1) = (n / 2 ^ k) / 2 := div_pow_succ n k
  have hm_split := Nat.div_add_mod (m / 2 ^ k) 2
  have hn_split := Nat.div_add_mod (n / 2 ^ k) 2
  omega

/-- If bit `k` of both `m` and `n` is `1`, then equality modulo `2 ^ k` (high-bits sense)
is equivalent to equality modulo `2 ^ (k + 1)`. -/
private lemma div_pow_succ_eq_of_both_true {m n k : ℕ}
    (hm : m.testBit k = true) (hn : n.testBit k = true) :
    m / 2 ^ k = n / 2 ^ k ↔ m / 2 ^ (k + 1) = n / 2 ^ (k + 1) := by
  have hm_odd : (m / 2 ^ k) % 2 = 1 := div_mod2_of_testBit_true hm
  have hn_odd : (n / 2 ^ k) % 2 = 1 := div_mod2_of_testBit_true hn
  have hm_div : m / 2 ^ (k + 1) = (m / 2 ^ k) / 2 := div_pow_succ m k
  have hn_div : n / 2 ^ (k + 1) = (n / 2 ^ k) / 2 := div_pow_succ n k
  have hm_split := Nat.div_add_mod (m / 2 ^ k) 2
  have hn_split := Nat.div_add_mod (n / 2 ^ k) 2
  omega

/-- When bit `k` disagrees between `m` and `n` (set vs clear), the quotients
`m / 2 ^ k` and `n / 2 ^ k` have different parities and are therefore unequal. -/
private lemma div_pow_ne_of_diff {m n k : ℕ}
    (hm : m.testBit k = true) (hn : n.testBit k = false) :
    m / 2 ^ k ≠ n / 2 ^ k := by
  have hm_odd : (m / 2 ^ k) % 2 = 1 := div_mod2_of_testBit_true hm
  have hn_even : (n / 2 ^ k) % 2 = 0 := div_mod2_of_testBit_false hn
  intro h; rw [h] at hm_odd; omega

/-- Clearing bit `k` in `m` (when set) preserves the high-bits quotient at level `k + 1`:
`(m - 2 ^ k) / 2 ^ (k + 1) = m / 2 ^ (k + 1)`. -/
private lemma div_pow_succ_sub_of_testBit_true {m k : ℕ}
    (hbit : m.testBit k = true) :
    (m - 2 ^ k) / 2 ^ (k + 1) = m / 2 ^ (k + 1) := by
  have hm_ge : 2 ^ k ≤ m := Nat.ge_two_pow_of_testBit hbit
  have hpos : 0 < 2 ^ (k + 1) := Nat.two_pow_pos (k + 1)
  have hmod_sub : (m - 2 ^ k) % 2 ^ (k + 1) = m % 2 ^ k :=
    mod_pow_succ_sub_of_testBit_true hbit
  have hmod_m : m % 2 ^ (k + 1) = 2 ^ k + m % 2 ^ k := by
    have := mod_double_of_odd_div m (2 ^ k) (Nat.two_pow_pos k)
      (div_mod2_of_testBit_true hbit)
    rwa [pow_succ]
  have h1 := Nat.div_add_mod m (2 ^ (k + 1))
  have h2 := Nat.div_add_mod (m - 2 ^ k) (2 ^ (k + 1))
  have hstep :
      2 ^ (k + 1) * (m / 2 ^ (k + 1)) =
      2 ^ (k + 1) * ((m - 2 ^ k) / 2 ^ (k + 1)) := by omega
  exact (Nat.eq_of_mul_eq_mul_left hpos hstep).symm

/-- Step lemma (zeta version): applying `monoToLagrangeLevel k` to the partial zeta sum
at level `k` gives the partial sum at level `k + 1`. -/
private lemma zetaPartial_step
    {k : ℕ} (hk : k < n) (p : Vector R (2 ^ n))
    (i : Fin (2 ^ n)) :
    Vector.get
      (monoToLagrangeLevel ⟨k, hk⟩
        (Vector.ofFn (zetaPartial k p)))
      i =
    zetaPartial (k + 1) p i := by
  unfold monoToLagrangeLevel zetaPartial
  simp only [Vector.get_eq_getElem, Vector.getElem_ofFn,
    BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin]
  if hbit : i.val.testBit k = true then
    simp only [hbit, ↓reduceIte]
    have h2k_le := Nat.ge_two_pow_of_testBit hbit
    have hbit' : (i.val - 2 ^ k).testBit k = false := testBit_sub_self hbit
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    by_cases hjbit : j.val.testBit k = true
    · -- bit k of j = 1: contributes to zetaPartial k p i but not to zetaPartial k p (i - 2^k).
      have hnsub' : ¬((i.val - 2 ^ k) &&& j.val = j.val) := by
        intro h; have := submask_testBit_false h hbit'; simp [this] at hjbit
      simp only [hnsub', false_and, ite_false, add_zero]
      by_cases hsub : i.val &&& j.val = j.val
      · simp only [hsub, true_and]
        have hiff := div_pow_succ_eq_of_both_true hbit hjbit
        by_cases heq : i.val / 2 ^ k = j.val / 2 ^ k
        · simp [heq, hiff.mp heq]
        · have : ¬ i.val / 2 ^ (k + 1) = j.val / 2 ^ (k + 1) := fun h => heq (hiff.mpr h)
          simp [heq, this]
      · simp [hsub]
    · -- bit k of j = 0
      simp only [Bool.not_eq_true] at hjbit
      by_cases hsub : i.val &&& j.val = j.val
      · -- j ⊆ i, bit k of i = 1, bit k of j = 0.
        have hne : i.val / 2 ^ k ≠ j.val / 2 ^ k := div_pow_ne_of_diff hbit hjbit
        have hsub' : (i.val - 2 ^ k) &&& j.val = j.val :=
          submask_sub_two_pow hsub hbit hjbit
        have hbit_sub : (i.val - 2 ^ k).testBit k = false := hbit'
        simp only [hsub, hsub', true_and, hne, ite_false, zero_add]
        have hiff := div_pow_succ_eq_of_both_false hbit_sub hjbit
        have hdiv_sub := div_pow_succ_sub_of_testBit_true hbit
        by_cases heq : (i.val - 2 ^ k) / 2 ^ k = j.val / 2 ^ k
        · have hiff_applied := hiff.mp heq
          rw [hdiv_sub] at hiff_applied
          simp [heq, hiff_applied]
        · have : ¬ i.val / 2 ^ (k + 1) = j.val / 2 ^ (k + 1) := by
            intro h; apply heq
            apply hiff.mpr
            rw [hdiv_sub]; exact h
          simp [heq, this]
      · -- j not a subset of i; also not a subset of i - 2^k.
        have hnsub' : ¬((i.val - 2 ^ k) &&& j.val = j.val) := by
          intro h'; apply hsub
          apply Nat.eq_of_testBit_eq; intro l
          rw [Nat.testBit_and]
          have hh := Nat.testBit_and (i.val - 2 ^ k) j.val l
          rw [h'] at hh
          if hl : l = k then
            subst hl; simp [hjbit]
          else
            rw [testBit_sub_ne hbit hl] at hh; exact hh.symm
        simp [hsub, hnsub']
  else
    simp only [Bool.not_eq_true] at hbit
    simp only [hbit]
    apply Finset.sum_congr rfl; intro j _
    by_cases hsub : i.val &&& j.val = j.val
    · have hjf : j.val.testBit k = false := submask_testBit_false hsub hbit
      simp only [hsub, true_and]
      have hiff := div_pow_succ_eq_of_both_false hbit hjf
      by_cases heq : i.val / 2 ^ k = j.val / 2 ^ k
      · simp [heq, hiff.mp heq]
      · have : ¬ i.val / 2 ^ (k + 1) = j.val / 2 ^ (k + 1) := fun h => heq (hiff.mpr h)
        simp [heq, this]
    · simp [hsub]

/-- Fold lemma (zeta version): applying all `n` levels of `monoToLagrange` via `foldl`
yields `Vector.ofFn (zetaPartial n p)`. Proved by induction on the number of levels
already applied, using `zetaPartial_step`. -/
private lemma monoToLagrange_eq_zetaPartial_n
    (p : Vector R (2 ^ n)) :
    monoToLagrange n p = Vector.ofFn (zetaPartial n p) := by
  unfold monoToLagrange
  have htake_full : (List.finRange n).take n = List.finRange n :=
    List.take_of_length_le (by simp)
  suffices h : ∀ m ≤ n,
      ((List.finRange n).take m).foldl
        (fun acc level => monoToLagrangeLevel level acc)
        p =
      Vector.ofFn (zetaPartial m p) by
    have := h n (le_refl n)
    rw [htake_full] at this
    exact this
  intro m hm
  induction m with
  | zero =>
    simp only [List.take_zero, List.foldl_nil]
    ext i hi
    simp only [Vector.getElem_ofFn]
    exact (zetaPartial_zero p ⟨i, hi⟩).symm
  | succ m' ih =>
    have hm' : m' ≤ n := by omega
    have hk : m' < n := by omega
    have hlen : m' < (List.finRange n).length := by
      rw [List.length_finRange]; exact hk
    have hget : (List.finRange n)[m'] = ⟨m', hk⟩ := List.getElem_finRange hlen
    have htake : (List.finRange n).take (m' + 1) =
        (List.finRange n).take m' ++ [⟨m', hk⟩] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlen, hget]
      rfl
    rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil, ih hm']
    ext idx hidx
    simp only [Vector.getElem_ofFn]
    have hstep := zetaPartial_step hk p ⟨idx, hidx⟩
    simp only [Vector.get_eq_getElem] at hstep
    exact hstep

/-- The fast zeta transform `monoToLagrange` is pointwise equal to the naive
`monoToLagrangeSpec`. Mirror of `lagrangeToMono_eq_lagrangeToMonoSpec`. -/
theorem monoToLagrange_eq_monoToLagrangeSpec
    {R : Type*} [AddCommGroup R] {n : ℕ}
    (p : Vector R (2 ^ n)) :
    CMlPolynomial.monoToLagrange n p =
      CMlPolynomial.monoToLagrangeSpec p := by
  rw [monoToLagrange_eq_zetaPartial_n]
  ext i hi
  simp only [Vector.getElem_ofFn]
  exact zetaPartial_n_eq_spec p ⟨i, hi⟩

end ZetaEquivalence

/--
Generates a list of indices representing a range of bit positions [l, r] in increasing order.
Used for optimized recursive transforms that operate on segments of variables.
Returns a list containing `l, l+1, ..., r`.
The result is used to fold over dimensions in `monoToLagrangeSegment` and `lagrangeToMonoSegment`.
-/
def forwardRange (n : ℕ) (r : Fin (n)) (l : Fin (r.val + 1)) : List (Fin n) :=
  let len := r.val - l.val + 1
  List.ofFn (fun (k : Fin len) =>
    let val := l.val + k.val
    have h_bound : val < n := by omega
    ⟨val, h_bound⟩
  )

lemma forwardRange_length (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) :
    (forwardRange n r l).length = r.val - l.val + 1 := by
  unfold forwardRange
  simp only [List.length_ofFn]

lemma forwardRange_eq_of_r_eq (n : ℕ) (r1 r2 : Fin n) (h_r_eq : r1 = r2) (l : Fin (r1.val + 1)) :
    forwardRange n r1 l = forwardRange n r2 ⟨l, by omega⟩ := by
  subst h_r_eq
  rfl

lemma forwardRange_getElem (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) (k : Fin (r.val - l.val + 1)) :
    (forwardRange n r l).get ⟨k, by
    rw [forwardRange]; simp only [List.length_ofFn]; omega⟩ = ⟨l.val + k, by omega⟩ := by
  unfold forwardRange
  simp only [List.get_eq_getElem]
  simp only [List.getElem_ofFn]

lemma forwardRange_succ_right_ne_empty (n : ℕ) (r : Fin (n - 1)) (l : Fin (r.val + 1)) :
    forwardRange n ⟨r + 1, by omega⟩ ⟨l, by simp only; omega⟩ ≠ [] := by
  rw [forwardRange]
  simp only [List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ, ne_eq,
    reduceCtorEq, not_false_eq_true]

lemma forwardRange_pred_le_ne_empty (n : ℕ) (r : Fin n) (l : Fin (r.val + 1))
    (h_l_gt_0 : l.val > 0) : forwardRange n r ⟨l.val - 1, by omega⟩ ≠ [] := by
  rw [forwardRange]
  simp only [List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ, ne_eq,
    reduceCtorEq, not_false_eq_true]

lemma forwardRange_dropLast (n : ℕ) (r : Fin (n - 1)) (l : Fin (r.val + 1)) :
    (forwardRange n ⟨r + 1, by omega⟩ ⟨l, by simp only; omega⟩).dropLast
  = forwardRange n ⟨r, by omega⟩ ⟨l, by simp only [Fin.is_lt]⟩ := by
  apply List.ext_getElem
  · rw [List.length_dropLast, forwardRange_length, forwardRange_length]
    simp only [add_tsub_cancel_right]
    omega
  · intro i h₁ h₂
    simp only [List.length_dropLast, forwardRange_length, add_tsub_cancel_right, Fin.eta] at h₁ h₂
    simp only [List.getElem_dropLast, Fin.eta]
    have hleft := forwardRange_getElem n
      ⟨r.val + 1, by omega⟩ ⟨l, by simp only; omega⟩ (k:=⟨i, by simp only; omega⟩)
    have hright := forwardRange_getElem n
      ⟨r.val, by omega⟩ ⟨l, by simp only; omega⟩ (k:=⟨i, by simp only; omega⟩)
    simp only [List.get_eq_getElem, Fin.eta] at hleft hright
    rw [hleft, hright]

lemma forwardRange_tail (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) (h_l_gt_0 : l.val > 0) :
    (forwardRange n r ⟨l.val - 1, by omega⟩).tail = forwardRange n r l := by
  apply List.ext_getElem
  · rw [List.length_tail, forwardRange_length, forwardRange_length]
    simp only [add_tsub_cancel_right]
    omega
  · intro i h₁ h₂
    simp only [List.length_tail, forwardRange_length, add_tsub_cancel_right] at h₁ h₂
    simp only [List.getElem_tail]
    have hleft := forwardRange_getElem n r ⟨l.val - 1, by omega⟩ (k:=⟨i + 1, by simp only; omega⟩)
    have hright := forwardRange_getElem n r l (k:=⟨i, by omega⟩)
    simp only [List.get_eq_getElem] at hleft hright
    rw [hleft, hright]
    rw [Fin.mk.injEq, Nat.add_comm i 1, ←Nat.add_assoc, Nat.sub_one_add_one (a:=l.val) (by omega)]

lemma forwardRange_0_eq_finRange (n : ℕ) [NeZero n] : forwardRange n ⟨n - 1, by
    have h_ne_zero : n ≠ 0 := NeZero.ne n
    omega
  ⟩ 0 = List.finRange n := by
  apply List.ext_get
  · rw [forwardRange_length, List.length_finRange]
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, tsub_zero]
    have : n ≥ 1 := by
      exact NeZero.one_le
    simp_all only [ge_iff_le, Nat.sub_add_cancel]
  · intro i hi h₂
    have h_fr_get := forwardRange_getElem (n:=n) (r:=⟨n - 1, by grind⟩) (l:=0) (k:=⟨i, by
      rw [forwardRange_length] at hi
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, tsub_zero] at hi
      exact hi
    ⟩)
    simpa [forwardRange] using h_fr_get

/--
Performs the zeta-transform (coefficient to evaluation) on a segment of dimensions from `l` to `r`.
Iteratively applies `monoToLagrangeLevel` for each dimension in the range.
`0 ≤ l ≤ r < n`.
-/
def monoToLagrangeSegment (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) :
    Vector R (2 ^ n) → Vector R (2 ^ n) :=
  let range := forwardRange n r l
  (range.foldl (fun acc h => monoToLagrangeLevel h acc))

/--

Performs the inverse zeta-transform (evaluation to coefficient) on a segment of dimensions

from `l` to `r`.

Iteratively applies `lagrangeToMonoLevel` for each dimension in the range (in reverse order).

`0 ≤ l ≤ r < n`.

-/
def lagrangeToMonoSegment (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) :

    Vector R (2 ^ n) → Vector R (2 ^ n) :=

  let range := forwardRange n r l

  (range.foldr (fun h acc => lagrangeToMonoLevel h acc))

lemma monoToLagrange_eq_monoToLagrangeSegment (n : ℕ) [NeZero n] (v : Vector R (2 ^ n)) :
    have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  monoToLagrange n v = monoToLagrangeSegment n (r:=⟨n - 1, by omega⟩) (l:=⟨0, by omega⟩) v := by
  have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  unfold monoToLagrange monoToLagrangeSegment
  simp only [Fin.zero_eta]
  congr
  exact Eq.symm (forwardRange_0_eq_finRange n)

lemma lagrangeToMono_eq_lagrangeToMonoSegment (n : ℕ) [NeZero n] (v : Vector R (2 ^ n)) :
    have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  lagrangeToMono n v = lagrangeToMonoSegment n (r:=⟨n - 1, by omega⟩) (l:=⟨0, by omega⟩) v := by
  have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  unfold lagrangeToMono lagrangeToMonoSegment
  simp only [Fin.zero_eta]
  congr
  exact Eq.symm (forwardRange_0_eq_finRange n)

lemma testBit_of_sub_two_pow_of_bit_1 {n i : ℕ} (h_testBit_eq_1 : (n).testBit i = true) :
    (n - 2^i).testBit i = false := by
  have h := Nat.testBit_false_eq_getBit_eq_0 (n:=n - 2^i) (k:=i)
  rw [h]
  have h_getBit_eq_0: Nat.getBit i (n - 2^i) = 0 := by
    rw [Nat.getBit_of_sub_two_pow_of_bit_1]
    simp only [↓reduceIte]
    rw [Nat.testBit_true_eq_getBit_eq_1] at h_testBit_eq_1
    exact h_testBit_eq_1
  exact h_getBit_eq_0

theorem lagrangeToMonoLevel_monoToLagrangeLevel_id (v : Vector R (2 ^ n)) (i : Fin n) :
    lagrangeToMonoLevel i (monoToLagrangeLevel i v) = v := by
  unfold lagrangeToMonoLevel monoToLagrangeLevel
  simp only [Vector.getElem_ofFn]
  ext i1 i1_isLt
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]
  if h_i1_testBit: i1.testBit i.val = true then
    simp only [h_i1_testBit, ↓reduceIte]
    have h_testBit_sub_two_pow := testBit_of_sub_two_pow_of_bit_1 h_i1_testBit
    simp only [h_testBit_sub_two_pow, Bool.false_eq_true, ↓reduceIte]
    have hi1_lt : i1 < 2 ^ n := by
      simpa using i1_isLt
    have h_id_lt: i1 - 2 ^ i.val < 2 ^ n := by
      exact Nat.sub_lt_of_lt hi1_lt
    have h_as_assoc := add_sub_assoc (a:=v[i1]'(by omega))
      (b:=v[i1 - 2 ^ i.val]'(h_id_lt)) (c:=v[i1 - 2 ^ i.val]'(h_id_lt))
    rw [h_as_assoc, sub_self, add_zero]
  else
    simp only [h_i1_testBit, Bool.false_eq_true, ↓reduceIte]

theorem monoToLagrangeLevel_lagrangeToMonoLevel_id (v : Vector R (2 ^ n)) (i : Fin n) :
    monoToLagrangeLevel i (lagrangeToMonoLevel i v) = v := by
  unfold lagrangeToMonoLevel monoToLagrangeLevel
  simp only [Vector.getElem_ofFn]
  ext i1 i1_isLt
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]
  if h_i1_testBit: i1.testBit i.val = true then
    simp only [h_i1_testBit, ↓reduceIte]
    have h_testBit_sub_two_pow := testBit_of_sub_two_pow_of_bit_1 h_i1_testBit
    simp only [h_testBit_sub_two_pow, Bool.false_eq_true, ↓reduceIte]
    have hi1_lt : i1 < 2 ^ n := by
      simpa using i1_isLt
    have h_id_lt: i1 - 2 ^ i.val < 2 ^ n := by
      exact Nat.sub_lt_of_lt hi1_lt
    rw [sub_add_cancel]
  else
    simp only [h_i1_testBit, Bool.false_eq_true, ↓reduceIte]

theorem mobius_apply_zeta_apply_eq_id (n : ℕ) [NeZero n] (r : Fin n) (l : Fin (r.val + 1))
    (v : Vector R (2 ^ n)) : lagrangeToMonoSegment n r l (monoToLagrangeSegment n r l v) = v := by
  induction r using Fin.succRecOnSameFinType with
  | zero =>
    rw [lagrangeToMonoSegment, monoToLagrangeSegment, forwardRange]
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_eq_zero, tsub_self, zero_add,
      List.ofFn_succ, Fin.isValue, Fin.cast_zero, Nat.mod_succ, add_zero, Fin.mk_zero',
      Fin.val_cast, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
      List.foldr_cons, List.foldr_nil]
    exact lagrangeToMonoLevel_monoToLagrangeLevel_id v 0
  | succ r1 r1_lt_n h_r1 =>
    unfold lagrangeToMonoSegment monoToLagrangeSegment
    if h_l_eq_r: l.val = (r1 + 1).val then
      rw [forwardRange]
      simp only [List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ,
        List.foldl_cons, List.foldr_cons]
      simp_rw [h_l_eq_r]
      simp only [Fin.eta, tsub_self, List.ofFn_zero, List.foldl_nil, List.foldr_nil]
      exact lagrangeToMonoLevel_monoToLagrangeLevel_id v (r1 + 1)
    else
      have h_l_lt_r: l.val < (r1 + 1).val := by omega
      have h_r1_add_1_val: (r1 + 1).val = r1.val + 1 := by
        rw [Fin.val_add_one']; omega
      have h_range_ne_empty: forwardRange n (r1 + 1) l ≠ [] := by
        have h:= forwardRange_succ_right_ne_empty n
          (r:=⟨r1, by omega⟩) (l:=⟨l, by simp only; omega⟩)
        simp only [ne_eq] at h
        have h_r1_add_1: r1 + 1 = ⟨r1.val + 1, by omega⟩ := by
          exact Fin.eq_mk_iff_val_eq.mpr h_r1_add_1_val
        rw [forwardRange_eq_of_r_eq (r1:=r1 + 1) (r2:=⟨r1.val + 1, by omega⟩) (h_r_eq:=h_r1_add_1)]
        exact h
      rw [List.foldr_split_inner (h:=h_range_ne_empty)]
      rw [List.foldl_split_outer (h:=h_range_ne_empty)]
      rw [lagrangeToMonoLevel_monoToLagrangeLevel_id]
      have h_inductive := h_r1 (l := ⟨l, by exact Nat.lt_of_lt_of_eq h_l_lt_r h_r1_add_1_val⟩)
      rw [lagrangeToMonoSegment, monoToLagrangeSegment] at h_inductive
      simp only at h_inductive
      have h_range_droplast: (forwardRange n (r1 + 1) l).dropLast
        = forwardRange n r1 ⟨↑l, by omega⟩ := by
        have h := forwardRange_dropLast n (r:=⟨r1, by omega⟩) (l:=⟨l, by simp only; omega⟩)
        simp only [Fin.eta] at h
        convert h
      convert h_inductive

lemma zeta_apply_mobius_apply_eq_id (n : ℕ) (r : Fin n) (l : Fin (r.val + 1))
    (v : Vector R (2 ^ n)) :
    monoToLagrangeSegment n r l (lagrangeToMonoSegment n r l v) = v := by
  induction l using Fin.predRecOnSameFinType with
  | last =>
    rw [lagrangeToMonoSegment, monoToLagrangeSegment, forwardRange]
    simp only [add_tsub_cancel_right, tsub_self, zero_add, List.ofFn_succ, Nat.add_one_sub_one,
      Fin.isValue, Fin.cast_zero, Fin.coe_ofNat_eq_mod, Nat.mod_succ, add_zero, Fin.eta,
      Fin.val_cast, List.ofFn_zero, List.foldr_cons, List.foldr_nil,
      List.foldl_cons, List.foldl_nil]
    exact monoToLagrangeLevel_lagrangeToMonoLevel_id v r
  | succ l1 l1_gt_0 h_l1 =>
    unfold lagrangeToMonoSegment monoToLagrangeSegment
    have h_l1_sub_1_lt_r: (⟨l1.val - 1, by omega⟩: Fin (r.val + 1)).val < r.val := by
      simp only
      have h_l1 := l1.isLt
      apply Nat.lt_of_add_lt_add_right (n:=1)
      rw [Nat.sub_one_add_one (by omega)]
      omega
    have h_range_ne_empty: forwardRange n r ⟨l1.val - 1, by omega⟩ ≠ [] := by
      have h:= forwardRange_pred_le_ne_empty n
        (r:=⟨r, by omega⟩) (l:=⟨l1, by simp only; omega⟩) (by omega)
      simp only [ne_eq, h, not_false_eq_true]
    rw [List.foldr_split_outer (h:=h_range_ne_empty)]
    rw [List.foldl_split_inner (h:=h_range_ne_empty)]
    rw [monoToLagrangeLevel_lagrangeToMonoLevel_id]
    have h_inductive := h_l1
    rw [lagrangeToMonoSegment, monoToLagrangeSegment] at h_inductive
    simp only at h_inductive
    have h_range_tail: (forwardRange n r ⟨l1.val - 1, by omega⟩).tail = forwardRange n r l1 := by
      have h := forwardRange_tail n (r:=r) (l:=l1) (by omega)
      convert h
    convert h_inductive

/--
The equivalence between the monomial basis representation (`CMlPolynomial`)
and the Lagrange basis representation (`CMlPolynomialEval`) of a multilinear polynomial.
The forward map is `monoToLagrange` (zeta transform) and the inverse is `lagrangeToMono`
(inverse zeta transform/Mobius transform).
-/
def equivMonomialLagrangeRepr : CMlPolynomial R n ≃ CMlPolynomialEval R n where
  toFun := monoToLagrange n
  invFun := lagrangeToMono n
  left_inv v := by
    if h_n_eq_0: n = 0 then
      subst h_n_eq_0; rfl
    else
      have h_n_ne_zero: n ≠ 0 := by omega
      letI: NeZero n := by exact { out := h_n_eq_0 }
      rw [lagrangeToMono_eq_lagrangeToMonoSegment (n:=n)]
      rw [monoToLagrange_eq_monoToLagrangeSegment (n:=n)]
      simp only [Fin.zero_eta]
      exact
        mobius_apply_zeta_apply_eq_id n
          ⟨n - 1,
            Decidable.byContradiction fun a ↦
              monoToLagrange_eq_monoToLagrangeSegment._proof_1 n (NeZero.ne n) a⟩
          0 v
  right_inv v := by
    if h_n_eq_0: n = 0 then
      subst h_n_eq_0; rfl
    else
      have h_n_ne_zero: n ≠ 0 := by omega
      letI: NeZero n := by exact { out := h_n_eq_0 }
      rw [lagrangeToMono_eq_lagrangeToMonoSegment (n:=n)]
      rw [monoToLagrange_eq_monoToLagrangeSegment (n:=n)]
      exact
        zeta_apply_mobius_apply_eq_id n
          ⟨n - 1,
            Decidable.byContradiction fun a ↦
              monoToLagrange_eq_monoToLagrangeSegment._proof_1 n (NeZero.ne n) a⟩
          ⟨0,
            Decidable.byContradiction fun a ↦
              monoToLagrange_eq_monoToLagrangeSegment._proof_2 n (NeZero.ne n) a⟩
          v

end CMlPolynomial

end CompPoly

/-! ### #eval Tests

This section contains tests to verify the functionality of multilinear polynomial operations.
-/
section Tests

-- #eval CMlPolynomial.zero (n := 2) (R := ℤ)
-- #eval CMlPolynomial.add #v[1, 2, 3, 4] #v[5, 6, 7, 8] (n := 2) (R := ℤ)
-- #eval CMlPolynomial.smul 2 #v[1, 2, 3, 4] (n := 2) (R := ℤ)
-- #eval CMlPolynomialEval.lagrangeBasis #v[(1 : ℤ), 2, 3] (n := 3)
-- #eval CMlPolynomialEval.lagrangeBasis #v[(1 : ℤ), 2] (n := 2)
-- #eval CMlPolynomialEval.eval #v[1, 2, 3, 4] #v[(1 : ℤ), 2] (n := 2)
-- #eval CMlPolynomial.monoToLagrange 2 #v[(1 : ℤ), 2, 3, 4]
-- #eval CMlPolynomial.lagrangeToMono 2 #v[(1 : ℤ), 3, 4, 10]
-- #eval CMlPolynomial.lagrangeToMono 2 (CMlPolynomial.monoToLagrange 2 #v[(1 : ℤ), 2, 3, 4])
-- #eval CMlPolynomial.monoToLagrange 2 (CMlPolynomial.lagrangeToMono 2 #v[(1 : ℤ), 3, 4, 10])
-- #eval CMlPolynomial.monoToLagrange 1 #v[(1 : ℤ), 2]
-- #eval CMlPolynomial.monoToLagrange 3 #v[(1 : ℤ), 2, 3, 4, 5, 6, 7, 8]
-- #eval CMlPolynomialEval.lagrangeBasis #v[(1 : ℤ)] (n := 1)
-- #eval CMlPolynomialEval.lagrangeBasis #v[(1 : ℤ), 2, 3, 4] (n := 4)
-- #eval (CMlPolynomial.mk 2 #v[1, 2, 3, 4]) + (CMlPolynomial.mk 2 #v[5, 6, 7, 8])
-- #eval ((4: ℤ) • (CMlPolynomial.mk 2 #v[(1: ℤ), 2, 3, 4]))

end Tests
