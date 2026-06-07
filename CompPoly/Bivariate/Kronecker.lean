/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/

import CompPoly.Bivariate.Basic
import CompPoly.Univariate.ToPoly
import CompPoly.Univariate.NTT.FastMul
import CompPoly.Univariate.NTTFast.Correctness

/-!
# Kronecker substitution for bivariate polynomials

Kronecker substitution (linearization) reduces a bivariate multiplication to a single
univariate multiplication. With a stride `D` we substitute `X ↦ t`, `Y ↦ t^D`, packing
`p : CBivariate R` into `kroneckerPack D p : CPolynomial R`. The coefficient of `X^i Y^j`
lands at position `D * j + i`, so the packing is faithful whenever each monomial has
X-degree `< D`.

`kroneckerPack` is the evaluation of the ring homomorphism that fixes the X-coefficients
and sends `Y` to `X^D`, hence it is multiplicative unconditionally. `kroneckerUnpack`
recovers the bivariate coefficients via Euclidean division by `D`. The main result
`kroneckerUnpack_mul` states that

  `kroneckerUnpack D (kroneckerPack D p * kroneckerPack D q) = p * q`

whenever `natDegreeX (p * q) < D`, i.e. the product fits in the stride. Once an NTT-based
univariate multiplication lands, this turns bivariate multiplication into a single fast
univariate multiplication.
-/

namespace CompPoly

namespace CPolynomial

variable {R : Type*}

/-- A coefficient above the `natDegree` vanishes. -/
theorem coeff_eq_zero_of_natDegree_lt [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial R} {i : ℕ} (h : p.natDegree < i) : coeff p i = 0 := by
  by_contra hc
  exact absurd (le_natDegree_of_ne_zero hc) (Nat.not_le.2 h)

/-- Coefficients of a polynomial shifted by `X ^ m`: a clean stride lemma used by
Kronecker packing. -/
theorem coeff_mul_X_pow [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (c : CPolynomial R) (m n : ℕ) :
    coeff (c * X ^ m) n = if m ≤ n then coeff c (n - m) else 0 := by
  induction m generalizing n with
  | zero => simp [pow_zero]
  | succ m ih =>
    rw [pow_succ, ← mul_assoc]
    cases n with
    | zero => rw [coeff_mul_X_zero]; simp
    | succ k =>
      rw [coeff_mul_X_succ, ih]
      by_cases h : m ≤ k
      · rw [if_pos h, if_pos (Nat.succ_le_succ h), Nat.succ_sub_succ]
      · rw [if_neg h, if_neg (fun hc => h (Nat.le_of_succ_le_succ hc))]

end CPolynomial

namespace CBivariate

section Coeff

variable {R : Type*}

/-- Bivariate coefficients are additive. -/
theorem coeff_add [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p q : CBivariate R) (i j : ℕ) :
    coeff (p + q) i j = coeff p i j + coeff q i j := by
  show ((p + q).val.coeff j).coeff i = (p.val.coeff j).coeff i + (q.val.coeff j).coeff i
  rw [show (p + q).val.coeff j = p.val.coeff j + q.val.coeff j from CPolynomial.coeff_add p q j]
  exact CPolynomial.coeff_add _ _ i

/-- Bivariate coefficients distribute over finite sums. -/
theorem coeff_finset_sum [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → CBivariate R) (i j : ℕ) :
    coeff (s.sum f) i j = s.sum (fun t => coeff (f t) i j) := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    show ((0 : CBivariate R).val.coeff j).coeff i = 0
    rw [show (0 : CBivariate R).val.coeff j = 0 from CPolynomial.coeff_zero j]
    exact CPolynomial.coeff_zero i
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [coeff_add, ih]

/-- Coefficient of a bivariate monomial `c * X^a * Y^b`. -/
theorem coeff_monomialXY [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a b : ℕ) (c : R) (i j : ℕ) :
    coeff (monomialXY a b c) i j = if i = a ∧ j = b then c else 0 := by
  show (CPolynomial.coeff (monomialXY a b c) j).coeff i = if i = a ∧ j = b then c else 0
  unfold monomialXY
  rw [CPolynomial.coeff_monomial]
  by_cases hj : j = b
  · rw [if_pos hj, CPolynomial.coeff_monomial]
    by_cases hi : i = a
    · rw [if_pos hi, if_pos ⟨hi, hj⟩]
    · rw [if_neg hi, if_neg (fun h => hi h.1)]
  · rw [if_neg hj, CPolynomial.coeff_zero, if_neg (fun h => hj h.2)]

/-- Two bivariate polynomials are equal iff all their coefficients agree. -/
theorem eq_iff_coeff [Zero R] [BEq R] [LawfulBEq R] {p q : CBivariate R} :
    p = q ↔ ∀ i j, coeff p i j = coeff q i j := by
  constructor
  · intro h i j; rw [h]
  · intro h
    refine CPolynomial.eq_iff_coeff.2 (fun j => ?_)
    rw [CPolynomial.eq_iff_coeff]
    intro i
    exact h i j

end Coeff

section Pack

variable {R : Type*}

/-- Pack a bivariate polynomial into a univariate one by substituting `X ↦ t`, `Y ↦ t^D`.
The coefficient of `X^i Y^j` (with `i < D`) lands at position `D * j + i`. -/
def kroneckerPack [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (D : ℕ) (p : CBivariate R) : CPolynomial R :=
  CPolynomial.eval₂ (RingHom.id (CPolynomial R)) (CPolynomial.X ^ D) p

/-- Unpack a univariate polynomial into a bivariate one: position `k` becomes the
monomial `X^(k % D) Y^(k / D)`. -/
def kroneckerUnpack [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (D : ℕ) (P : CPolynomial R) : CBivariate R :=
  (CPolynomial.support P).sum
    (fun k => monomialXY (k % D) (k / D) (CPolynomial.coeff P k))

/-- Packing is multiplicative: it is the evaluation of a ring homomorphism. -/
theorem kroneckerPack_mul [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (D : ℕ) (p q : CBivariate R) :
    kroneckerPack D (p * q) = kroneckerPack D p * kroneckerPack D q := by
  unfold kroneckerPack
  simp only [CPolynomial.eval₂_toPoly]
  rw [show CPolynomial.toPoly (p * q) = CPolynomial.toPoly p * CPolynomial.toPoly q from
    CPolynomial.toPoly_mul p q, Polynomial.eval₂_mul]

/-- Packing coefficient lemma: when every X-degree is `< D`, the coefficient at position
`n` of the packed polynomial is the bivariate coefficient at `(n % D, n / D)`. -/
theorem coeff_kroneckerPack [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    {D : ℕ} (hD : 0 < D) (p : CBivariate R) (hp : natDegreeX p < D) (n : ℕ) :
    CPolynomial.coeff (kroneckerPack D p) n = coeff p (n % D) (n / D) := by
  have hsum : kroneckerPack D p
      = (CPolynomial.support p).sum
          (fun i => CPolynomial.coeff p i * CPolynomial.X ^ (D * i)) := by
    unfold kroneckerPack
    rw [CPolynomial.eval₂_eq_sum_support]
    apply Finset.sum_congr rfl
    intro i _
    rw [RingHom.id_apply, ← pow_mul]
  rw [hsum, CPolynomial.coeff_finset_sum]
  rw [Finset.sum_eq_single (n / D)]
  · rw [CPolynomial.coeff_mul_X_pow]
    have hle : D * (n / D) ≤ n := Nat.mul_div_le n D
    rw [if_pos hle]
    have hsub : n - D * (n / D) = n % D := by
      have := Nat.mod_add_div n D; omega
    rw [hsub]
    rfl
  · intro i hi hine
    rw [CPolynomial.coeff_mul_X_pow]
    split_ifs with hle
    · by_contra hc
      have hdeg : n - D * i ≤ (CPolynomial.coeff p i).natDegree :=
        CPolynomial.le_natDegree_of_ne_zero hc
      have hsup : (CPolynomial.coeff p i).natDegree ≤ natDegreeX p := by
        unfold natDegreeX
        exact Finset.le_sup (f := fun n => (p.val.coeff n).natDegree) hi
      have hlt : n - D * i < D := lt_of_le_of_lt (le_trans hdeg hsup) hp
      apply hine
      have h1 : i ≤ n / D := (Nat.le_div_iff_mul_le hD).2 (by rw [Nat.mul_comm]; exact hle)
      have h2 : n / D < i + 1 :=
        (Nat.div_lt_iff_lt_mul hD).2 (by rw [Nat.mul_comm, Nat.mul_succ]; omega)
      omega
    · rfl
  · intro hns
    have h0 : CPolynomial.coeff p (n / D) = 0 := by
      by_contra hc
      exact hns ((CPolynomial.mem_support_iff p (n / D)).2 hc)
    rw [h0, zero_mul, CPolynomial.coeff_zero]

end Pack

section Unpack

variable {R : Type*}

/-- Unpacking coefficient lemma (above the stride): a bivariate coefficient with
X-exponent `≥ D` is zero. -/
theorem coeff_kroneckerUnpack_of_le [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R] {D : ℕ} (hD : 0 < D) (P : CPolynomial R) (i j : ℕ) (hi : D ≤ i) :
    coeff (kroneckerUnpack D P) i j = 0 := by
  unfold kroneckerUnpack
  rw [coeff_finset_sum]
  apply Finset.sum_eq_zero
  intro k _
  rw [coeff_monomialXY, if_neg]
  rintro ⟨hik, _⟩
  have : k % D < D := Nat.mod_lt _ hD
  omega

/-- Unpacking coefficient lemma (within the stride): for `i < D`, the bivariate coefficient
at `(i, j)` of the unpacked polynomial is the univariate coefficient at `D * j + i`. -/
theorem coeff_kroneckerUnpack [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R] {D : ℕ} (hD : 0 < D) (P : CPolynomial R) (i j : ℕ) (hi : i < D) :
    coeff (kroneckerUnpack D P) i j = CPolynomial.coeff P (D * j + i) := by
  have hmod : (D * j + i) % D = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  have hdiv : (D * j + i) / D = j := by
    rw [Nat.add_comm, Nat.add_mul_div_left i j hD, Nat.div_eq_of_lt hi, Nat.zero_add]
  unfold kroneckerUnpack
  rw [coeff_finset_sum]
  rw [Finset.sum_eq_single (D * j + i)]
  · rw [coeff_monomialXY, if_pos]
    exact ⟨hmod.symm, hdiv.symm⟩
  · intro k _ hkne
    rw [coeff_monomialXY, if_neg]
    rintro ⟨hik, hjk⟩
    apply hkne
    subst hik; subst hjk
    have := Nat.mod_add_div k D
    omega
  · intro hns
    rw [coeff_monomialXY, if_pos ⟨hmod.symm, hdiv.symm⟩]
    by_contra hc
    exact hns ((CPolynomial.mem_support_iff P (D * j + i)).2 hc)

end Unpack

section Correctness

variable {R : Type*}

/-- Round-trip: under the X-degree bound, unpacking recovers the packed polynomial. -/
theorem kroneckerUnpack_kroneckerPack [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R] {D : ℕ} (hD : 0 < D) (p : CBivariate R) (hp : natDegreeX p < D) :
    kroneckerUnpack D (kroneckerPack D p) = p := by
  rw [eq_iff_coeff]
  intro i j
  by_cases hi : i < D
  · rw [coeff_kroneckerUnpack hD _ i j hi, coeff_kroneckerPack hD p hp]
    have hmod : (D * j + i) % D = i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
    have hdiv : (D * j + i) / D = j := by
      rw [Nat.add_comm, Nat.add_mul_div_left i j hD, Nat.div_eq_of_lt hi, Nat.zero_add]
    rw [hmod, hdiv]
  · rw [coeff_kroneckerUnpack_of_le hD _ i j (Nat.le_of_not_lt hi)]
    -- the bivariate coefficient at X-exponent `i ≥ D > natDegreeX p` vanishes
    have hdeg : (CPolynomial.coeff p j).natDegree < i := by
      by_cases hj : j ∈ CPolynomial.support p
      · have : (CPolynomial.coeff p j).natDegree ≤ natDegreeX p := by
          unfold natDegreeX
          exact Finset.le_sup (f := fun n => (p.val.coeff n).natDegree) hj
        omega
      · have h0 : CPolynomial.coeff p j = 0 := by
          by_contra hc
          exact hj ((CPolynomial.mem_support_iff p j).2 hc)
        rw [h0]
        have hz : (0 : CPolynomial R).natDegree = 0 := rfl
        omega
    exact (CPolynomial.coeff_eq_zero_of_natDegree_lt hdeg).symm

/-- **Kronecker substitution correctness.** When the product fits within the stride
(`natDegreeX (p * q) < D`), bivariate multiplication equals one univariate multiplication
followed by unpacking. -/
theorem kroneckerUnpack_mul [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R] {D : ℕ} (hD : 0 < D) (p q : CBivariate R)
    (hpq : natDegreeX (p * q) < D) :
    kroneckerUnpack D (kroneckerPack D p * kroneckerPack D q) = p * q := by
  rw [← kroneckerPack_mul]
  exact kroneckerUnpack_kroneckerPack hD (p * q) hpq

/-- **Kronecker substitution backed by NTT multiplication.** Combines `kroneckerPack` /
`kroneckerUnpack` with the NTT-accelerated `withFallback` univariate multiplication: when
the product fits the stride (`natDegreeX (p * q) < D`), bivariate multiplication reduces to
a single fast univariate multiplication.

No domain-fit hypothesis is needed: `withFallback` selects a fitting NTT domain when one
exists and otherwise falls back to schoolbook multiplication, so it is unconditionally equal
to `*`. The only remaining hypothesis, `natDegreeX (p * q) < D`, is intrinsic to Kronecker
packing, not to the multiplication backend. -/
theorem kroneckerUnpack_withFallback [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (bestDomainForLength? : (requiredLen : Nat) →
      Option (CPolynomial.NTT.FittingDomain R requiredLen))
    {D : ℕ} (hD : 0 < D) (p q : CBivariate R) (hpq : natDegreeX (p * q) < D) :
    kroneckerUnpack D
        (CPolynomial.NTT.FastMul.withFallback bestDomainForLength?
          (kroneckerPack D p) (kroneckerPack D q))
      = p * q := by
  rw [CPolynomial.NTT.FastMul.withFallback_eq_mul]
  exact kroneckerUnpack_mul hD p q hpq

/-- **Kronecker substitution backed by the recursive (NTTFast) multiplication.** As
`kroneckerUnpack_withFallback`, but using the recursive radix-2/radix-4 NTT pipeline
(`CPolynomial.NTTFast.withFallback`) as the univariate multiplication backend.

No domain-fit hypothesis is needed: `withFallback` falls back to schoolbook multiplication
when no NTT domain fits, so it is unconditionally equal to `*`. The only remaining
hypothesis, `natDegreeX (p * q) < D`, is intrinsic to Kronecker packing. -/
theorem kroneckerUnpack_withFallbackFast [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (bestDomainForLength? : (requiredLen : Nat) →
      Option (CPolynomial.NTT.FittingDomain R requiredLen))
    {D : ℕ} (hD : 0 < D) (p q : CBivariate R) (hpq : natDegreeX (p * q) < D) :
    kroneckerUnpack D
        (CPolynomial.NTTFast.withFallback bestDomainForLength?
          (kroneckerPack D p) (kroneckerPack D q))
      = p * q := by
  rw [CPolynomial.NTTFast.withFallback_eq_mul]
  exact kroneckerUnpack_mul hD p q hpq

end Correctness

end CBivariate

end CompPoly
