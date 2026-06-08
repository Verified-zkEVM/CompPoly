/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/

import CompPoly.Bivariate.Basic
import CompPoly.Univariate.ToPoly
import CompPoly.Univariate.NTT.FastMul
import CompPoly.Univariate.NTTFast.Correctness

/-!
# Kronecker substitution for bivariate polynomials

Kronecker substitution turns a bivariate multiplication into a univariate multiplication by
fixing a gap `D` and substituting `X ↦ t`, `Y ↦ t ^ D`. This sends a bivariate
polynomial `p : CBivariate R` to a univariate polynomial `kroneckerPack D p : CPolynomial R`
in which the coefficient of `X ^ i Y ^ j` is placed at position `D * j + i`.

Packing is a ring homomorphism, so for any `p` and `q` the packed product equals the
product of the packed operands, with no condition on degrees. A condition is needed only to
unpack the result. The position `D * j + i` determines `i` and `j` only when `i < D`, so
packing can be reversed exactly on polynomials with `natDegreeX < D`. Recovering a product
`p * q` therefore needs
`natDegreeX (p * q) < D`, and since `natDegreeX (p * q) ≤ natDegreeX p + natDegreeX q`, it is
enough to choose `D` greater than `natDegreeX p + natDegreeX q`.

Kronecker substitution is not itself an optimisation; it lets a fast univariate
multiplication carry out the bivariate one. The NTT versions multiply through `withFallback`,
which uses an NTT domain when one fits and otherwise multiplies the ordinary way, so it is
always equal to `*` and adds no assumption about the domain beyond the gap condition above.

## Main results

* `kroneckerPack` / `kroneckerUnpack` — the substitution and its inverse.
* `kroneckerPack_mul` — packing is multiplicative.
* `kroneckerUnpack_mul` — bivariate multiplication as pack, multiply, unpack.
* `kroneckerPackFast` / `kroneckerUnpackFast` — linear-time versions, proved equal to the above.
* `kroneckerUnpack_withFallback` / `kroneckerUnpack_withFallbackFast` — multiplication backed by
  the classic and recursive NTT.
-/

namespace CompPoly

namespace CPolynomial

variable {R : Type*}

/-- A coefficient past the degree is zero. -/
theorem coeff_eq_zero_of_natDegree_lt [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial R} {i : ℕ} (h : p.natDegree < i) : coeff p i = 0 := by
  by_contra hc
  exact absurd (le_natDegree_of_ne_zero hc) (Nat.not_le.2 h)

/-- Coefficient of `c * X ^ m`. -/
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

/-- Multiplication by `X ^ m`, implemented as a coefficient shift. -/
def shiftPow [Zero R] [BEq R] [LawfulBEq R] (m : ℕ) (p : CPolynomial R) : CPolynomial R :=
  ⟨(p.val.mulPowX m).trim, CPolynomial.Raw.Trim.isCanonical_trim _⟩

/-- Coefficient of `shiftPow m p`. -/
theorem coeff_shiftPow [Zero R] [BEq R] [LawfulBEq R] (m : ℕ) (p : CPolynomial R) (n : ℕ) :
    coeff (shiftPow m p) n = if m ≤ n then coeff p (n - m) else 0 := by
  show ((p.val.mulPowX m).trim).coeff n = _
  rw [CPolynomial.Raw.Trim.coeff_eq_coeff]
  simp only [CPolynomial.Raw.mulPowX, CPolynomial.Raw.coeff, CPolynomial.Raw.mk,
    Array.getD_eq_getD_getElem?]
  by_cases h : m ≤ n
  · rw [if_pos h, Array.getElem?_append_right (by simpa using h)]
    simp
  · rw [if_neg h, Array.getElem?_append_left (by simpa using Nat.lt_of_not_le h)]
    simp [Nat.lt_of_not_le h]

/-- `shiftPow m p = p * X ^ m`. -/
theorem shiftPow_eq_mul_X_pow [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (m : ℕ) (p : CPolynomial R) : shiftPow m p = p * X ^ m := by
  rw [eq_iff_coeff]
  intro n
  rw [coeff_shiftPow, coeff_mul_X_pow]

end CPolynomial

namespace CBivariate

section Gap

variable {D i j : ℕ}

/-- The remainder of the packed position `D * j + i` is `i`. -/
private theorem gap_mod (hi : i < D) : (D * j + i) % D = i := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]

/-- The quotient of the packed position `D * j + i` is `j`. -/
private theorem gap_div (hD : 0 < D) (hi : i < D) : (D * j + i) / D = j := by
  rw [Nat.add_comm, Nat.add_mul_div_left i j hD, Nat.div_eq_of_lt hi, Nat.zero_add]

end Gap

section Pack

variable {R : Type*}

/-- Pack a bivariate polynomial into a univariate one with gap `D`. -/
def kroneckerPack [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (D : ℕ) (p : CBivariate R) : CPolynomial R :=
  CPolynomial.eval₂ (RingHom.id (CPolynomial R)) (CPolynomial.X ^ D) p

/-- Unpack a univariate polynomial into a bivariate one with gap `D`. -/
def kroneckerUnpack [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (D : ℕ) (P : CPolynomial R) : CBivariate R :=
  (CPolynomial.support P).sum
    (fun k => monomialXY (k % D) (k / D) (CPolynomial.coeff P k))

/-- Packing is multiplicative. -/
theorem kroneckerPack_mul [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (D : ℕ) (p q : CBivariate R) :
    kroneckerPack D (p * q) = kroneckerPack D p * kroneckerPack D q := by
  unfold kroneckerPack
  simp only [CPolynomial.eval₂_toPoly]
  rw [show CPolynomial.toPoly (p * q) = CPolynomial.toPoly p * CPolynomial.toPoly q from
    CPolynomial.toPoly_mul p q, Polynomial.eval₂_mul]

/-- Packing written as a sum of shifted `Y`-coefficients. -/
theorem kroneckerPack_eq_sum [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (D : ℕ) (p : CBivariate R) :
    kroneckerPack D p
      = (CPolynomial.support p).sum
          (fun i => CPolynomial.coeff p i * CPolynomial.X ^ (D * i)) := by
  unfold kroneckerPack
  rw [CPolynomial.eval₂_eq_sum_support]
  apply Finset.sum_congr rfl
  intro i _
  rw [RingHom.id_apply, ← pow_mul]

/-- Coefficient of the packed polynomial, when the `X`-degree is below the gap. -/
theorem coeff_kroneckerPack [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    {D : ℕ} (hD : 0 < D) (p : CBivariate R) (hp : natDegreeX p < D) (n : ℕ) :
    CPolynomial.coeff (kroneckerPack D p) n = coeff p (n % D) (n / D) := by
  rw [kroneckerPack_eq_sum, CPolynomial.coeff_finset_sum, Finset.sum_eq_single (n / D)]
  · rw [CPolynomial.coeff_mul_X_pow, if_pos (Nat.mul_div_le n D)]
    have hsub : n - D * (n / D) = n % D := by have := Nat.mod_add_div n D; omega
    rw [hsub]; rfl
  · intro i hi hine
    rw [CPolynomial.coeff_mul_X_pow]
    split_ifs with hle
    · refine CPolynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (b := natDegreeX p) ?_ ?_)
      · exact Finset.le_sup (f := fun m => (p.val.coeff m).natDegree) hi
      · have hilt : i < n / D :=
          lt_of_le_of_ne ((Nat.le_div_iff_mul_le hD).2 (by rw [Nat.mul_comm]; exact hle)) hine
        have : D * i + D ≤ n := by
          have := Nat.mul_le_mul_left D hilt; rw [Nat.mul_succ] at this
          exact this.trans (Nat.mul_div_le n D)
        omega
    · rfl
  · intro hns
    have h0 : CPolynomial.coeff p (n / D) = 0 := by
      by_contra hc; exact hns ((CPolynomial.mem_support_iff p (n / D)).2 hc)
    rw [h0, zero_mul, CPolynomial.coeff_zero]

/-- Efficient packing, linear in the output. -/
def kroneckerPackFast [Semiring R] [BEq R] [LawfulBEq R]
    (D : ℕ) (p : CBivariate R) : CPolynomial R :=
  (CPolynomial.support p).sum
    (fun j => CPolynomial.shiftPow (D * j) (CPolynomial.coeff p j))

/-- `kroneckerPackFast` equals `kroneckerPack`. -/
theorem kroneckerPackFast_eq [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (D : ℕ) (p : CBivariate R) : kroneckerPackFast D p = kroneckerPack D p := by
  rw [kroneckerPackFast, kroneckerPack_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [CPolynomial.shiftPow_eq_mul_X_pow]

end Pack

section Unpack

variable {R : Type*}

/-- Unpacked coefficients with `X`-exponent at least `D` are zero. -/
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

/-- Unpacked coefficient at `(i, j)` with `i < D`. -/
theorem coeff_kroneckerUnpack [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R] {D : ℕ} (hD : 0 < D) (P : CPolynomial R) (i j : ℕ) (hi : i < D) :
    coeff (kroneckerUnpack D P) i j = CPolynomial.coeff P (D * j + i) := by
  have hkey : i = (D * j + i) % D ∧ j = (D * j + i) / D :=
    ⟨(gap_mod hi).symm, (gap_div hD hi).symm⟩
  unfold kroneckerUnpack
  rw [coeff_finset_sum, Finset.sum_eq_single (D * j + i)]
  · rw [coeff_monomialXY, if_pos hkey]
  · intro k _ hkne
    rw [coeff_monomialXY, if_neg]
    rintro ⟨hik, hjk⟩
    apply hkne
    subst hik; subst hjk
    have := Nat.mod_add_div k D
    omega
  · intro hns
    rw [coeff_monomialXY, if_pos hkey]
    by_contra hc
    exact hns ((CPolynomial.mem_support_iff P (D * j + i)).2 hc)

/-- The length-`D` slice of `P` holding column `j`. -/
def window [Zero R] [BEq R] [LawfulBEq R] (D j : ℕ) (P : CPolynomial R) : CPolynomial R :=
  ⟨CPolynomial.Raw.trim (P.val.extract (D * j) (D * j + D)),
    CPolynomial.Raw.Trim.isCanonical_trim _⟩

/-- Coefficient of a column slice. -/
theorem coeff_window [Zero R] [BEq R] [LawfulBEq R] (D j : ℕ) (P : CPolynomial R) (i : ℕ) :
    CPolynomial.coeff (window D j P) i =
      if i < D then CPolynomial.coeff P (D * j + i) else 0 := by
  have hcoe : CPolynomial.coeff P (D * j + i) = (P.val[D * j + i]?).getD 0 := by
    rw [CPolynomial.coeff, CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?]
  show CPolynomial.Raw.coeff (CPolynomial.Raw.trim (P.val.extract (D * j) (D * j + D))) i = _
  rw [CPolynomial.Raw.Trim.coeff_eq_coeff, CPolynomial.Raw.coeff,
    Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  by_cases hiD : i < D
  · rw [if_pos hiD, hcoe]
    by_cases hb : i < min (D * j + D) P.val.size - D * j
    · rw [if_pos hb]
    · rw [if_neg hb, Nat.not_lt] at *
      have hsz : P.val.size ≤ D * j + i := by omega
      rw [Array.getElem?_eq_none hsz]
  · rw [if_neg hiD, Nat.not_lt] at *
    rw [if_neg (by omega : ¬ i < min (D * j + D) P.val.size - D * j)]
    rfl

/-- Efficient unpacking, assembling columns directly. -/
def kroneckerUnpackFast [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (D : ℕ) (P : CPolynomial R) : CBivariate R :=
  (Finset.range (P.natDegree / D + 1)).sum
    (fun j => CPolynomial.monomial j (window D j P))

/-- `kroneckerUnpackFast` equals `kroneckerUnpack`. -/
theorem kroneckerUnpackFast_eq [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    {D : ℕ} (hD : 0 < D) (P : CPolynomial R) :
    kroneckerUnpackFast D P = kroneckerUnpack D P := by
  rw [eq_iff_coeff]
  intro i j
  rw [kroneckerUnpackFast, coeff_finset_sum]
  simp only [coeff_monomialY]
  rw [Finset.sum_ite_eq (Finset.range (P.natDegree / D + 1)) j
    (fun j' => CPolynomial.coeff (window D j' P) i), coeff_window]
  by_cases hiD : i < D
  · rw [if_pos hiD, coeff_kroneckerUnpack hD _ i j hiD]
    by_cases hjr : j ∈ Finset.range (P.natDegree / D + 1)
    · rw [if_pos hjr]
    · rw [if_neg hjr]
      rw [Finset.mem_range, Nat.not_lt] at hjr
      refine (CPolynomial.coeff_eq_zero_of_natDegree_lt ?_).symm
      have : P.natDegree < D * j := by
        rw [Nat.mul_comm]; exact (Nat.div_lt_iff_lt_mul hD).1 hjr
      omega
  · rw [if_neg hiD, coeff_kroneckerUnpack_of_le hD _ i j (Nat.le_of_not_lt hiD)]
    by_cases hjr : j ∈ Finset.range (P.natDegree / D + 1) <;> simp [hjr]

end Unpack

section Correctness

variable {R : Type*}

/-- Unpacking recovers a packed polynomial when its `X`-degree is below the gap. -/
theorem kroneckerUnpack_kroneckerPack [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R] {D : ℕ} (hD : 0 < D) (p : CBivariate R) (hp : natDegreeX p < D) :
    kroneckerUnpack D (kroneckerPack D p) = p := by
  rw [eq_iff_coeff]
  intro i j
  by_cases hi : i < D
  · rw [coeff_kroneckerUnpack hD _ i j hi, coeff_kroneckerPack hD p hp,
      gap_mod hi, gap_div hD hi]
  · rw [coeff_kroneckerUnpack_of_le hD _ i j (Nat.le_of_not_lt hi)]
    have hdeg : (CPolynomial.coeff p j).natDegree < i := by
      by_cases hj : j ∈ CPolynomial.support p
      · exact lt_of_le_of_lt (Finset.le_sup (f := fun n => (p.val.coeff n).natDegree) hj)
          (lt_of_lt_of_le hp (Nat.le_of_not_lt hi))
      · have h0 : CPolynomial.coeff p j = 0 := by
          by_contra hc; exact hj ((CPolynomial.mem_support_iff p j).2 hc)
        rw [h0]; show 0 < i; omega
    exact (CPolynomial.coeff_eq_zero_of_natDegree_lt hdeg).symm

/-- Bivariate multiplication as pack, univariate multiply, unpack, when the product fits
the gap. -/
theorem kroneckerUnpack_mul [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R] {D : ℕ} (hD : 0 < D) (p q : CBivariate R)
    (hpq : natDegreeX (p * q) < D) :
    kroneckerUnpack D (kroneckerPack D p * kroneckerPack D q) = p * q := by
  rw [← kroneckerPack_mul]
  exact kroneckerUnpack_kroneckerPack hD (p * q) hpq

/-- `kroneckerUnpack_mul` for the efficient `kroneckerPackFast` / `kroneckerUnpackFast`. -/
theorem kroneckerUnpackFast_mul [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R] {D : ℕ} (hD : 0 < D) (p q : CBivariate R)
    (hpq : natDegreeX (p * q) < D) :
    kroneckerUnpackFast D (kroneckerPackFast D p * kroneckerPackFast D q) = p * q := by
  rw [kroneckerPackFast_eq, kroneckerPackFast_eq, kroneckerUnpackFast_eq hD]
  exact kroneckerUnpack_mul hD p q hpq

/-- Bivariate multiplication using the NTT (`withFallback`) as the univariate backend. -/
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

/-- Bivariate multiplication using the recursive NTT (`NTTFast.withFallback`) as the
univariate backend. -/
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
