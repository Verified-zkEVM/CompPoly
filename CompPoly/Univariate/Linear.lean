/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Desmond Coles, Derek Sorensen
-/
import CompPoly.Univariate.Basic

/-!
# Linear Algebra API for Computable Univariate Polynomials

This file contains linear maps and instance-stable bounded-degree predicates for `CPolynomial`.
-/

namespace CompPoly

namespace CPolynomial

variable {R : Type*}

section LinearMaps

variable [Semiring R] [BEq R] [LawfulBEq R]

/-- This is an R-linear function that returns the coefficient of X^n. -/
def lcoeff (n : ℕ) : (CPolynomial R) →ₗ[R] R where
  toFun p := coeff p n
  map_add' p q := coeff_add p q n
  map_smul' r p := coeff_smul r p n

end LinearMaps

section DegreeBounds

variable [Semiring R] [BEq R]

/-- The set of `CPolynomial R` consisting of polynomials of degree ≤ `n`. -/
def degreeLE (n : WithBot ℕ) : Set (CPolynomial R) :=
  { p | p.val.degreeBound ≤ n }

/-- The set of `CPolynomial R` consisting of polynomials of degree < `n`. -/
def degreeLT (n : ℕ) : Set (CPolynomial R) :=
  { p | p.val.degreeBound < n }

omit [BEq R] in
/-- `degreeLT n` is exactly the bounded-size carrier storing at most `n` coefficients. -/
theorem mem_degreeLT_iff_size_le {n : ℕ} {p : CPolynomial R} :
    p ∈ degreeLT (R := R) n ↔ p.val.size ≤ n := by
  cases hs : p.val.size with
  | zero =>
      simp [degreeLT, Raw.degreeBound, hs]
  | succ m =>
      simp [degreeLT, Raw.degreeBound, hs]

omit [BEq R] in
/-- The zero polynomial has bounded degree for every cutoff. -/
theorem zero_mem_degreeLT (n : ℕ) : (0 : CPolynomial R) ∈ degreeLT (R := R) n := by
  rw [mem_degreeLT_iff_size_le]
  exact Nat.zero_le n

end DegreeBounds

section DegreeLTSubtype

variable [Semiring R] [BEq R] [LawfulBEq R]

/-- `degreeLT n` is closed under addition. -/
theorem add_mem_degreeLT {n : ℕ} {p q : CPolynomial R}
    (hp : p ∈ degreeLT (R := R) n) (hq : q ∈ degreeLT (R := R) n) :
    p + q ∈ degreeLT (R := R) n := by
  rw [mem_degreeLT_iff_size_le] at hp hq ⊢
  calc
    (p + q).val.size = (Raw.addRaw p.val q.val).trim.size := by rfl
    _ ≤ (Raw.addRaw p.val q.val).size := Raw.Trim.size_le_size _
    _ = max p.val.size q.val.size := Raw.add_size
    _ ≤ n := max_le hp hq

/-- `degreeLT n` is closed under additive scalar multiplication. -/
theorem nsmul_mem_degreeLT {n m : ℕ} {p : CPolynomial R}
    (hp : p ∈ degreeLT (R := R) n) :
    m • p ∈ degreeLT (R := R) n := by
  rw [mem_degreeLT_iff_size_le] at hp ⊢
  calc
    (m • p).val.size = (Raw.nsmulRaw m p.val).trim.size := by rfl
    _ ≤ (Raw.nsmulRaw m p.val).size := Raw.Trim.size_le_size _
    _ = p.val.size := by simp [Raw.nsmulRaw]
    _ ≤ n := hp

/-- `degreeLT n` is closed under semiring scalar multiplication. -/
theorem smul_mem_degreeLT {n : ℕ} (r : R) {p : CPolynomial R}
    (hp : p ∈ degreeLT (R := R) n) :
    r • p ∈ degreeLT (R := R) n := by
  rw [mem_degreeLT_iff_size_le] at hp ⊢
  calc
    (r • p).val.size = (Raw.smul r p.val).trim.size := by rfl
    _ ≤ (Raw.smul r p.val).size := Raw.Trim.size_le_size _
    _ = p.val.size := by simp [Raw.smul]
    _ ≤ n := hp

instance (n : ℕ) : AddCommMonoid ↥(degreeLT (R := R) n) where
  zero := ⟨0, zero_mem_degreeLT (R := R) n⟩
  add p q := ⟨p.1 + q.1, add_mem_degreeLT p.2 q.2⟩
  add_assoc := by
    intro a b c
    apply Subtype.ext
    simpa using (CPolynomial.add_assoc a.1 b.1 c.1)
  add_comm := by
    intro a b
    apply Subtype.ext
    simpa using (CPolynomial.add_comm a.1 b.1)
  zero_add := by
    intro a
    apply Subtype.ext
    exact CPolynomial.zero_add a.1
  add_zero := by
    intro a
    apply Subtype.ext
    exact CPolynomial.add_zero a.1
  nsmul m p := ⟨m • p.1, nsmul_mem_degreeLT (R := R) (n := n) (m := m) p.2⟩
  nsmul_zero := by
    intro p
    apply Subtype.ext
    exact CPolynomial.nsmul_zero p.1
  nsmul_succ := by
    intro m p
    apply Subtype.ext
    simpa using (CPolynomial.nsmul_succ m p.1)

instance (n : ℕ) : Module R ↥(degreeLT (R := R) n) where
  smul r p := ⟨r • p.1, smul_mem_degreeLT (R := R) (n := n) r p.2⟩
  one_smul := by
    intro p
    apply Subtype.ext
    exact CPolynomial.one_smul p.1
  mul_smul := by
    intro r s p
    apply Subtype.ext
    simpa using (CPolynomial.mul_smul r s p.1)
  smul_zero := by
    intro r
    apply Subtype.ext
    exact CPolynomial.smul_zero (R := R) r
  smul_add := by
    intro r p q
    apply Subtype.ext
    exact CPolynomial.smul_add r p.1 q.1
  add_smul := by
    intro r s p
    apply Subtype.ext
    simpa using (CPolynomial.add_smul r s p.1)
  zero_smul := by
    intro p
    apply Subtype.ext
    exact CPolynomial.zero_smul p.1

/-- The first `n` coefficients on `degreeLT n` form a computable linear map to `Fin n → R`. -/
def degreeLTCoeffs (n : ℕ) : ↥(degreeLT (R := R) n) →ₗ[R] (Fin n → R) where
  toFun p i := coeff p.1 i
  map_add' := by
    intro p q
    funext i
    exact coeff_add p.1 q.1 i
  map_smul' := by
    intro r p
    funext i
    exact coeff_smul r p.1 i

end DegreeLTSubtype

end CPolynomial

end CompPoly
