/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/

import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import CompPoly.Data.Array.Lemmas
import CompPoly.Univariate.Basic

/-!
  # Quotient of Univariate Polynomials

  This file defines `QuotientCPolynomial R`, the quotient of `CPolynomial R` by the equivalence
  relation that identifies polynomials with the same coefficients (allowing zero-padding).
  This quotient is intended to be equivalent to mathlib's `Polynomial R`.

  Operations on `CPolynomial` (addition, multiplication, etc.) are shown to respect the
  equivalence relation and thus descend to the quotient.
-/

namespace CompPoly

namespace CPolynomial

variable {R : Type*} [Ring R] [BEq R]
variable {Q : Type*} [Ring Q]

section Quotient

open Trim

/-- Reflexivity of the equivalence relation. -/
@[simp] theorem equiv_refl (p : CPolynomial Q) : equiv p p :=
  by simp [equiv]

/-- Symmetry of the equivalence relation. -/
@[simp] theorem equiv_symm {p q : CPolynomial Q} : equiv p q → equiv q p := by
  simp [equiv]
  intro h i
  exact Eq.symm (h i)

/-- Transitivity of the equivalence relation. -/
@[simp] theorem equiv_trans {p q r : CPolynomial Q} : Trim.equiv p q → equiv q r → equiv p r := by
  simp_all [Trim.equiv]

/-- The `CPolynomial.equiv` is indeed an equivalence relation. -/
instance instEquivalenceEquiv : Equivalence (equiv (R := R)) where
  refl := equiv_refl
  symm := equiv_symm
  trans := equiv_trans

/-- The `Setoid` instance for `CPolynomial R` induced by `CPolynomial.equiv`. -/
instance instSetoidCPolynomial : Setoid (CPolynomial R) where
  r := equiv
  iseqv := instEquivalenceEquiv

/-- The quotient of `CPolynomial R` by coefficient-wise equivalence.

  This quotient identifies polynomials that differ only by trailing zeros, and is intended
  to be equivalent to mathlib's `Polynomial R`. -/
def QuotientCPolynomial (R : Type*) [Ring R] [BEq R] := Quotient (@instSetoidCPolynomial R _)

-- The operations on `CPolynomial` descend to `QuotientCPolynomial`
namespace QuotientCPolynomial

section EquivalenceLemmas

/-- Scalar multiplication by 0 is equivalent to the zero polynomial. -/
lemma smul_zero_equiv {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    (smul 0 p) ≈ 0 := by
  have h_smul_zero : ∀ (p : CPolynomial R), (smul 0 p).coeff = 0 := by
    intro p; ext i; simp [smul]
    cases p[i]? <;> simp
  exact fun i => by simpa using congr_fun (h_smul_zero p) i

/-- Addition respects the equivalence relation. -/
lemma add_equiv {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (p1 p2 q1 q2 : CPolynomial R)
    (hp : equiv p1 p2) (hq : equiv q1 q2) :
    equiv (p1.add q1) (p2.add q2) := by
  have h_add_equiv_raw : ∀ p q : CPolynomial R, equiv (p.add q) (p.add_raw q) := by
    exact fun p q => add_equiv_raw p q
  have h_add_coeff : ∀ i, (p1.add_raw q1).coeff i = p1.coeff i + q1.coeff i
      ∧ (p2.add_raw q2).coeff i = p2.coeff i + q2.coeff i := by
    exact fun i => ⟨ add_coeff? p1 q1 i, add_coeff? p2 q2 i ⟩
  simp_all [ equiv ]

/-- Multiplication by `X^i` respects the equivalence relation. -/
lemma mulPowX_equiv {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (i : ℕ) (p q : CPolynomial R) (h : equiv p q) :
    equiv (mulPowX i p) (mulPowX i q) := by
  unfold equiv at *
  intro j
  by_cases hj : j < i <;> simp_all +decide [ mulPowX ]
  · unfold mk; rw [ Array.getElem?_append, Array.getElem?_append ]; aesop
  · convert h ( j - i ) using 1 <;> rw [ Array.getElem?_append ] <;> simp +decide [ hj ]
    · rw [ if_neg ( not_lt_of_ge hj ) ]
    · rw [ if_neg ( not_lt_of_ge hj ) ]

/-- Adding a polynomial equivalent to zero acts as the identity. -/
lemma add_zero_equiv {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) (hq : equiv q 0) :
    equiv (add p q) p := by
  intro x
  have := add_coeff? p q x
  have hq_zero : q.coeff x = 0 := by exact hq x
  unfold add
  rw [ coeff_eq_coeff ]
  aesop

/-- Multiplying the zero polynomial by `X^i` results in a polynomial equivalent to zero. -/
lemma mulPowX_zero_equiv {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (i : ℕ) : equiv (mulPowX i (0 : CPolynomial R)) 0 := by
  unfold equiv
  simp [coeff]
  unfold mulPowX
  grind

/-- A single step in polynomial multiplication: add `(coefficient * q) * X^power` to accumulator. -/
def mul_step {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (q : CPolynomial R) (acc : CPolynomial R) (x : R × ℕ) : CPolynomial R :=
  acc.add ((smul x.1 q).mulPowX x.2)

/-- The multiplication step respects equivalence of the accumulator. -/
lemma mul_step_equiv {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (q : CPolynomial R) (acc1 acc2 : CPolynomial R) (x : R × ℕ)
    (h : equiv acc1 acc2) :
    equiv (mul_step q acc1 x) (mul_step q acc2 x) := by
  apply_rules [ add_equiv, mulPowX_equiv, smul_equiv ]

/-- The multiplication step with a zero coefficient acts as the identity modulo equivalence. -/
lemma mul_step_zero {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (q : CPolynomial R) (acc : CPolynomial R) (i : ℕ) :
    equiv (mul_step q acc (0, i)) acc := by
  have h_mul_step : mul_step q acc (0, i) = acc.add ((smul 0 q).mulPowX i) := by exact rfl
  have h_mulPowX : mulPowX i (smul 0 q) = smul 0 (mulPowX i q) := by unfold mulPowX smul; aesop
  rw [ h_mul_step, h_mulPowX ]
  exact add_zero_equiv _ _ ( smul_zero_equiv _ )

/-- Folding `mul_step` over a list of zero coefficients preserves equivalence. -/
lemma foldl_mul_step_zeros {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (q : CPolynomial R) (acc : CPolynomial R) (l : List (R × ℕ))
    (hl : ∀ x ∈ l, x.1 = 0) :
    equiv (l.foldl (mul_step q) acc) acc := by
  induction' l using List.reverseRecOn with x xs ih generalizing acc
  · exact fun _ => rfl
  · simp_all +decide [ List.foldl_append ]
    -- use the multiplication step and the induction hypothesis
    have h_mul_step : equiv (mul_step q (List.foldl (mul_step q) acc x) xs)
        (List.foldl (mul_step q) acc x) := by
      convert mul_step_zero q ( List.foldl ( mul_step q ) acc x ) xs.2 using 1
      specialize hl _ _ ( Or.inr rfl )
      aesop
    exact equiv_trans h_mul_step (ih acc)

/-- The `zipIdx` of a polynomial is the `zipIdx` of its trim followed by zero coefficients. -/
lemma zipIdx_trim_append {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) :
    ∃ l, p.zipIdx.toList = p.trim.zipIdx.toList ++ l ∧ ∀ x ∈ l, x.1 = 0 := by
  -- Let `n` be `p.trim.size`. `p.trim` is the prefix of `p` of length `n`.
  set n := p.trim.size with hn_def
  by_cases hn : n = 0
  · unfold n at hn
    -- Since `p.trim` is empty, `p` must be the zero polynomial.
    have hp_zero : ∀ i (hi : i < p.size), p[i] = 0 := by
      have := Trim.elim p; aesop
    use List.map (fun i => (0, i)) (List.range p.size)
    simp
    refine' List.ext_get _ _ <;> aesop
  · -- Since `n` is not zero, `p.last_nonzero` is `some k` and `n = k + 1`.
    obtain ⟨k, hk⟩ : ∃ k : Fin p.size,
      p.trim = p.extract 0 (k.val + 1) ∧ p[k] ≠ 0
      ∧ (∀ j, (hj : j < p.size) → j > k → p[j] = 0) := by
        have := Trim.elim p; aesop
    refine' ⟨ _, _, _ ⟩
    exact ( Array.zipIdx p ).toList.drop ( k + 1 )
    · rw [ hk.1 ]
      refine' List.ext_get _ _ <;> simp
      · rw [ min_eq_left ( by linarith [ Fin.is_lt k ] ),
          add_tsub_cancel_of_le ( by linarith [ Fin.is_lt k ] ) ]
      · intro n h₁ h₂; rw [ List.getElem_append ]; simp +decide [ h₁ ]
        grind
    · simp +decide [ List.mem_iff_get ]
      intro a; specialize hk; have := hk.2.2 ( k + 1 + a ); simp_all +decide [ Nat.add_assoc ]

lemma mul_trim_equiv [LawfulBEq R] (a b : CPolynomial R) :
    a.mul b ≈ a.trim.mul b := by
  have h_zipIdx_split : ∃ l, a.zipIdx.toList = a.trim.zipIdx.toList ++ l ∧ ∀ x ∈ l, x.1 = 0 := by
    exact zipIdx_trim_append a
  obtain ⟨l, hl⟩ := h_zipIdx_split
  have h_foldl_split : ∃ acc, (a.mul b) = (l.foldl (mul_step b) acc) ∧ (a.trim.mul b) = acc := by
    -- By definition of `mul`, we can rewrite `a.mul b` using `mul_step` and the foldl operation.
    have h_mul_def : a.mul b = (a.zipIdx.toList.foldl (mul_step b) (C 0)) := by
      unfold mul
      exact Eq.symm (Array.foldl_toList (mul_step b))
    have h_mul_def_trim : a.trim.mul b = (a.trim.zipIdx.toList.foldl (mul_step b) (C 0)) := by
      unfold mul
      exact Eq.symm (Array.foldl_toList (mul_step b))
    aesop
  obtain ⟨ acc, h₁, h₂ ⟩ := h_foldl_split
  exact h₁.symm ▸ h₂.symm ▸ foldl_mul_step_zeros b acc l hl.2

lemma mul_equiv [LawfulBEq R] (a₁ a₂ b : CPolynomial R) :
    a₁ ≈ a₂ → a₁.mul b ≈ a₂.mul b := by
  intro h
  calc
    a₁.mul b ≈ a₁.trim.mul b := mul_trim_equiv a₁ b
    _ ≈ a₂.trim.mul b := by rw [eq_of_equiv h]
    _ ≈ a₂.mul b := equiv_symm (mul_trim_equiv a₂ b)

lemma mul_equiv₂ [LawfulBEq R] (a b₁ b₂ : CPolynomial R) :
    b₁ ≈ b₂ → a.mul b₁ ≈ a.mul b₂ := by
  -- By definition of multiplication, we can express `a.mul b₁` and `a.mul b₂` in terms of
  -- their sums of products of coefficients.
  have h_mul_def : ∀ (a b : CompPoly.CPolynomial R),
    a.mul b = (a.zipIdx.foldl (fun acc ⟨a', i⟩ => acc.add ((smul a' b).mulPowX i)) (C 0)) :=
      by exact fun a b => rfl
  intro h
  have h_foldl_equiv : ∀ (l : List (R × ℕ)) (acc : CompPoly.CPolynomial R),
    List.foldl (fun acc (a', i) => acc.add ((smul a' b₁).mulPowX i)) acc l ≈
    List.foldl (fun acc (a', i) => acc.add ((smul a' b₂).mulPowX i)) acc l := by
    intro l acc
    induction' l using List.reverseRecOn with l ih generalizing acc; rfl
    · simp +zetaDelta at *
      -- Apply the add_equiv lemma to the foldl results and the mulPowX terms.
      apply add_equiv
      · expose_names; exact h_1 acc
      · -- Apply the lemma that multiplying by X^i preserves equivalence.
        apply mulPowX_equiv
        exact fun i => by rw [ smul_equiv, smul_equiv ]; exact congr_arg _ ( h i )
  convert h_foldl_equiv ( Array.toList ( Array.zipIdx a ) ) ( C 0 ) using 1 <;> grind

end EquivalenceLemmas

/-- Helper function showing addition descends to the quotient. -/
def add_descending (p q : CPolynomial R) : QuotientCPolynomial R :=
  Quotient.mk _ (add p q)

lemma add_descends [LawfulBEq R] (a₁ b₁ a₂ b₂ : CPolynomial R) :
    equiv a₁ a₂ → equiv b₁ b₂ → add_descending a₁ b₁ = add_descending a₂ b₂ := by
  intros heq_a heq_b
  unfold add_descending
  rw [Quotient.eq]
  simp [instSetoidCPolynomial]
  calc
    add a₁ b₁ ≈ add_raw a₁ b₁ := add_equiv_raw a₁ b₁
    _ ≈ add_raw a₂ b₂ := by
      intro i
      rw [add_coeff? a₁ b₁ i, add_coeff? a₂ b₂ i, heq_a i, heq_b i]
    _ ≈ add a₂ b₂ := equiv_symm (add_equiv_raw a₂ b₂)

/-- Addition on the quotient. -/
@[inline, specialize]
def add {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p q : QuotientCPolynomial R) :
    QuotientCPolynomial R :=
  Quotient.lift₂ add_descending add_descends p q

/-- Helper function showing scalar multiplication descends to the quotient. -/
def smul_descending (r : R) (p : CPolynomial R) : QuotientCPolynomial R :=
  Quotient.mk _ (smul r p)

lemma smul_descends [LawfulBEq R] (r : R) (p₁ p₂ : CPolynomial R) :
    equiv p₁ p₂ → smul_descending r p₁ = smul_descending r p₂ := by
  unfold equiv smul_descending
  intro heq
  rw [Quotient.eq]
  simp [instSetoidCPolynomial]
  intro i
  rw [smul_equiv, smul_equiv, heq i]

/-- Scalar multiplication on the quotient. -/
@[inline, specialize]
def smul {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (r : R) (p : QuotientCPolynomial R) :
    QuotientCPolynomial R :=
  Quotient.lift (smul_descending r) (smul_descends r) p

/-- Helper function showing natural number scalar multiplication descends to the quotient. -/
def nsmul_descending (n : ℕ) (p : CPolynomial R) : QuotientCPolynomial R :=
  Quotient.mk _ (nsmul n p)

lemma nsmul_descends [LawfulBEq R] (n : ℕ) (p₁ p₂ : CPolynomial R) :
    equiv p₁ p₂ → nsmul_descending n p₁ = nsmul_descending n p₂ := by
  unfold equiv
  intro heq
  unfold nsmul_descending
  rw [Quotient.eq]
  simp [instSetoidCPolynomial]
  unfold nsmul equiv
  intro i
  repeat rw [nsmul_raw_equiv, coeff_eq_coeff]
  rw [heq i]

/-- Natural number scalar multiplication on the quotient. -/
@[inline, specialize]
def nsmul {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (n : ℕ) (p : QuotientCPolynomial R) :
    QuotientCPolynomial R :=
  Quotient.lift (nsmul_descending n) (nsmul_descends n) p

/-- Helper function showing negation descends to the quotient. -/
def neg_descending (p : CPolynomial R) : QuotientCPolynomial R :=
  Quotient.mk _ (neg p)

lemma neg_descends (a b : CPolynomial R) : equiv a b → neg_descending a = neg_descending b := by
  unfold equiv neg_descending
  intros heq
  rw [Quotient.eq]
  simp [instSetoidCPolynomial]
  unfold equiv
  intro i
  rw [neg_coeff a i, neg_coeff b i, heq i]

/-- Negation on the quotient. -/
@[inline, specialize]
def neg {R : Type*} [Ring R] [BEq R] (p : QuotientCPolynomial R) : QuotientCPolynomial R :=
  Quotient.lift neg_descending neg_descends p

/-- Helper function showing subtraction descends to the quotient. -/
def sub_descending (p q : CPolynomial R) : QuotientCPolynomial R :=
  Quotient.mk _ (sub p q)

lemma sub_descends [LawfulBEq R] (a₁ b₁ a₂ b₂ : CPolynomial R) :
    equiv a₁ a₂ → equiv b₁ b₂ → sub_descending a₁ b₁ = sub_descending a₂ b₂ := by
  unfold equiv sub_descending
  intros heq_a heq_b
  rw [Quotient.eq]
  simp [instSetoidCPolynomial]
  unfold sub equiv
  calc
    a₁.add b₁.neg ≈ a₁.add_raw b₁.neg := add_equiv_raw a₁ b₁.neg
    _ ≈ a₂.add_raw b₂.neg := by
      intro i
      rw [add_coeff? a₁ b₁.neg i, add_coeff? a₂ b₂.neg i]
      rw [neg_coeff b₁ i, neg_coeff b₂ i, heq_a i, heq_b i]
    _ ≈ a₂.add b₂.neg := equiv_symm (add_equiv_raw a₂ b₂.neg)

/-- Subtraction on the quotient. -/
@[inline, specialize]
def sub {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p q : QuotientCPolynomial R) :
    QuotientCPolynomial R :=
  Quotient.lift₂ sub_descending sub_descends p q

/-- Helper function showing multiplication by `X^i` descends to the quotient. -/
def mulPowX_descending (i : ℕ) (p : CPolynomial R) : QuotientCPolynomial R :=
  Quotient.mk _ (mulPowX i p)

lemma mulPowX_descends [LawfulBEq R] (i : ℕ) (p₁ p₂ : CPolynomial R) :
    equiv p₁ p₂ → mulPowX_descending i p₁ = mulPowX_descending i p₂ := by
  unfold mulPowX_descending
  intro heq
  rw [Quotient.eq]
  simp [instSetoidCPolynomial]
  apply mulPowX_equiv; exact heq

/-- Multiplication by `X^i` on the quotient. -/
@[inline, specialize]
def mulPowX {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (i : ℕ) (p : QuotientCPolynomial R) :
    QuotientCPolynomial R :=
  Quotient.lift (mulPowX_descending i) (mulPowX_descends i) p

/-- Multiplication by `X` on the quotient (equivalent to `mulPowX 1`). -/
@[inline, specialize]
def mulX [LawfulBEq R] (p : QuotientCPolynomial R) : QuotientCPolynomial R := p.mulPowX 1

/-- Helper function showing multiplication descends to the quotient. -/
def mul_descending (p q : CPolynomial R) : QuotientCPolynomial R :=
  Quotient.mk _ (mul p q)

lemma mul_descends [LawfulBEq R] (a₁ b₁ a₂ b₂ : CPolynomial R) :
    equiv a₁ a₂ → equiv b₁ b₂ → mul_descending a₁ b₁ = mul_descending a₂ b₂ := by
  unfold mul_descending
  intros heq_a heq_b
  rw [Quotient.eq]
  simp [instSetoidCPolynomial]
  calc
    a₁.mul b₁ ≈ a₂.mul b₁ := mul_equiv a₁ a₂ b₁ heq_a
    _ ≈ a₂.mul b₂ := mul_equiv₂ a₂ b₁ b₂ heq_b

/-- Multiplication on the quotient. -/
@[inline, specialize]
def mul {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p q : QuotientCPolynomial R) :
    QuotientCPolynomial R :=
  Quotient.lift₂ mul_descending mul_descends p q

/-- Helper function showing exponentiation descends to the quotient. -/
def pow_descending (p : CPolynomial R) (n : ℕ) : QuotientCPolynomial R :=
  Quotient.mk _ (pow p n)

lemma pow_descends [LawfulBEq R] (n : ℕ) (p₁ p₂ : CPolynomial R) :
    equiv p₁ p₂ → pow_descending p₁ n = pow_descending p₂ n := by
  intro heq
  unfold pow_descending
  rw [Quotient.eq]
  simp [instSetoidCPolynomial]
  unfold pow
  have mul_pow_succ_equiv (p : CPolynomial R) (n : ℕ):
    p.mul^[n + 1] (C 1) ≈ p.mul (p.mul^[n] (C 1)) := by
    rw [mul_pow_succ]
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      p₁.mul^[n + 1] (C 1) ≈ p₁.mul (p₁.mul^[n] (C 1)) := mul_pow_succ_equiv p₁ n
      _ ≈ p₁.mul (p₂.mul^[n] (C 1)) := mul_equiv₂ p₁ _ _ ih
      _ ≈ p₂.mul (p₂.mul^[n] (C 1)) := mul_equiv _ _ (p₂.mul^[n] (C 1)) heq
      _ ≈ p₂.mul^[n + 1] (C 1) := equiv_symm (mul_pow_succ_equiv p₂ n)

/-- Exponentiation on the quotient. -/
@[inline, specialize]
def pow {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p : QuotientCPolynomial R) (n : ℕ) :
    QuotientCPolynomial R :=
  Quotient.lift (fun p => pow_descending p n) (pow_descends n) p

-- TODO: div/field operations?

end QuotientCPolynomial

end Quotient

end CPolynomial

end CompPoly
