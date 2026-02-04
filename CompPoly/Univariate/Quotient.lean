/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/
import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import CompPoly.Data.Array.Lemmas
import CompPoly.Univariate.Raw

/-!
  # Quotient of Univariate Polynomials

  This file defines `QuotientCPolynomial R`, the quotient of `CPolynomialRaw R` by the equivalence
  relation that identifies polynomials with the same coefficients (allowing zero-padding).
  This quotient is intended to be equivalent to mathlib's `Polynomial R`.

  Operations on `CPolynomialRaw` (addition, multiplication, etc.) are shown to respect the
  equivalence relation and thus descend to the quotient.
-/
namespace CompPoly

namespace CPolynomialRaw

variable {R : Type*} [Ring R] [BEq R]
variable {Q : Type*} [Ring Q]

section Quotient

open Trim

/-- Reflexivity of the equivalence relation. -/
@[simp] theorem equiv_refl (p : CPolynomialRaw Q) : equiv p p :=
  by simp [equiv]

/-- Symmetry of the equivalence relation. -/
@[simp] theorem equiv_symm {p q : CPolynomialRaw Q} : equiv p q → equiv q p := by
  simp [equiv]
  intro h i
  exact Eq.symm (h i)

/-- Transitivity of the equivalence relation. -/
@[simp] theorem equiv_trans {p q r : CPolynomialRaw Q} : Trim.equiv p q → equiv q r → equiv p r := by
  simp_all [Trim.equiv]

/-- The `CPolynomialRaw.equiv` is indeed an equivalence relation. -/
instance instEquivalenceEquiv : Equivalence (equiv (R := R)) where
  refl := equiv_refl
  symm := equiv_symm
  trans := equiv_trans

/-- The `Setoid` instance for `CPolynomialRaw R` induced by `CPolynomialRaw.equiv`. -/
instance instSetoidCPolynomialRaw : Setoid (CPolynomialRaw R) where
  r := equiv
  iseqv := instEquivalenceEquiv

/-- The quotient of `CPolynomialRaw R` by coefficient-wise equivalence.

  This quotient identifies polynomials that differ only by trailing zeros, and is intended
  to be equivalent to mathlib's `Polynomial R`. -/
def QuotientCPolynomial (R : Type*) [Ring R] [BEq R] := Quotient (@instSetoidCPolynomialRaw R _)

-- The operations on `CPolynomialRaw` descend to `QuotientCPolynomial`
namespace QuotientCPolynomial

section EquivalenceLemmas

omit [BEq R] in
/-- Convert propositional equality to equivalence. -/
lemma eq_to_equiv (p q : CPolynomialRaw R) : p = q → p ≈ q := by intro h; rw [h]

/-- Scalar multiplication by 0 is equivalent to the zero polynomial. -/
lemma smul_zero_equiv {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p : CPolynomialRaw R) :
    (smul 0 p) ≈ 0 := by
  have h_smul_zero : ∀ (p : CPolynomialRaw R), (smul 0 p).coeff = 0 := by
    intro p; ext i; simp [smul]
    cases p[i]? <;> simp
  exact fun i => by simpa using congr_fun (h_smul_zero p) i

/-- Addition respects the equivalence relation. -/
lemma add_equiv {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (p1 p2 q1 q2 : CPolynomialRaw R)
  (hp : equiv p1 p2) (hq : equiv q1 q2) :
  equiv (p1.add q1) (p2.add q2) := by
  have h_add_equiv_raw : ∀ p q : CPolynomialRaw R, equiv (p.add q) (p.addRaw q) := by
    exact fun p q => add_equiv_raw p q
  have h_add_coeff : ∀ i, (p1.addRaw q1).coeff i = p1.coeff i + q1.coeff i
      ∧ (p2.addRaw q2).coeff i = p2.coeff i + q2.coeff i := by
    exact fun i => ⟨ add_coeff? p1 q1 i, add_coeff? p2 q2 i ⟩
  simp_all [ equiv ]

/-- Multiplication by `X^i` respects the equivalence relation. -/
lemma mulPowX_equiv {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (i : ℕ) (p q : CPolynomialRaw R) (h : equiv p q) :
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
    (p q : CPolynomialRaw R) (hq : equiv q 0) :
  equiv (add p q) p := by
  intro x
  have := add_coeff? p q x
  have hq_zero : q.coeff x = 0 := by exact hq x
  unfold add
  rw [ coeff_eq_coeff ]
  aesop

/-- Multiplying the zero polynomial by `X^i` results in a polynomial equivalent to zero. -/
lemma mulPowX_zero_equiv {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (i : ℕ) : equiv (mulPowX i (0 : CPolynomialRaw R)) 0 := by
  unfold equiv
  simp [coeff]
  unfold mulPowX
  grind

/-- A single step in polynomial multiplication: add `(coefficient * q) * X^power` to accumulator. -/
def mulStep {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (q : CPolynomialRaw R) (acc : CPolynomialRaw R) (x : R × ℕ) : CPolynomialRaw R :=
  acc.add ((smul x.1 q).mulPowX x.2)

/-- The multiplication step respects equivalence of the accumulator. -/
lemma mulStep_equiv {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (q : CPolynomialRaw R) (acc1 acc2 : CPolynomialRaw R) (x : R × ℕ)
  (h : equiv acc1 acc2) :
  equiv (mulStep q acc1 x) (mulStep q acc2 x) := by
  apply_rules [ add_equiv, mulPowX_equiv, smul_equiv ]

/-- The multiplication step with a zero coefficient acts as the identity modulo equivalence. -/
lemma mulStep_zero {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (q : CPolynomialRaw R) (acc : CPolynomialRaw R) (i : ℕ) :
  equiv (mulStep q acc (0, i)) acc := by
  have h_mulStep : mulStep q acc (0, i) = acc.add ((smul 0 q).mulPowX i) := by exact rfl
  have h_mulPowX : mulPowX i (smul 0 q) = smul 0 (mulPowX i q) := by unfold mulPowX smul; aesop
  rw [ h_mulStep, h_mulPowX ]
  exact add_zero_equiv _ _ ( smul_zero_equiv _ )

/-- Folding `mulStep` over a list of zero coefficients preserves equivalence. -/
lemma foldl_mulStep_zeros {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (q : CPolynomialRaw R) (acc : CPolynomialRaw R) (l : List (R × ℕ))
  (hl : ∀ x ∈ l, x.1 = 0) :
  equiv (l.foldl (mulStep q) acc) acc := by
  induction' l using List.reverseRecOn with x xs ih generalizing acc
  · intro _; rfl
  · simp_all +decide [ List.foldl_append ]
    -- use the multiplication step and the induction hypothesis
    have h_mulStep : equiv (mulStep q (List.foldl (mulStep q) acc x) xs)
        (List.foldl (mulStep q) acc x) := by
      convert mulStep_zero q ( List.foldl ( mulStep q ) acc x ) xs.2 using 1
      specialize hl _ _ ( Or.inr rfl )
      aesop
    exact equiv_trans h_mulStep (ih acc)

/-- The `zipIdx` of a polynomial is the `zipIdx` of its trim followed by zero coefficients. -/
lemma zipIdx_trim_append {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (p : CPolynomialRaw R) :
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
  · -- Since `n` is not zero, `p.lastNonzero` is `some k` and `n = k + 1`.
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

/-- Multiplication by a trimmed polynomial is equivalent to multiplication by the original. -/
lemma mul_trim_equiv [LawfulBEq R] (a b : CPolynomialRaw R) :
    a.mul b ≈ a.trim.mul b := by
  have h_zipIdx_split : ∃ l, a.zipIdx.toList = a.trim.zipIdx.toList ++ l ∧ ∀ x ∈ l, x.1 = 0 := by
    exact zipIdx_trim_append a
  obtain ⟨l, hl⟩ := h_zipIdx_split
  have h_foldl_split : ∃ acc, (a.mul b) = (l.foldl (mulStep b) acc) ∧ (a.trim.mul b) = acc := by
    -- By definition of `mul`, we can rewrite `a.mul b` using `mulStep` and the foldl operation.
    have h_mul_def : a.mul b = (a.zipIdx.toList.foldl (mulStep b) (mk #[])) := by
      unfold mul
      exact Eq.symm (Array.foldl_toList (mulStep b))
    have h_mul_def_trim : a.trim.mul b = (a.trim.zipIdx.toList.foldl (mulStep b) (mk #[])) := by
      unfold mul
      exact Eq.symm (Array.foldl_toList (mulStep b))
    aesop
  obtain ⟨ acc, h₁, h₂ ⟩ := h_foldl_split
  exact h₁.symm ▸ h₂.symm ▸ foldl_mulStep_zeros b acc l hl.2

/-- Multiplication is well-defined on the left with respect to equivalence. -/
lemma mul_equiv [LawfulBEq R] (a₁ a₂ b : CPolynomialRaw R) :
    a₁ ≈ a₂ → a₁.mul b ≈ a₂.mul b := by
  intro h
  calc
    a₁.mul b ≈ a₁.trim.mul b := mul_trim_equiv a₁ b
    _ ≈ a₂.trim.mul b := by rw [eq_of_equiv h]
    _ ≈ a₂.mul b := equiv_symm (mul_trim_equiv a₂ b)

/-- Multiplication is well-defined on the right with respect to equivalence. -/
lemma mul_equiv₂ [LawfulBEq R] (a b₁ b₂ : CPolynomialRaw R) :
    b₁ ≈ b₂ → a.mul b₁ ≈ a.mul b₂ := by
  -- By definition of multiplication, we can express `a.mul b₁` and `a.mul b₂` in terms of
  -- their sums of products of coefficients.
  have h_mul_def : ∀ (a b : CompPoly.CPolynomialRaw R),
    a.mul b = (a.zipIdx.foldl (fun acc ⟨a', i⟩ => acc.add ((smul a' b).mulPowX i)) (mk #[])) :=
      by exact fun a b => rfl
  intro h
  have h_foldl_equiv : ∀ (l : List (R × ℕ)) (acc : CompPoly.CPolynomialRaw R),
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
  convert h_foldl_equiv ( Array.toList ( Array.zipIdx a ) ) ( mk #[] ) using 1 <;> grind

end EquivalenceLemmas

/-- Helper function showing addition descends to the quotient. -/
def addDescending (p q : CPolynomialRaw R) : QuotientCPolynomial R :=
  Quotient.mk _ (add p q)

lemma add_descends [LawfulBEq R] (a₁ b₁ a₂ b₂ : CPolynomialRaw R) :
    equiv a₁ a₂ → equiv b₁ b₂ → addDescending a₁ b₁ = addDescending a₂ b₂ := by
  intros heq_a heq_b
  unfold addDescending
  rw [Quotient.eq]
  simp [instSetoidCPolynomialRaw]
  calc
    add a₁ b₁ ≈ addRaw a₁ b₁ := add_equiv_raw a₁ b₁
    _ ≈ addRaw a₂ b₂ := by
      intro i
      rw [add_coeff? a₁ b₁ i, add_coeff? a₂ b₂ i, heq_a i, heq_b i]
    _ ≈ add a₂ b₂ := equiv_symm (add_equiv_raw a₂ b₂)

/-- Addition on the quotient. -/
@[inline, specialize]
def add {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p q : QuotientCPolynomial R) :
    QuotientCPolynomial R :=
  Quotient.lift₂ addDescending add_descends p q

/-- Helper function showing scalar multiplication descends to the quotient. -/
def smulDescending (r : R) (p : CPolynomialRaw R) : QuotientCPolynomial R :=
  Quotient.mk _ (smul r p)

lemma smul_descends [LawfulBEq R] (r : R) (p₁ p₂ : CPolynomialRaw R) :
    equiv p₁ p₂ → smulDescending r p₁ = smulDescending r p₂ := by
  unfold equiv smulDescending
  intro heq
  rw [Quotient.eq]
  simp [instSetoidCPolynomialRaw]
  intro i
  rw [smul_equiv, smul_equiv, heq i]

/-- Scalar multiplication on the quotient. -/
@[inline, specialize]
def smul {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (r : R) (p : QuotientCPolynomial R) :
    QuotientCPolynomial R :=
  Quotient.lift (smulDescending r) (smul_descends r) p

/-- Helper function showing natural number scalar multiplication descends to the quotient. -/
def nsmulDescending (n : ℕ) (p : CPolynomialRaw R) : QuotientCPolynomial R :=
  Quotient.mk _ (nsmul n p)

lemma nsmul_descends [LawfulBEq R] (n : ℕ) (p₁ p₂ : CPolynomialRaw R) :
    equiv p₁ p₂ → nsmulDescending n p₁ = nsmulDescending n p₂ := by
  unfold equiv
  intro heq
  unfold nsmulDescending
  rw [Quotient.eq]
  simp [instSetoidCPolynomialRaw]
  unfold nsmul equiv
  intro i
  repeat rw [nsmulRaw_equiv, coeff_eq_coeff]
  rw [heq i]

/-- Natural number scalar multiplication on the quotient. -/
@[inline, specialize]
def nsmul {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (n : ℕ) (p : QuotientCPolynomial R) :
    QuotientCPolynomial R :=
  Quotient.lift (nsmulDescending n) (nsmul_descends n) p

/-- Helper function showing negation descends to the quotient. -/
def negDescending (p : CPolynomialRaw R) : QuotientCPolynomial R :=
  Quotient.mk _ (neg p)

lemma neg_descends (a b : CPolynomialRaw R) : equiv a b → negDescending a = negDescending b := by
  unfold equiv negDescending
  intros heq
  rw [Quotient.eq]
  simp [instSetoidCPolynomialRaw]
  unfold equiv
  intro i
  rw [neg_coeff a i, neg_coeff b i, heq i]

/-- Negation on the quotient. -/
@[inline, specialize]
def neg {R : Type*} [Ring R] [BEq R] (p : QuotientCPolynomial R) : QuotientCPolynomial R :=
  Quotient.lift negDescending neg_descends p

/-- Helper function showing subtraction descends to the quotient. -/
def subDescending (p q : CPolynomialRaw R) : QuotientCPolynomial R :=
  Quotient.mk _ (sub p q)

lemma sub_descends [LawfulBEq R] (a₁ b₁ a₂ b₂ : CPolynomialRaw R) :
    equiv a₁ a₂ → equiv b₁ b₂ → subDescending a₁ b₁ = subDescending a₂ b₂ := by
  unfold equiv subDescending
  intros heq_a heq_b
  rw [Quotient.eq]
  simp [instSetoidCPolynomialRaw]
  unfold sub equiv
  calc
    a₁.add b₁.neg ≈ a₁.addRaw b₁.neg := add_equiv_raw a₁ b₁.neg
    _ ≈ a₂.addRaw b₂.neg := by
      intro i
      rw [add_coeff? a₁ b₁.neg i, add_coeff? a₂ b₂.neg i]
      rw [neg_coeff b₁ i, neg_coeff b₂ i, heq_a i, heq_b i]
    _ ≈ a₂.add b₂.neg := equiv_symm (add_equiv_raw a₂ b₂.neg)

/-- Subtraction on the quotient. -/
@[inline, specialize]
def sub {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p q : QuotientCPolynomial R) :
    QuotientCPolynomial R :=
  Quotient.lift₂ subDescending sub_descends p q

/-- Helper function showing multiplication by `X^i` descends to the quotient. -/
def mulPowXDescending (i : ℕ) (p : CPolynomialRaw R) : QuotientCPolynomial R :=
  Quotient.mk _ (mulPowX i p)

lemma mulPowX_descends [LawfulBEq R] (i : ℕ) (p₁ p₂ : CPolynomialRaw R) :
    equiv p₁ p₂ → mulPowXDescending i p₁ = mulPowXDescending i p₂ := by
  unfold mulPowXDescending
  intro heq
  rw [Quotient.eq]
  simp [instSetoidCPolynomialRaw]
  apply mulPowX_equiv; exact heq

/-- Multiplication by `X^i` on the quotient. -/
@[inline, specialize]
def mulPowX {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (i : ℕ) (p : QuotientCPolynomial R) :
    QuotientCPolynomial R :=
  Quotient.lift (mulPowXDescending i) (mulPowX_descends i) p

/-- Multiplication by `X` on the quotient (equivalent to `mulPowX 1`). -/
@[inline, specialize]
def mulX [LawfulBEq R] (p : QuotientCPolynomial R) : QuotientCPolynomial R := p.mulPowX 1

/-- Helper function showing multiplication descends to the quotient. -/
def mulDescending (p q : CPolynomialRaw R) : QuotientCPolynomial R :=
  Quotient.mk _ (mul p q)

lemma mul_descends [LawfulBEq R] (a₁ b₁ a₂ b₂ : CPolynomialRaw R) :
    equiv a₁ a₂ → equiv b₁ b₂ → mulDescending a₁ b₁ = mulDescending a₂ b₂ := by
  unfold mulDescending
  intros heq_a heq_b
  rw [Quotient.eq]
  simp [instSetoidCPolynomialRaw]
  calc
    a₁.mul b₁ ≈ a₂.mul b₁ := mul_equiv a₁ a₂ b₁ heq_a
    _ ≈ a₂.mul b₂ := mul_equiv₂ a₂ b₁ b₂ heq_b

/-- Multiplication on the quotient. -/
@[inline, specialize]
def mul {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p q : QuotientCPolynomial R) :
    QuotientCPolynomial R :=
  Quotient.lift₂ mulDescending mul_descends p q

/-- Helper function showing exponentiation descends to the quotient. -/
def powDescending (p : CPolynomialRaw R) (n : ℕ) : QuotientCPolynomial R :=
  Quotient.mk _ (pow p n)

lemma pow_descends [LawfulBEq R] (n : ℕ) (p₁ p₂ : CPolynomialRaw R) :
    equiv p₁ p₂ → powDescending p₁ n = powDescending p₂ n := by
  intro heq
  unfold powDescending
  rw [Quotient.eq]
  simp [instSetoidCPolynomialRaw]
  unfold pow
  have mul_pow_succ_equiv (p : CPolynomialRaw R) (n : ℕ):
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
  Quotient.lift (fun p => powDescending p n) (pow_descends n) p

-- TODO: div/field operations?

instance : Zero (QuotientCPolynomial R) := ⟨Quotient.mk _ #[]⟩
instance : One (QuotientCPolynomial R) := ⟨Quotient.mk _ (CPolynomialRaw.C 1)⟩
instance [LawfulBEq R] : Add (QuotientCPolynomial R) := ⟨QuotientCPolynomial.add⟩
instance [LawfulBEq R] : SMul R (QuotientCPolynomial R) := ⟨smul⟩
instance [LawfulBEq R] : SMul ℕ (QuotientCPolynomial R) := ⟨nsmul⟩
instance : Neg (QuotientCPolynomial R) := ⟨neg⟩
instance [LawfulBEq R] : Sub (QuotientCPolynomial R) := ⟨sub⟩
instance [LawfulBEq R] : Mul (QuotientCPolynomial R) := ⟨mul⟩
instance [LawfulBEq R] : Pow (QuotientCPolynomial R) Nat := ⟨pow⟩
instance : NatCast (QuotientCPolynomial R) := ⟨fun n => Quotient.mk _ (CPolynomialRaw.C (n : R))⟩
instance : IntCast (QuotientCPolynomial R) := ⟨fun n => Quotient.mk _ (CPolynomialRaw.C (n : R))⟩
-- instance [Field R] : Div (QuotientCPolynomial R) := ⟨div⟩
-- instance [Field R] : Mod (QuotientCPolynomial R) := ⟨mod⟩

section AddCommGroup

@[grind =_]
lemma add_assoc [LawfulBEq R] : ∀ (a b c : QuotientCPolynomial R), a + b + c = a + (b + c) := by
  intro a b c
  refine Quotient.inductionOn₃ a b c ?_
  intro p q r; clear a b c
  apply Quotient.sound
  apply eq_to_equiv
  apply CPolynomialRaw.add_assoc

@[simp]
lemma zero_add_equiv [LawfulBEq R] (p : CPolynomialRaw R) : 0 + p ≈ p := by
  intro i
  change ((0 : CPolynomialRaw R).add p).coeff i = p.coeff i
  unfold CPolynomialRaw.add
  rw [Trim.coeff_eq_coeff]
  rw [add_coeff?]
  simp

@[simp]
lemma zero_add [LawfulBEq R] : ∀ (a : QuotientCPolynomial R), 0 + a = a := by
  intros a
  refine Quotient.inductionOn a ?_
  intro p; clear a
  apply Quotient.sound
  apply zero_add_equiv

@[simp]
lemma add_zero [LawfulBEq R] : ∀ (a : QuotientCPolynomial R), a + 0 = a := by
  intros a
  refine Quotient.inductionOn a ?_
  intro p; clear a
  apply Quotient.sound
  intro i
  unfold CPolynomialRaw.add
  rw [Trim.coeff_eq_coeff]
  rw [add_coeff?]
  simp

@[grind =>]
lemma add_comm [LawfulBEq R] : ∀ (a b : QuotientCPolynomial R), a + b = b + a := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intros p q; clear a b
  apply Quotient.sound
  apply eq_to_equiv
  apply CPolynomialRaw.add_comm

@[simp]
lemma neg_add_cancel [LawfulBEq R] : ∀ (a : QuotientCPolynomial R), -a + a = 0 := by
  intros a
  refine Quotient.inductionOn a ?_
  intro p; clear a
  apply Quotient.sound
  apply eq_to_equiv
  apply CPolynomialRaw.neg_add_cancel

@[simp]
lemma nsmul_zero [LawfulBEq R] : ∀ (x : QuotientCPolynomial R),
    QuotientCPolynomial.nsmul 0 x = 0 := by
  intros x
  refine Quotient.inductionOn x ?_
  intro p; clear x
  apply Quotient.sound
  apply eq_to_equiv
  apply CPolynomialRaw.nsmul_zero

@[grind =>]
lemma nsmul_succ [LawfulBEq R] : ∀ (n : ℕ) (x : QuotientCPolynomial R),
    QuotientCPolynomial.nsmul (n + 1) x = QuotientCPolynomial.nsmul n x + x := by
  intro n x
  refine Quotient.inductionOn x ?_
  intro p; clear x
  apply Quotient.sound
  apply eq_to_equiv
  apply CPolynomialRaw.nsmul_succ

@[grind =]
lemma sub_eq_add_neg [LawfulBEq R] : ∀ (a b : QuotientCPolynomial R), a - b = a + -b := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intros p q; clear a b
  apply Quotient.sound
  apply eq_to_equiv
  rfl

instance [LawfulBEq R] : AddCommGroup (QuotientCPolynomial R) where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  neg_add_cancel := neg_add_cancel
  nsmul := nsmul
  nsmul_zero := nsmul_zero
  nsmul_succ := nsmul_succ
  zsmul := zsmulRec
  sub_eq_add_neg := sub_eq_add_neg

end AddCommGroup

section Semiring
variable [LawfulBEq R]

lemma mul_assoc {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (a b c : QuotientCPolynomial R) :
    a * b * c = a * (b * c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro p q r
  apply Quotient.sound
  exact mul_assoc_equiv p q r

lemma one_mul : ∀ (a : QuotientCPolynomial R), 1 * a = a := by
  intros a
  refine Quotient.inductionOn a ?_
  intro p; clear a
  apply Quotient.sound
  change 1 * p ≈ p
  rw [one_mul_trim]
  apply trim_equiv

lemma mul_one : ∀ (a : QuotientCPolynomial R), a * 1 = a := by
  intros a
  refine Quotient.inductionOn a ?_
  intro p; clear a
  apply Quotient.sound
  change p * 1 ≈ p
  rw [mul_one_trim]
  apply trim_equiv

lemma zero_mul : ∀ (a : QuotientCPolynomial R), 0 * a = 0 := by
  intros a
  refine Quotient.inductionOn a ?_
  intro p; clear a
  apply Quotient.sound
  change 0 * p ≈ 0
  rw [CPolynomialRaw.zero_mul]

lemma mul_zero : ∀ (a : QuotientCPolynomial R), a * 0 = 0 := by
  intros a
  refine Quotient.inductionOn a ?_
  intro p; clear a
  apply Quotient.sound
  change p * 0 ≈ 0
  rw [CPolynomialRaw.mul_zero]

lemma left_distrib : ∀ (a b c : QuotientCPolynomial R),
    a * (b + c) = a * b + a * c := by
  intro a b c
  refine Quotient.inductionOn₃ a b c ?_
  intro p q r
  apply Quotient.sound
  change p * (q + r) ≈ (p * q) + (p * r)
  rw [CPolynomialRaw.left_distrib p q r]

lemma right_distrib : ∀ (a b c : QuotientCPolynomial R), (a + b) * c = a * c + b * c := by
  intro a b c
  refine Quotient.inductionOn₃ a b c ?_
  intro p q r; clear a b c
  apply Quotient.sound
  change (p + q) * r ≈ (p * r) + (q * r)
  rw [CPolynomialRaw.right_distrib]

lemma npow_zero : ∀ (x : QuotientCPolynomial R), x.pow 0 = 1 := by
  intros x
  refine Quotient.inductionOn x ?_
  intro p; clear x
  apply Quotient.sound
  unfold CPolynomialRaw.pow
  simp

@[grind]
lemma const_sum (r s : R) : (C r).add (C s) ≈ C (r + s) := by
  calc
    ((C r).addRaw (C s)).trim ≈ ((C r).addRaw (C s)) := by apply trim_equiv
    _ ≈ C (r + s) := by
      unfold C addRaw; simp

/-
x^(n+1) = x * x^n for QuotientCPolynomial
-/
lemma pow_succ_left {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (n : ℕ)
    (x : QuotientCPolynomial R) :
    x.pow (n + 1) = x * x.pow n := by
  refine Quotient.inductionOn x ?_
  intro p
  apply Quotient.sound
  -- p.pow (n+1) = p * p.pow n is true by definition of pow for CPolynomialRaw
  -- By definition of pow, we have p.pow (n + 1) = p.mul (p.pow n).
  have h_pow : p.pow (n + 1) = p.mul (p.pow n) := by
    exact Function.iterate_succ_apply' _ _ _
  exact congrFun (congrArg coeff h_pow)

/-
x commutes with x^n
-/
lemma commute_pow_self {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (n : ℕ)
    (x : QuotientCPolynomial R) :
    x * x.pow n = x.pow n * x := by
  induction' n with n ih generalizing x
  all_goals generalize_proofs at *
  · rw [show x.pow 0 = 1 from _]
    · simp +decide [mul_one, one_mul]
    · exact npow_zero x
  · rw [ pow_succ_left, mul_assoc, ih, ← mul_assoc ]

lemma npow_succ : ∀ (n : ℕ) (x : QuotientCPolynomial R), x.pow (n + 1) = x.pow n * x := by
  intro n x
  refine Quotient.inductionOn x ?_
  intro p; clear x
  apply Quotient.sound
  -- By definition of exponentiation, we have `p.pow (n + 1) = p * p.pow n` for any `p`.
  rw [show p.pow (n + 1) = p.mul (p.pow n) from by
        exact Function.iterate_succ_apply' _ _ _]
  convert commute_pow_self n ( Quotient.mk ( instSetoidCPolynomialRaw ) p ) using 1
  erw [ Quotient.eq ]
  rfl

/-- `CPolynomialRaw R` forms a semiring when `R` is a semiring.

  The semiring structure is inherited from the coefficient-wise operations on arrays,
  with addition and multiplication defined via the standard polynomial operations.
-/
instance [Semiring R] [LawfulBEq R] : Semiring (QuotientCPolynomial R) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := left_distrib
  right_distrib := right_distrib
  npow n p := p.pow n
  npow_zero := npow_zero
  npow_succ := npow_succ
  natCast_zero := by
    apply Quotient.sound
    intro i; unfold C; simp
  natCast_succ := by
    intro n
    apply Quotient.sound
    intro i; rw [const_sum (n : R) (1 : R)]; simp

end Semiring

section CommSemiring

variable {R : Type*} [CommRing R] [BEq R]

lemma mul_comm [LawfulBEq R]: ∀ (a b : QuotientCPolynomial R), a * b = b * a := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intros p q; clear a b
  apply Quotient.sound
  change p * q ≈ q * p
  simp [CPolynomialRaw.mul_comm p q]

/-- `CPolynomialRaw R` forms a commutative semiring when `R` is a commutative semiring.

  Commutativity follows from the commutativity of multiplication in the base ring.
-/
instance [CommRing R] [LawfulBEq R] : CommSemiring (QuotientCPolynomial R) where
  mul_comm := mul_comm

end CommSemiring

section Ring

lemma zsmul_zero' [LawfulBEq R] : ∀ (a : QuotientCPolynomial R), zsmulRec nsmulRec 0 a = 0 := by
  intro a; simp [zsmulRec]; simp [nsmulRec]

/-- `CPolynomialRaw R` forms a ring when `R` is a ring.

  The ring structure extends the semiring structure with negation and subtraction.
  Most of the structure is already provided by the `Semiring` instance.
-/
instance [LawfulBEq R] : Ring (QuotientCPolynomial R) where
  sub_eq_add_neg := by intro a b; (grind)
  zsmul := zsmulRec
  zsmul_zero' := zsmul_zero'
  zsmul_succ' := by intros _ _; rfl
  zsmul_neg' := by intros n a; simp [zsmulRec]
  intCast_ofNat := by intro n; simp [IntCast.intCast]; rfl
  intCast_negSucc := by
    -- By definition of `Int.negSucc`, we have `Int.negSucc n = - (n + 1)`.
    have h_neg_succ : ∀ n : ℕ, Int.negSucc n = - (n + 1 : ℤ) := by grind
    convert h_neg_succ
    convert Quotient.eq using 1
    simp +decide [ CPolynomialRaw.instSetoidCPolynomialRaw ]
    simp +decide [ CPolynomialRaw.C, CPolynomialRaw.neg ]
    grind
  neg_add_cancel := QuotientCPolynomial.neg_add_cancel

end Ring

section CommRing

variable {R : Type*} [CommRing R] [BEq R]

/-- `CPolynomialRaw R` forms a commutative ring when `R` is a commutative ring.

  This combines the `CommSemiring` and `Ring` structures.
-/
instance [CommRing R] [BEq R] [LawfulBEq R] : CommRing (QuotientCPolynomial R) where
  -- All structure inherited from `CommSemiring` and `Ring` instances

end CommRing

end QuotientCPolynomial

end Quotient

end CPolynomialRaw

end CompPoly
