/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Conejero
-/
import CompPoly.Univariate.Basic
import CompPoly.Univariate.DivisionCorrectness

/-!
# Extended Euclidean Algorithm for `CPolynomial`

`xgcd p q` returns a triple `(r, s, t)` with `r = s * p + t * q`.
Early stop when `r.natDegree < threshold`.
The default `threshold = 0` makes `r` the Greatest Common Divisior of `p` and `q`.
-/

namespace CompPoly

namespace CPolynomial

variable {R : Type*}

/-- Extended euclidean algorithm on `p, q`.

Stops when `r = 0`, `r.natDegree < threshold`, or fuel `n` exhausted.

Potential optimization: the raw long division behind `r' / r` already computes
`r' - (r' / r) * r` but it's not exposed through `CPolynomial R`.
-/
def xgcdAux [Field R] [BEq R] [LawfulBEq R]
  (threshold n : ℕ) (r s t r' s' t' : CPolynomial R) :
  CPolynomial R × CPolynomial R × CPolynomial R :=
  match n with
  | 0 => (r', s', t')
  | k + 1 =>
    if r == 0 then
      (r', s', t')
    else if r.natDegree < threshold then
      (r, s, t)
    else
      let q := r' / r
      xgcdAux threshold k
        (r' - q * r) (s' - q * s) (t' - q * t) r s t

/-- Extended euclidean algorithm for `(p, q)`.

Returns `(r, s, t)` with `r = s * p + t * q`.

With the default `threshold = 0` returns the gcd of `p` and `q`.
With `threshold > 0` stops when `r.natDegree < threshold`. -/
def xgcd [Field R] [BEq R] [LawfulBEq R]
  (p q : CPolynomial R) (threshold : ℕ := 0) :
  CPolynomial R × CPolynomial R × CPolynomial R :=
  xgcdAux threshold p.val.size p 1 0 q 0 1

/-! ### Bezout-identity correctness -/

/-- Bezout predicate on a triple `(r, s, t)`: `r = s * p + t * q`. -/
def Bezout [Semiring R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) :
  CPolynomial R × CPolynomial R × CPolynomial R → Prop
  | (r, s, t) => r = s * p + t * q

/-- `xgcdAux` preserves the Bezout identity. -/
theorem xgcdAux_bezout [Field R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) (threshold n : ℕ)
    {r r' : CPolynomial R} {s t s' t'}
    (h : Bezout p q (r, s, t)) (h' : Bezout p q (r', s', t')) :
    Bezout p q (xgcdAux threshold n r s t r' s' t') := by
  induction n generalizing r s t r' s' t' with
  | zero => exact h'
  | succ k ih =>
    unfold xgcdAux; split_ifs <;> try assumption
    apply ih ?_ h; simp only [Bezout] at *
    rw [h, h']; ring

/-- The output of `xgcd` is a Bezout triple for `(p, q)`. -/
theorem xgcd_bezout [Field R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) (threshold : ℕ) :
    Bezout p q (xgcd p q threshold) := by
  unfold xgcd
  apply xgcdAux_bezout p q threshold p.val.size
  all_goals (simp only [Bezout]; ring)

/-! # `xgcd` correctness (threshold 0)

Correctness theorems for `xgcd` with the default threshold 0.
-/

private lemma toPoly_sub_div_mul [Field R] [BEq R] [LawfulBEq R]
    (r r' a b : CPolynomial R) :
    (a - (r' / r) * b).toPoly = a.toPoly - (r'.toPoly / r.toPoly) * b.toPoly := by
  rw [show r' / r = r'.div r from rfl, toPoly_sub, toPoly_mul, div_toPoly_eq_div]

/-- The gcd component of CompPoly's `xgcdAux` at threshold `0` coincides with
Mathlib's `EuclideanDomain.gcd`. -/
lemma xgcdAux_toPoly_eq_gcd
    [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (n : ℕ) (r r' s t s' t' : CPolynomial R)
    (hn : r.toPoly.degree < n) :
    (xgcdAux 0 n r s t r' s' t').1.toPoly =
      EuclideanDomain.gcd r.toPoly r'.toPoly := by
  induction n generalizing r r' s t s' t' with
  | zero =>
    have hr : r = 0 := (toPoly_eq_zero_iff r).mp
      (Polynomial.degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp hn))
    rw [xgcdAux, hr, toPoly_zero, EuclideanDomain.gcd_zero_left]
  | succ k ih =>
    rw [xgcdAux, if_neg (Nat.not_lt_zero _)]
    by_cases hr : r = 0; simp [hr, toPoly_zero, EuclideanDomain.gcd_zero_left]
    rw [if_neg (by simpa), ih] <;>
    rw [toPoly_sub_div_mul, _root_.mul_comm, ←EuclideanDomain.mod_eq_sub_mul_div]
    · rw [EuclideanDomain.gcd_val r.toPoly r'.toPoly]
    · have hrtp : r.toPoly ≠ 0 := (toPoly_eq_zero_iff r).not.mpr hr
      exact lt_of_lt_of_le (Polynomial.degree_mod_lt _ hrtp) (Order.le_of_lt_succ hn)

/-- The gcd component of CompPoly's `xgcd` at threshold `0`
coincides with Mathlib's `EuclideanDomain.gcd`. -/
theorem xgcd_toPoly_eq_gcd [Field R] [BEq R] [LawfulBEq R] [DecidableEq R] (p q : CPolynomial R) :
    (xgcd p q).1.toPoly = EuclideanDomain.gcd p.toPoly q.toPoly := by
  unfold xgcd; apply xgcdAux_toPoly_eq_gcd
  rw [←degree_toPoly]; exact mem_degreeLT_iff_size_le.mpr le_rfl

/-- CompPoly's `xgcdAux` at threshold `0` coincides with
Mathlib's `EuclideanDomain.xgcdAux`. -/
lemma xgcdAux_toPoly_eq_xgcdAux
    [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (n : ℕ) (r s t r' s' t' : CPolynomial R)
    (hn : r.toPoly.degree < n) :
    Prod.map (·.toPoly) (·.map (·.toPoly) (·.toPoly))
      (xgcdAux 0 n r s t r' s' t') =
      EuclideanDomain.xgcdAux r.toPoly s.toPoly t.toPoly r'.toPoly s'.toPoly t'.toPoly := by
  induction n generalizing r s t r' s' t' with
  | zero =>
    have hr : r.toPoly = 0 := Polynomial.degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp hn)
    rw [xgcdAux, hr, EuclideanDomain.xgcd_zero_left]
    rfl
  | succ k ih =>
    rw [xgcdAux, if_neg (Nat.not_lt_zero _)]
    by_cases hr : r = 0
    · rw [if_pos (by simpa), hr, toPoly_zero, EuclideanDomain.xgcd_zero_left]
      rfl
    · rw [if_neg (by simpa)]
      have hrtp : r.toPoly ≠ 0 := (toPoly_eq_zero_iff r).not.mpr hr
      rw [ih, EuclideanDomain.xgcdAux_rec hrtp] <;>
      rw [toPoly_sub_div_mul, _root_.mul_comm, ←EuclideanDomain.mod_eq_sub_mul_div] <;>
      try exact lt_of_lt_of_le (Polynomial.degree_mod_lt _ hrtp) (Order.le_of_lt_succ hn)
      rw [toPoly_sub_div_mul, toPoly_sub_div_mul]

/-- The Bezout component of CompPoly's `xgcd` coincides with
Mathlib's `EuclideanDomain.xgcd`. -/
theorem xgcd_toPoly_eq_xgcd
    [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (p q : CPolynomial R) :
    (xgcd p q).2.map (·.toPoly) (·.toPoly) =
      EuclideanDomain.xgcd p.toPoly q.toPoly := by
  unfold xgcd EuclideanDomain.xgcd
  have h := xgcdAux_toPoly_eq_xgcdAux p.val.size p 1 0 q 0 1
    (by rw [←degree_toPoly]; exact mem_degreeLT_iff_size_le.mpr le_rfl)
  rw [toPoly_one, toPoly_zero] at h
  exact congrArg Prod.snd h

