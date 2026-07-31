/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Data.Polynomial.Rabin

/-!
# Irreducibility of binomials `X^d - W` over a finite field

Applying Rabin's test (`CompPoly/Data/Polynomial/Rabin.lean`) to a *binomial* defining
polynomial collapses both conditions into single exponentiations **in the base field**.

The reason is that `X^d ≡ W`, so whenever `d ∣ N - 1`, writing `k = (N-1)/d`,

`X^N - X = X * (X^(d*k) - 1)`  and  `X^(d*k) ≡ W^k  (mod X^d - W)`.

Hence `X^d - W` divides `X^N - X` exactly when `W^k = 1`, and is coprime to it exactly when
`W^k ≠ 1`: the residue is then `X * C (W^k - 1)`, a unit multiple of `X`, and `X` does not
divide `X^d - W` because `W ≠ 0`.

Instantiating at `N = q^d` and `N = q^(d/ℓ)` turns Rabin's test into
`irreducible_X_pow_sub_C_iff`, whose conditions are two base-field exponentiations. Contrast
the ~2100 lines of hand-generated `BitVec` step certificates in
`CompPoly/Fields/Binary/BF128Ghash/XPowTwoPow{Mod,Gcd}Certificate.lean`, which is what the
same test costs when the defining polynomial is not a binomial.

## Main statements

* `Polynomial.X_pow_sub_C_dvd_X_pow_sub_X` / `Polynomial.isCoprime_X_pow_sub_C_X_pow_sub_X`:
  the two collapsed Rabin conditions, and their converses.
* `Polynomial.irreducible_X_pow_sub_C_iff`: the criterion for general `d`.
* `Polynomial.irreducible_X_pow_four_sub_C`: the `d = 4` corollary, which discharges
  `Nat.primeFactors` internally. This is the degree used by BabyBear, KoalaBear and Hachi
  extension fields.

## References

* [Rabin80] Michael O. Rabin, *Probabilistic Algorithms in Finite Fields*,
  SIAM Journal on Computing 9(2), 1980.
* [LN97] Rudolf Lidl and Harald Niederreiter, *Finite Fields*, 2nd ed., Theorem 3.75.
-/

namespace Polynomial

variable {F : Type*} [Field F]

/-! ### Reducing powers of `X` modulo a binomial -/

/--
`X^d - C W` divides `X^(d * k) - C (W ^ k)`.

This is the algebraic content of "substituting `X^d = W`": apply `a - b ∣ a^k - b^k` with
`a = X^d` and `b = C W`.
-/
theorem X_pow_sub_C_dvd_X_pow_mul_sub_C_pow (W : F) (d k : ℕ) :
    (X ^ d - C W) ∣ X ^ (d * k) - C (W ^ k) := by
  rw [pow_mul, map_pow]
  exact sub_dvd_pow_sub_pow _ _ k

/-- Splitting `X^N - X` as `X * (X^(N-1) - 1)`, in the form needed below. -/
private theorem X_pow_sub_X_eq {d k N : ℕ} (hN : d * k + 1 = N) :
    (X : F[X]) ^ N - X = X * (X ^ (d * k) - 1) := by
  rw [← hN]; ring

/-- `(N - 1) / d = k` given `N - 1 = d * k` and `0 < d`. -/
private theorem div_eq_of_sub_one_eq {d k N : ℕ} (hd : 0 < d) (hk : N - 1 = d * k) :
    (N - 1) / d = k := by
  rw [hk, Nat.mul_div_cancel_left k hd]

/-- A binomial `X^d - C W` of positive degree is never a unit. -/
private theorem not_isUnit_X_pow_sub_C (W : F) {d : ℕ} (hd : 0 < d) :
    ¬ IsUnit ((X : F[X]) ^ d - C W) :=
  not_isUnit_of_natDegree_pos _ (by rw [natDegree_X_pow_sub_C]; omega)

/-- `X` does not divide `X^d - C W` when `W ≠ 0`: the constant coefficient is `-W`. -/
theorem not_X_dvd_X_pow_sub_C {W : F} {d : ℕ} (hd : 0 < d) (hW : W ≠ 0) :
    ¬ (X : F[X]) ∣ X ^ d - C W := by
  rw [X_dvd_iff, coeff_sub, coeff_X_pow, coeff_C_zero, if_neg (by omega), zero_sub, neg_eq_zero]
  exact hW

/-! ### The two collapsed Rabin conditions -/

/--
**Rabin condition 1, collapsed.** If `d ∣ N - 1` and `W ^ ((N-1)/d) = 1`, then
`X^d - C W` divides `X^N - X`.
-/
theorem X_pow_sub_C_dvd_X_pow_sub_X {W : F} {d N : ℕ} (hd : 0 < d) (hN : 1 ≤ N)
    (hdvd : d ∣ N - 1) (hW : W ^ ((N - 1) / d) = 1) :
    (X ^ d - C W) ∣ X ^ N - X := by
  obtain ⟨k, hk⟩ := hdvd
  rw [div_eq_of_sub_one_eq hd hk] at hW
  rw [X_pow_sub_X_eq (d := d) (k := k) (by omega)]
  refine Dvd.dvd.mul_left ?_ X
  have h := X_pow_sub_C_dvd_X_pow_mul_sub_C_pow W d k
  rwa [hW, map_one] at h

/--
**Rabin condition 2, collapsed.** If `d ∣ N - 1`, `W ≠ 0` and `W ^ ((N-1)/d) ≠ 1`, then
`X^d - C W` is coprime to `X^N - X`.

Modulo `X^d - C W` the polynomial `X^N - X` reduces to `X * C (W^k - 1)`, a unit multiple of
`X`, and `X` is coprime to `X^d - C W` by `not_X_dvd_X_pow_sub_C`.
-/
theorem isCoprime_X_pow_sub_C_X_pow_sub_X {W : F} {d N : ℕ} (hd : 0 < d) (hW0 : W ≠ 0)
    (hN : 1 ≤ N) (hdvd : d ∣ N - 1) (hW : W ^ ((N - 1) / d) ≠ 1) :
    IsCoprime (X ^ d - C W) (X ^ N - X) := by
  obtain ⟨k, hk⟩ := hdvd
  rw [div_eq_of_sub_one_eq hd hk] at hW
  obtain ⟨t, ht⟩ := X_pow_sub_C_dvd_X_pow_mul_sub_C_pow W d k
  -- Rewrite `X^N - X` as `X * C (W^k - 1)` plus a multiple of `X^d - C W`.
  have hsplit : (X : F[X]) ^ N - X = X * C (W ^ k - 1) + (X ^ d - C W) * (X * t) := by
    rw [X_pow_sub_X_eq (d := d) (k := k) (by omega)]
    have hXdk : (X : F[X]) ^ (d * k) = C (W ^ k) + (X ^ d - C W) * t := by rw [← ht]; ring
    rw [hXdk, map_sub, map_one]; ring
  rw [hsplit]
  refine IsCoprime.add_mul_left_right (IsCoprime.mul_right ?_ ?_) (X * t)
  · exact ((irreducible_X.coprime_iff_not_dvd).mpr (not_X_dvd_X_pow_sub_C hd hW0)).symm
  · -- A nonzero constant is coprime to everything.
    refine ⟨0, C (W ^ k - 1)⁻¹, ?_⟩
    rw [zero_mul, zero_add, ← map_mul, inv_mul_cancel₀ (sub_ne_zero_of_ne hW), map_one]

/-- Converse of `X_pow_sub_C_dvd_X_pow_sub_X`: divisibility forces `W ^ ((N-1)/d) = 1`. -/
theorem eq_one_of_X_pow_sub_C_dvd_X_pow_sub_X {W : F} {d N : ℕ} (hd : 0 < d) (hW0 : W ≠ 0)
    (hN : 1 ≤ N) (hdvd : d ∣ N - 1) (h : (X ^ d - C W) ∣ X ^ N - X) :
    W ^ ((N - 1) / d) = 1 := by
  by_contra hW
  exact not_isUnit_X_pow_sub_C W hd
    ((isCoprime_X_pow_sub_C_X_pow_sub_X hd hW0 hN hdvd hW).isUnit_of_dvd h)

/-- Converse of `isCoprime_X_pow_sub_C_X_pow_sub_X`: coprimality forces `W ^ ((N-1)/d) ≠ 1`. -/
theorem ne_one_of_isCoprime_X_pow_sub_C_X_pow_sub_X {W : F} {d N : ℕ} (hd : 0 < d) (hN : 1 ≤ N)
    (hdvd : d ∣ N - 1) (h : IsCoprime ((X : F[X]) ^ d - C W) (X ^ N - X)) :
    W ^ ((N - 1) / d) ≠ 1 := fun hW =>
  not_isUnit_X_pow_sub_C W hd (h.isUnit_of_dvd (X_pow_sub_C_dvd_X_pow_sub_X hd hN hdvd hW))

/-! ### The irreducibility criterion -/

variable [Fintype F]

/-- `1 ≤ q ^ n` for `q = |F|`, used to instantiate the collapsed conditions. -/
private theorem one_le_card_pow (n : ℕ) : 1 ≤ Fintype.card F ^ n :=
  Nat.one_le_pow _ _ Fintype.card_pos

/--
**Irreducibility criterion for binomials.**

Over a finite field with `q` elements, `X^d - W` is irreducible if and only if
`W^((q^d - 1)/d) = 1` and `W^((q^(d/ℓ) - 1)/d) ≠ 1` for every prime `ℓ ∣ d`.

The divisibility side conditions `h_top` and `h_mid` hold in every case of interest — for
`d = 4` and `q ≡ 1 mod 4`, for instance — and are decidable arithmetic facts about `q` and `d`.
-/
theorem irreducible_X_pow_sub_C_iff {d : ℕ} {W : F} (hd : 0 < d) (hW0 : W ≠ 0)
    (h_top : d ∣ Fintype.card F ^ d - 1)
    (h_mid : ∀ ℓ ∈ d.primeFactors, d ∣ Fintype.card F ^ (d / ℓ) - 1) :
    Irreducible ((X : F[X]) ^ d - C W) ↔
      (W ^ ((Fintype.card F ^ d - 1) / d) = 1 ∧
        ∀ ℓ ∈ d.primeFactors, W ^ ((Fintype.card F ^ (d / ℓ) - 1) / d) ≠ 1) := by
  have h_deg : ((X : F[X]) ^ d - C W).natDegree = d := natDegree_X_pow_sub_C
  constructor
  · intro h_irr
    obtain ⟨h₁, h₂⟩ := rabin_of_irreducible h_deg hd h_irr
    refine ⟨eq_one_of_X_pow_sub_C_dvd_X_pow_sub_X hd hW0 (one_le_card_pow d) h_top h₁,
      fun ℓ hℓ => ?_⟩
    exact ne_one_of_isCoprime_X_pow_sub_C_X_pow_sub_X hd (one_le_card_pow _) (h_mid ℓ hℓ) (h₂ ℓ hℓ)
  · intro ⟨h₁, h₂⟩
    refine irreducible_of_rabin h_deg hd
      (X_pow_sub_C_dvd_X_pow_sub_X hd (one_le_card_pow d) h_top h₁) (fun ℓ hℓ => ?_)
    exact isCoprime_X_pow_sub_C_X_pow_sub_X hd hW0 (one_le_card_pow _) (h_mid ℓ hℓ) (h₂ ℓ hℓ)

/-- The prime factors of `4`. -/
private theorem primeFactors_four : (4 : ℕ).primeFactors = {2} := by
  rw [show (4 : ℕ) = 2 ^ 2 from by norm_num,
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]

/--
**Irreducibility criterion for quartic binomials.**

`X^4 - W` is irreducible over a finite field with `q` elements exactly when
`W^((q^4 - 1)/4) = 1` and `W^((q^2 - 1)/4) ≠ 1`.

This is the shape used by the BabyBear, KoalaBear and Hachi degree-4 extensions. It differs
from `irreducible_X_pow_sub_C_iff` only in discharging `Nat.primeFactors 4 = {2}` internally,
so callers never touch `Nat.primeFactors`.

Being an `iff`, a *failed* check proves reducibility rather than merely failing to prove
irreducibility.
-/
theorem irreducible_X_pow_four_sub_C_iff {W : F} (hW0 : W ≠ 0)
    (h_top : 4 ∣ Fintype.card F ^ 4 - 1)
    (h_mid : 4 ∣ Fintype.card F ^ 2 - 1) :
    Irreducible ((X : F[X]) ^ 4 - C W) ↔
      (W ^ ((Fintype.card F ^ 4 - 1) / 4) = 1 ∧
        W ^ ((Fintype.card F ^ 2 - 1) / 4) ≠ 1) := by
  have hmid' : ∀ ℓ ∈ (4 : ℕ).primeFactors, 4 ∣ Fintype.card F ^ (4 / ℓ) - 1 := by
    simp only [primeFactors_four, Finset.mem_singleton]
    rintro ℓ rfl
    simpa using h_mid
  rw [irreducible_X_pow_sub_C_iff (by norm_num) hW0 h_top hmid']
  simp only [primeFactors_four, Finset.mem_singleton, forall_eq]

/-- The `mpr` direction of `irreducible_X_pow_four_sub_C_iff`, as a standalone lemma. -/
theorem irreducible_X_pow_four_sub_C {W : F} (hW0 : W ≠ 0)
    (h_top : 4 ∣ Fintype.card F ^ 4 - 1)
    (h_mid : 4 ∣ Fintype.card F ^ 2 - 1)
    (rabin_top : W ^ ((Fintype.card F ^ 4 - 1) / 4) = 1)
    (rabin_mid : W ^ ((Fintype.card F ^ 2 - 1) / 4) ≠ 1) :
    Irreducible ((X : F[X]) ^ 4 - C W) :=
  (irreducible_X_pow_four_sub_C_iff hW0 h_top h_mid).mpr ⟨rabin_top, rabin_mid⟩

/--
`irreducible_X_pow_four_sub_C` with the cardinality abstracted into a numeral `q`.

Concrete fields are defined as `ZMod fieldSize` where `fieldSize` is an *expression* such as
`2 ^ 31 - 2 ^ 24 + 1`. Stating the hypotheses in terms of a literal `q` lets callers discharge
them with `norm_num` and `reduce_mod_char`, both of which need the modulus as a numeral.
Supply `hcard` as `ZMod.card _`.

Note that `reduce_mod_char` still needs to see the *type* as `ZMod <numeral>`, so the two
exponentiation goals are usually preceded by a `show`; see
`CompPoly/Fields/KoalaBear/Ext4.lean` for the idiom.
-/
theorem irreducible_X_pow_four_sub_C_of_card {q : ℕ} {W : F}
    (hcard : Fintype.card F = q) (hW0 : W ≠ 0)
    (h_top : 4 ∣ q ^ 4 - 1) (h_mid : 4 ∣ q ^ 2 - 1)
    (rabin_top : W ^ ((q ^ 4 - 1) / 4) = 1)
    (rabin_mid : W ^ ((q ^ 2 - 1) / 4) ≠ 1) :
    Irreducible ((X : F[X]) ^ 4 - C W) := by
  subst hcard
  exact irreducible_X_pow_four_sub_C hW0 h_top h_mid rabin_top rabin_mid

/-- `irreducible_X_pow_four_sub_C_iff` with the cardinality abstracted into a numeral `q`. -/
theorem irreducible_X_pow_four_sub_C_iff_of_card {q : ℕ} {W : F}
    (hcard : Fintype.card F = q) (hW0 : W ≠ 0)
    (h_top : 4 ∣ q ^ 4 - 1) (h_mid : 4 ∣ q ^ 2 - 1) :
    Irreducible ((X : F[X]) ^ 4 - C W) ↔
      (W ^ ((q ^ 4 - 1) / 4) = 1 ∧ W ^ ((q ^ 2 - 1) / 4) ≠ 1) := by
  subst hcard
  exact irreducible_X_pow_four_sub_C_iff hW0 h_top h_mid

end Polynomial
