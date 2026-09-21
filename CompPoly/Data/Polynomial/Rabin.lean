/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Data.Polynomial.Frobenius
public import CompPoly.ToMathlib.Polynomial.Irreducible
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Rabin's irreducibility test

A polynomial `f` of degree `d` over a finite field `F` with `q = |F|` elements is irreducible
exactly when

* `f ∣ X^(q^d) - X`, and
* `f` is coprime to `X^(q^(d/ℓ)) - X` for every prime `ℓ ∣ d`.

The first condition says every irreducible factor of `f` has degree dividing `d`; the second
rules out all *proper* divisors of `d` as factor degrees, forcing `f` itself to be irreducible.
Both rest on the fundamental correspondence
`Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd` from
`CompPoly/Data/Polynomial/Frobenius.lean`.

This generalizes `irreducible_of_rabin_128_passed_over_GF2`
(`CompPoly/Fields/Binary/BF128Ghash/Basic.lean`), which is the `d = 128`, `F = GF(2)`
specialization, to arbitrary degree over any finite field.

## Main statements

* `Polynomial.irreducible_of_rabin`: the two conditions imply irreducibility.
* `Polynomial.rabin_of_irreducible`: the converse, so the test is exact.
* `Polynomial.irreducible_iff_rabin`: the resulting characterization.

All three take the field size as a numeral `q` with `hcard : Fintype.card F = q`; see "The shape
of these statements" below for why, and pass `rfl` if you have no numeral.

## References

* [Rabin80] Michael O. Rabin, *Probabilistic Algorithms in Finite Fields*,
  SIAM Journal on Computing 9(2), 1980.
-/

@[expose] public section

namespace Nat

/--
If `m` is a proper divisor of a nonzero `d`, then `m` divides `d / ℓ` for some prime factor `ℓ`
of `d`.

This is the arithmetic core of Rabin's test: it is why checking the prime-index quotients
`d / ℓ` suffices to rule out *every* proper divisor of `d`.
-/
theorem exists_primeFactor_dvd_div_of_dvd {m d : ℕ} (hd : d ≠ 0) (hmd : m ∣ d) (hne : m ≠ d) :
    ∃ ℓ ∈ d.primeFactors, m ∣ d / ℓ := by
  obtain ⟨k, hk⟩ := hmd
  have hk0 : k ≠ 0 := by rintro rfl; exact hd (by simpa using hk)
  have hk1 : k ≠ 1 := by rintro rfl; exact hne (by simpa using hk.symm)
  -- Generalize away from `minFac` so rewriting `k` cannot disturb the chosen prime.
  obtain ⟨ℓ, hℓp, hℓ_dvd_k⟩ : ∃ ℓ, ℓ.Prime ∧ ℓ ∣ k :=
    ⟨k.minFac, Nat.minFac_prime hk1, Nat.minFac_dvd k⟩
  obtain ⟨k', hk'⟩ := hℓ_dvd_k
  have hd_eq : d = ℓ * (m * k') := by rw [hk, hk']; ring
  refine ⟨ℓ, Nat.mem_primeFactors.mpr ⟨hℓp, ?_, hd⟩, ?_⟩
  · exact ⟨m * k', hd_eq⟩
  · rw [hd_eq, Nat.mul_div_cancel_left _ hℓp.pos]
    exact dvd_mul_right m k'

end Nat

namespace Polynomial

variable {F : Type*} [Field F] [Fintype F]

/--
The `Fact` instance required by `irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd`.

Deliberately *not* a global instance: it would apply to every finite field, and a blanket
`Fact` in the instance graph is easy to trip over later. The two proofs below introduce it
locally with `haveI` instead, so it never escapes this file and appears in no statement.
-/
private theorem factPrimeRingChar : Fact (Nat.Prime (ringChar F)) :=
  ⟨CharP.prime_ringChar F⟩

/-! ### The shape of these statements

Each test below takes the field size as a numeral `q` together with `hcard : Fintype.card F = q`,
rather than reading it off as `Fintype.card F`, and substitutes it away internally. Both kinds of
caller are served: a concrete field supplies `hcard` as `ZMod.card _` (or its own cardinality
lemma) and states its conditions at the numeral its certificates were generated for; a caller with
no numeral in hand passes `rfl` and gets the `Fintype.card F` statement back verbatim.

The alternative — stating the conditions at `Fintype.card F` and having concrete callers cast each
one with `rw [hcard]` — is what this shape exists to rule out. Such a cast leaves an `Eq.mpr`
transport around a certificate argument whose type carries a huge exponent (`X ^ (q ^ d)`), and a
kernel replay from an empty environment need not follow the same normalization path the elaborator
took: one such transport has been observed to send the kernel into
`Polynomial.pow → npowRec → Nat.rec`, unfolding the power one exponent step at a time until the
deep-recursion guard fired. Since there is only one form of each statement, that cast has no
occasion to appear. `docs/wiki/field-extensions.md` records the history, and
`CompPoly/Data/Polynomial/RabinCertificate.lean` packages these tests at concrete degrees.
-/

/--
**Rabin's irreducibility test (soundness).**

If a degree-`d` polynomial `f` over a finite field with `q` elements divides `X^(q^d) - X` and is
coprime to `X^(q^(d/ℓ)) - X` for every prime `ℓ ∣ d`, then `f` is irreducible.
-/
theorem irreducible_of_rabin {f : F[X]} {d q : ℕ} (hcard : Fintype.card F = q)
    (h_deg : f.natDegree = d) (h_pos : 0 < d)
    (h_trace : f ∣ X ^ (q ^ d) - X)
    (h_coprime : ∀ ℓ ∈ d.primeFactors, IsCoprime f (X ^ (q ^ (d / ℓ)) - X)) :
    Irreducible f := by
  subst hcard
  have := factPrimeRingChar (F := F)
  by_contra h_red
  -- A reducible `f` has an irreducible factor of degree at most `d / 2`.
  obtain ⟨p, hp_irr, hp_dvd_f, hp_deg⟩ :=
    exists_factor_natDegree_le_of_reducible f h_deg h_pos h_red
  -- `p ∣ f ∣ X^(q^d) - X`, so `deg p ∣ d`.
  have hp_dvd_d : p.natDegree ∣ d :=
    (irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd rfl d p hp_irr).mp (hp_dvd_f.trans h_trace)
  -- The bound `deg p ≤ d / 2` makes it a *proper* divisor.
  have hp_ne : p.natDegree ≠ d := by omega
  obtain ⟨ℓ, hℓ_mem, hℓ_dvd⟩ :=
    Nat.exists_primeFactor_dvd_div_of_dvd (by omega) hp_dvd_d hp_ne
  -- So `p` also divides the `ℓ`-th check polynomial, contradicting coprimality.
  have hp_dvd_mid : p ∣ X ^ (Fintype.card F ^ (d / ℓ)) - X :=
    (irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd rfl (d / ℓ) p hp_irr).mpr hℓ_dvd
  exact hp_irr.not_isUnit ((h_coprime ℓ hℓ_mem).isUnit_of_dvd' hp_dvd_f hp_dvd_mid)

/--
**Rabin's irreducibility test (completeness).**

An irreducible polynomial of degree `d` satisfies both Rabin conditions.
-/
theorem rabin_of_irreducible {f : F[X]} {d q : ℕ} (hcard : Fintype.card F = q)
    (h_deg : f.natDegree = d) (h_pos : 0 < d) (h_irr : Irreducible f) :
    f ∣ X ^ (q ^ d) - X ∧
      ∀ ℓ ∈ d.primeFactors, IsCoprime f (X ^ (q ^ (d / ℓ)) - X) := by
  subst hcard
  have := factPrimeRingChar (F := F)
  refine ⟨(irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd rfl d f h_irr).mpr (h_deg ▸ dvd_rfl),
    fun ℓ hℓ => ?_⟩
  -- For irreducible `f`, coprimality is exactly non-divisibility.
  rw [h_irr.coprime_iff_not_dvd,
    irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd rfl (d / ℓ) f h_irr, h_deg]
  -- `d ∤ d / ℓ` because `d / ℓ` is a positive proper divisor of `d`.
  obtain ⟨hℓ_prime, hℓ_dvd, -⟩ := Nat.mem_primeFactors.mp hℓ
  intro h_dvd
  have h_le : d ≤ d / ℓ := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd h_pos hℓ_dvd) hℓ_prime.pos)
    h_dvd
  have h_lt : d / ℓ < d := Nat.div_lt_self h_pos hℓ_prime.one_lt
  omega

/-- **Rabin's irreducibility test.** For a polynomial of positive degree `d` over a finite field
with `q` elements, irreducibility is equivalent to the two Rabin conditions. -/
theorem irreducible_iff_rabin {f : F[X]} {d q : ℕ} (hcard : Fintype.card F = q)
    (h_deg : f.natDegree = d) (h_pos : 0 < d) :
    Irreducible f ↔
      (f ∣ X ^ (q ^ d) - X ∧
        ∀ ℓ ∈ d.primeFactors, IsCoprime f (X ^ (q ^ (d / ℓ)) - X)) :=
  ⟨rabin_of_irreducible hcard h_deg h_pos,
    fun ⟨h₁, h₂⟩ => irreducible_of_rabin hcard h_deg h_pos h₁ h₂⟩

end Polynomial
