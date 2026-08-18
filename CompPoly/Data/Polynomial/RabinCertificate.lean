/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Data.Polynomial.Rabin
public import CompPoly.Data.RingTheory.CanonicalEuclideanDomain
public import Mathlib.Data.ZMod.Basic

/-!
# Kernel-checkable Rabin irreducibility certificates over prime fields

Rabin's test (`CompPoly/Data/Polynomial/Rabin.lean`) reduces irreducibility of a degree-`d`
polynomial `f` over `ZMod p` to divisibility and coprimality conditions against `X^(p^k) - X`.
Verifying those conditions requires computing `X^(p^k) mod f` — around `d · log₂ p` modular
squarings — which is far beyond what `decide` can do on `Polynomial` values and which this
repository's TCB policy forbids delegating to `native_decide`.

This file provides the reusable, degree-agnostic *certificate* infrastructure:

* Polynomials are represented as little-endian `ℕ`-coefficient lists (`toPoly` interprets them
  in `(ZMod p)[X]`), with schoolbook arithmetic (`addNat`, `mulNat`) by structural recursion,
  so every check reduces in the kernel via GMP-accelerated `Nat` operations.
* A certificate `Step` records a squaring (or multiply-by-`X`) together with the quotient and
  remainder of the division by `f`; `checkStep` verifies `cur² = q·f + r` (coefficientwise,
  mod `p`) and `runChain` folds a whole square-and-multiply chain, so an entire exponentiation
  certificate is one list literal checked by a single kernel reduction.
* `runChain_sound` lifts a checked chain to `X^N % f = r % f` in `(ZMod p)[X]`; the two Rabin
  conditions follow via `dvd_X_pow_sub_X_of_runChain` (trace) and
  `isCoprime_X_pow_sub_X_of_runChain` (coprimality, from a Bézout certificate on the reduced
  residue).
* `irreducible_of_rabin_prime_degree` packages Rabin's test for *prime* degree `d`, where the
  conditions collapse to a single trace and a single coprimality check. The `_of_card` variants
  of the packaged forms take the field size as a numeral `q` with `Fintype.card F = q`; that is
  the shape concrete extensions use.

Certificate data is produced by the untrusted generator `scripts/gen_rabin_certificate.py`;
the kernel re-checks every step. Contrast `CompPoly/Fields/Binary/BF128Ghash/`, the bespoke
GF(2¹²⁸) predecessor of this framework, which spells out each step as a separate lemma.
-/

@[expose] public section

namespace CompPoly.RabinCert

open Polynomial

/-! ### `ℕ`-level polynomial arithmetic

Little-endian coefficient lists. No coefficient is ever reduced during a product — entries
stay below `d² · p²`, comfortably inside GMP range — and comparisons reduce mod `p` at the
end (`eqModP`), so no subtraction (and hence no truncation) occurs anywhere.
-/

/-- Coefficientwise addition of little-endian coefficient lists. -/
def addNat : List ℕ → List ℕ → List ℕ
  | [], b => b
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: addNat as bs

/-- Scale a coefficient list by a constant. -/
def scaleNat (c : ℕ) (l : List ℕ) : List ℕ := l.map (c * ·)

/-- Schoolbook product of little-endian coefficient lists. -/
def mulNat : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: as, b => addNat (scaleNat a b) (0 :: mulNat as b)

/-- Coefficientwise equality modulo `p`, treating entries beyond a list's end as `0`. -/
def eqModP (p : ℕ) : List ℕ → List ℕ → Bool
  | [], b => b.all (· % p == 0)
  | a :: as, [] => (a % p == 0) && eqModP p as []
  | a :: as, b :: bs => (a % p == b % p) && eqModP p as bs

/-! ### The specification bridge -/

/-- Interpret a little-endian coefficient list in `(ZMod p)[X]`, Horner-style. Specification
only; certificate checking never evaluates it. -/
noncomputable def toPoly (p : ℕ) : List ℕ → (ZMod p)[X]
  | [] => 0
  | c :: cs => C (c : ZMod p) + X * toPoly p cs

@[simp] theorem toPoly_nil {p : ℕ} : toPoly p [] = 0 := rfl

theorem toPoly_cons {p : ℕ} (c : ℕ) (cs : List ℕ) :
    toPoly p (c :: cs) = C (c : ZMod p) + X * toPoly p cs := rfl

@[simp] theorem toPoly_X {p : ℕ} : toPoly p [0, 1] = X := by
  rw [toPoly_cons, toPoly_cons, toPoly_nil, Nat.cast_zero, Nat.cast_one, map_zero, map_one]
  ring

@[simp] theorem toPoly_one {p : ℕ} : toPoly p [1] = 1 := by
  rw [toPoly_cons, toPoly_nil, Nat.cast_one, map_one, mul_zero, add_zero]

theorem toPoly_addNat {p : ℕ} : ∀ a b : List ℕ,
    toPoly p (addNat a b) = toPoly p a + toPoly p b
  | [], b => by rw [show addNat [] b = b from rfl, toPoly_nil, zero_add]
  | a :: as, [] => by rw [show addNat (a :: as) [] = a :: as from rfl, toPoly_nil, add_zero]
  | a :: as, b :: bs => by
    rw [show addNat (a :: as) (b :: bs) = (a + b) :: addNat as bs from rfl, toPoly_cons,
      toPoly_addNat as bs, toPoly_cons, toPoly_cons, Nat.cast_add, map_add]
    ring

theorem toPoly_scaleNat {p : ℕ} (c : ℕ) : ∀ l : List ℕ,
    toPoly p (scaleNat c l) = C (c : ZMod p) * toPoly p l
  | [] => by rw [show scaleNat c [] = [] from rfl, toPoly_nil, mul_zero]
  | a :: as => by
    rw [show scaleNat c (a :: as) = (c * a) :: scaleNat c as from rfl, toPoly_cons,
      toPoly_scaleNat c as, toPoly_cons, Nat.cast_mul, map_mul]
    ring

theorem toPoly_mulNat {p : ℕ} : ∀ a b : List ℕ,
    toPoly p (mulNat a b) = toPoly p a * toPoly p b
  | [], b => by rw [show mulNat [] b = [] from rfl, toPoly_nil, zero_mul]
  | a :: as, b => by
    rw [show mulNat (a :: as) b = addNat (scaleNat a b) (0 :: mulNat as b) from rfl,
      toPoly_addNat, toPoly_scaleNat, toPoly_cons, toPoly_mulNat as b, Nat.cast_zero, map_zero,
      toPoly_cons]
    ring

/-- Two naturals equal mod `p` cast to the same element of `ZMod p`. -/
theorem cast_eq_cast_of_mod_eq {p a b : ℕ} (h : a % p = b % p) :
    (a : ZMod p) = (b : ZMod p) := by
  rw [← ZMod.natCast_mod a p, ← ZMod.natCast_mod b p, h]

theorem toPoly_eq_zero_of_all_mod_eq_zero {p : ℕ} : ∀ {l : List ℕ},
    l.all (· % p == 0) = true → toPoly p l = 0
  | [], _ => rfl
  | c :: cs, h => by
    rw [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [toPoly_cons, toPoly_eq_zero_of_all_mod_eq_zero h.2, mul_zero, add_zero,
      cast_eq_cast_of_mod_eq (h.1.trans (Nat.zero_mod p).symm), Nat.cast_zero, map_zero]

/-- Soundness of the coefficientwise checker: `eqModP` lists denote the same polynomial. -/
theorem toPoly_eq_of_eqModP {p : ℕ} : ∀ {a b : List ℕ},
    eqModP p a b = true → toPoly p a = toPoly p b
  | [], b, h => by
    rw [show eqModP p [] b = b.all (· % p == 0) from rfl] at h
    rw [toPoly_nil, toPoly_eq_zero_of_all_mod_eq_zero h]
  | a :: as, [], h => by
    rw [show eqModP p (a :: as) [] = ((a % p == 0) && eqModP p as []) from rfl,
      Bool.and_eq_true, beq_iff_eq] at h
    rw [toPoly_cons, toPoly_eq_of_eqModP h.2, toPoly_nil, mul_zero, add_zero,
      cast_eq_cast_of_mod_eq (h.1.trans (Nat.zero_mod p).symm), Nat.cast_zero, map_zero]
  | a :: as, b :: bs, h => by
    rw [show eqModP p (a :: as) (b :: bs) = ((a % p == b % p) && eqModP p as bs) from rfl,
      Bool.and_eq_true, beq_iff_eq] at h
    rw [toPoly_cons, toPoly_cons, toPoly_eq_of_eqModP h.2, cast_eq_cast_of_mod_eq h.1]

/-- Lift a checked `ℕ`-level identity `a·b ≡ q·f + r (mod p)` to `(ZMod p)[X]`. -/
theorem verify_mulAdd {p : ℕ} {a b q fL r : List ℕ}
    (h : eqModP p (mulNat a b) (addNat (mulNat q fL) r) = true) :
    toPoly p a * toPoly p b = toPoly p q * toPoly p fL + toPoly p r := by
  have h' := toPoly_eq_of_eqModP h
  rwa [toPoly_mulNat, toPoly_addNat, toPoly_mulNat] at h'

/-! ### Square-and-multiply chains -/

/--
One step of a square-and-multiply chain modulo `f`: from the current residue `cur`, either
square it (`mulX = false`) or multiply it by `X` (`mulX = true`), and divide by `f` to get
quotient `q` and next residue `r`. The generator supplies `q` and `r`; the checker only has
to confirm one polynomial identity per step.
-/
structure Step where
  /-- `true` for a multiply-by-`X` step, `false` for a squaring step. -/
  mulX : Bool
  /-- The quotient of the step's product by the modulus. -/
  q : List ℕ
  /-- The remainder — the next residue in the chain. -/
  r : List ℕ

/-- Check one chain step: `cur² = q·f + r` (or `X·cur = q·f + r`), coefficientwise mod `p`. -/
def checkStep (p : ℕ) (fL cur : List ℕ) (s : Step) : Bool :=
  eqModP p (cond s.mulX (0 :: cur) (mulNat cur cur)) (addNat (mulNat s.q fL) s.r)

/-- Fold a chain of steps from the residue `cur`, checking each; returns the final residue,
or `none` if any check fails. One kernel reduction of `runChain` verifies a whole chain. -/
def runChain (p : ℕ) (fL : List ℕ) : List ℕ → List Step → Option (List ℕ)
  | cur, [] => some cur
  | cur, s :: rest => cond (checkStep p fL cur s) (runChain p fL s.r rest) none

/-- The exponent a chain computes: squaring doubles it, multiply-by-`X` adds one. -/
def chainExp : ℕ → List Step → ℕ
  | e, [] => e
  | e, s :: rest => chainExp (cond s.mulX (e + 1) (2 * e)) rest

/-- `(q·f + r) % f = r % f`: the checked identity discharges one step of the chain. -/
private theorem mod_add_mul_cancel {p : ℕ} [Fact p.Prime] {f q r : (ZMod p)[X]} (hf0 : f ≠ 0) :
    (q * f + r) % f = r % f := by
  have h : q * f + r = r + f * q := by ring
  rw [h, CanonicalEuclideanDomain.add_mul_mod_right r f q hf0]

/-- Soundness of one chain step. -/
theorem step_sound {p : ℕ} [Fact p.Prime] {fL cur : List ℕ} {f : (ZMod p)[X]}
    (hfL : toPoly p fL = f) (hf0 : f ≠ 0) {s : Step} {e : ℕ}
    (hcheck : checkStep p fL cur s = true)
    (hprev : (X : (ZMod p)[X]) ^ e % f = toPoly p cur % f) :
    (X : (ZMod p)[X]) ^ (cond s.mulX (e + 1) (2 * e)) % f = toPoly p s.r % f := by
  rw [checkStep] at hcheck
  cases hm : s.mulX with
  | false =>
    rw [hm, cond_false] at hcheck
    rw [cond_false]
    have hstep := verify_mulAdd hcheck
    rw [hfL] at hstep
    calc (X : (ZMod p)[X]) ^ (2 * e) % f
        = (X ^ e * X ^ e) % f := by rw [two_mul, pow_add]
      _ = (X ^ e % f) * (X ^ e % f) % f := CanonicalEuclideanDomain.mul_mod_eq _ _ _ hf0
      _ = (toPoly p cur % f) * (toPoly p cur % f) % f := by rw [hprev]
      _ = (toPoly p cur * toPoly p cur) % f :=
          (CanonicalEuclideanDomain.mul_mod_eq _ _ _ hf0).symm
      _ = (toPoly p s.q * f + toPoly p s.r) % f := by rw [hstep]
      _ = toPoly p s.r % f := mod_add_mul_cancel hf0
  | true =>
    rw [hm, cond_true] at hcheck
    rw [cond_true]
    have hstep := toPoly_eq_of_eqModP hcheck
    rw [toPoly_addNat, toPoly_mulNat, hfL, toPoly_cons, Nat.cast_zero, map_zero,
      zero_add] at hstep
    calc (X : (ZMod p)[X]) ^ (e + 1) % f
        = (X ^ e * X) % f := by rw [pow_succ]
      _ = (X ^ e % f) * (X % f) % f := CanonicalEuclideanDomain.mul_mod_eq _ _ _ hf0
      _ = (toPoly p cur % f) * (X % f) % f := by rw [hprev]
      _ = (toPoly p cur * X) % f := (CanonicalEuclideanDomain.mul_mod_eq _ _ _ hf0).symm
      _ = (X * toPoly p cur) % f := by rw [mul_comm]
      _ = (toPoly p s.q * f + toPoly p s.r) % f := by rw [hstep]
      _ = toPoly p s.r % f := mod_add_mul_cancel hf0

/-- **Soundness of a whole chain**: a checked chain starting at the residue of `X^e` ends at
the residue of `X^(chainExp e steps)`. -/
theorem runChain_sound {p : ℕ} [Fact p.Prime] {fL : List ℕ} {f : (ZMod p)[X]}
    (hfL : toPoly p fL = f) (hf0 : f ≠ 0) :
    ∀ (steps : List Step) (cur out : List ℕ) (e : ℕ),
      runChain p fL cur steps = some out →
      (X : (ZMod p)[X]) ^ e % f = toPoly p cur % f →
      (X : (ZMod p)[X]) ^ chainExp e steps % f = toPoly p out % f
  | [], cur, out, e, hrun, hprev => by
    rw [show runChain p fL cur [] = some cur from rfl, Option.some.injEq] at hrun
    subst hrun
    exact hprev
  | s :: rest, cur, out, e, hrun, hprev => by
    rw [show runChain p fL cur (s :: rest)
        = cond (checkStep p fL cur s) (runChain p fL s.r rest) none from rfl] at hrun
    cases hc : checkStep p fL cur s with
    | false => rw [hc, cond_false] at hrun; exact absurd hrun (by simp)
    | true =>
      rw [hc, cond_true] at hrun
      exact runChain_sound hfL hf0 rest s.r out _ hrun (step_sound hfL hf0 hc hprev)

/-- A chain started at `[0, 1]` (the residue of `X¹`) computes `X^N % f`. -/
theorem xpow_mod_of_runChain {p : ℕ} [Fact p.Prime] {fL : List ℕ} {f : (ZMod p)[X]}
    (hfL : toPoly p fL = f) (hf0 : f ≠ 0) {steps : List Step} {out : List ℕ} {N : ℕ}
    (hrun : runChain p fL [0, 1] steps = some out)
    (hexp : chainExp 1 steps = N) :
    (X : (ZMod p)[X]) ^ N % f = toPoly p out % f := by
  subst hexp
  refine runChain_sound hfL hf0 steps [0, 1] out 1 hrun ?_
  rw [toPoly_X, pow_one]

/-! ### The two Rabin conditions from certificates -/

/-- Equal remainders mean the divisor divides the difference. -/
theorem dvd_sub_of_mod_eq {R : Type*} [EuclideanDomain R] {a b n : R} (h : a % n = b % n) :
    n ∣ a - b := by
  refine ⟨a / n - b / n, ?_⟩
  have ha := EuclideanDomain.div_add_mod a n
  have hb := EuclideanDomain.div_add_mod b n
  calc a - b = (n * (a / n) + a % n) - (n * (b / n) + b % n) := by rw [ha, hb]
    _ = n * (a / n - b / n) := by rw [h]; ring

/-- **The trace condition from a chain.** A checked chain for `X^N` ending back at `[0, 1]`
(the residue `X`) proves `f ∣ X^N - X`. -/
theorem dvd_X_pow_sub_X_of_runChain {p : ℕ} [Fact p.Prime] {fL : List ℕ} {f : (ZMod p)[X]}
    (hfL : toPoly p fL = f) (hf0 : f ≠ 0) {steps : List Step} {N : ℕ}
    (hrun : runChain p fL [0, 1] steps = some [0, 1])
    (hexp : chainExp 1 steps = N) :
    f ∣ (X : (ZMod p)[X]) ^ N - X := by
  have h := xpow_mod_of_runChain hfL hf0 hrun hexp
  rw [toPoly_X] at h
  exact dvd_sub_of_mod_eq h

/--
**The coprimality condition from a chain plus a Bézout certificate.**

The chain reduces `X^N` to a residue `rp`; writing `rp = w + X` (checked by `eqModP`), we have
`X^N - X ≡ w (mod f)`, so a Bézout identity `u·f + v·w = 1` (again checked by `eqModP`)
witnesses `IsCoprime f (X^N - X)`.
-/
theorem isCoprime_X_pow_sub_X_of_runChain {p : ℕ} [Fact p.Prime] {fL : List ℕ} {f : (ZMod p)[X]}
    (hfL : toPoly p fL = f) (hf0 : f ≠ 0) {steps : List Step} {rp w u v : List ℕ} {N : ℕ}
    (hrun : runChain p fL [0, 1] steps = some rp)
    (hexp : chainExp 1 steps = N)
    (hw : eqModP p rp (addNat w [0, 1]) = true)
    (hbez : eqModP p (addNat (mulNat u fL) (mulNat v w)) [1] = true) :
    IsCoprime f ((X : (ZMod p)[X]) ^ N - X) := by
  have hmod := xpow_mod_of_runChain hfL hf0 hrun hexp
  have hrw : toPoly p rp = toPoly p w + X := by
    have h' := toPoly_eq_of_eqModP hw
    rwa [toPoly_addNat, toPoly_X] at h'
  have hb : toPoly p u * f + toPoly p v * toPoly p w = 1 := by
    have h' := toPoly_eq_of_eqModP hbez
    rwa [toPoly_addNat, toPoly_mulNat, toPoly_mulNat, hfL, toPoly_one] at h'
  have hdvd : f ∣ ((X : (ZMod p)[X]) ^ N - X) - toPoly p w := by
    have h1 : f ∣ (X : (ZMod p)[X]) ^ N - toPoly p rp := dvd_sub_of_mod_eq hmod
    have h2 : (X : (ZMod p)[X]) ^ N - toPoly p rp = (X ^ N - X) - toPoly p w := by
      rw [hrw]; ring
    rwa [h2] at h1
  obtain ⟨c, hc⟩ := hdvd
  have hXN : (X : (ZMod p)[X]) ^ N - X = toPoly p w + f * c := by rw [← hc]; ring
  rw [hXN]
  exact IsCoprime.add_mul_left_right ⟨toPoly p u, toPoly p v, hb⟩ c

/-! ### Packaging Rabin's test at a concrete degree

`Polynomial.irreducible_of_rabin` already quantifies the coprimality condition over
`d.primeFactors`. The wrappers below discharge that quantifier for the two shapes of `d` that
concrete extensions use, so a caller supplies one coprimality proof per prime factor and nothing
else. Note that `irreducible_of_rabin_prime_degree` does **not** apply at composite `d`, and its
collapsed condition is not merely inconvenient but unsound there: a product of equal-degree
factors divides `X^(q^d) - X` and is coprime to `X^q - X`, so it would pass.
-/

/--
**Rabin's test for prime degree.** For `f` of *prime* degree `d` over a finite field, the
per-prime-factor conditions collapse to a single coprimality check at exponent `q = |F|`:
`f` is irreducible provided `f ∣ X^(q^d) - X` and `IsCoprime f (X^q - X)`.
-/
theorem irreducible_of_rabin_prime_degree {F : Type*} [Field F] [Fintype F] {f : F[X]} {d : ℕ}
    (hd : d.Prime) (h_deg : f.natDegree = d)
    (h_trace : f ∣ X ^ (Fintype.card F ^ d) - X)
    (h_cop : IsCoprime f (X ^ Fintype.card F - X)) :
    Irreducible f := by
  refine Polynomial.irreducible_of_rabin h_deg hd.pos h_trace fun ℓ hℓ => ?_
  rw [hd.primeFactors, Finset.mem_singleton] at hℓ
  subst hℓ
  rw [Nat.div_self hd.pos, pow_one]
  exact h_cop

/--
**Rabin's test for a degree with exactly two prime factors**, such as `d = 6`.

The caller supplies the trace condition plus one coprimality certificate per prime factor, at
exponents `q^(d/ℓ₁)` and `q^(d/ℓ₂)`. The hypothesis `h_factors` is `by decide` at a concrete
degree — for `d = 6` it is `(6 : ℕ).primeFactors = {2, 3}`, giving checks at `q^3` and `q^2`.

Both checks are needed. Dropping the `q^3` one admits a product of two irreducible cubics;
dropping the `q^2` one admits a product of three irreducible quadratics.
-/
theorem irreducible_of_rabin_two_prime_factors {F : Type*} [Field F] [Fintype F] {f : F[X]}
    {d ℓ₁ ℓ₂ : ℕ} (h_deg : f.natDegree = d) (h_pos : 0 < d)
    (h_factors : d.primeFactors = {ℓ₁, ℓ₂})
    (h_trace : f ∣ X ^ (Fintype.card F ^ d) - X)
    (h_cop₁ : IsCoprime f (X ^ (Fintype.card F ^ (d / ℓ₁)) - X))
    (h_cop₂ : IsCoprime f (X ^ (Fintype.card F ^ (d / ℓ₂)) - X)) :
    Irreducible f := by
  refine Polynomial.irreducible_of_rabin h_deg h_pos h_trace fun ℓ hℓ => ?_
  rw [h_factors] at hℓ
  rcases Finset.mem_insert.mp hℓ with h | h
  · subst h; exact h_cop₁
  · rw [Finset.mem_singleton] at h; subst h; exact h_cop₂

/-- The prime factors of `6`. Mirrors `primeFactors_four` in
`CompPoly/Fields/Extension/Binomial.lean`; `decide` cannot do this because
`Nat.primeFactorsList` is well-founded recursive and does not reduce in the kernel. -/
private theorem primeFactors_six : (6 : ℕ).primeFactors = {2, 3} := by
  rw [show (6 : ℕ) = 2 * 3 from by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
  rfl

/--
**Rabin's test at degree 6.** `f` of degree 6 over a finite field with `q` elements is irreducible
provided `f ∣ X^(q^6) - X`, `IsCoprime f (X^(q^3) - X)`, and `IsCoprime f (X^(q^2) - X)`.

This is the shape used by the KoalaBear degree-6 extension. It differs from
`irreducible_of_rabin_two_prime_factors` only in discharging `Nat.primeFactors 6 = {2, 3}`
internally, so callers never touch `Nat.primeFactors`.

The `q^3` check is what rules out a product of two irreducible cubics, and the `q^2` check a
product of three irreducible quadratics; the trace condition alone permits both.
-/
theorem irreducible_of_rabin_degree_six {F : Type*} [Field F] [Fintype F] {f : F[X]}
    (h_deg : f.natDegree = 6)
    (h_trace : f ∣ X ^ (Fintype.card F ^ 6) - X)
    (h_cop₃ : IsCoprime f (X ^ (Fintype.card F ^ 3) - X))
    (h_cop₂ : IsCoprime f (X ^ (Fintype.card F ^ 2) - X)) :
    Irreducible f :=
  irreducible_of_rabin_two_prime_factors h_deg (by norm_num) primeFactors_six h_trace
    (by simpa using h_cop₃) (by simpa using h_cop₂)

/-! ### Explicit-cardinality forms

The wrappers above state their conditions at `Fintype.card F`. Concrete extensions instead define
their field as `ZMod fieldSize` and generate certificates already stated in terms of the numeral
(`chainExp 1 steps = fieldSize ^ d`), so the `_of_card` forms below take the field size as a
caller-supplied `q` with `hcard : Fintype.card F = q`. Same shape as
`irreducible_X_pow_four_sub_C_of_card` in `CompPoly/Fields/Extension/Binomial.lean`.
-/

/--
**Rabin's test for prime degree, with the cardinality abstracted into a numeral `q`.**

Identical content to `irreducible_of_rabin_prime_degree`, with the field size supplied as `q` and
`hcard : Fintype.card F = q` rather than read off as `Fintype.card F`. Each Rabin condition is then
discharged by applying its certificate directly, rather than first casting the goal with
`rw [hcard]`. Supply `hcard` as `ZMod.card _`.

Nothing is weakened: instantiating at `q := Fintype.card F` with `rfl` recovers
`irreducible_of_rabin_prime_degree` verbatim, and `CompPolyTests.RabinCertificate` pins that
instantiation as a regression test.
-/
theorem irreducible_of_rabin_prime_degree_of_card {F : Type*} [Field F] [Fintype F]
    {f : F[X]} {d q : ℕ} (hcard : Fintype.card F = q)
    (hd : d.Prime) (h_deg : f.natDegree = d)
    (h_trace : f ∣ X ^ (q ^ d) - X)
    (h_cop : IsCoprime f (X ^ q - X)) :
    Irreducible f := by
  subst hcard
  exact irreducible_of_rabin_prime_degree hd h_deg h_trace h_cop

/-- **Rabin's test at degree 6, with the cardinality abstracted into a numeral `q`.** See
`irreducible_of_rabin_prime_degree_of_card`; the same reasoning applies at composite degree 6. -/
theorem irreducible_of_rabin_degree_six_of_card {F : Type*} [Field F] [Fintype F]
    {f : F[X]} {q : ℕ} (hcard : Fintype.card F = q)
    (h_deg : f.natDegree = 6)
    (h_trace : f ∣ X ^ (q ^ 6) - X)
    (h_cop₃ : IsCoprime f (X ^ (q ^ 3) - X))
    (h_cop₂ : IsCoprime f (X ^ (q ^ 2) - X)) :
    Irreducible f := by
  subst hcard
  exact irreducible_of_rabin_degree_six h_deg h_trace h_cop₃ h_cop₂

end CompPoly.RabinCert
