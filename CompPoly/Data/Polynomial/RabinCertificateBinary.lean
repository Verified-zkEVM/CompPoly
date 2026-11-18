/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Data.Polynomial.RabinCertificate

/-!
# Rabin certificates over `GF(2)` on `ℕ` bitmasks

`CompPoly/Data/Polynomial/RabinCertificate.lean` checks a square-and-multiply chain on
little-endian coefficient lists with schoolbook arithmetic, which works over any prime field.
Over `GF(2)` a polynomial is a bitmask: bit `i` of `n : ℕ` is the coefficient of `X^i`.
Addition is `xor` and multiplication is carry-less, so the kernel checks each step with a few
GMP-backed `Nat` operations (`xor`, `shiftLeft`, `%`, `/`) instead of walking lists of
numerals. For the degree-64 modulus of `BF64` this takes the certificate check from about 26 s
to about 2 s.

The chain format mirrors the list version: each `Step` carries the quotient and remainder of
one squaring (or multiply-by-`X`) step, the kernel checks `cur² = q·f + r` exactly, and
`runChain_sound` lifts a checked chain to `X^N % f = r % f` in `(ZMod 2)[X]`. Because the
bitmask of a `GF(2)` polynomial is unique, checks compare with `==` and need no reduction.

## Main definitions

* `clmul` — carry-less product of two bitmasks, by structural recursion on a bit count.
* `toPoly` — the polynomial a bitmask denotes. Specification only; checking never evaluates it.
* `Step`, `checkStep`, `runChain`, `chainExp` — the chain checker.

## Main statements

* `toPoly_clmul` — `clmul` is polynomial multiplication.
* `dvd_X_pow_sub_X_of_runChain`, `isCoprime_X_pow_sub_X_of_runChain` — the two Rabin
  conditions from certificates, with the same shape as the list versions, so they feed
  `irreducible_of_rabin_prime_degree` and its siblings unchanged.

Certificate data comes from `scripts/gen_rabin_certificate.py --binary`.
-/

@[expose] public section

namespace CompPoly.RabinCert.Binary

open Polynomial

/-! ### Carry-less multiplication -/

/-- Carry-less product of the low `n` bits of `a` with `b`. Structural recursion on `n`, so the
kernel unfolds it once per bit of `a`. -/
def clmulBits : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, a, b => cond (a % 2 == 1) b 0 ^^^ (clmulBits n (a / 2) b <<< 1)

/-- Carry-less product of two bitmasks: polynomial multiplication over `GF(2)`. -/
def clmul (a b : ℕ) : ℕ := clmulBits (Nat.log2 a + 1) a b

/-! ### The specification bridge -/

/-- The polynomial over `GF(2)` whose coefficient of `X^i` is bit `i` of `n`. Every set bit of
`n` is below `n`, so the sum over `range n` covers them. Specification only. -/
noncomputable def toPoly (n : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range n, if n.testBit i then X ^ i else 0

theorem coeff_toPoly (n i : ℕ) :
    (toPoly n).coeff i = if n.testBit i then 1 else 0 := by
  rw [toPoly, finsetSum_coeff]
  by_cases hi : i < n
  · rw [Finset.sum_eq_single i]
    · split <;> simp
    · intro j _ hji
      split <;> simp [coeff_X_pow, Ne.symm hji]
    · intro h
      exact absurd (Finset.mem_range.2 hi) h
  · have hbit : n.testBit i = false := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi)))
    rw [hbit, Finset.sum_eq_zero]
    · simp
    · intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ Finset.mem_range.1 hj)
      split <;> simp [coeff_X_pow, Ne.symm hji]

/-- Two bitmasks with the same bits denote the same polynomial. -/
theorem toPoly_congr {a b : ℕ} (h : ∀ i, a.testBit i = b.testBit i) : toPoly a = toPoly b := by
  ext i
  rw [coeff_toPoly, coeff_toPoly, h]

@[simp] theorem toPoly_zero : toPoly 0 = 0 := by
  ext i
  simp [coeff_toPoly]

theorem toPoly_xor (a b : ℕ) : toPoly (a ^^^ b) = toPoly a + toPoly b := by
  ext i
  rw [coeff_add, coeff_toPoly, coeff_toPoly, coeff_toPoly, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem toPoly_two_pow (k : ℕ) : toPoly (2 ^ k) = X ^ k := by
  ext i
  rw [coeff_toPoly, Nat.testBit_two_pow, coeff_X_pow]
  by_cases h : k = i
  · simp [h]
  · simp [h, Ne.symm h]

theorem toPoly_one : toPoly 1 = 1 := by
  simpa using toPoly_two_pow 0

/-- The bitmask `2` is `X`. -/
theorem toPoly_two : toPoly 2 = X := by
  simpa using toPoly_two_pow 1

theorem toPoly_shiftLeft_one (a : ℕ) : toPoly (a <<< 1) = X * toPoly a := by
  ext i
  rw [coeff_toPoly, Nat.testBit_shiftLeft]
  cases i with
  | zero => simp
  | succ i => simp [coeff_X_mul, coeff_toPoly]

/-- Splitting off the lowest bit: the low `n + 1` bits of `a` are bit `0` plus `X` times the low
`n` bits of `a / 2`. -/
theorem toPoly_mod_two_pow_succ (a n : ℕ) :
    toPoly (a % 2 ^ (n + 1)) = (if a % 2 = 1 then 1 else 0) + X * toPoly (a / 2 % 2 ^ n) := by
  ext i
  rw [coeff_add, coeff_toPoly, Nat.testBit_mod_two_pow]
  cases i with
  | zero =>
    rw [coeff_X_mul_zero, add_zero, Nat.testBit_zero]
    split <;> simp_all
  | succ i =>
    rw [coeff_X_mul, coeff_toPoly, Nat.testBit_mod_two_pow, Nat.testBit_succ]
    have hc : (if a % 2 = 1 then (1 : (ZMod 2)[X]) else 0).coeff (i + 1) = 0 := by
      split <;> simp only [coeff_one, coeff_zero, Nat.succ_ne_zero, ite_false]
    rw [hc, zero_add]
    simp only [Nat.add_lt_add_iff_right]

theorem toPoly_clmulBits (n a b : ℕ) :
    toPoly (clmulBits n a b) = toPoly (a % 2 ^ n) * toPoly b := by
  induction n generalizing a with
  | zero => simp [clmulBits, Nat.mod_one]
  | succ n ih =>
    rw [clmulBits, toPoly_xor, toPoly_shiftLeft_one, ih, toPoly_mod_two_pow_succ]
    by_cases h : a % 2 = 1
    · simp [h]; ring
    · simp [h]; ring

/-- **`clmul` is polynomial multiplication over `GF(2)`.** -/
theorem toPoly_clmul (a b : ℕ) : toPoly (clmul a b) = toPoly a * toPoly b := by
  rw [clmul, toPoly_clmulBits, Nat.mod_eq_of_lt Nat.lt_log2_self]

/-! ### Square-and-multiply chains -/

/-- One step of a square-and-multiply chain modulo `f`, as for the list checker: square the
current residue (`mulX = false`) or multiply it by `X` (`mulX = true`), with quotient `q` and
next residue `r` supplied by the generator. -/
structure Step where
  /-- `true` for a multiply-by-`X` step, `false` for a squaring step. -/
  mulX : Bool
  /-- The quotient of the step's product by the modulus, as a bitmask. -/
  q : ℕ
  /-- The remainder — the next residue in the chain — as a bitmask. -/
  r : ℕ

/-- Check one chain step: `cur² = q·f + r` (or `X·cur = q·f + r`) over `GF(2)`. -/
def checkStep (f cur : ℕ) (s : Step) : Bool :=
  cond s.mulX (cur <<< 1) (clmul cur cur) == (clmul s.q f ^^^ s.r)

/-- Fold a chain of steps from the residue `cur`, checking each; returns the final residue, or
`none` if any check fails. One kernel reduction of `runChain` verifies a whole chain. -/
def runChain (f : ℕ) : ℕ → List Step → Option ℕ
  | cur, [] => some cur
  | cur, s :: rest => cond (checkStep f cur s) (runChain f s.r rest) none

/-- The exponent a chain computes: squaring doubles it, multiply-by-`X` adds one. -/
def chainExp : ℕ → List Step → ℕ
  | e, [] => e
  | e, s :: rest => chainExp (cond s.mulX (e + 1) (2 * e)) rest

/-- A checked step is a polynomial identity. -/
theorem checkStep_sound {f cur : ℕ} {s : Step} (h : checkStep f cur s = true) :
    toPoly (cond s.mulX (cur <<< 1) (clmul cur cur)) = toPoly s.q * toPoly f + toPoly s.r := by
  rw [checkStep, beq_iff_eq] at h
  rw [h, toPoly_xor, toPoly_clmul]

private theorem mod_add_mul_cancel {f q r : (ZMod 2)[X]} (hf0 : f ≠ 0) :
    (q * f + r) % f = r % f := by
  have h : q * f + r = r + f * q := by ring
  rw [h, CanonicalEuclideanDomain.add_mul_mod_right r f q hf0]

/-- Soundness of one chain step. -/
theorem step_sound {fN cur : ℕ} {f : (ZMod 2)[X]} (hfN : toPoly fN = f) (hf0 : f ≠ 0)
    {s : Step} {e : ℕ} (hcheck : checkStep fN cur s = true)
    (hprev : (X : (ZMod 2)[X]) ^ e % f = toPoly cur % f) :
    (X : (ZMod 2)[X]) ^ (cond s.mulX (e + 1) (2 * e)) % f = toPoly s.r % f := by
  have hstep := checkStep_sound hcheck
  rw [hfN] at hstep
  cases hm : s.mulX with
  | false =>
    rw [hm, Bool.cond_false, toPoly_clmul] at hstep
    rw [Bool.cond_false]
    calc (X : (ZMod 2)[X]) ^ (2 * e) % f
        = (X ^ e * X ^ e) % f := by rw [two_mul, pow_add]
      _ = (X ^ e % f) * (X ^ e % f) % f := CanonicalEuclideanDomain.mul_mod_eq _ _ _ hf0
      _ = (toPoly cur % f) * (toPoly cur % f) % f := by rw [hprev]
      _ = (toPoly cur * toPoly cur) % f :=
          (CanonicalEuclideanDomain.mul_mod_eq _ _ _ hf0).symm
      _ = (toPoly s.q * f + toPoly s.r) % f := by rw [hstep]
      _ = toPoly s.r % f := mod_add_mul_cancel hf0
  | true =>
    rw [hm, Bool.cond_true, toPoly_shiftLeft_one] at hstep
    rw [Bool.cond_true]
    calc (X : (ZMod 2)[X]) ^ (e + 1) % f
        = (X ^ e * X) % f := by rw [pow_succ]
      _ = (X ^ e % f) * (X % f) % f := CanonicalEuclideanDomain.mul_mod_eq _ _ _ hf0
      _ = (toPoly cur % f) * (X % f) % f := by rw [hprev]
      _ = (toPoly cur * X) % f := (CanonicalEuclideanDomain.mul_mod_eq _ _ _ hf0).symm
      _ = (X * toPoly cur) % f := by rw [mul_comm]
      _ = (toPoly s.q * f + toPoly s.r) % f := by rw [hstep]
      _ = toPoly s.r % f := mod_add_mul_cancel hf0

/-- **Soundness of a whole chain**: a checked chain starting at the residue of `X^e` ends at
the residue of `X^(chainExp e steps)`. -/
theorem runChain_sound {fN : ℕ} {f : (ZMod 2)[X]} (hfN : toPoly fN = f) (hf0 : f ≠ 0) :
    ∀ (steps : List Step) (cur out : ℕ) (e : ℕ),
      runChain fN cur steps = some out →
      (X : (ZMod 2)[X]) ^ e % f = toPoly cur % f →
      (X : (ZMod 2)[X]) ^ chainExp e steps % f = toPoly out % f
  | [], cur, out, e, hrun, hprev => by
    rw [show runChain fN cur [] = some cur from rfl, Option.some.injEq] at hrun
    subst hrun
    exact hprev
  | s :: rest, cur, out, e, hrun, hprev => by
    rw [show runChain fN cur (s :: rest)
        = cond (checkStep fN cur s) (runChain fN s.r rest) none from rfl] at hrun
    cases hc : checkStep fN cur s with
    | false => rw [hc, Bool.cond_false] at hrun; exact absurd hrun (by simp)
    | true =>
      rw [hc, Bool.cond_true] at hrun
      exact runChain_sound hfN hf0 rest s.r out _ hrun (step_sound hfN hf0 hc hprev)

/-- A chain started at `2` (the bitmask of `X`) computes `X^N % f`. -/
theorem xpow_mod_of_runChain {fN : ℕ} {f : (ZMod 2)[X]} (hfN : toPoly fN = f) (hf0 : f ≠ 0)
    {steps : List Step} {out N : ℕ} (hrun : runChain fN 2 steps = some out)
    (hexp : chainExp 1 steps = N) :
    (X : (ZMod 2)[X]) ^ N % f = toPoly out % f := by
  subst hexp
  refine runChain_sound hfN hf0 steps 2 out 1 hrun ?_
  rw [pow_one, toPoly_two]

/-! ### The two Rabin conditions from certificates -/

/-- **The trace condition from a chain.** A checked chain for `X^N` ending back at `2` (the
residue `X`) proves `f ∣ X^N - X`. -/
theorem dvd_X_pow_sub_X_of_runChain {fN : ℕ} {f : (ZMod 2)[X]} (hfN : toPoly fN = f)
    (hf0 : f ≠ 0) {steps : List Step} {N : ℕ} (hrun : runChain fN 2 steps = some 2)
    (hexp : chainExp 1 steps = N) :
    f ∣ (X : (ZMod 2)[X]) ^ N - X := by
  have h := xpow_mod_of_runChain hfN hf0 hrun hexp
  rw [toPoly_two] at h
  exact dvd_sub_of_mod_eq h

/--
**The coprimality condition from a chain plus a Bézout certificate.** The chain reduces `X^N`
to a residue `rp`; `rp = w ^^^ 2` says `rp = w + X`, so `X^N - X ≡ w (mod f)`, and the Bézout
identity `u·f + v·w = 1` witnesses `IsCoprime f (X^N - X)`.
-/
theorem isCoprime_X_pow_sub_X_of_runChain {fN : ℕ} {f : (ZMod 2)[X]} (hfN : toPoly fN = f)
    (hf0 : f ≠ 0) {steps : List Step} {rp w u v N : ℕ}
    (hrun : runChain fN 2 steps = some rp)
    (hexp : chainExp 1 steps = N)
    (hw : (rp == w ^^^ 2) = true)
    (hbez : (clmul u fN ^^^ clmul v w == 1) = true) :
    IsCoprime f ((X : (ZMod 2)[X]) ^ N - X) := by
  have hmod := xpow_mod_of_runChain hfN hf0 hrun hexp
  have hrw : toPoly rp = toPoly w + X := by
    rw [beq_iff_eq] at hw
    rw [hw, toPoly_xor, toPoly_two]
  have hb : toPoly u * f + toPoly v * toPoly w = 1 := by
    rw [beq_iff_eq] at hbez
    have h' := congrArg toPoly hbez
    rwa [toPoly_xor, toPoly_clmul, toPoly_clmul, hfN, toPoly_one] at h'
  have hdvd : f ∣ ((X : (ZMod 2)[X]) ^ N - X) - toPoly w := by
    have h1 : f ∣ (X : (ZMod 2)[X]) ^ N - toPoly rp := dvd_sub_of_mod_eq hmod
    have h2 : (X : (ZMod 2)[X]) ^ N - toPoly rp = (X ^ N - X) - toPoly w := by
      rw [hrw]; ring
    rwa [h2] at h1
  obtain ⟨c, hc⟩ := hdvd
  have hXN : (X : (ZMod 2)[X]) ^ N - X = toPoly w + f * c := by rw [← hc]; ring
  rw [hXN]
  exact IsCoprime.add_mul_left_right ⟨toPoly u, toPoly v, hb⟩ c

end CompPoly.RabinCert.Binary
