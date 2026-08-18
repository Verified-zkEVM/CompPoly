/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Data.Polynomial.RabinCertificate
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.NormNum.Prime

/-!
# Rabin-certificate framework tests

End-to-end exercise of `CompPoly/Data/Polynomial/RabinCertificate.lean` at a size where the
certificate can be checked by hand: `X^2 + X + 1` is irreducible over `ZMod 5` (it has no
roots: squares mod 5 are `{0, 1, 4}` and `x^2 + x + 1` hits `1, 3, 2, 3, 1`). The certificate
data below is what `scripts/gen_rabin_certificate.py --p 5 --f "1,1,1"` emits.

This keeps the framework honest independently of the (much larger) KoalaBear quintic
certificate in `CompPoly/Fields/KoalaBear/Ext5/QuinticCertData.lean`.
-/

@[expose] public section

namespace CompPolyTests.RabinCertificate

open Polynomial CompPoly.RabinCert

abbrev P : ℕ := 5

instance : Fact (Nat.Prime P) := ⟨by norm_num⟩

def fL : List ℕ := [1, 1, 1]

noncomputable def fPoly : (ZMod P)[X] := X ^ 2 + X + C 1

theorem toPoly_fL : toPoly P fL = fPoly := by
  show toPoly P [1, 1, 1] = fPoly
  rw [fPoly, toPoly_cons, toPoly_cons, toPoly_cons, toPoly_nil, Nat.cast_one, map_one]
  ring

theorem fPoly_natDegree : fPoly.natDegree = 2 := by
  rw [fPoly]
  compute_degree!

theorem fPoly_ne_zero : fPoly ≠ 0 := by
  intro h
  have h2 := fPoly_natDegree
  rw [h, natDegree_zero] at h2
  exact absurd h2 (by norm_num)

/-- Chain for `X^(5^2) mod f`: `25 = 11001₂`. -/
def traceSteps : List Step := [
  ⟨false, [1], [4, 4]⟩,
  ⟨true, [4], [1]⟩,
  ⟨false, [0], [1]⟩,
  ⟨false, [0], [1]⟩,
  ⟨false, [0], [1]⟩,
  ⟨true, [0], [0, 1]⟩]

/-- Chain for `X^5 mod f`: `5 = 101₂`. -/
def frobSteps : List Step := [
  ⟨false, [1], [4, 4]⟩,
  ⟨false, [1], [0, 1]⟩,
  ⟨true, [1], [4, 4]⟩]

def w : List ℕ := [4, 3]
def u : List ℕ := [3]
def v : List ℕ := [2, 4]

-- The kernel checks: a whole chain per reduction.
theorem trace_chain : runChain P fL [0, 1] traceSteps = some [0, 1] := by rfl
theorem trace_exp : chainExp 1 traceSteps = P ^ 2 := by rfl
theorem frob_chain : runChain P fL [0, 1] frobSteps = some [4, 4] := by rfl
theorem frob_exp : chainExp 1 frobSteps = P := by rfl
theorem w_check : eqModP P [4, 4] (addNat w [0, 1]) = true := by rfl
theorem bez_check : eqModP P (addNat (mulNat u fL) (mulNat v w)) [1] = true := by rfl

-- A corrupted step is rejected: the last remainder should be `[0, 1]`, not `[1, 1]`.
theorem corrupted_chain_rejected :
    runChain P fL [0, 1] (traceSteps.dropLast ++ [⟨true, [0], [1, 1]⟩]) = none := by rfl

-- The assembled irreducibility proof, entirely from the certificate.
theorem fPoly_irreducible : Irreducible fPoly := by
  have hcard : Fintype.card (ZMod P) = P := ZMod.card P
  refine irreducible_of_rabin_prime_degree (by norm_num) fPoly_natDegree ?_ ?_
  · rw [hcard]
    exact dvd_X_pow_sub_X_of_runChain toPoly_fL fPoly_ne_zero trace_chain trace_exp
  · rw [hcard]
    exact isCoprime_X_pow_sub_X_of_runChain toPoly_fL fPoly_ne_zero frob_chain frob_exp
      w_check bez_check

/-! ### Composite degree

At composite `d` the coprimality condition must be checked once per prime factor of `d`, and the
prime-degree collapse to "no linear factors" is *unsound*. Both halves are exercised here at
`d = 6` over `ZMod 5`, where the chains are still short enough to eyeball.

The polynomial is `X^6 + X^3 + 1 = Φ₉`, irreducible over `F_5` because `5` has multiplicative
order 6 modulo 9 — the same reason it is irreducible over KoalaBear.
-/

namespace Sextic

def fL6 : List ℕ := [1, 0, 0, 1, 0, 0, 1]

noncomputable def f6 : (ZMod P)[X] := X ^ 6 + X ^ 3 + C 1

theorem toPoly_fL6 : toPoly P fL6 = f6 := by
  show toPoly P [1, 0, 0, 1, 0, 0, 1] = f6
  rw [f6, toPoly_cons, toPoly_cons, toPoly_cons, toPoly_cons, toPoly_cons, toPoly_cons,
    toPoly_cons, toPoly_nil, Nat.cast_zero, Nat.cast_one, map_zero, map_one]
  ring

theorem f6_natDegree : f6.natDegree = 6 := by
  rw [f6]
  compute_degree!

theorem f6_ne_zero : f6 ≠ 0 := by
  intro h
  have h6 := f6_natDegree
  rw [h, natDegree_zero] at h6
  exact absurd h6 (by norm_num)

/-- Chain for `X^(5^6) mod f`: `15625` in binary. -/
def traceSteps6 : List Step := [
  ⟨false, [0], [0, 0, 1]⟩,
  ⟨true, [0], [0, 0, 0, 1]⟩,
  ⟨false, [1], [4, 0, 0, 4]⟩,
  ⟨true, [0], [0, 4, 0, 0, 4]⟩,
  ⟨false, [0, 0, 1], [0, 0, 0, 0, 0, 1]⟩,
  ⟨true, [1], [4, 0, 0, 4]⟩,
  ⟨false, [1], [0, 0, 0, 1]⟩,
  ⟨false, [1], [4, 0, 0, 4]⟩,
  ⟨true, [0], [0, 4, 0, 0, 4]⟩,
  ⟨false, [0, 0, 1], [0, 0, 0, 0, 0, 1]⟩,
  ⟨false, [0, 4, 0, 0, 1], [0, 1]⟩,
  ⟨false, [0], [0, 0, 1]⟩,
  ⟨false, [0], [0, 0, 0, 0, 1]⟩,
  ⟨false, [0, 0, 1], [0, 0, 4, 0, 0, 4]⟩,
  ⟨true, [4], [1]⟩,
  ⟨false, [0], [1]⟩,
  ⟨false, [0], [1]⟩,
  ⟨false, [0], [1]⟩,
  ⟨true, [0], [0, 1]⟩]

/-- Chain for `X^(5^3) mod f`, the check for the prime factor `2` of `6`. -/
def cop3Steps : List Step := [
  ⟨false, [0], [0, 0, 1]⟩,
  ⟨true, [0], [0, 0, 0, 1]⟩,
  ⟨false, [1], [4, 0, 0, 4]⟩,
  ⟨true, [0], [0, 4, 0, 0, 4]⟩,
  ⟨false, [0, 0, 1], [0, 0, 0, 0, 0, 1]⟩,
  ⟨true, [1], [4, 0, 0, 4]⟩,
  ⟨false, [1], [0, 0, 0, 1]⟩,
  ⟨true, [0], [0, 0, 0, 0, 1]⟩,
  ⟨false, [0, 0, 1], [0, 0, 4, 0, 0, 4]⟩,
  ⟨false, [0, 1, 0, 0, 1], [0, 4, 0, 0, 4]⟩,
  ⟨true, [0], [0, 0, 4, 0, 0, 4]⟩]

def cop3Rp : List ℕ := [0, 0, 4, 0, 0, 4]
def cop3W : List ℕ := [0, 4, 4, 0, 0, 4]
def cop3U : List ℕ := [1, 2, 4, 3, 4]
def cop3V : List ℕ := [2, 2, 2, 4, 3, 4]

/-- Chain for `X^(5^2) mod f`, the check for the prime factor `3` of `6`. -/
def cop2Steps : List Step := [
  ⟨false, [0], [0, 0, 1]⟩,
  ⟨true, [0], [0, 0, 0, 1]⟩,
  ⟨false, [1], [4, 0, 0, 4]⟩,
  ⟨false, [1], [0, 0, 0, 1]⟩,
  ⟨false, [1], [4, 0, 0, 4]⟩,
  ⟨true, [0], [0, 4, 0, 0, 4]⟩]

def cop2Rp : List ℕ := [0, 4, 0, 0, 4]
def cop2W : List ℕ := [0, 3, 0, 0, 4]
def cop2U : List ℕ := [1, 0, 0, 2]
def cop2V : List ℕ := [0, 0, 4, 0, 0, 2]

theorem trace6_chain : runChain P fL6 [0, 1] traceSteps6 = some [0, 1] := by rfl
theorem trace6_exp : chainExp 1 traceSteps6 = P ^ 6 := by rfl
theorem cop3_chain : runChain P fL6 [0, 1] cop3Steps = some cop3Rp := by rfl
theorem cop3_exp : chainExp 1 cop3Steps = P ^ 3 := by rfl
theorem cop3_w : eqModP P cop3Rp (addNat cop3W [0, 1]) = true := by rfl
theorem cop3_bez : eqModP P (addNat (mulNat cop3U fL6) (mulNat cop3V cop3W)) [1] = true := by rfl
theorem cop2_chain : runChain P fL6 [0, 1] cop2Steps = some cop2Rp := by rfl
theorem cop2_exp : chainExp 1 cop2Steps = P ^ 2 := by rfl
theorem cop2_w : eqModP P cop2Rp (addNat cop2W [0, 1]) = true := by rfl
theorem cop2_bez : eqModP P (addNat (mulNat cop2U fL6) (mulNat cop2V cop2W)) [1] = true := by rfl

/-- The assembled degree-6 irreducibility proof, entirely from certificates. -/
theorem f6_irreducible : Irreducible f6 := by
  have hcard : Fintype.card (ZMod P) = P := ZMod.card P
  refine irreducible_of_rabin_degree_six f6_natDegree ?_ ?_ ?_
  · rw [hcard]
    exact dvd_X_pow_sub_X_of_runChain toPoly_fL6 f6_ne_zero trace6_chain trace6_exp
  · rw [hcard]
    exact isCoprime_X_pow_sub_X_of_runChain toPoly_fL6 f6_ne_zero cop3_chain cop3_exp cop3_w
      cop3_bez
  · rw [hcard]
    exact isCoprime_X_pow_sub_X_of_runChain toPoly_fL6 f6_ne_zero cop2_chain cop2_exp cop2_w
      cop2_bez

end Sextic

/-! ### Why the per-prime-factor checks are not optional

`fRed = (X^3 + X^2 + 1)(X^3 + 2X^2 + 1)` over `ZMod 5` is visibly reducible, yet it divides
`X^(5^6) - X` (all its roots lie in `F_(5^6)`) and is coprime to `X^5 - X` (it has no root in
`F_5`). So it satisfies the *prime-degree* form of Rabin's test verbatim. The theorem below is the
certified witness of what actually rules it out: `X^(5^3) ≡ X (mod fRed)`, so `fRed` shares a
factor with `X^(5^3) - X` and the `ℓ = 2` coprimality check fails.

This is the regression guard for the bug that `irreducible_of_rabin_degree_six` and the
per-prime-factor loop in `scripts/gen_rabin_certificate.py` exist to prevent.
-/

namespace ReducibleSextic

def fRedL : List ℕ := [1, 3, 2, 2, 3, 0, 1]

noncomputable def fRed : (ZMod P)[X] :=
  X ^ 6 + C 3 * X ^ 4 + C 2 * X ^ 3 + C 2 * X ^ 2 + C 3 * X + C 1

theorem toPoly_fRedL : toPoly P fRedL = fRed := by
  show toPoly P [1, 3, 2, 2, 3, 0, 1] = fRed
  rw [fRed, toPoly_cons, toPoly_cons, toPoly_cons, toPoly_cons, toPoly_cons, toPoly_cons,
    toPoly_cons, toPoly_nil]
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, map_zero, map_one]
  ring

theorem fRed_natDegree : fRed.natDegree = 6 := by
  rw [fRed]
  compute_degree!

theorem fRed_ne_zero : fRed ≠ 0 := by
  intro h
  have h6 := fRed_natDegree
  rw [h, natDegree_zero] at h6
  exact absurd h6 (by norm_num)

/-- Chain for `X^(5^3) mod fRed`. Unlike the irreducible case it ends back at `X`. -/
def cop3Steps : List Step := [
  ⟨false, [0], [0, 0, 1]⟩,
  ⟨true, [0], [0, 0, 0, 1]⟩,
  ⟨false, [1], [4, 2, 3, 3, 2]⟩,
  ⟨true, [0], [0, 4, 2, 3, 3, 2]⟩,
  ⟨false, [3, 2, 4, 2, 4], [2, 4, 0, 2, 2, 1]⟩,
  ⟨true, [1], [4, 4, 2, 3, 4, 2]⟩,
  ⟨false, [3, 1, 1, 1, 4], [3, 2, 2, 3, 0, 1]⟩,
  ⟨true, [1], [4]⟩,
  ⟨false, [0], [1]⟩,
  ⟨false, [0], [1]⟩,
  ⟨true, [0], [0, 1]⟩]

theorem cop3_chain : runChain P fRedL [0, 1] cop3Steps = some [0, 1] := by rfl
theorem cop3_exp : chainExp 1 cop3Steps = P ^ 3 := by rfl

/-- `fRed ∣ X^(5^3) - X`: its irreducible factors have degree 3, not 6. -/
theorem dvd_X_pow_sub_X : fRed ∣ (X : (ZMod P)[X]) ^ (P ^ 3) - X :=
  dvd_X_pow_sub_X_of_runChain toPoly_fRedL fRed_ne_zero cop3_chain cop3_exp

/-- Hence the `ℓ = 2` coprimality hypothesis of `irreducible_of_rabin_degree_six` genuinely fails
for `fRed`, so the wrapper cannot be applied to it. -/
theorem not_isCoprime : ¬ IsCoprime fRed ((X : (ZMod P)[X]) ^ (P ^ 3) - X) := by
  intro h
  have hunit : IsUnit fRed := h.isUnit_of_dvd' dvd_rfl dvd_X_pow_sub_X
  have h0 : fRed.natDegree = 0 := natDegree_eq_zero_of_isUnit hunit
  rw [fRed_natDegree] at h0
  exact absurd h0 (by norm_num)

end ReducibleSextic

/-! ### The `_of_card` forms are equivalent to the plain ones

`irreducible_of_rabin_prime_degree_of_card` and `irreducible_of_rabin_degree_six_of_card` state
their conditions at a caller-supplied numeral `q` with `hcard : Fintype.card F = q`, which is the
shape concrete extensions use. Their docstrings claim nothing is weakened; the two theorems below
are that claim, machine-checked. Instantiating at `q := Fintype.card F` with `rfl` has to recover
the plain form *verbatim*, so a future edit cannot silently add a hypothesis or shift an exponent.
The opposite direction is the `_of_card` proof body itself, checked whenever the library builds.
-/

namespace OfCardRoundTrip

/-- `irreducible_of_rabin_prime_degree_of_card` recovers `irreducible_of_rabin_prime_degree`. -/
theorem prime_degree_recovered {F : Type*} [Field F] [Fintype F] {f : F[X]} {d : ℕ}
    (hd : d.Prime) (h_deg : f.natDegree = d)
    (h_trace : f ∣ X ^ (Fintype.card F ^ d) - X)
    (h_cop : IsCoprime f (X ^ Fintype.card F - X)) :
    Irreducible f :=
  irreducible_of_rabin_prime_degree_of_card rfl hd h_deg h_trace h_cop

/-- `irreducible_of_rabin_degree_six_of_card` recovers `irreducible_of_rabin_degree_six`. -/
theorem degree_six_recovered {F : Type*} [Field F] [Fintype F] {f : F[X]}
    (h_deg : f.natDegree = 6)
    (h_trace : f ∣ X ^ (Fintype.card F ^ 6) - X)
    (h_cop₃ : IsCoprime f (X ^ (Fintype.card F ^ 3) - X))
    (h_cop₂ : IsCoprime f (X ^ (Fintype.card F ^ 2) - X)) :
    Irreducible f :=
  irreducible_of_rabin_degree_six_of_card rfl h_deg h_trace h_cop₃ h_cop₂

end OfCardRoundTrip

end CompPolyTests.RabinCertificate
