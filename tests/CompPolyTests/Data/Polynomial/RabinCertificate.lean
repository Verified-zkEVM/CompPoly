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

end CompPolyTests.RabinCertificate
