/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.Aes.Arithmetic
public import CompPoly.Fields.Binary.Aes.Certificate
public import CompPoly.Fields.Extension.Field
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.ComputeDegree

/-!
# The certified AES polynomial field

The degree-eight modulus `X^8 + X^4 + X^3 + X + 1` is irreducible over `GF(2)`.
Rabin's general criterion uses eight Frobenius squarings and the coprimality condition
at `X^16 - X`, since two is the sole prime divisor of eight. The existing kernel-checked
certificate API verifies those conditions; generated data lives in `Aes.Certificate`.

The monic-extension framework supplies executable field operations and the quotient bridge
for the nominal `AesField` carrier. Its byte coordinates and raw arithmetic can be imported
separately from `Aes.Arithmetic`. Field numerals are characteristic-two sums of ones, whereas
`ofBitVec` explicitly interprets the eight polynomial coefficients of a byte.

## References

* NIST, *Advanced Encryption Standard (AES)*, FIPS 197, updated May 9, 2023, Section 4.
  https://doi.org/10.6028/NIST.FIPS.197-upd1
-/

@[expose] public section

namespace AesField

open Polynomial CompPoly.Extension CompPoly.RabinCert Certificate

/-- The AES defining polynomial over `GF(2)`. -/
noncomputable def modulus : Polynomial (ZMod 2) := X ^ 8 + X ^ 4 + X ^ 3 + X + 1

/-- The defining polynomial has degree eight. -/
theorem modulus_natDegree : modulus.natDegree = 8 := by
  rw [modulus]
  compute_degree!

/-- The defining polynomial is nonzero. -/
theorem modulus_ne_zero : modulus ≠ 0 := by
  intro h
  have hd := modulus_natDegree
  rw [h, natDegree_zero] at hd
  exact Nat.zero_ne_add_one 7 hd

/-- The extension's lower coefficient vector encodes exactly the AES defining polynomial. -/
theorem params_poly : params.poly = modulus := by
  change (X : (ZMod 2)[X]) ^ 8 +
    (∑ i : Fin 8, C ((#v[1, 1, 0, 1, 1, 0, 0, 0] : Vector (ZMod 2) 8)[i.val]) * X ^ (i : ℕ)) =
      X ^ 8 + X ^ 4 + X ^ 3 + X + 1
  norm_num [Fin.sum_univ_succ]
  ring

private def modulusCoeffs : List ℕ := [1, 1, 0, 1, 1, 0, 0, 0, 1]

private theorem toPoly_modulusCoeffs : toPoly 2 modulusCoeffs = modulus := by
  simp only [modulusCoeffs, toPoly_cons, toPoly_nil, Nat.cast_zero, Nat.cast_one,
    map_zero, map_one, modulus]
  ring

private theorem primeFactors_eight : (8 : ℕ).primeFactors = {2} := by
  rw [show (8 : ℕ) = 2 ^ 3 from rfl, Nat.primeFactors_prime_pow (by decide) Nat.prime_two]

/-- The AES defining polynomial is irreducible over `GF(2)`. -/
theorem modulus_irreducible : Irreducible modulus := by
  refine Polynomial.irreducible_of_rabin (d := 8) modulus_natDegree (by decide) ?_ ?_
  · rw [ZMod.card]
    exact dvd_X_pow_sub_X_of_runChain (steps := traceSteps) toPoly_modulusCoeffs modulus_ne_zero
      (by rfl) (by rfl)
  · intro ℓ hℓ
    rw [primeFactors_eight, Finset.mem_singleton] at hℓ
    subst ℓ
    rw [ZMod.card]
    exact isCoprime_X_pow_sub_X_of_runChain (steps := cop4Steps) (rp := cop4Rp)
      (w := cop4W) (u := cop4U) (v := cop4V) toPoly_modulusCoeffs modulus_ne_zero
      (by rfl) (by rfl) (by rfl) (by rfl)

instance : Fact (Irreducible params.poly) := ⟨params_poly ▸ modulus_irreducible⟩

instance : Fact (Nat.card (ZMod 2) = params.q) := by
  constructor
  rw [Nat.card_eq_fintype_card, ZMod.card]
  rfl

/-- The AES field has characteristic two. -/
instance : CharP AesField 2 := charP_of_injective_algebraMap' (ZMod 2) 2

/-- The AES field has exactly 256 elements, without choosing an enumeration. -/
theorem nat_card : Nat.card AesField = 256 := by
  rw [Ext.nat_card_ext]
  rfl

/-- The polynomial generator is a root of the AES modulus. -/
theorem aeval_gen : aeval gen modulus = 0 := by
  rw [← params_poly]
  exact Ext.aeval_gen_poly

/-- The field is isomorphic to the quotient by its certified defining polynomial. -/
noncomputable def ringEquivQuot : AesField ≃+* AdjoinRoot params.poly := Ext.ringEquivQuot params

end AesField
