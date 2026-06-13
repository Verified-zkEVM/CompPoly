/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Extension.Primitive
import CompPoly.Fields.Binary.GF2_64.XPowTwoPowGcdCertificate
import CompPoly.Fields.Binary.GF2_64.PrimitivePowerCertificate
import Mathlib.GroupTheory.OrderOfElement
import CompPoly.Fields.Binary.GF2_64.Impl

/-!
# GF(2^64) Primitive-Order Scaffold

Small primitive-order metadata and Rabin irreducibility certificate for the
`GF(2^64)` candidate.
-/

namespace GF2_64

set_option maxRecDepth 100000

/-- Distinct prime factors of `2^64 - 1`. -/
def primitivePrimeFactors : List Nat :=
  [3, 5, 17, 257, 641, 65537, 6700417]

/-- Factorization of the multiplicative-group order `2^64 - 1`. -/
lemma multiplicativeGroupOrder_factorization :
    multiplicativeGroupOrder = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417 := by
  unfold multiplicativeGroupOrder BinaryField.Extension.multiplicativeGroupOrder
    BinaryField.Extension.fieldSize extensionDegree
  norm_num

/-- The GF2_64 candidate polynomial passes Rabin's irreducibility test. -/
theorem definingPolynomial_irreducible : Irreducible definingPolynomial :=
  BinaryField.Extension.irreducible_of_rabin_64_passed_over_GF2
    definingPolynomial
    (by simpa [extensionDegree] using definingPolynomial_natDegree)
    X_pow_2_pow_64_add_X_dvd
    rabin_gcd_condition_32

/-- Register the certified irreducibility fact for quotient-field instances. -/
instance instIrreducibleDefiningPolynomial : Fact (Irreducible definingPolynomial) :=
  ⟨definingPolynomial_irreducible⟩

/-- Local kernel-safe primality certificate for the `65537` group-order factor. -/
private theorem prime_65537 : Nat.Prime 65537 := by
  rw [Nat.prime_def_le_sqrt]
  constructor
  · norm_num
  · intro m hm2 hmsqrt hdvd
    have hm_le_sq : m * m ≤ 65537 := (Nat.le_sqrt.mp hmsqrt)
    have hm_le : m ≤ 256 := by
      by_contra h
      have hm257 : 257 ≤ m := by omega
      have hsq : 257 * 257 ≤ m * m := Nat.mul_le_mul hm257 hm257
      omega
    interval_cases m <;> norm_num at hdvd

/-- Local kernel-safe primality certificate for the largest GF64 group-order factor. -/
private theorem prime_6700417 : Nat.Prime 6700417 := by
  rw [Nat.prime_def_le_sqrt]
  constructor
  · norm_num
  · intro m hm2 hmsqrt hdvd
    have hm_le_sq : m * m ≤ 6700417 := (Nat.le_sqrt.mp hmsqrt)
    have hm_le : m ≤ 2588 := by
      by_contra h
      have hm2589 : 2589 ≤ m := by omega
      have hsq : 2589 * 2589 ≤ m * m := Nat.mul_le_mul hm2589 hm2589
      omega
    interval_cases m <;> norm_num at hdvd

/-- Prime divisors of `fieldSize - 1` are exactly the certified prime factors. -/
private lemma prime_dvd_fieldSize_sub_one_cases {p : Nat}
    (hp : p.Prime) (hdvd : p ∣ fieldSize - 1) :
    p = 3 ∨ p = 5 ∨ p = 17 ∨ p = 257 ∨ p = 641 ∨ p = 65537 ∨ p = 6700417 := by
  have hpdvd : p ∣ multiplicativeGroupOrder := by
    simpa [multiplicativeGroupOrder, BinaryField.Extension.multiplicativeGroupOrder] using hdvd
  rw [multiplicativeGroupOrder_factorization] at hpdvd
  rcases hp.dvd_mul.mp hpdvd with hpdvd | h6700417
  · rcases hp.dvd_mul.mp hpdvd with hpdvd | h65537
    · rcases hp.dvd_mul.mp hpdvd with hpdvd | h641
      · rcases hp.dvd_mul.mp hpdvd with hpdvd | h257
        · rcases hp.dvd_mul.mp hpdvd with hpdvd | h17
          · rcases hp.dvd_mul.mp hpdvd with h3 | h5
            · left
              exact
                  (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp
                    h3
            · right
              left
              exact
                  (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp
                    h5
          · right
            right
            left
            exact
                (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17)).mp
                  h17
        · right
          right
          right
          left
          exact
              (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 257)).mp
                h257
      · right
        right
        right
        right
        left
        exact
            (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 641)).mp
              h641
    · right
      right
      right
      right
      right
      left
      exact
          (Nat.prime_dvd_prime_iff_eq hp prime_65537).mp
            h65537
  · right
    right
    right
    right
    right
    right
    exact
      (Nat.prime_dvd_prime_iff_eq hp prime_6700417).mp
        h6700417

/-- Polynomial-basis generator used by smooth root contexts. -/
def primitiveRoot : ConcreteField :=
  ConcreteField.root

/-- The polynomial-basis generator is nonzero. -/
theorem primitiveRoot_ne_zero : primitiveRoot ≠ (0 : ConcreteField) := by
  unfold primitiveRoot ConcreteField.root BinaryField.Extension.Concrete.root
  change BinaryField.Extension.Concrete.ofNat Concrete.params 2 ≠
    BinaryField.Extension.Concrete.zero Concrete.params
  intro h
  have hnat := congrArg (BinaryField.Extension.Concrete.toNat Concrete.params) h
  rw [BinaryField.Extension.Concrete.toNat_ofNat_of_lt Concrete.params
    (by unfold Concrete.params extensionDegree; norm_num)] at hnat
  have hzero :
      BinaryField.Extension.Concrete.toNat Concrete.params
        (BinaryField.Extension.Concrete.zero Concrete.params) = 0 := by
    unfold BinaryField.Extension.Concrete.zero
    exact BinaryField.Extension.Concrete.toNat_ofNat_of_lt Concrete.params
      (n := 0) (by unfold Concrete.params extensionDegree; norm_num)
  rw [hzero] at hnat
  norm_num at hnat

/-- The polynomial-basis generator has full multiplicative order. -/
theorem primitiveRoot_order : orderOf primitiveRoot = fieldSize - 1 := by
  let fieldInst : Field ConcreteField := ConcreteField.instFieldConcreteField
  letI : Field ConcreteField := fieldInst
  refine orderOf_eq_of_pow_and_pow_div_prime (n := fieldSize - 1) ?_ ?_ ?_
  · unfold fieldSize BinaryField.Extension.fieldSize extensionDegree
    norm_num
  · have hcard : Fintype.card ConcreteField = fieldSize := by
      simpa [fieldSize] using ConcreteField.card
    have hfermat := FiniteField.pow_card_sub_one_eq_one
      (K := ConcreteField) primitiveRoot primitiveRoot_ne_zero
    simpa [hcard] using hfermat
  · intro p hp hdvd
    rcases prime_dvd_fieldSize_sub_one_cases hp hdvd with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [primitiveRoot] using root_pow_div_3_ne_one
    · simpa [primitiveRoot] using root_pow_div_5_ne_one
    · simpa [primitiveRoot] using root_pow_div_17_ne_one
    · simpa [primitiveRoot] using root_pow_div_257_ne_one
    · simpa [primitiveRoot] using root_pow_div_641_ne_one
    · simpa [primitiveRoot] using root_pow_div_65537_ne_one
    · simpa [primitiveRoot] using root_pow_div_6700417_ne_one

end GF2_64
