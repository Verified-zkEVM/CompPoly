/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Extension.Primitive
import CompPoly.Fields.Binary.GF2_72.XPowTwoPowGcdCertificate
import CompPoly.Fields.Binary.GF2_72.PrimitivePowerCertificate
import Mathlib.GroupTheory.OrderOfElement
import CompPoly.Fields.Binary.GF2_72.Impl

/-!
# GF(2^72) Primitive-Order Scaffold

Small primitive-order metadata and Rabin irreducibility certificate for the
`GF(2^72)` candidate.
-/

namespace GF2_72

set_option maxRecDepth 100000

/-- Distinct prime factors of `2^72 - 1`. -/
def primitivePrimeFactors : List Nat :=
  [3, 5, 7, 13, 17, 19, 37, 73, 109, 241, 433, 38737]

/-- Factorization of the multiplicative-group order `2^72 - 1`. -/
lemma multiplicativeGroupOrder_factorization :
    multiplicativeGroupOrder =
      3 ^ 3 * 5 * 7 * 13 * 17 * 19 * 37 * 73 * 109 * 241 * 433 * 38737 := by
  unfold multiplicativeGroupOrder BinaryField.Extension.multiplicativeGroupOrder
    BinaryField.Extension.fieldSize extensionDegree
  norm_num

/-- The GF72 candidate polynomial passes Rabin's irreducibility test. -/
theorem definingPolynomial_irreducible : Irreducible definingPolynomial :=
  BinaryField.Extension.irreducible_of_rabin_72_passed_over_GF2
    definingPolynomial
    (by simpa [extensionDegree] using definingPolynomial_natDegree)
    X_pow_2_pow_72_add_X_dvd
    rabin_gcd_condition_36
    rabin_gcd_condition_24

/-- Register the certified irreducibility fact for quotient-field instances. -/
instance instIrreducibleDefiningPolynomial : Fact (Irreducible definingPolynomial) :=
  ⟨definingPolynomial_irreducible⟩

/-- Local kernel-safe primality certificate for the largest GF72 group-order factor. -/
private theorem prime_38737 : Nat.Prime 38737 := by
  rw [Nat.prime_def_le_sqrt]
  constructor
  · norm_num
  · intro m hm2 hmsqrt hdvd
    have hm_le_sq : m * m ≤ 38737 := (Nat.le_sqrt.mp hmsqrt)
    have hm_le : m ≤ 196 := by
      by_contra h
      have hm197 : 197 ≤ m := by omega
      have hsq : 197 * 197 ≤ m * m := Nat.mul_le_mul hm197 hm197
      omega
    interval_cases m <;> norm_num at hdvd

/-- Prime divisors of `fieldSize - 1` are exactly the certified prime factors. -/
private lemma prime_dvd_fieldSize_sub_one_cases {p : Nat}
    (hp : p.Prime) (hdvd : p ∣ fieldSize - 1) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 37 ∨
      p = 73 ∨ p = 109 ∨ p = 241 ∨ p = 433 ∨ p = 38737 := by
  have hpdvd : p ∣ multiplicativeGroupOrder := by
    simpa [multiplicativeGroupOrder, BinaryField.Extension.multiplicativeGroupOrder] using hdvd
  rw [multiplicativeGroupOrder_factorization] at hpdvd
  rcases hp.dvd_mul.mp hpdvd with hpdvd | h38737
  · rcases hp.dvd_mul.mp hpdvd with hpdvd | h433
    · rcases hp.dvd_mul.mp hpdvd with hpdvd | h241
      · rcases hp.dvd_mul.mp hpdvd with hpdvd | h109
        · rcases hp.dvd_mul.mp hpdvd with hpdvd | h73
          · rcases hp.dvd_mul.mp hpdvd with hpdvd | h37
            · rcases hp.dvd_mul.mp hpdvd with hpdvd | h19
              · rcases hp.dvd_mul.mp hpdvd with hpdvd | h17
                · rcases hp.dvd_mul.mp hpdvd with hpdvd | h13
                  · rcases hp.dvd_mul.mp hpdvd with hpdvd | h7
                    · rcases hp.dvd_mul.mp hpdvd with h3pow | h5
                      · left
                        exact
                          (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp
                            (hp.dvd_of_dvd_pow h3pow)
                      · right
                        left
                        exact
                          (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp
                            h5
                    · right
                      right
                      left
                      exact
                        (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp
                          h7
                  · right
                    right
                    right
                    left
                    exact
                      (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13)).mp
                        h13
                · right
                  right
                  right
                  right
                  left
                  exact
                    (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17)).mp
                      h17
              · right
                right
                right
                right
                right
                left
                exact
                  (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 19)).mp
                    h19
            · right
              right
              right
              right
              right
              right
              left
              exact
                (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 37)).mp
                  h37
          · right
            right
            right
            right
            right
            right
            right
            left
            exact
              (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 73)).mp
                h73
        · right
          right
          right
          right
          right
          right
          right
          right
          left
          exact
            (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 109)).mp
              h109
      · right
        right
        right
        right
        right
        right
        right
        right
        right
        left
        exact
          (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 241)).mp
            h241
    · right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      left
      exact
        (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 433)).mp
          h433
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    exact
      (Nat.prime_dvd_prime_iff_eq hp prime_38737).mp
        h38737

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
      rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · simpa [primitiveRoot] using root_pow_div_3_ne_one
    · simpa [primitiveRoot] using root_pow_div_5_ne_one
    · simpa [primitiveRoot] using root_pow_div_7_ne_one
    · simpa [primitiveRoot] using root_pow_div_13_ne_one
    · simpa [primitiveRoot] using root_pow_div_17_ne_one
    · simpa [primitiveRoot] using root_pow_div_19_ne_one
    · simpa [primitiveRoot] using root_pow_div_37_ne_one
    · simpa [primitiveRoot] using root_pow_div_73_ne_one
    · simpa [primitiveRoot] using root_pow_div_109_ne_one
    · simpa [primitiveRoot] using root_pow_div_241_ne_one
    · simpa [primitiveRoot] using root_pow_div_433_ne_one
    · simpa [primitiveRoot] using root_pow_div_38737_ne_one

end GF2_72
