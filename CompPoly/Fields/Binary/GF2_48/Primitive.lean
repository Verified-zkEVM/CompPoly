/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Extension.Primitive
import CompPoly.Fields.Binary.GF2_48.XPowTwoPowGcdCertificate
import CompPoly.Fields.Binary.GF2_48.PrimitivePowerCertificate
import Mathlib.GroupTheory.OrderOfElement
import CompPoly.Fields.Binary.GF2_48.Impl

/-!
# GF(2^48) Primitive-Order Scaffold

Small primitive-order metadata and Rabin irreducibility certificate for the
`GF(2^48)` candidate.
-/

namespace GF2_48

set_option maxRecDepth 20000

/-- Distinct prime factors of `2^48 - 1`. -/
def primitivePrimeFactors : List Nat :=
  [3, 5, 7, 13, 17, 97, 241, 257, 673]

/-- Factorization of the multiplicative-group order `2^48 - 1`. -/
lemma multiplicativeGroupOrder_factorization :
    multiplicativeGroupOrder = 3 ^ 2 * 5 * 7 * 13 * 17 * 97 * 241 * 257 * 673 := by
  unfold multiplicativeGroupOrder BinaryField.Extension.multiplicativeGroupOrder
    BinaryField.Extension.fieldSize extensionDegree
  norm_num

/-- The GF48 candidate polynomial passes Rabin's irreducibility test. -/
theorem definingPolynomial_irreducible : Irreducible definingPolynomial :=
  BinaryField.Extension.irreducible_of_rabin_48_passed_over_GF2
    definingPolynomial
    (by simpa [extensionDegree] using definingPolynomial_natDegree)
    X_pow_2_pow_48_add_X_dvd
    rabin_gcd_condition_24
    rabin_gcd_condition_16

/-- Register the certified irreducibility fact for quotient-field instances. -/
instance instIrreducibleDefiningPolynomial : Fact (Irreducible definingPolynomial) :=
  ⟨definingPolynomial_irreducible⟩

/-- Prime divisors of `fieldSize - 1` are exactly the certified prime factors. -/
private lemma prime_dvd_fieldSize_sub_one_cases {p : Nat}
    (hp : p.Prime) (hdvd : p ∣ fieldSize - 1) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 17 ∨ p = 97 ∨ p = 241 ∨ p = 257 ∨ p = 673 := by
  have hpdvd : p ∣ multiplicativeGroupOrder := by
    simpa [multiplicativeGroupOrder, BinaryField.Extension.multiplicativeGroupOrder] using hdvd
  rw [multiplicativeGroupOrder_factorization] at hpdvd
  rcases hp.dvd_mul.mp hpdvd with hpdvd | h673
  · rcases hp.dvd_mul.mp hpdvd with hpdvd | h257
    · rcases hp.dvd_mul.mp hpdvd with hpdvd | h241
      · rcases hp.dvd_mul.mp hpdvd with hpdvd | h97
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
            (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 97)).mp
              h97
      · right
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
      left
      exact
        (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 257)).mp
          h257
  · right
    right
    right
    right
    right
    right
    right
    right
    exact
      (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 673)).mp
        h673

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
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [primitiveRoot] using root_pow_div_3_ne_one
    · simpa [primitiveRoot] using root_pow_div_5_ne_one
    · simpa [primitiveRoot] using root_pow_div_7_ne_one
    · simpa [primitiveRoot] using root_pow_div_13_ne_one
    · simpa [primitiveRoot] using root_pow_div_17_ne_one
    · simpa [primitiveRoot] using root_pow_div_97_ne_one
    · simpa [primitiveRoot] using root_pow_div_241_ne_one
    · simpa [primitiveRoot] using root_pow_div_257_ne_one
    · simpa [primitiveRoot] using root_pow_div_673_ne_one

end GF2_48
