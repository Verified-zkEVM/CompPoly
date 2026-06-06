/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Extension.Prelude
import Mathlib.Tactic.ComputeDegree

/-!
# GF(2^48) Prelude

Defining constants and small executable metadata for the direct binary extension
with candidate primitive polynomial

`X^48 + X^9 + X^7 + X^4 + 1`.

Irreducibility and primitive-order certificates are added in later `GF2_48`
modules before this polynomial is used to construct public field instances.
-/

namespace GF2_48

open Polynomial

noncomputable section

/-- Extension degree for `GF(2^48)`. -/
def extensionDegree : Nat :=
  48

/-- Raw executable carrier width for `GF(2^48)`. -/
abbrev B48 : Type :=
  BitVec extensionDegree

/-- Field cardinality of `GF(2^48)`. -/
def fieldSize : Nat :=
  BinaryField.Extension.fieldSize extensionDegree

/-- Multiplicative group order of `GF(2^48)`. -/
def multiplicativeGroupOrder : Nat :=
  BinaryField.Extension.multiplicativeGroupOrder extensionDegree

/-- Low-degree tail `X^9 + X^7 + X^4 + 1`. -/
def definingTail : Polynomial (ZMod 2) :=
  X ^ 9 + X ^ 7 + X ^ 4 + 1

/-- Candidate primitive polynomial bitmask: `X^48 + X^9 + X^7 + X^4 + 1`. -/
def definingBitmask : Nat :=
  0x1000000000291

/-- Exponents with nonzero coefficients in the full defining polynomial. -/
def definingPolynomialExponents : List Nat :=
  [0, 4, 7, 9, 48]

/-- The tail has natural degree `9`. -/
lemma definingTail_natDegree :
    definingTail.natDegree = 9 := by
  unfold definingTail
  compute_degree!

/-- The tail is monic. -/
lemma definingTail_monic :
    definingTail.Monic := by
  unfold definingTail
  monicity!

/-- Metadata for the direct binary extension polynomial. -/
def definingPolynomialData : BinaryField.Extension.DefiningPolynomialData where
  degree := extensionDegree
  tail := definingTail
  tailDegree := 9
  bitmask := definingBitmask
  tail_natDegree := definingTail_natDegree
  tailDegree_lt_degree := by
    unfold extensionDegree
    omega

/-- Candidate defining polynomial for `GF(2^48)`. -/
def definingPolynomial : Polynomial (ZMod 2) :=
  BinaryField.Extension.polynomial definingPolynomialData

/-- Expanded form of the candidate defining polynomial. -/
lemma definingPolynomial_eq_X_pow_add_tail :
    definingPolynomial = X ^ 48 + definingTail := by
  rfl

/-- Expanded sparse form of the candidate defining polynomial. -/
lemma definingPolynomial_eq_sparse :
    definingPolynomial = X ^ 48 + X ^ 9 + X ^ 7 + X ^ 4 + 1 := by
  unfold definingPolynomial BinaryField.Extension.polynomial definingPolynomialData definingTail
    extensionDegree
  ring

/-- The candidate defining polynomial is monic of degree `48`. -/
lemma definingPolynomial_isMonicOfDegree :
    IsMonicOfDegree definingPolynomial extensionDegree :=
  BinaryField.Extension.polynomial_isMonicOfDegree definingPolynomialData

/-- The candidate defining polynomial has natural degree `48`. -/
lemma definingPolynomial_natDegree :
    definingPolynomial.natDegree = extensionDegree :=
  BinaryField.Extension.polynomial_natDegree definingPolynomialData

/-- The candidate defining polynomial is monic. -/
lemma definingPolynomial_monic :
    definingPolynomial.Monic :=
  BinaryField.Extension.polynomial_monic definingPolynomialData

/-- The candidate defining polynomial is nonzero. -/
lemma definingPolynomial_ne_zero :
    definingPolynomial ≠ 0 :=
  BinaryField.Extension.polynomial_ne_zero definingPolynomialData

/-- The candidate defining polynomial has degree `48`. -/
lemma definingPolynomial_degree :
    definingPolynomial.degree = extensionDegree :=
  BinaryField.Extension.polynomial_degree definingPolynomialData

/-- Bit-vector encoding of the candidate defining polynomial. -/
def P_val : BitVec (2 * extensionDegree) :=
  (1 <<< 48) ^^^ (1 <<< 9) ^^^ (1 <<< 7) ^^^ (1 <<< 4) ^^^ 1

/-- The `BitVec` encoding denotes the candidate defining polynomial. -/
lemma definingPolynomial_eq_P_val :
    definingPolynomial = BinaryField.toPoly P_val := by
  rw [definingPolynomial_eq_sparse]
  unfold P_val extensionDegree
  repeat rw [BinaryField.toPoly_xor]
  rw [BinaryField.Extension.toPoly_one_shiftLeft 48 (by omega)]
  rw [BinaryField.Extension.toPoly_one_shiftLeft 9 (by omega)]
  rw [BinaryField.Extension.toPoly_one_shiftLeft 7 (by omega)]
  rw [BinaryField.Extension.toPoly_one_shiftLeft 4 (by omega)]
  rw [(show (1 : BitVec 96) = 1 <<< 0 by simp)]
  rw [BinaryField.Extension.toPoly_one_shiftLeft 0 (by omega)]
  simp only [pow_zero]

/-- The exponent list denotes the candidate defining polynomial. -/
lemma sparsePolynomial_definingPolynomialExponents :
    BinaryField.Extension.sparsePolynomial definingPolynomialExponents = definingPolynomial := by
  rw [definingPolynomial_eq_sparse]
  simp [definingPolynomialExponents, BinaryField.Extension.sparsePolynomial]
  ring_nf

/-- Smooth subgroup refinement schedule for `2^48 - 1`. -/
def smoothRootSchedule : Array Nat :=
  #[3, 3, 5, 7, 13, 17, 97, 241, 257, 673]

/-- The GF48 smooth schedule refines the multiplicative group down to singleton cosets. -/
lemma smoothRootSchedule_fold_eq_one :
    smoothRootSchedule.toList.foldl (fun order ell ↦ order / ell)
      (fieldSize - 1) = 1 := by
  unfold smoothRootSchedule fieldSize BinaryField.Extension.fieldSize extensionDegree
  decide

end

end GF2_48
