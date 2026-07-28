/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Extension.Prelude
import Mathlib.Tactic.ComputeDegree

/-!
# GF(2^72) Prelude

Defining constants and small executable metadata for the direct binary extension
with candidate primitive polynomial

`X^72 + X^6 + X^4 + X^3 + X^2 + X + 1`.

Irreducibility and primitive-order certificates are added in later `GF2_72`
modules before this polynomial is used to construct public field instances.
-/

namespace GF2_72

open Polynomial

noncomputable section

/-- Extension degree for `GF(2^72)`. -/
def extensionDegree : Nat :=
  72

/-- Raw executable carrier width for `GF(2^72)`. -/
abbrev B72 : Type :=
  BitVec extensionDegree

/-- Field cardinality of `GF(2^72)`. -/
def fieldSize : Nat :=
  BinaryField.Extension.fieldSize extensionDegree

/-- Multiplicative group order of `GF(2^72)`. -/
def multiplicativeGroupOrder : Nat :=
  BinaryField.Extension.multiplicativeGroupOrder extensionDegree

/-- Low-degree tail `X^6 + X^4 + X^3 + X^2 + X + 1`. -/
def definingTail : Polynomial (ZMod 2) :=
  X ^ 6 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1

/-- Candidate primitive polynomial bitmask: `X^72 + X^6 + X^4 + X^3 + X^2 + X + 1`. -/
def definingBitmask : Nat :=
  0x100000000000000005f

/-- Exponents with nonzero coefficients in the full defining polynomial. -/
def definingPolynomialExponents : List Nat :=
  [0, 1, 2, 3, 4, 6, 72]

/-- The tail has natural degree `6`. -/
lemma definingTail_natDegree :
    definingTail.natDegree = 6 := by
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
  tailDegree := 6
  bitmask := definingBitmask
  tail_natDegree := definingTail_natDegree
  tailDegree_lt_degree := by
    unfold extensionDegree
    omega

/-- Candidate defining polynomial for `GF(2^72)`. -/
def definingPolynomial : Polynomial (ZMod 2) :=
  BinaryField.Extension.polynomial definingPolynomialData

/-- Expanded form of the candidate defining polynomial. -/
lemma definingPolynomial_eq_X_pow_add_tail :
    definingPolynomial = X ^ 72 + definingTail := by
  rfl

/-- Expanded sparse form of the candidate defining polynomial. -/
lemma definingPolynomial_eq_sparse :
    definingPolynomial = X ^ 72 + X ^ 6 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  unfold definingPolynomial BinaryField.Extension.polynomial definingPolynomialData definingTail
    extensionDegree
  ring

/-- The candidate defining polynomial is monic of degree `72`. -/
lemma definingPolynomial_isMonicOfDegree :
    IsMonicOfDegree definingPolynomial extensionDegree :=
  BinaryField.Extension.polynomial_isMonicOfDegree definingPolynomialData

/-- The candidate defining polynomial has natural degree `72`. -/
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

/-- The candidate defining polynomial has degree `72`. -/
lemma definingPolynomial_degree :
    definingPolynomial.degree = extensionDegree :=
  BinaryField.Extension.polynomial_degree definingPolynomialData

/-- Bit-vector encoding of the candidate defining polynomial. -/
def P_val : BitVec (2 * extensionDegree) :=
  (1 <<< 72) ^^^ (1 <<< 6) ^^^ (1 <<< 4) ^^^ (1 <<< 3) ^^^
    (1 <<< 2) ^^^ (1 <<< 1) ^^^ 1

/-- The `BitVec` encoding denotes the candidate defining polynomial. -/
lemma definingPolynomial_eq_P_val :
    definingPolynomial = BinaryField.toPoly P_val := by
  rw [definingPolynomial_eq_sparse]
  unfold P_val extensionDegree
  repeat rw [BinaryField.toPoly_xor]
  rw [BinaryField.Extension.toPoly_one_shiftLeft 72 (by omega)]
  rw [BinaryField.Extension.toPoly_one_shiftLeft 6 (by omega)]
  rw [BinaryField.Extension.toPoly_one_shiftLeft 4 (by omega)]
  rw [BinaryField.Extension.toPoly_one_shiftLeft 3 (by omega)]
  rw [BinaryField.Extension.toPoly_one_shiftLeft 2 (by omega)]
  rw [BinaryField.Extension.toPoly_one_shiftLeft 1 (by omega)]
  rw [(show (1 : BitVec 144) = 1 <<< 0 by simp)]
  rw [BinaryField.Extension.toPoly_one_shiftLeft 0 (by omega)]
  simp only [pow_zero, pow_one]

/-- The exponent list denotes the candidate defining polynomial. -/
lemma sparsePolynomial_definingPolynomialExponents :
    BinaryField.Extension.sparsePolynomial definingPolynomialExponents = definingPolynomial := by
  rw [definingPolynomial_eq_sparse]
  simp [definingPolynomialExponents, BinaryField.Extension.sparsePolynomial]
  ring_nf

/-- Smooth subgroup refinement schedule for `2^72 - 1`. -/
def smoothRootSchedule : Array Nat :=
  #[3, 3, 3, 5, 7, 13, 17, 19, 37, 73, 109, 241, 433, 38737]

/-- The GF72 smooth schedule refines the multiplicative group down to singleton cosets. -/
lemma smoothRootSchedule_fold_eq_one :
    smoothRootSchedule.toList.foldl (fun order ell ↦ order / ell)
      (fieldSize - 1) = 1 := by
  unfold smoothRootSchedule fieldSize BinaryField.Extension.fieldSize extensionDegree
  decide

end

end GF2_72
