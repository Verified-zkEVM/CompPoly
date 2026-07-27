/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Extension.Impl
import CompPoly.Fields.Binary.GF2_72.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.CharAndCard
import Init.Data.Array.Lemmas

/-!
# GF(2^72) Executable Bit-Vector Operations

Executable operations for the `GF(2^72)` candidate polynomial
`X^72 + X^6 + X^4 + X^3 + X^2 + X + 1`.

This file exposes the raw `BitVec` carrier and arithmetic definitions. It does
claim the certified `Field` instance conditionally on the irreducibility
certificate supplied by `GF2_72.Primitive`.
-/

namespace GF2_72

namespace Concrete

/-- Executable parameters for the `GF(2^72)` candidate polynomial. -/
def params : BinaryField.Extension.ExecutableParams where
  degree := extensionDegree
  tailExponents := [0, 1, 2, 3, 4, 6]
  tailExponents_bound := by
    intro exponent h
    simp at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold extensionDegree <;> omega

/-- The executable tail list denotes the low-degree part of the GF72 polynomial. -/
lemma definingPolynomial_eq_executableSparse :
    BinaryField.Extension.polynomial definingPolynomialData =
      Polynomial.X ^ params.degree +
        BinaryField.Extension.sparsePolynomial params.tailExponents := by
  rw [show BinaryField.Extension.polynomial definingPolynomialData = definingPolynomial by rfl]
  rw [definingPolynomial_eq_X_pow_add_tail]
  simp [params, extensionDegree, definingTail, BinaryField.Extension.sparsePolynomial]
  ring_nf

end Concrete

/-- Executable bit-vector carrier for `GF(2^72)`. -/
@[reducible]
def ConcreteField : Type :=
  BinaryField.Extension.ConcreteField Concrete.params

namespace ConcreteField

abbrev rawWidth : Nat :=
  extensionDegree

def toBitVec : ConcreteField → B72 :=
  BinaryField.Extension.Concrete.toBitVec Concrete.params

def ofBitVec : B72 → ConcreteField :=
  BinaryField.Extension.Concrete.ofBitVec Concrete.params

def toNat : ConcreteField → Nat :=
  BinaryField.Extension.Concrete.toNat Concrete.params

def ofNat (n : Nat) : ConcreteField :=
  BinaryField.Extension.Concrete.ofNat Concrete.params n

def root : ConcreteField :=
  BinaryField.Extension.Concrete.root Concrete.params

def add : ConcreteField → ConcreteField → ConcreteField :=
  BinaryField.Extension.Concrete.add Concrete.params

def mul : ConcreteField → ConcreteField → ConcreteField :=
  BinaryField.Extension.Concrete.mul Concrete.params

def square : ConcreteField → ConcreteField :=
  BinaryField.Extension.Concrete.square Concrete.params

def pow : ConcreteField → Nat → ConcreteField :=
  BinaryField.Extension.Concrete.pow Concrete.params

def inv : ConcreteField → ConcreteField :=
  BinaryField.Extension.Concrete.inv Concrete.params

def traceValue : ConcreteField → ConcreteField :=
  BinaryField.Extension.Concrete.traceValue Concrete.params

def polynomialBasis : Array ConcreteField :=
  BinaryField.Extension.Concrete.polynomialBasis Concrete.params

def baseConstants : Array ConcreteField :=
  BinaryField.Extension.Concrete.baseConstants Concrete.params

noncomputable def toSpec : ConcreteField → SpecField :=
  BinaryField.Extension.Concrete.toSpec Concrete.params (data := definingPolynomialData)

instance : BEq ConcreteField :=
  BinaryField.Extension.Concrete.instBEqConcreteField Concrete.params

instance : LawfulBEq ConcreteField :=
  BinaryField.Extension.Concrete.instLawfulBEqConcreteField Concrete.params

instance : Inhabited ConcreteField :=
  BinaryField.Extension.Concrete.instInhabitedConcreteField Concrete.params

instance : Zero ConcreteField :=
  BinaryField.Extension.Concrete.instZeroConcreteField Concrete.params

instance : One ConcreteField :=
  BinaryField.Extension.Concrete.instOneConcreteField Concrete.params

instance : Add ConcreteField :=
  BinaryField.Extension.Concrete.instAddConcreteField Concrete.params

instance : Neg ConcreteField :=
  BinaryField.Extension.Concrete.instNegConcreteField Concrete.params

instance : Sub ConcreteField :=
  BinaryField.Extension.Concrete.instSubConcreteField Concrete.params

instance : Mul ConcreteField :=
  BinaryField.Extension.Concrete.instMulConcreteField Concrete.params

instance : Pow ConcreteField Nat :=
  BinaryField.Extension.Concrete.instPowConcreteField Concrete.params

instance : Inv ConcreteField :=
  BinaryField.Extension.Concrete.instInvConcreteField Concrete.params

/-- Certified executable field structure for `GF(2^72)`. -/
instance (priority := 2000) instFieldConcreteField
    [Fact (Irreducible definingPolynomial)] :
    Field ConcreteField := by
  haveI :
      Fact (Irreducible (BinaryField.Extension.polynomial definingPolynomialData)) := by
    simpa [definingPolynomial] using
      (inferInstance : Fact (Irreducible definingPolynomial))
  let hP :
      BinaryField.Extension.polynomial definingPolynomialData =
        Polynomial.X ^ Concrete.params.degree +
          BinaryField.Extension.sparsePolynomial Concrete.params.tailExponents :=
    Concrete.definingPolynomial_eq_executableSparse
  let hP_degree :
      (BinaryField.Extension.polynomial definingPolynomialData).degree =
        Concrete.params.degree := by
    simpa [Concrete.params, definingPolynomial] using definingPolynomial_degree
  let hDegree_pos : 0 < Concrete.params.degree := by
    unfold Concrete.params extensionDegree
    norm_num
  exact
    { toDivisionRing :=
        { toRing :=
            { add := BinaryField.Extension.Concrete.add Concrete.params
              zero := BinaryField.Extension.Concrete.zero Concrete.params
              neg := BinaryField.Extension.Concrete.neg Concrete.params
              sub := BinaryField.Extension.Concrete.sub Concrete.params
              mul := BinaryField.Extension.Concrete.mul Concrete.params
              one := BinaryField.Extension.Concrete.one Concrete.params
              nsmul := fun n x =>
                if n % 2 = 0 then BinaryField.Extension.Concrete.zero Concrete.params else x
              zsmul := fun n x =>
                if n % 2 = 0 then BinaryField.Extension.Concrete.zero Concrete.params else x
              npow := fun n x => BinaryField.Extension.Concrete.pow Concrete.params x n
              add_assoc := BinaryField.Extension.Concrete.add_assoc Concrete.params
              add_comm := BinaryField.Extension.Concrete.add_comm Concrete.params
              add_zero := BinaryField.Extension.Concrete.add_zero Concrete.params
              zero_add := BinaryField.Extension.Concrete.zero_add Concrete.params
              neg_add_cancel := BinaryField.Extension.Concrete.neg_add_cancel Concrete.params
              sub_eq_add_neg := by intro _ _; rfl
              nsmul_zero := fun _ => rfl
              nsmul_succ := BinaryField.Extension.Concrete.nsmul_succ Concrete.params
              zsmul_zero' := fun _ => rfl
              zsmul_succ' := BinaryField.Extension.Concrete.zsmul_succ Concrete.params
              zsmul_neg' := BinaryField.Extension.Concrete.zsmul_neg Concrete.params
              mul_assoc :=
                BinaryField.Extension.Concrete.mul_assoc_of_spec Concrete.params
                  (data := definingPolynomialData) hP hP_degree hDegree_pos
              one_mul :=
                BinaryField.Extension.Concrete.one_mul_of_spec Concrete.params
                  (data := definingPolynomialData) hP hP_degree hDegree_pos
              mul_one :=
                BinaryField.Extension.Concrete.mul_one_of_spec Concrete.params
                  (data := definingPolynomialData) hP hP_degree hDegree_pos
              left_distrib :=
                BinaryField.Extension.Concrete.left_distrib_of_spec Concrete.params
                  (data := definingPolynomialData) hP hP_degree hDegree_pos
              right_distrib :=
                BinaryField.Extension.Concrete.right_distrib_of_spec Concrete.params
                  (data := definingPolynomialData) hP hP_degree hDegree_pos
              zero_mul :=
                BinaryField.Extension.Concrete.zero_mul_of_spec Concrete.params
                  (data := definingPolynomialData) hP hP_degree hDegree_pos
              mul_zero :=
                BinaryField.Extension.Concrete.mul_zero_of_spec Concrete.params
                  (data := definingPolynomialData) hP hP_degree hDegree_pos
              natCast := BinaryField.Extension.Concrete.natCast Concrete.params
              natCast_zero := BinaryField.Extension.Concrete.natCast_zero Concrete.params
              natCast_succ := BinaryField.Extension.Concrete.natCast_succ Concrete.params
              intCast := BinaryField.Extension.Concrete.intCast Concrete.params
              intCast_ofNat := BinaryField.Extension.Concrete.intCast_ofNat Concrete.params
              intCast_negSucc := BinaryField.Extension.Concrete.intCast_negSucc Concrete.params
              npow_zero := by
                intro x
                change BinaryField.Extension.Concrete.pow Concrete.params x 0 =
                  BinaryField.Extension.Concrete.one Concrete.params
                simp [BinaryField.Extension.Concrete.pow]
              npow_succ := by
                intro n x
                change BinaryField.Extension.Concrete.pow Concrete.params x (n + 1) =
                  BinaryField.Extension.Concrete.mul Concrete.params
                    (BinaryField.Extension.Concrete.pow Concrete.params x n) x
                exact BinaryField.Extension.Concrete.pow_succ_of_spec Concrete.params
                  (data := definingPolynomialData) hP hP_degree hDegree_pos n x }
          inv := BinaryField.Extension.Concrete.inv Concrete.params
          div := fun a b =>
            BinaryField.Extension.Concrete.mul Concrete.params a
              (BinaryField.Extension.Concrete.inv Concrete.params b)
          exists_pair_ne :=
            BinaryField.Extension.Concrete.exists_pair_ne Concrete.params hDegree_pos
          mul_inv_cancel := by
            intro a h
            change BinaryField.Extension.Concrete.mul Concrete.params a
                (BinaryField.Extension.Concrete.inv Concrete.params a) =
              BinaryField.Extension.Concrete.one Concrete.params
            exact BinaryField.Extension.Concrete.mul_inv_cancel_of_spec Concrete.params
              (data := definingPolynomialData) hP hP_degree hDegree_pos a (by simpa using h)
          inv_zero := by
            change BinaryField.Extension.Concrete.inv Concrete.params
                (BinaryField.Extension.Concrete.zero Concrete.params) =
              BinaryField.Extension.Concrete.zero Concrete.params
            exact BinaryField.Extension.Concrete.inv_zero Concrete.params
          div_eq_mul_inv := by
            intro a b
            rfl
          qsmul := _
          nnqsmul := _ }
      mul_comm := by
        intro a b
        change BinaryField.Extension.Concrete.mul Concrete.params a b =
          BinaryField.Extension.Concrete.mul Concrete.params b a
        exact BinaryField.Extension.Concrete.mul_comm_of_spec Concrete.params
          (data := definingPolynomialData) hP hP_degree hDegree_pos a b }

noncomputable instance : Fintype ConcreteField :=
  BinaryField.Extension.Concrete.instFintypeConcreteField Concrete.params

instance : Finite ConcreteField :=
  BinaryField.Extension.Concrete.instFiniteConcreteField Concrete.params

/-- The raw executable carrier has `2^72` bit-patterns. -/
theorem card :
    Fintype.card ConcreteField = 2 ^ extensionDegree := by
  simpa [Concrete.params] using
    BinaryField.Extension.Concrete.concreteField_card Concrete.params

/-- The certified executable carrier has characteristic two. -/
noncomputable instance instCharTwoConcreteField [Fact (Irreducible definingPolynomial)] :
    CharP ConcreteField 2 := by
  let fieldInst : Field ConcreteField := instFieldConcreteField
  letI : Field ConcreteField := fieldInst
  letI : CommRing ConcreteField := fieldInst.toCommRing
  letI : IsDomain ConcreteField := Field.isDomain
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (R := ConcreteField) (p := 2)
    (f := extensionDegree) card

/-- Canonical `GF(2)` algebra structure on the certified executable carrier. -/
noncomputable instance instAlgebraConcreteField [Fact (Irreducible definingPolynomial)] :
    Algebra (ZMod 2) ConcreteField := by
  let fieldInst : Field ConcreteField := instFieldConcreteField
  letI : Field ConcreteField := fieldInst
  letI : CommRing ConcreteField := fieldInst.toCommRing
  letI : CharP ConcreteField 2 := instCharTwoConcreteField
  exact ZMod.algebra ConcreteField 2

@[simp]
theorem polynomialBasis_size :
    polynomialBasis.size = extensionDegree := by
  rw [polynomialBasis, BinaryField.Extension.Concrete.polynomialBasis]
  exact Array.size_ofFn

@[simp]
theorem baseConstants_size :
    baseConstants.size = 2 := by
  simp [baseConstants, BinaryField.Extension.Concrete.baseConstants]

theorem toSpec_injective :
    Function.Injective toSpec := by
  apply BinaryField.Extension.Concrete.toSpec_injective
  · simpa [Concrete.params, definingPolynomial] using definingPolynomial_degree
  · unfold Concrete.params extensionDegree
    norm_num

theorem toSpec_zero :
    toSpec 0 = 0 := by
  exact BinaryField.Extension.Concrete.toSpec_zero Concrete.params

theorem toSpec_one :
    toSpec 1 = 1 := by
  exact BinaryField.Extension.Concrete.toSpec_one Concrete.params
    (by unfold Concrete.params extensionDegree; norm_num)

theorem toSpec_add (a b : ConcreteField) :
    toSpec (a + b) = toSpec a + toSpec b := by
  exact BinaryField.Extension.Concrete.toSpec_add Concrete.params a b

theorem toSpec_neg (a : ConcreteField) :
    toSpec (-a) = -toSpec a := by
  exact BinaryField.Extension.Concrete.toSpec_neg Concrete.params a

theorem toSpec_sub (a b : ConcreteField) :
    toSpec (a - b) = toSpec a - toSpec b := by
  exact BinaryField.Extension.Concrete.toSpec_sub Concrete.params a b

theorem toSpec_mul (a b : ConcreteField) :
    toSpec (a * b) = toSpec a * toSpec b := by
  exact BinaryField.Extension.Concrete.toSpec_mul Concrete.params
    (data := definingPolynomialData)
    Concrete.definingPolynomial_eq_executableSparse
    (by simpa [Concrete.params, definingPolynomial] using definingPolynomial_degree)
    a b

/-- Ring homomorphism from executable GF72 elements to the quotient specification. -/
noncomputable def toSpecRingHom [Fact (Irreducible definingPolynomial)] :
    ConcreteField →+* SpecField where
  toFun := toSpec
  map_zero' := toSpec_zero
  map_one' := toSpec_one
  map_add' := toSpec_add
  map_mul' := toSpec_mul

/-- Algebra homomorphism from executable GF72 elements to the quotient specification. -/
noncomputable def toSpecAlgHom [Fact (Irreducible definingPolynomial)] :
    ConcreteField →ₐ[ZMod 2] SpecField where
  __ := toSpecRingHom
  commutes' := by
    intro r
    exact RingHom.congr_fun
      (RingHom.ext_zmod (toSpecRingHom.comp (algebraMap (ZMod 2) ConcreteField))
        (algebraMap (ZMod 2) SpecField)) r

/-- Algebra equivalence between executable GF72 elements and the quotient specification. -/
noncomputable def toSpecAlgEquiv [Fact (Irreducible definingPolynomial)] :
    ConcreteField ≃ₐ[ZMod 2] SpecField :=
  AlgEquiv.ofBijective toSpecAlgHom <| by
    apply Function.Injective.bijective_of_nat_card_le
    · exact toSpec_injective
    · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      rw [card, BinaryField.Extension.specField_card definingPolynomialData]
      simp [definingPolynomialData, extensionDegree]

/-- The executable polynomial-basis generator maps to the quotient root. -/
theorem toSpec_root :
    toSpec root = GF2_72.root := by
  exact BinaryField.Extension.Concrete.toSpec_root Concrete.params
    (data := definingPolynomialData)
    (by unfold Concrete.params extensionDegree; norm_num)

end ConcreteField

end GF2_72
