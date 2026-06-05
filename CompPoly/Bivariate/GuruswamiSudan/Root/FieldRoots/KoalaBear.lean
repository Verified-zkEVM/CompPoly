/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField
import CompPoly.Fields.KoalaBear
import CompPoly.Univariate.NTT.KoalaBear
import CompPoly.Univariate.Roots.SmoothSubgroup

/-!
# KoalaBear Guruswami-Sudan Field-Root Backends

Concrete finite-field root backends for canonical KoalaBear and native-word fast
KoalaBear. Both use the generic finite-field algorithm directly over their field
carriers.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Finite-field context for canonical KoalaBear. -/
def koalaBearFiniteFieldContext :
    CPolynomial.Roots.FiniteField.FiniteFieldContext KoalaBear.Field where
  q := KoalaBear.fieldSize
  finite := by infer_instance
  card_eq := by
    simp [KoalaBear.Field, KoalaBear.fieldSize, Nat.card_eq_fintype_card, ZMod.card]
  frobenius_fixed := by
    intro a
    simpa [KoalaBear.Field, KoalaBear.fieldSize] using ZMod.pow_card a

/-- Smooth cyclic splitter context for canonical KoalaBear. -/
def koalaBearSmoothCyclicRootContext :
    CPolynomial.Roots.FiniteField.SmoothCyclicRootContext KoalaBear.Field :=
  CPolynomial.Roots.FiniteField.smoothCyclicRootContextOf
    KoalaBear.fieldSize
    KoalaBear.primitiveRoot
    KoalaBear.smoothRootSchedule
    (CPolynomial.BatchEvalContext.horner KoalaBear.Field)
    (CPolynomial.Roots.FiniteField.smoothSplitterInput
      KoalaBear.fieldSize KoalaBear.primitiveRoot KoalaBear.smoothRootSchedule)
    (by
      simp [KoalaBear.Field, KoalaBear.fieldSize, Nat.card_eq_fintype_card, ZMod.card])
    KoalaBear.primitiveRoot_order
    KoalaBear.smoothRootSchedule_fold_eq_one
    (by
      intro M D p factor h
      exact CPolynomial.Roots.FiniteField.smoothLinearFactorsAlgorithmWith_sound
        M D (CPolynomial.BatchEvalContext.horner KoalaBear.Field)
        KoalaBear.fieldSize KoalaBear.primitiveRoot KoalaBear.smoothRootSchedule h)
    (by
      intro M D p a _hvalid hp hroot
      exact CPolynomial.Roots.FiniteField.smoothLinearFactorsAlgorithmWith_complete
        M D (CPolynomial.BatchEvalContext.horner KoalaBear.Field)
        KoalaBear.fieldSize KoalaBear.primitiveRoot KoalaBear.smoothRootSchedule
        (by
          simp [KoalaBear.Field, KoalaBear.fieldSize, Nat.card_eq_fintype_card, ZMod.card])
        KoalaBear.primitiveRoot_order
        (by decide)
        hp hroot)

/-- The KoalaBear smooth splitter accepts finite-field root products. -/
private theorem koalaBearSmoothRootProduct_valid
    (M : CPolynomial.Raw.MulContext KoalaBear.Field)
    (D : CPolynomial.Raw.ModContext KoalaBear.Field)
    {p : CPolynomial KoalaBear.Field} (hp : p ≠ 0) :
    koalaBearSmoothCyclicRootContext.validInput
      (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith M D
        koalaBearFiniteFieldContext p) := by
  simpa [koalaBearSmoothCyclicRootContext, koalaBearFiniteFieldContext] using
    (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith_smoothSplitterInput
      M D koalaBearFiniteFieldContext KoalaBear.primitiveRoot
      KoalaBear.smoothRootSchedule hp)

/-- Complete GS-facing finite-field root backend for canonical KoalaBear. -/
def koalaBearFieldRootContext : FieldRootContext KoalaBear.Field :=
  smoothFiniteFieldRootContext KoalaBear.Field
    koalaBearFiniteFieldContext koalaBearSmoothCyclicRootContext
    (by
      intro p hp
      exact koalaBearSmoothRootProduct_valid
        CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive hp)

/-- Complete GS-facing finite-field root backend for canonical KoalaBear with NTT arithmetic. -/
def koalaBearNttFieldRootContext : FieldRootContext KoalaBear.Field :=
  smoothFiniteFieldRootContextWith KoalaBear.Field
    (CPolynomial.Raw.MulContext.ntt CPolynomial.NTT.KoalaBear.bestDomainForLength?)
    (CPolynomial.Raw.ModContext.reversalNtt CPolynomial.NTT.KoalaBear.bestDomainForLength?)
    koalaBearFiniteFieldContext koalaBearSmoothCyclicRootContext
    (by
      intro p hp
      exact koalaBearSmoothRootProduct_valid
        (CPolynomial.Raw.MulContext.ntt CPolynomial.NTT.KoalaBear.bestDomainForLength?)
        (CPolynomial.Raw.ModContext.reversalNtt CPolynomial.NTT.KoalaBear.bestDomainForLength?)
        hp)

/-- Complete GS-facing finite-field root backend for canonical KoalaBear with NTTFast arithmetic. -/
def koalaBearNttFastFieldRootContext : FieldRootContext KoalaBear.Field :=
  smoothFiniteFieldRootContextWith KoalaBear.Field
    (CPolynomial.Raw.MulContext.nttFast CPolynomial.NTT.KoalaBear.bestDomainForLength?)
    (CPolynomial.Raw.ModContext.reversalNttFast CPolynomial.NTT.KoalaBear.bestDomainForLength?)
    koalaBearFiniteFieldContext koalaBearSmoothCyclicRootContext
    (by
      intro p hp
      exact koalaBearSmoothRootProduct_valid
        (CPolynomial.Raw.MulContext.nttFast CPolynomial.NTT.KoalaBear.bestDomainForLength?)
        (CPolynomial.Raw.ModContext.reversalNttFast CPolynomial.NTT.KoalaBear.bestDomainForLength?)
        hp)

/-- Finite-field context for native-word fast KoalaBear. -/
def fastKoalaBearFiniteFieldContext :
    CPolynomial.Roots.FiniteField.FiniteFieldContext KoalaBear.Fast.Field where
  q := KoalaBear.fieldSize
  finite := by
    exact Finite.of_equiv KoalaBear.Field KoalaBear.Fast.ringEquiv.toEquiv.symm
  card_eq := by
    have hcard : Nat.card KoalaBear.Fast.Field = Nat.card KoalaBear.Field :=
      Nat.card_congr KoalaBear.Fast.ringEquiv.toEquiv
    rw [hcard]
    simp [KoalaBear.Field, Nat.card_eq_fintype_card, ZMod.card]
  frobenius_fixed := by
    intro a
    apply KoalaBear.Fast.toField_injective
    rw [KoalaBear.Fast.toField_npow]
    simpa [KoalaBear.Field, KoalaBear.fieldSize] using
      ZMod.pow_card (KoalaBear.Fast.toField a)

/-- Primitive generator transported to native-word fast KoalaBear. -/
def fastKoalaBearPrimitiveRoot : KoalaBear.Fast.Field :=
  KoalaBear.Fast.ofField KoalaBear.primitiveRoot

/-- The transported fast KoalaBear generator has full multiplicative order. -/
lemma fastKoalaBearPrimitiveRoot_order :
    orderOf fastKoalaBearPrimitiveRoot = KoalaBear.fieldSize - 1 := by
  unfold fastKoalaBearPrimitiveRoot
  have h := MulEquiv.orderOf_eq KoalaBear.Fast.ringEquiv.toMulEquiv
    (KoalaBear.Fast.ofField KoalaBear.primitiveRoot)
  rw [← h]
  simpa [KoalaBear.Fast.ringEquiv_apply, KoalaBear.Fast.toField_ofField] using
    KoalaBear.primitiveRoot_order

/-- Smooth cyclic splitter context for native-word fast KoalaBear. -/
def fastKoalaBearSmoothCyclicRootContext :
    CPolynomial.Roots.FiniteField.SmoothCyclicRootContext KoalaBear.Fast.Field :=
  CPolynomial.Roots.FiniteField.smoothCyclicRootContextOf
    KoalaBear.fieldSize
    fastKoalaBearPrimitiveRoot
    KoalaBear.smoothRootSchedule
    (CPolynomial.BatchEvalContext.horner KoalaBear.Fast.Field)
    (CPolynomial.Roots.FiniteField.smoothSplitterInput
      KoalaBear.fieldSize fastKoalaBearPrimitiveRoot KoalaBear.smoothRootSchedule)
    (by
      have hcard : Nat.card KoalaBear.Fast.Field = Nat.card KoalaBear.Field :=
        Nat.card_congr KoalaBear.Fast.ringEquiv.toEquiv
      rw [hcard]
      simp [KoalaBear.Field, Nat.card_eq_fintype_card, ZMod.card])
    fastKoalaBearPrimitiveRoot_order
    KoalaBear.smoothRootSchedule_fold_eq_one
    (by
      intro M D p factor h
      exact CPolynomial.Roots.FiniteField.smoothLinearFactorsAlgorithmWith_sound
        M D (CPolynomial.BatchEvalContext.horner KoalaBear.Fast.Field)
        KoalaBear.fieldSize fastKoalaBearPrimitiveRoot KoalaBear.smoothRootSchedule h)
    (by
      intro M D p a _hvalid hp hroot
      letI : Finite KoalaBear.Fast.Field :=
        Finite.of_equiv KoalaBear.Field KoalaBear.Fast.ringEquiv.toEquiv.symm
      exact CPolynomial.Roots.FiniteField.smoothLinearFactorsAlgorithmWith_complete
        M D (CPolynomial.BatchEvalContext.horner KoalaBear.Fast.Field)
        KoalaBear.fieldSize fastKoalaBearPrimitiveRoot KoalaBear.smoothRootSchedule
        (by
          have hcard : Nat.card KoalaBear.Fast.Field = Nat.card KoalaBear.Field :=
            Nat.card_congr KoalaBear.Fast.ringEquiv.toEquiv
          rw [hcard]
          simp [KoalaBear.Field, Nat.card_eq_fintype_card, ZMod.card])
        fastKoalaBearPrimitiveRoot_order
        (by
          decide)
        hp hroot)

/-- The fast KoalaBear smooth splitter accepts finite-field root products. -/
private theorem fastKoalaBearSmoothRootProduct_valid
    (M : CPolynomial.Raw.MulContext KoalaBear.Fast.Field)
    (D : CPolynomial.Raw.ModContext KoalaBear.Fast.Field)
    {p : CPolynomial KoalaBear.Fast.Field} (hp : p ≠ 0) :
    fastKoalaBearSmoothCyclicRootContext.validInput
      (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith M D
        fastKoalaBearFiniteFieldContext p) := by
  simpa [fastKoalaBearSmoothCyclicRootContext, fastKoalaBearFiniteFieldContext] using
    (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith_smoothSplitterInput
      M D fastKoalaBearFiniteFieldContext fastKoalaBearPrimitiveRoot
      KoalaBear.smoothRootSchedule hp)

/-- Complete GS-facing finite-field root backend for native-word fast KoalaBear. -/
def fastKoalaBearFieldRootContext : FieldRootContext KoalaBear.Fast.Field :=
  smoothFiniteFieldRootContext KoalaBear.Fast.Field
    fastKoalaBearFiniteFieldContext fastKoalaBearSmoothCyclicRootContext
    (by
      intro p hp
      exact fastKoalaBearSmoothRootProduct_valid
        CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive hp)

/--
Complete GS-facing finite-field root backend for native-word fast KoalaBear with
NTT arithmetic.
-/
def fastKoalaBearNttFieldRootContext : FieldRootContext KoalaBear.Fast.Field :=
  smoothFiniteFieldRootContextWith KoalaBear.Fast.Field
    (CPolynomial.Raw.MulContext.ntt CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
    (CPolynomial.Raw.ModContext.reversalNtt CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
    fastKoalaBearFiniteFieldContext fastKoalaBearSmoothCyclicRootContext
    (by
      intro p hp
      exact fastKoalaBearSmoothRootProduct_valid
        (CPolynomial.Raw.MulContext.ntt CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
        (CPolynomial.Raw.ModContext.reversalNtt CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
        hp)

/--
Complete GS-facing finite-field root backend for native-word fast KoalaBear with
NTTFast arithmetic.
-/
def fastKoalaBearNttFastFieldRootContext : FieldRootContext KoalaBear.Fast.Field :=
  smoothFiniteFieldRootContextWith KoalaBear.Fast.Field
    (CPolynomial.Raw.MulContext.nttFast CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
    (CPolynomial.Raw.ModContext.reversalNttFast CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
    fastKoalaBearFiniteFieldContext fastKoalaBearSmoothCyclicRootContext
    (by
      intro p hp
      exact fastKoalaBearSmoothRootProduct_valid
        (CPolynomial.Raw.MulContext.nttFast CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
        (CPolynomial.Raw.ModContext.reversalNttFast
          CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
        hp)

end GuruswamiSudan

end CompPoly
