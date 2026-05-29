/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField
import CompPoly.Fields.KoalaBear
import CompPoly.Univariate.NTT.KoalaBear
import CompPoly.Univariate.Roots.SmoothSubgroupCorrectness

/-!
# KoalaBear Guruswami-Sudan Field-Root Backends

Concrete finite-field root backends for canonical KoalaBear and native-word fast
KoalaBear. Both use the generic odd finite-field algorithm directly over their
field carriers.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Odd finite-field context for canonical KoalaBear. -/
def koalaBearOddFiniteFieldContext :
    CPolynomial.Roots.FiniteField.OddFiniteFieldContext KoalaBear.Field where
  q := KoalaBear.fieldSize
  finite := by infer_instance
  card_eq := by
    simp [KoalaBear.Field, KoalaBear.fieldSize, Nat.card_eq_fintype_card, ZMod.card]
  q_odd := by
    unfold KoalaBear.fieldSize
    decide
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
    (CPolynomial.Roots.FiniteField.BatchEvalContext.horner KoalaBear.Field)
    (CPolynomial.Roots.FiniteField.smoothSplitterInput
      KoalaBear.fieldSize KoalaBear.primitiveRoot KoalaBear.smoothRootSchedule)
    (by
      simp [KoalaBear.Field, KoalaBear.fieldSize, Nat.card_eq_fintype_card, ZMod.card])
    KoalaBear.primitiveRoot_order
    KoalaBear.smoothRootSchedule_fold_eq_one
    (by
      intro M D p factor h
      exact CPolynomial.Roots.FiniteField.smoothLinearFactorsAlgorithmWith_sound
        M D (CPolynomial.Roots.FiniteField.BatchEvalContext.horner KoalaBear.Field)
        KoalaBear.fieldSize KoalaBear.primitiveRoot KoalaBear.smoothRootSchedule h)
    (by
      intro M D p a _hvalid hp hroot
      exact CPolynomial.Roots.FiniteField.smoothLinearFactorsAlgorithmWith_complete
        M D (CPolynomial.Roots.FiniteField.BatchEvalContext.horner KoalaBear.Field)
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
        koalaBearOddFiniteFieldContext p) := by
  simpa [koalaBearSmoothCyclicRootContext, koalaBearOddFiniteFieldContext] using
    (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith_smoothSplitterInput
      M D koalaBearOddFiniteFieldContext KoalaBear.primitiveRoot
      KoalaBear.smoothRootSchedule hp)

/-- Complete GS-facing finite-field root backend for canonical KoalaBear. -/
def koalaBearFieldRootBackend : FieldRootBackend KoalaBear.Field :=
  smoothOddFiniteFieldRootBackend KoalaBear.Field
    koalaBearOddFiniteFieldContext koalaBearSmoothCyclicRootContext
    (by
      intro p hp
      exact koalaBearSmoothRootProduct_valid
        CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive hp)

/-- Complete GS-facing finite-field root backend for canonical KoalaBear with NTT arithmetic. -/
def koalaBearNttFieldRootBackend : FieldRootBackend KoalaBear.Field :=
  smoothOddFiniteFieldRootBackendWith KoalaBear.Field
    (CPolynomial.Raw.MulContext.ntt CPolynomial.NTT.KoalaBear.bestDomainForLength?)
    (CPolynomial.Raw.ModContext.reversalNtt CPolynomial.NTT.KoalaBear.bestDomainForLength?)
    koalaBearOddFiniteFieldContext koalaBearSmoothCyclicRootContext
    (by
      intro p hp
      exact koalaBearSmoothRootProduct_valid
        (CPolynomial.Raw.MulContext.ntt CPolynomial.NTT.KoalaBear.bestDomainForLength?)
        (CPolynomial.Raw.ModContext.reversalNtt CPolynomial.NTT.KoalaBear.bestDomainForLength?)
        hp)

/-- Complete GS-facing finite-field root backend for canonical KoalaBear with NTTFast arithmetic. -/
def koalaBearNttFastFieldRootBackend : FieldRootBackend KoalaBear.Field :=
  smoothOddFiniteFieldRootBackendWith KoalaBear.Field
    (CPolynomial.Raw.MulContext.nttFast CPolynomial.NTT.KoalaBear.bestDomainForLength?)
    (CPolynomial.Raw.ModContext.reversalNttFast CPolynomial.NTT.KoalaBear.bestDomainForLength?)
    koalaBearOddFiniteFieldContext koalaBearSmoothCyclicRootContext
    (by
      intro p hp
      exact koalaBearSmoothRootProduct_valid
        (CPolynomial.Raw.MulContext.nttFast CPolynomial.NTT.KoalaBear.bestDomainForLength?)
        (CPolynomial.Raw.ModContext.reversalNttFast CPolynomial.NTT.KoalaBear.bestDomainForLength?)
        hp)

/-- Odd finite-field context for native-word fast KoalaBear. -/
def fastKoalaBearOddFiniteFieldContext :
    CPolynomial.Roots.FiniteField.OddFiniteFieldContext KoalaBear.Fast.Field where
  q := KoalaBear.fieldSize
  finite := by
    exact Finite.of_equiv KoalaBear.Field KoalaBear.Fast.ringEquiv.toEquiv.symm
  card_eq := by
    have hcard : Nat.card KoalaBear.Fast.Field = Nat.card KoalaBear.Field :=
      Nat.card_congr KoalaBear.Fast.ringEquiv.toEquiv
    rw [hcard]
    simp [KoalaBear.Field, Nat.card_eq_fintype_card, ZMod.card]
  q_odd := by
    unfold KoalaBear.fieldSize
    decide
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
    (CPolynomial.Roots.FiniteField.BatchEvalContext.horner KoalaBear.Fast.Field)
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
        M D (CPolynomial.Roots.FiniteField.BatchEvalContext.horner KoalaBear.Fast.Field)
        KoalaBear.fieldSize fastKoalaBearPrimitiveRoot KoalaBear.smoothRootSchedule h)
    (by
      intro M D p a _hvalid hp hroot
      letI : Finite KoalaBear.Fast.Field :=
        Finite.of_equiv KoalaBear.Field KoalaBear.Fast.ringEquiv.toEquiv.symm
      exact CPolynomial.Roots.FiniteField.smoothLinearFactorsAlgorithmWith_complete
        M D (CPolynomial.Roots.FiniteField.BatchEvalContext.horner KoalaBear.Fast.Field)
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
        fastKoalaBearOddFiniteFieldContext p) := by
  simpa [fastKoalaBearSmoothCyclicRootContext, fastKoalaBearOddFiniteFieldContext] using
    (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith_smoothSplitterInput
      M D fastKoalaBearOddFiniteFieldContext fastKoalaBearPrimitiveRoot
      KoalaBear.smoothRootSchedule hp)

/-- Complete GS-facing finite-field root backend for native-word fast KoalaBear. -/
def fastKoalaBearFieldRootBackend : FieldRootBackend KoalaBear.Fast.Field :=
  smoothOddFiniteFieldRootBackend KoalaBear.Fast.Field
    fastKoalaBearOddFiniteFieldContext fastKoalaBearSmoothCyclicRootContext
    (by
      intro p hp
      exact fastKoalaBearSmoothRootProduct_valid
        CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive hp)

/--
Complete GS-facing finite-field root backend for native-word fast KoalaBear with
NTT arithmetic.
-/
def fastKoalaBearNttFieldRootBackend : FieldRootBackend KoalaBear.Fast.Field :=
  smoothOddFiniteFieldRootBackendWith KoalaBear.Fast.Field
    (CPolynomial.Raw.MulContext.ntt CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
    (CPolynomial.Raw.ModContext.reversalNtt CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
    fastKoalaBearOddFiniteFieldContext fastKoalaBearSmoothCyclicRootContext
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
def fastKoalaBearNttFastFieldRootBackend : FieldRootBackend KoalaBear.Fast.Field :=
  smoothOddFiniteFieldRootBackendWith KoalaBear.Fast.Field
    (CPolynomial.Raw.MulContext.nttFast CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
    (CPolynomial.Raw.ModContext.reversalNttFast CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
    fastKoalaBearOddFiniteFieldContext fastKoalaBearSmoothCyclicRootContext
    (by
      intro p hp
      exact fastKoalaBearSmoothRootProduct_valid
        (CPolynomial.Raw.MulContext.nttFast CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
        (CPolynomial.Raw.ModContext.reversalNttFast
          CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
        hp)

end GuruswamiSudan

end CompPoly
