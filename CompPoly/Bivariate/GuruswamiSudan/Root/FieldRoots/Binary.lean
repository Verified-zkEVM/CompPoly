/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField
import CompPoly.Fields.Binary.GF2_32
import CompPoly.Fields.Binary.GF2_48
import CompPoly.Fields.Binary.GF2_64
import CompPoly.Fields.Binary.GF2_72

/-!
# Binary-Field Guruswami-Sudan Field-Root Backends

GS-facing finite-field root backends for the executable `GF(2^32)`, `GF(2^48)`,
`GF(2^64)`, and `GF(2^72)` carriers.
-/

namespace CompPoly

namespace GuruswamiSudan

namespace Binary

open CPolynomial.Roots.FiniteField

private theorem directBinaryToNat_lt
    (params : BinaryField.Extension.ExecutableParams)
    (a : BinaryField.Extension.ConcreteField params) :
    BinaryField.Extension.Concrete.toNat params a <
      BinaryField.Extension.fieldSize params.degree := by
  simpa [BinaryField.Extension.Concrete.toNat, BinaryField.Extension.Concrete.toBitVec,
    BinaryField.Extension.fieldSize] using
    (BinaryField.Extension.Concrete.toBitVec params a).isLt

private theorem directBinaryOfNat_toNat
    (params : BinaryField.Extension.ExecutableParams)
    (a : BinaryField.Extension.ConcreteField params) :
    BinaryField.Extension.Concrete.ofNat params
        (BinaryField.Extension.Concrete.toNat params a) =
      a := by
  apply BitVec.eq_of_toNat_eq
  simp [BinaryField.Extension.Concrete.toNat, BinaryField.Extension.Concrete.toBitVec,
    BinaryField.Extension.Concrete.ofNat, BinaryField.Extension.Concrete.ofBitVec]

/-- Lazy complete enumeration for direct executable binary-extension carriers. -/
private def directBinaryFieldEnumeration
    (params : BinaryField.Extension.ExecutableParams) :
    FieldEnumeration (BinaryField.Extension.ConcreteField params) where
  size := BinaryField.Extension.fieldSize params.degree
  elem i := BinaryField.Extension.Concrete.ofNat params i.val
  complete := by
    intro a
    exact ⟨⟨BinaryField.Extension.Concrete.toNat params a,
      directBinaryToNat_lt params a⟩, directBinaryOfNat_toNat params a⟩

/-- Lazy complete enumeration for `GF(2^32)`. -/
def gf2_32FieldEnumeration : FieldEnumeration GF2_32.ConcreteField :=
  directBinaryFieldEnumeration GF2_32.Concrete.params

/-- Lazy complete enumeration for `GF(2^48)`. -/
def gf2_48FieldEnumeration : FieldEnumeration GF2_48.ConcreteField :=
  directBinaryFieldEnumeration GF2_48.Concrete.params

/-- Lazy complete enumeration for `GF(2^64)`. -/
def gf2_64FieldEnumeration : FieldEnumeration GF2_64.ConcreteField :=
  directBinaryFieldEnumeration GF2_64.Concrete.params

/-- Lazy complete enumeration for `GF(2^72)`. -/
def gf2_72FieldEnumeration : FieldEnumeration GF2_72.ConcreteField :=
  directBinaryFieldEnumeration GF2_72.Concrete.params

/-- Default Las Vegas trace configuration for `GF(2^32)`. -/
def gf2_32LasVegasConfig : LasVegasConfig where
  cutoff := GF2_32.extensionDegree
  tryOddRandomizedSplitting := true
  tryEvenTraceSplitting := true

/-- Default Las Vegas trace configuration for `GF(2^48)`. -/
def gf2_48LasVegasConfig : LasVegasConfig where
  cutoff := GF2_48.extensionDegree
  tryOddRandomizedSplitting := true
  tryEvenTraceSplitting := true

/-- Default Las Vegas trace configuration for `GF(2^64)`. -/
def gf2_64LasVegasConfig : LasVegasConfig where
  cutoff := GF2_64.extensionDegree
  tryOddRandomizedSplitting := true
  tryEvenTraceSplitting := true

/-- Default Las Vegas trace configuration for `GF(2^72)`. -/
def gf2_72LasVegasConfig : LasVegasConfig where
  cutoff := GF2_72.extensionDegree
  tryOddRandomizedSplitting := true
  tryEvenTraceSplitting := true

/-- Deterministic basis-cycle Las Vegas probes for `GF(2^32)`. -/
def gf2_32LasVegasProbeFamily : ProbeFamily GF2_32.ConcreteField :=
  traceBasisProbeFamily GF2_32.shoupTraceContext

/-- Deterministic basis-cycle Las Vegas probes for `GF(2^48)`. -/
def gf2_48LasVegasProbeFamily : ProbeFamily GF2_48.ConcreteField :=
  traceBasisProbeFamily GF2_48.shoupTraceContext

/-- Deterministic basis-cycle Las Vegas probes for `GF(2^64)`. -/
def gf2_64LasVegasProbeFamily : ProbeFamily GF2_64.ConcreteField :=
  traceBasisProbeFamily GF2_64.shoupTraceContext

/-- Deterministic basis-cycle Las Vegas probes for `GF(2^72)`. -/
def gf2_72LasVegasProbeFamily : ProbeFamily GF2_72.ConcreteField :=
  traceBasisProbeFamily GF2_72.shoupTraceContext

/-- The GF32 smooth splitter accepts finite-field root products. -/
private theorem gf2_32SmoothRootProduct_valid
    (M : CPolynomial.Raw.MulContext GF2_32.ConcreteField)
    (D : CPolynomial.Raw.ModContext GF2_32.ConcreteField)
    {p : CPolynomial GF2_32.ConcreteField} (hp : p ≠ 0) :
    GF2_32.smoothHornerRootContext.validInput
      (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith M D
        GF2_32.finiteFieldContext p) := by
  simpa [GF2_32.smoothHornerRootContext, GF2_32.smoothCyclicRootContextWith,
    GF2_32.finiteFieldContext] using
    (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith_smoothSplitterInput
      M D GF2_32.finiteFieldContext GF2_32.primitiveRoot
      GF2_32.smoothRootSchedule hp)

/-- The GF32 smooth-subproduct splitter accepts finite-field root products. -/
private theorem gf2_32SmoothSubproductRootProduct_valid
    (M : CPolynomial.Raw.MulContext GF2_32.ConcreteField)
    (D : CPolynomial.Raw.ModContext GF2_32.ConcreteField)
    {p : CPolynomial GF2_32.ConcreteField} (hp : p ≠ 0) :
    GF2_32.smoothSubproductRootContext.validInput
      (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith M D
        GF2_32.finiteFieldContext p) := by
  simpa [GF2_32.smoothSubproductRootContext, GF2_32.smoothCyclicRootContextWith,
    GF2_32.finiteFieldContext] using
    (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith_smoothSplitterInput
      M D GF2_32.finiteFieldContext GF2_32.primitiveRoot
      GF2_32.smoothRootSchedule hp)

/-- The GF48 smooth splitter accepts finite-field root products. -/
private theorem gf2_48SmoothRootProduct_valid
    (M : CPolynomial.Raw.MulContext GF2_48.ConcreteField)
    (D : CPolynomial.Raw.ModContext GF2_48.ConcreteField)
    {p : CPolynomial GF2_48.ConcreteField} (hp : p ≠ 0) :
    GF2_48.smoothHornerRootContext.validInput
      (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith M D
        GF2_48.finiteFieldContext p) := by
  simpa [GF2_48.smoothHornerRootContext, GF2_48.smoothCyclicRootContextWith,
    GF2_48.finiteFieldContext] using
    (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith_smoothSplitterInput
      M D GF2_48.finiteFieldContext GF2_48.primitiveRoot
      GF2_48.smoothRootSchedule hp)

/-- The GF48 smooth-subproduct splitter accepts finite-field root products. -/
private theorem gf2_48SmoothSubproductRootProduct_valid
    (M : CPolynomial.Raw.MulContext GF2_48.ConcreteField)
    (D : CPolynomial.Raw.ModContext GF2_48.ConcreteField)
    {p : CPolynomial GF2_48.ConcreteField} (hp : p ≠ 0) :
    GF2_48.smoothSubproductRootContext.validInput
      (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith M D
        GF2_48.finiteFieldContext p) := by
  simpa [GF2_48.smoothSubproductRootContext, GF2_48.smoothCyclicRootContextWith,
    GF2_48.finiteFieldContext] using
    (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith_smoothSplitterInput
      M D GF2_48.finiteFieldContext GF2_48.primitiveRoot
      GF2_48.smoothRootSchedule hp)

/-- The GF64 smooth splitter accepts finite-field root products. -/
private theorem gf2_64SmoothRootProduct_valid
    (M : CPolynomial.Raw.MulContext GF2_64.ConcreteField)
    (D : CPolynomial.Raw.ModContext GF2_64.ConcreteField)
    {p : CPolynomial GF2_64.ConcreteField} (hp : p ≠ 0) :
    GF2_64.smoothHornerRootContext.validInput
      (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith M D
        GF2_64.finiteFieldContext p) := by
  simpa [GF2_64.smoothHornerRootContext, GF2_64.smoothCyclicRootContextWith,
    GF2_64.finiteFieldContext] using
    (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith_smoothSplitterInput
      M D GF2_64.finiteFieldContext GF2_64.primitiveRoot
      GF2_64.smoothRootSchedule hp)

/-- The GF64 smooth-subproduct splitter accepts finite-field root products. -/
private theorem gf2_64SmoothSubproductRootProduct_valid
    (M : CPolynomial.Raw.MulContext GF2_64.ConcreteField)
    (D : CPolynomial.Raw.ModContext GF2_64.ConcreteField)
    {p : CPolynomial GF2_64.ConcreteField} (hp : p ≠ 0) :
    GF2_64.smoothSubproductRootContext.validInput
      (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith M D
        GF2_64.finiteFieldContext p) := by
  simpa [GF2_64.smoothSubproductRootContext, GF2_64.smoothCyclicRootContextWith,
    GF2_64.finiteFieldContext] using
    (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith_smoothSplitterInput
      M D GF2_64.finiteFieldContext GF2_64.primitiveRoot
      GF2_64.smoothRootSchedule hp)

/-- The GF72 smooth splitter accepts finite-field root products. -/
private theorem gf2_72SmoothRootProduct_valid
    (M : CPolynomial.Raw.MulContext GF2_72.ConcreteField)
    (D : CPolynomial.Raw.ModContext GF2_72.ConcreteField)
    {p : CPolynomial GF2_72.ConcreteField} (hp : p ≠ 0) :
    GF2_72.smoothHornerRootContext.validInput
      (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith M D
        GF2_72.finiteFieldContext p) := by
  simpa [GF2_72.smoothHornerRootContext, GF2_72.smoothCyclicRootContextWith,
    GF2_72.finiteFieldContext] using
    (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith_smoothSplitterInput
      M D GF2_72.finiteFieldContext GF2_72.primitiveRoot
      GF2_72.smoothRootSchedule hp)

/-- The GF72 smooth-subproduct splitter accepts finite-field root products. -/
private theorem gf2_72SmoothSubproductRootProduct_valid
    (M : CPolynomial.Raw.MulContext GF2_72.ConcreteField)
    (D : CPolynomial.Raw.ModContext GF2_72.ConcreteField)
    {p : CPolynomial GF2_72.ConcreteField} (hp : p ≠ 0) :
    GF2_72.smoothSubproductRootContext.validInput
      (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith M D
        GF2_72.finiteFieldContext p) := by
  simpa [GF2_72.smoothSubproductRootContext, GF2_72.smoothCyclicRootContextWith,
    GF2_72.finiteFieldContext] using
    (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith_smoothSplitterInput
      M D GF2_72.finiteFieldContext GF2_72.primitiveRoot
      GF2_72.smoothRootSchedule hp)

/-- GS field-root backend over GF32 using the smooth Horner leaf evaluator. -/
def gf2_32SmoothFieldRootContext :
    FieldRootContext GF2_32.ConcreteField :=
  smoothFiniteFieldRootContext GF2_32.ConcreteField
    GF2_32.finiteFieldContext GF2_32.smoothHornerRootContext
    (by
      intro p hp
      exact gf2_32SmoothRootProduct_valid
        CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive hp)

/-- GS field-root backend over GF32 using the smooth subproduct-tree leaf evaluator. -/
def gf2_32SmoothSubproductFieldRootContext :
    FieldRootContext GF2_32.ConcreteField :=
  smoothFiniteFieldRootContext GF2_32.ConcreteField
    GF2_32.finiteFieldContext GF2_32.smoothSubproductRootContext
    (by
      intro p hp
      exact gf2_32SmoothSubproductRootProduct_valid
        CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive hp)

/-- GS field-root backend over GF32 using the Shoup trace splitter. -/
def gf2_32ShoupFieldRootContext :
    FieldRootContext GF2_32.ConcreteField :=
  shoupFiniteFieldRootContext GF2_32.ConcreteField GF2_32.shoupTraceContext

/-- GS field-root backend over GF32 using Las Vegas trace splitting. -/
def gf2_32LasVegasFieldRootContext :
    FieldRootContext GF2_32.ConcreteField :=
  lasVegasFiniteFieldRootContextWithTrace GF2_32.ConcreteField
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
    GF2_32.finiteFieldContext gf2_32FieldEnumeration GF2_32.shoupTraceContext
    gf2_32LasVegasConfig gf2_32LasVegasProbeFamily

/-- GS field-root backend over GF48 using the smooth Horner leaf evaluator. -/
def gf2_48SmoothFieldRootContext :
    FieldRootContext GF2_48.ConcreteField :=
  smoothFiniteFieldRootContext GF2_48.ConcreteField
    GF2_48.finiteFieldContext GF2_48.smoothHornerRootContext
    (by
      intro p hp
      exact gf2_48SmoothRootProduct_valid
        CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive hp)

/-- GS field-root backend over GF48 using the smooth subproduct-tree leaf evaluator. -/
def gf2_48SmoothSubproductFieldRootContext :
    FieldRootContext GF2_48.ConcreteField :=
  smoothFiniteFieldRootContext GF2_48.ConcreteField
    GF2_48.finiteFieldContext GF2_48.smoothSubproductRootContext
    (by
      intro p hp
      exact gf2_48SmoothSubproductRootProduct_valid
        CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive hp)

/-- GS field-root backend over GF48 using the Shoup trace splitter. -/
def gf2_48ShoupFieldRootContext :
    FieldRootContext GF2_48.ConcreteField :=
  shoupFiniteFieldRootContext GF2_48.ConcreteField GF2_48.shoupTraceContext

/-- GS field-root backend over GF48 using Las Vegas trace splitting. -/
def gf2_48LasVegasFieldRootContext :
    FieldRootContext GF2_48.ConcreteField :=
  lasVegasFiniteFieldRootContextWithTrace GF2_48.ConcreteField
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
    GF2_48.finiteFieldContext gf2_48FieldEnumeration GF2_48.shoupTraceContext
    gf2_48LasVegasConfig gf2_48LasVegasProbeFamily

/-- GS field-root backend over GF64 using the smooth Horner leaf evaluator. -/
def gf2_64SmoothFieldRootContext :
    FieldRootContext GF2_64.ConcreteField :=
  smoothFiniteFieldRootContext GF2_64.ConcreteField
    GF2_64.finiteFieldContext GF2_64.smoothHornerRootContext
    (by
      intro p hp
      exact gf2_64SmoothRootProduct_valid
        CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive hp)

/-- GS field-root backend over GF64 using the smooth subproduct-tree leaf evaluator. -/
def gf2_64SmoothSubproductFieldRootContext :
    FieldRootContext GF2_64.ConcreteField :=
  smoothFiniteFieldRootContext GF2_64.ConcreteField
    GF2_64.finiteFieldContext GF2_64.smoothSubproductRootContext
    (by
      intro p hp
      exact gf2_64SmoothSubproductRootProduct_valid
        CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive hp)

/-- GS field-root backend over GF64 using the Shoup trace splitter. -/
def gf2_64ShoupFieldRootContext :
    FieldRootContext GF2_64.ConcreteField :=
  shoupFiniteFieldRootContext GF2_64.ConcreteField GF2_64.shoupTraceContext

/-- GS field-root backend over GF64 using Las Vegas trace splitting. -/
def gf2_64LasVegasFieldRootContext :
    FieldRootContext GF2_64.ConcreteField :=
  lasVegasFiniteFieldRootContextWithTrace GF2_64.ConcreteField
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
    GF2_64.finiteFieldContext gf2_64FieldEnumeration GF2_64.shoupTraceContext
    gf2_64LasVegasConfig gf2_64LasVegasProbeFamily

/-- GS field-root backend over GF72 using the smooth Horner leaf evaluator. -/
def gf2_72SmoothFieldRootContext :
    FieldRootContext GF2_72.ConcreteField :=
  smoothFiniteFieldRootContext GF2_72.ConcreteField
    GF2_72.finiteFieldContext GF2_72.smoothHornerRootContext
    (by
      intro p hp
      exact gf2_72SmoothRootProduct_valid
        CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive hp)

/-- GS field-root backend over GF72 using the smooth subproduct-tree leaf evaluator. -/
def gf2_72SmoothSubproductFieldRootContext :
    FieldRootContext GF2_72.ConcreteField :=
  smoothFiniteFieldRootContext GF2_72.ConcreteField
    GF2_72.finiteFieldContext GF2_72.smoothSubproductRootContext
    (by
      intro p hp
      exact gf2_72SmoothSubproductRootProduct_valid
        CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive hp)

/-- GS field-root backend over GF72 using the Shoup trace splitter. -/
def gf2_72ShoupFieldRootContext :
    FieldRootContext GF2_72.ConcreteField :=
  shoupFiniteFieldRootContext GF2_72.ConcreteField GF2_72.shoupTraceContext

/-- GS field-root backend over GF72 using Las Vegas trace splitting. -/
def gf2_72LasVegasFieldRootContext :
    FieldRootContext GF2_72.ConcreteField :=
  lasVegasFiniteFieldRootContextWithTrace GF2_72.ConcreteField
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
    GF2_72.finiteFieldContext gf2_72FieldEnumeration GF2_72.shoupTraceContext
    gf2_72LasVegasConfig gf2_72LasVegasProbeFamily

end Binary

end GuruswamiSudan

end CompPoly
