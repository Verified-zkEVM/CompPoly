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
    GF2_32.finiteFieldContext GF2_32.fieldEnumeration GF2_32.shoupTraceContext
    GF2_32.lasVegasConfig GF2_32.lasVegasProbeFamily

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
    GF2_48.finiteFieldContext GF2_48.fieldEnumeration GF2_48.shoupTraceContext
    GF2_48.lasVegasConfig GF2_48.lasVegasProbeFamily

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
    GF2_64.finiteFieldContext GF2_64.fieldEnumeration GF2_64.shoupTraceContext
    GF2_64.lasVegasConfig GF2_64.lasVegasProbeFamily

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
    GF2_72.finiteFieldContext GF2_72.fieldEnumeration GF2_72.shoupTraceContext
    GF2_72.lasVegasConfig GF2_72.lasVegasProbeFamily

end Binary

end GuruswamiSudan

end CompPoly
