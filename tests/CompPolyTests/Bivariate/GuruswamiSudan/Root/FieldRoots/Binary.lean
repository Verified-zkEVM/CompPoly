/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.Binary

/-!
# Binary-Field GS Field-Root Tests

Contract-level smoke tests for the smooth and Shoup GS field-root adapters over
`GF(2^32)`, `GF(2^48)`, `GF(2^64)`, and `GF(2^72)`.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.GuruswamiSudan
open CompPoly.GuruswamiSudan.Binary

namespace GuruswamiSudan.Root.FieldRoots.Binary

private abbrev F32 := GF2_32.ConcreteField

private abbrev F48 := GF2_48.ConcreteField

private abbrev F64 := GF2_64.ConcreteField

private abbrev F72 := GF2_72.ConcreteField

noncomputable example : FieldRootContext F32 :=
  gf2_32SmoothFieldRootContext

noncomputable example : FieldRootContext F32 :=
  gf2_32SmoothSubproductFieldRootContext

noncomputable example : FieldRootContext F32 :=
  gf2_32ShoupFieldRootContext

noncomputable example : FieldRootContext F32 :=
  gf2_32LasVegasFieldRootContext

noncomputable example : FieldRootContext F48 :=
  gf2_48SmoothFieldRootContext

noncomputable example : FieldRootContext F48 :=
  gf2_48SmoothSubproductFieldRootContext

noncomputable example : FieldRootContext F48 :=
  gf2_48ShoupFieldRootContext

noncomputable example : FieldRootContext F48 :=
  gf2_48LasVegasFieldRootContext

noncomputable example : FieldRootContext F64 :=
  gf2_64SmoothFieldRootContext

noncomputable example : FieldRootContext F64 :=
  gf2_64SmoothSubproductFieldRootContext

noncomputable example : FieldRootContext F64 :=
  gf2_64ShoupFieldRootContext

noncomputable example : FieldRootContext F64 :=
  gf2_64LasVegasFieldRootContext

noncomputable example : FieldRootContext F72 :=
  gf2_72SmoothFieldRootContext

noncomputable example : FieldRootContext F72 :=
  gf2_72SmoothSubproductFieldRootContext

noncomputable example : FieldRootContext F72 :=
  gf2_72ShoupFieldRootContext

noncomputable example : FieldRootContext F72 :=
  gf2_72LasVegasFieldRootContext

noncomputable example (p : CPolynomial F32) (a : F32)
    (hmem : a ∈ (gf2_32SmoothFieldRootContext.rootsInField p).toList) :
    CPolynomial.eval a p = 0 :=
  gf2_32SmoothFieldRootContext.sound p a hmem

noncomputable example (p : CPolynomial F32) (a : F32) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    a ∈ (gf2_32SmoothFieldRootContext.rootsInField p).toList :=
  gf2_32SmoothFieldRootContext.complete p a hp hroot

noncomputable example (p : CPolynomial F32) (a : F32)
    (hmem : a ∈ (gf2_32SmoothSubproductFieldRootContext.rootsInField p).toList) :
    CPolynomial.eval a p = 0 :=
  gf2_32SmoothSubproductFieldRootContext.sound p a hmem

noncomputable example (p : CPolynomial F32) (a : F32) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    a ∈ (gf2_32SmoothSubproductFieldRootContext.rootsInField p).toList :=
  gf2_32SmoothSubproductFieldRootContext.complete p a hp hroot

noncomputable example (p : CPolynomial F32) (a : F32)
    (hmem : a ∈ (gf2_32ShoupFieldRootContext.rootsInField p).toList) :
    CPolynomial.eval a p = 0 :=
  gf2_32ShoupFieldRootContext.sound p a hmem

noncomputable example (p : CPolynomial F32) (a : F32) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    a ∈ (gf2_32ShoupFieldRootContext.rootsInField p).toList :=
  gf2_32ShoupFieldRootContext.complete p a hp hroot

noncomputable example (p : CPolynomial F48) (a : F48)
    (hmem : a ∈ (gf2_48SmoothFieldRootContext.rootsInField p).toList) :
    CPolynomial.eval a p = 0 :=
  gf2_48SmoothFieldRootContext.sound p a hmem

noncomputable example (p : CPolynomial F48) (a : F48) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    a ∈ (gf2_48SmoothFieldRootContext.rootsInField p).toList :=
  gf2_48SmoothFieldRootContext.complete p a hp hroot

noncomputable example (p : CPolynomial F48) (a : F48)
    (hmem : a ∈ (gf2_48SmoothSubproductFieldRootContext.rootsInField p).toList) :
    CPolynomial.eval a p = 0 :=
  gf2_48SmoothSubproductFieldRootContext.sound p a hmem

noncomputable example (p : CPolynomial F48) (a : F48) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    a ∈ (gf2_48SmoothSubproductFieldRootContext.rootsInField p).toList :=
  gf2_48SmoothSubproductFieldRootContext.complete p a hp hroot

noncomputable example (p : CPolynomial F48) (a : F48)
    (hmem : a ∈ (gf2_48ShoupFieldRootContext.rootsInField p).toList) :
    CPolynomial.eval a p = 0 :=
  gf2_48ShoupFieldRootContext.sound p a hmem

noncomputable example (p : CPolynomial F48) (a : F48) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    a ∈ (gf2_48ShoupFieldRootContext.rootsInField p).toList :=
  gf2_48ShoupFieldRootContext.complete p a hp hroot

noncomputable example (p : CPolynomial F64) (a : F64)
    (hmem : a ∈ (gf2_64SmoothFieldRootContext.rootsInField p).toList) :
    CPolynomial.eval a p = 0 :=
  gf2_64SmoothFieldRootContext.sound p a hmem

noncomputable example (p : CPolynomial F64) (a : F64) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    a ∈ (gf2_64SmoothFieldRootContext.rootsInField p).toList :=
  gf2_64SmoothFieldRootContext.complete p a hp hroot

noncomputable example (p : CPolynomial F64) (a : F64)
    (hmem : a ∈ (gf2_64SmoothSubproductFieldRootContext.rootsInField p).toList) :
    CPolynomial.eval a p = 0 :=
  gf2_64SmoothSubproductFieldRootContext.sound p a hmem

noncomputable example (p : CPolynomial F64) (a : F64) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    a ∈ (gf2_64SmoothSubproductFieldRootContext.rootsInField p).toList :=
  gf2_64SmoothSubproductFieldRootContext.complete p a hp hroot

noncomputable example (p : CPolynomial F64) (a : F64)
    (hmem : a ∈ (gf2_64ShoupFieldRootContext.rootsInField p).toList) :
    CPolynomial.eval a p = 0 :=
  gf2_64ShoupFieldRootContext.sound p a hmem

noncomputable example (p : CPolynomial F64) (a : F64) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    a ∈ (gf2_64ShoupFieldRootContext.rootsInField p).toList :=
  gf2_64ShoupFieldRootContext.complete p a hp hroot

noncomputable example (p : CPolynomial F72) (a : F72)
    (hmem : a ∈ (gf2_72SmoothFieldRootContext.rootsInField p).toList) :
    CPolynomial.eval a p = 0 :=
  gf2_72SmoothFieldRootContext.sound p a hmem

noncomputable example (p : CPolynomial F72) (a : F72) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    a ∈ (gf2_72SmoothFieldRootContext.rootsInField p).toList :=
  gf2_72SmoothFieldRootContext.complete p a hp hroot

noncomputable example (p : CPolynomial F72) (a : F72)
    (hmem : a ∈ (gf2_72SmoothSubproductFieldRootContext.rootsInField p).toList) :
    CPolynomial.eval a p = 0 :=
  gf2_72SmoothSubproductFieldRootContext.sound p a hmem

noncomputable example (p : CPolynomial F72) (a : F72) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    a ∈ (gf2_72SmoothSubproductFieldRootContext.rootsInField p).toList :=
  gf2_72SmoothSubproductFieldRootContext.complete p a hp hroot

noncomputable example (p : CPolynomial F72) (a : F72)
    (hmem : a ∈ (gf2_72ShoupFieldRootContext.rootsInField p).toList) :
    CPolynomial.eval a p = 0 :=
  gf2_72ShoupFieldRootContext.sound p a hmem

noncomputable example (p : CPolynomial F72) (a : F72) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    a ∈ (gf2_72ShoupFieldRootContext.rootsInField p).toList :=
  gf2_72ShoupFieldRootContext.complete p a hp hroot

end GuruswamiSudan.Root.FieldRoots.Binary

end CompPolyTests
