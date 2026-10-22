/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.CosetLde
public import CompPoly.Univariate.NTTFast.Packed.Plan
public import CompPoly.Fields.BabyBear.Fast
public import CompPoly.Fields.KoalaBear.Fast

/-! # Compiled packed transforms of the 32-bit Montgomery fields

`PackedNTT` and `PackedCosetLde` instances for KoalaBear and BabyBear. Each sets `run` to a
definition applying the generic `Native.run` or `Native.cosetLde` at the field's modulus, so the
compiler specializes the kernels here, with the field's constants as immediates, and this module
belongs to the CPU-targeted `CompPolyPackedNative` library.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The packed transform specialized to KoalaBear. -/
def runKoalaBear (tw : Array ByteArray) (logN : Nat) (parallel : Bool) (nInv : UInt32)
    (inverse : Bool) (a : ByteArray) : ByteArray :=
  Native.run KoalaBear.fieldSize tw logN parallel nInv inverse a

instance : PackedNTT KoalaBear.fieldSize := ⟨runKoalaBear, rfl⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The batched coset LDE specialized to KoalaBear. -/
def cosetLdeKoalaBear (P : LdePlan KoalaBear.fieldSize) (w : Nat) (ms : Array ByteArray) :
    Array ByteArray :=
  Native.cosetLde P w ms

instance : PackedCosetLde KoalaBear.fieldSize := ⟨cosetLdeKoalaBear, rfl⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The packed transform specialized to BabyBear. -/
def runBabyBear (tw : Array ByteArray) (logN : Nat) (parallel : Bool) (nInv : UInt32)
    (inverse : Bool) (a : ByteArray) : ByteArray :=
  Native.run BabyBear.fieldSize tw logN parallel nInv inverse a

instance : PackedNTT BabyBear.fieldSize := ⟨runBabyBear, rfl⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The batched coset LDE specialized to BabyBear. -/
def cosetLdeBabyBear (P : LdePlan BabyBear.fieldSize) (w : Nat) (ms : Array ByteArray) :
    Array ByteArray :=
  Native.cosetLde P w ms

instance : PackedCosetLde BabyBear.fieldSize := ⟨cosetLdeBabyBear, rfl⟩

end CompPoly.CPolynomial.NTTFast.Packed
