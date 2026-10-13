/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Plan
public import CompPoly.Univariate.NTTFast.Packed.NativeLeaf
public import CompPoly.Univariate.NTTFast.Packed.Stages

/-! # Refinement of fused leaves and the remaining radix-two pass -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open CompPoly.PackedRepr (encode)

/-- Local final layers preserve the working array's length. -/
@[simp] theorem size_leaf16Stages [Field R] (t3 t2 t1 : Array R) (a : Array R)
    (base : Nat) : (Expressions.leaf16Stages t3 t2 t1 a base).size = a.size := by
  simp only [Expressions.leaf16Stages, size_layer16_1, size_layer16_2,
    size_layer16_4, size_layer16_8]

/-- The packed leaf loop's guarded body. -/
def rawLeafBlock (t3 t2 t1 : ByteArray) (base : Nat) (a : ByteArray) : ByteArray :=
  if h : 4 * (base + 15) + 3 < a.size ∧ a.size < USize.size ∧
      31 < t3.size ∧ t3.size < USize.size ∧ 15 < t2.size ∧ t2.size < USize.size ∧
      7 < t1.size ∧ t1.size < USize.size then
    Native.leaf16 t3 t2 t1 (USize.ofNatLT base (by omega)) a
      (by simpa only [USize.toNat_ofNatLT] using h)
  else a

/-- Valid packed leaves always enter the optimized branch and implement local DIF layers. -/
theorem rawLeafBlock_encode (t3 t2 t1 : Array KoalaBear.Fast.Field) (base : Nat)
    (a : Array KoalaBear.Fast.Field)
    (ha : (encode a).size < USize.size) (hs : base + 16 ≤ a.size)
    (ht3 : t3.size = 8) (ht2 : t2.size = 4) (ht1 : t1.size = 2)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) :
    rawLeafBlock (encode t3) (encode t2) (encode t1) base (encode a) =
      encode (Expressions.leaf16Stages t3 t2 t1 a base) := by
  have hsize := USize.le_size
  unfold rawLeafBlock
  have hg : 4 * (base + 15) + 3 < (encode a).size ∧
      (encode a).size < USize.size ∧
      31 < (encode t3).size ∧ (encode t3).size < USize.size ∧
      15 < (encode t2).size ∧ (encode t2).size < USize.size ∧
      7 < (encode t1).size ∧ (encode t1).size < USize.size := by
    simp only [size_encode_fields, ht3, ht2, ht1] at *
    omega
  rw [dite_eq_left hg, Native.leaf16_correct _ _ _ _ _ _ h3 h2 h1]
  simp only [USize.toNat_ofNatLT]

/-- The unpaired final radix-two block in packed storage. -/
def rawPairBlock (a : ByteArray) (block : Nat) : ByteArray :=
  let x := Native.read a (2 * block)
  let y := Native.read a (2 * block + 1)
  Native.write (Native.write a (2 * block) (add x y)) (2 * block + 1) (sub x y)

/-- The final two-coordinate kernel is one ordinary DIF butterfly. -/
theorem rawPairBlock_encode (a : Array KoalaBear.Fast.Field) (block : Nat)
    (ha : (encode a).size < USize.size) (hs : 2 * block + 2 ≤ a.size) :
    rawPairBlock (encode a) block =
      encode (Plan.butterflyDIFInner #[1] 1 0 (2 * block) (2 * block + 1) a) := by
  unfold rawPairBlock
  rw [Native.read_encode _ _ ha (by omega), Native.read_encode _ _ ha (by omega)]
  dsimp only
  rw [add_val, sub_val, Native.write_encode _ _ ha (by omega)]
  rw [Native.write_encode _ _ (by simpa only [size_encode_fields, Array.size_setIfInBounds]
    using ha)
    (by simp only [Array.size_setIfInBounds]; omega)]
  simp only [Plan.butterflyDIFInner, Nat.zero_lt_one, ↓reduceIte,
    Array.getD_eq_getD_getElem?, Array.getElem?_singleton, Option.getD_some,
    MulOneClass.one_mul, Nat.lt_irrefl, Array.set!_eq_setIfInBounds]

/-- Complete final-layer blocks preserve packing throughout their traversal. -/
theorem fold_rawLeafBlock_encode (t3 t2 t1 : Array KoalaBear.Fast.Field) (blocks : Nat)
    (a : Array KoalaBear.Fast.Field)
    (ha : (encode a).size < USize.size) (hs : blocks * 16 ≤ a.size)
    (ht3 : t3.size = 8) (ht2 : t2.size = 4) (ht1 : t1.size = 2)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) :
    (List.range blocks).foldl (fun b block ↦
      rawLeafBlock (encode t3) (encode t2) (encode t1) (block * 16) b) (encode a) =
      encode ((List.range blocks).foldl (fun b block ↦
        Expressions.leaf16Stages t3 t2 t1 b (block * 16)) a) := by
  apply foldl_encode (List.range blocks) (fun b ↦ b.size = a.size)
  · intro block hb b hbs
    have hb' := List.mem_range.mp hb
    exact rawLeafBlock_encode t3 t2 t1 (block * 16) b
      (by simpa only [size_encode_fields, hbs] using ha) (by omega)
      ht3 ht2 ht1 h3 h2 h1
  · intro block hb b hbs
    rw [size_leaf16Stages, hbs]
  · rfl

/-- The remaining scalar final pass transports through packing. -/
theorem fold_rawPairBlock_encode (a : Array KoalaBear.Fast.Field) (blocks : Nat)
    (ha : (encode a).size < USize.size) (hs : blocks * 2 ≤ a.size) :
    (List.range blocks).foldl rawPairBlock (encode a) =
      encode ((List.range blocks).foldl (fun b block ↦
        Plan.butterflyDIFInner #[1] 1 0 (2 * block) (2 * block + 1) b) a) := by
  apply foldl_encode (List.range blocks) (fun b ↦ b.size = a.size)
  · intro block hb b hbs
    have hb' := List.mem_range.mp hb
    exact rawPairBlock_encode b block
      (by simpa only [size_encode_fields, hbs] using ha) (by omega)
  · intro block hb b hbs
    simpa only [Plan.size_butterflyDIFInner] using hbs
  · rfl

end CompPoly.CPolynomial.NTTFast.Packed
