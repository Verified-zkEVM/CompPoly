/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.StageTail

/-! # Complete packed sequential-stage refinement -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- The packed implementation's paired-pass body. -/
def rawPass (logN : Nat) (tw : Array ByteArray) (pass : Nat) (a : ByteArray) : ByteArray :=
  let high := logN - 1 - 2 * pass
  let low := high - 1
  let q := 2 ^ low
  (List.range (2 ^ logN / (4 * q))).foldl (fun b block ↦
    Native.inner16 (tw.getD high ByteArray.empty) (tw.getD low ByteArray.empty) q 0
      (block * (4 * q)) (block * (4 * q) + q)
      (block * (4 * q) + 2 * q) (block * (4 * q) + 3 * q) b) a

/-- Re-expressing the sequential loop as folds changes no implementation semantics. -/
theorem Native.stages_eq_folds (logN : Nat) (tw : Array ByteArray) (a : ByteArray)
    (factor : UInt32) (normalize : Bool) :
    Native.stages logN tw a factor normalize =
      let fused := logN ≥ 4 && logN % 2 == 0
      let b := (List.range (if fused then logN / 2 - 2 else logN / 2)).foldl
        (fun b pass ↦ rawPass logN tw pass b) a
      let c := if fused then (List.range (2 ^ logN / 16)).foldl
        (fun b block ↦ rawLeafBlock (tw.getD 3 ByteArray.empty) (tw.getD 2 ByteArray.empty)
          (tw.getD 1 ByteArray.empty) (block * 16) factor normalize b) b else b
      if logN % 2 = 1 then (List.range (2 ^ logN / 2)).foldl rawPairBlock c else c := by
  simp only [Native.stages, rawPass, rawLeafBlock,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    List.forIn_pure_yield_eq_foldl, bind_pure, pure_bind, Id.run_pure,
    ← apply_ite, ← apply_dite]
  by_cases hf : (decide (logN ≥ 4) && logN % 2 == 0) = true <;>
    simp only [hf, ite_true] <;>
    by_cases ho : logN % 2 = 1 <;> simp only [ho, ite_true, ite_false] <;> rfl

/-- Every twiddle stage starts at the multiplicative identity. -/
def TwiddleOnes (logN : Nat) (tw : Array (Array KoalaBear.Fast.Field)) : Prop :=
  ∀ stage < logN, (tw.getD stage #[]).getD 0 0 = 1

/-- The array semantics of the packed sequential pipeline, expressed with ordinary DIF kernels. -/
def fieldStages (logN : Nat) (tw : Array (Array KoalaBear.Fast.Field))
    (a : Array KoalaBear.Fast.Field) (factor : KoalaBear.Fast.Field)
    (normalize : Bool) : Array KoalaBear.Fast.Field :=
  let fused := logN ≥ 4 && logN % 2 == 0
  let b := (List.range (if fused then logN / 2 - 2 else logN / 2)).foldl
    (fun b pass ↦ fieldPass logN tw pass b) a
  let c := if fused then (List.range (2 ^ logN / 16)).foldl
    (fun b block ↦ leafBlock (tw.getD 3 #[]) (tw.getD 2 #[]) (tw.getD 1 #[])
      (block * 16) factor normalize b) b else b
  if logN % 2 = 1 then (List.range (2 ^ logN / 2)).foldl
    (fun b block ↦ Plan.butterflyDIFInner #[1] 1 0 (2 * block) (2 * block + 1) b) c else c

/-- All sequential packed passes, fused leaves and scalar tails preserve field-array semantics. -/
theorem Native.stages_packFields (logN : Nat) (tw : Array (Array KoalaBear.Fast.Field))
    (a : Array KoalaBear.Fast.Field) (factor : KoalaBear.Fast.Field) (normalize : Bool)
    (htw : TwiddleSizes logN tw) (hone : TwiddleOnes logN tw)
    (hs : a.size = 2 ^ logN) (hu : 4 * 2 ^ logN < USize.size) :
    Native.stages logN (tw.map packFields) (packFields a) factor.val normalize =
      packFields (fieldStages logN tw a factor normalize) := by
  let fused := logN ≥ 4 && logN % 2 == 0
  let count := if fused then logN / 2 - 2 else logN / 2
  let b := (List.range count).foldl (fun b pass ↦ fieldPass logN tw pass b) a
  have hc : count ≤ logN / 2 := by unfold count; split <;> omega
  have hprefix : (List.range count).foldl (fun b pass ↦
      rawPass logN (tw.map packFields) pass b) (packFields a) = packFields b :=
    Native.passes_packFields logN count tw a hc htw hs hu
  have hbs : b.size = 2 ^ logN :=
    foldl_invariant (List.range count) (fun b ↦ b.size = 2 ^ logN)
      (fun b pass ↦ fieldPass logN tw pass b)
      (fun pass hp b hb ↦ by simpa only [size_fieldPass] using hb) a hs
  let c := if fused then (List.range (2 ^ logN / 16)).foldl
    (fun b block ↦ leafBlock (tw.getD 3 #[]) (tw.getD 2 #[]) (tw.getD 1 #[])
      (block * 16) factor normalize b) b else b
  have hfinish : (if fused then (List.range (2 ^ logN / 16)).foldl
      (fun b block ↦ rawLeafBlock ((tw.map packFields).getD 3 ByteArray.empty)
        ((tw.map packFields).getD 2 ByteArray.empty)
        ((tw.map packFields).getD 1 ByteArray.empty)
        (block * 16) factor.val normalize b) (packFields b) else packFields b) =
      packFields c := by
    unfold c
    split
    · rename_i hf
      have hlog : 4 ≤ logN := by
        simp only [fused, Bool.and_eq_true, decide_eq_true_eq] at hf
        exact hf.1
      rw [getD_map_packFields, getD_map_packFields, getD_map_packFields]
      exact fold_rawLeafBlock_packFields _ _ _ _ _ _ b
        (by simpa only [size_packFields, hbs] using hu)
        (by rw [hbs]; exact Nat.div_mul_le_self _ _)
        (by simpa using htw 3 (by omega)) (by simpa using htw 2 (by omega))
        (by simpa using htw 1 (by omega))
        (hone 3 (by omega)) (hone 2 (by omega)) (hone 1 (by omega))
    · rfl
  have hcs : c.size = 2 ^ logN := by
    unfold c
    split
    · apply foldl_invariant (List.range (2 ^ logN / 16))
        (fun b : Array KoalaBear.Fast.Field ↦ b.size = 2 ^ logN)
      · intro block hb a ha
        have hb' := List.mem_range.mp hb
        have hbound := Nat.div_mul_le_self (2 ^ logN) 16
        rw [size_leafBlock _ _ _ _ _ _ _ (by omega)]
        exact ha
      · exact hbs
    · exact hbs
  rw [Native.stages_eq_folds]
  change (if logN % 2 = 1 then (List.range (2 ^ logN / 2)).foldl rawPairBlock
      (if fused then _ else _) else (if fused then _ else _)) = _
  rw [hprefix, hfinish]
  unfold fieldStages
  split
  · exact fold_rawPairBlock_packFields c _
      (by simpa only [size_packFields, hcs] using hu)
      (by rw [hcs]; exact Nat.div_mul_le_self _ _)
  · rfl

end CompPoly.CPolynomial.NTTFast.Packed
