/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Correctness.Radix4DIF
public import CompPoly.Univariate.NTTFast.Packed.StageRefinement
public import CompPoly.Univariate.NTTFast.Packed.LocalLayers

/-! # Mathematical correctness of the fused sequential stage schedule -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Fusing the final sixteen-coordinate blocks is exactly two ordinary radix-four passes. -/
theorem fold_leaf16Stages_eq_radix4 [Field R] (t3 t2 t1 : Array R) (blocks : Nat)
    (a : Array R) (hs : blocks * 16 ≤ a.size) :
    (List.range blocks).foldl (fun b block ↦
      Expressions.leaf16Stages t3 t2 t1 b (block * 16)) a =
      Plan.butterflyDIFRadix4Blocks t1 #[1] 4 1 (4 * blocks) 0
        (Plan.butterflyDIFRadix4Blocks t3 t2 16 4 blocks 0 a) := by
  rw [fold_leaf16Stages]
  symm
  rw [Plan.butterflyDIFRadix4Blocks_eq_two_dif_blocks t1 #[1] 1 (4 * blocks) _
    (by decide) (by simp only [Plan.size_butterflyDIFRadix4Blocks]; omega),
    Plan.butterflyDIFRadix4Blocks_eq_two_dif_blocks t3 t2 4 blocks a (by decide) hs]
  simp only [← Nat.mul_assoc, Nat.reduceMul]

/-- The pass counter uses the same stage and block widths as the ordinary plan. -/
theorem fieldPass_eq_stage (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) (pass : Nat)
    (a : Array KoalaBear.Fast.Field) :
    fieldPass D.logN tw pass a =
      Plan.butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
        (tw.getD (D.logN - 1 - 2 * pass) #[]) (tw.getD (D.logN - 1 - 2 * pass - 1) #[]) a := by
  unfold fieldPass Plan.butterflyRadix4StageDIFWithTwiddles
  have he (k : Nat) : 2 ^ (k + 2) = 4 * 2 ^ k := by
    rw [Nat.pow_add]
    omega
  rw [he]
  rfl

/-- A one-coordinate twiddle table beginning at one is the identity table. -/
theorem twiddle_zero_eq_one (tw : Array KoalaBear.Fast.Field)
    (hs : tw.size = 1) (hone : tw.getD 0 0 = 1) : tw = #[1] := by
  apply Array.ext (by simpa only [Array.size_singleton] using hs)
  intro i hi hj
  have he : i = 0 := by omega
  subst i
  simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
    Option.getD_some, Array.getElem_singleton] using hone

/-- The ordinary complete radix-four schedule with an optional final radix-two layer. -/
def allFieldStages (logN : Nat) (tw : Array (Array KoalaBear.Fast.Field))
    (a : Array KoalaBear.Fast.Field) : Array KoalaBear.Fast.Field :=
  let b := (List.range (logN / 2)).foldl (fun b pass ↦ fieldPass logN tw pass b) a
  if logN % 2 = 1 then (List.range (2 ^ logN / 2)).foldl
    (fun b block ↦ Plan.butterflyDIFInner #[1] 1 0 (2 * block) (2 * block + 1) b) b else b

/-- The fused forward stage schedule equals the ordinary complete paired-pass schedule. -/
theorem fieldStages_unscaled_eq_all (logN : Nat) (tw : Array (Array KoalaBear.Fast.Field))
    (a : Array KoalaBear.Fast.Field) (factor : KoalaBear.Fast.Field)
    (htw : TwiddleSizes logN tw) (hone : TwiddleOnes logN tw) (hs : a.size = 2 ^ logN) :
    fieldStages logN tw a factor false = allFieldStages logN tw a := by
  by_cases hf : (decide (logN ≥ 4) && logN % 2 == 0) = true
  · have hf' := hf
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hf'
    obtain ⟨hlog, hmod⟩ := hf'
    let count := logN / 2 - 2
    let b := (List.range count).foldl (fun b pass ↦ fieldPass logN tw pass b) a
    have hbs : b.size = 2 ^ logN :=
      foldl_invariant (List.range count) (fun b ↦ b.size = 2 ^ logN)
        (fun b pass ↦ fieldPass logN tw pass b)
        (fun pass hp b hb ↦ by simpa only [size_fieldPass] using hb) a hs
    have h3 : logN - 1 - 2 * count = 3 := by unfold count; omega
    have h1 : logN - 1 - 2 * (count + 1) = 1 := by unfold count; omega
    have hzero : tw.getD 0 #[] = #[1] :=
      twiddle_zero_eq_one _ (by simpa using htw 0 (by omega)) (hone 0 (by omega))
    have hd : 16 ∣ 2 ^ logN := by simpa using Nat.pow_dvd_pow 2 hlog
    have hdiv := Nat.div_mul_cancel hd
    have hquarters : 2 ^ logN / 4 = 4 * (2 ^ logN / 16) := by omega
    have hrange : List.range (logN / 2) = List.range count ++ [count, count + 1] := by
      have he : logN / 2 = count + 2 := by unfold count; omega
      rw [he, List.range_succ, List.range_succ, List.append_assoc]
      rfl
    simp only [fieldStages, allFieldStages]
    simp only [hf, ite_true]
    simp only [hmod, Nat.zero_ne_one, ite_false]
    change (List.range (2 ^ logN / 16)).foldl (fun b block ↦
      leafBlock (tw.getD 3 #[]) (tw.getD 2 #[]) (tw.getD 1 #[])
        (block * 16) factor false b) b = _
    simp only [leafBlock, Bool.false_eq_true, ite_false]
    rw [fold_leaf16Stages_eq_radix4 _ _ _ _ b (by rw [hbs]; exact Nat.div_mul_le_self _ _)]
    rw [hrange, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil]
    change _ = fieldPass logN tw (count + 1) (fieldPass logN tw count b)
    simp only [fieldPass, h3, h1, Nat.reduceSub, Nat.reducePow, hzero, hquarters]
  · simp only [fieldStages, allFieldStages, hf, Bool.false_eq_true, ite_false]

/-- The array schedule uses the ordinary plan's exact sequence of stages. -/
theorem allFieldStages_eq_plan (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (htw : TwiddleSizes D.logN tw) (hone : TwiddleOnes D.logN tw) :
    allFieldStages D.logN tw a = Plan.runStagesDIFRadix4WithTwiddles D tw a := by
  simp only [allFieldStages, Plan.runStagesDIFRadix4WithTwiddles,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure, ← apply_ite]
  simp_rw [fieldPass_eq_stage]
  by_cases ho : D.logN % 2 = 1
  · have hpos : 0 < D.logN := by omega
    have hzero : tw.getD 0 #[] = #[1] :=
      twiddle_zero_eq_one _ (by simpa using htw 0 hpos) (hone 0 hpos)
    simp only [ho, ite_true, hzero, Plan.butterflyStageDIFWithTwiddles,
      Nat.zero_add, Nat.pow_one, Nat.pow_zero]
    symm
    simpa only [NTT.Domain.n, ← List.range_eq_range', Nat.mul_one, Nat.mul_comm 2] using
      Plan.butterflyDIFBlocks_eq_foldl_inner #[1] 2 1 (D.n / 2) (D.n / 2) 0
        ((List.range (D.logN / 2)).foldl (fun b pass ↦
          Plan.butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
            (tw.getD (D.logN - 1 - 2 * pass) #[])
            (tw.getD (D.logN - 1 - 2 * pass - 1) #[]) b) a) (by omega)
  · simp only [ho, ite_false]

/-- Ordinary cached domain twiddles satisfy both packed-stage invariants. -/
theorem twiddleTable_invariants (D : NTT.Domain KoalaBear.Fast.Field) :
    TwiddleSizes D.logN (Plan.twiddleTable D) ∧
      TwiddleOnes D.logN (Plan.twiddleTable D) := by
  constructor
  · intro stage hs
    rw [Plan.twiddleTable_getD_eq_twiddlePowers D stage hs, Plan.twiddlePowers_size]
  · intro stage hs
    rw [Plan.twiddleTable_getD_eq_twiddlePowers D stage hs,
      Plan.twiddlePowers_getD_eq_pow D stage 0 (Nat.two_pow_pos stage), pow_zero]

/-- Without fused normalization, the packed sequential pipeline implements the verified DIF plan. -/
theorem Native.stages_unscaled_correct (D : NTT.Domain KoalaBear.Fast.Field)
    (a : Array KoalaBear.Fast.Field) (factor : KoalaBear.Fast.Field)
    (hs : a.size = D.n) (hu : 4 * D.n < USize.size) :
    Native.stages D.logN ((Plan.twiddleTable D).map packFields) (packFields a)
      factor.val false = packFields (Plan.runStagesDIFRadix4WithTwiddles D
        (Plan.twiddleTable D) a) := by
  obtain ⟨htw, hone⟩ := twiddleTable_invariants D
  rw [Native.stages_packFields _ _ _ _ _ htw hone hs hu,
    fieldStages_unscaled_eq_all _ _ _ _ htw hone hs, allFieldStages_eq_plan D _ a htw hone]

end CompPoly.CPolynomial.NTTFast.Packed
