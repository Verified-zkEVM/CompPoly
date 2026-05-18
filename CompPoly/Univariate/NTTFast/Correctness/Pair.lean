/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTTFast.Correctness.Radix4DIF

/-!
# Paired forward NTTFast correctness

Correctness proof for running the paired radix-4 DIF stage loop as two independent transforms.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast

open scoped BigOperators

variable {R : Type*} [Field R]

namespace Plan
set_option maxHeartbeats 800000 in
private theorem butterflyDIFPairInner_eq_pair
    (twiddles : Array R) :
    ∀ n limit j i0 i1 (accA accB : Array R),
      limit = j + n →
        butterflyDIFPairInner twiddles limit j i0 i1 accA accB =
          (butterflyDIFInner twiddles limit j i0 i1 accA,
            butterflyDIFInner twiddles limit j i0 i1 accB)
  | 0, limit, j, i0, i1, accA, accB, hlimit => by
      have hj : ¬ j < limit := by omega
      simp [butterflyDIFPairInner, butterflyDIFInner, hj]
  | n + 1, limit, j, i0, i1, accA, accB, hlimit => by
      have hj : j < limit := by omega
      have htail : limit = j + 1 + n := by omega
      let nextA :=
        ((accA.set! i0 (accA.getD i0 0 + accA.getD i1 0)).set! i1
          (twiddles.getD j 0 * (accA.getD i0 0 - accA.getD i1 0)))
      let nextB :=
        ((accB.set! i0 (accB.getD i0 0 + accB.getD i1 0)).set! i1
          (twiddles.getD j 0 * (accB.getD i0 0 - accB.getD i1 0)))
      have ih := butterflyDIFPairInner_eq_pair twiddles n limit (j + 1) (i0 + 1)
        (i1 + 1) nextA nextB htail
      rw [butterflyDIFPairInner]
      nth_rewrite 1 [butterflyDIFInner]
      nth_rewrite 2 [butterflyDIFInner]
      simp only [hj, ↓reduceIte]
      change butterflyDIFPairInner twiddles limit (j + 1) (i0 + 1) (i1 + 1) nextA
          nextB =
        (butterflyDIFInner twiddles limit (j + 1) (i0 + 1) (i1 + 1) nextA,
          butterflyDIFInner twiddles limit (j + 1) (i0 + 1) (i1 + 1) nextB)
      exact ih

set_option maxHeartbeats 800000 in
private theorem butterflyDIFPairBlocks_eq_pair
    (twiddles : Array R) (blockSize half : Nat) :
    ∀ n blocks block (accA accB : Array R),
      blocks = block + n →
        butterflyDIFPairBlocks twiddles blockSize half blocks block accA accB =
          (butterflyDIFBlocks twiddles blockSize half blocks block accA,
            butterflyDIFBlocks twiddles blockSize half blocks block accB)
  | 0, blocks, block, accA, accB, hblocks => by
      have hblock : ¬ block < blocks := by omega
      simp [butterflyDIFPairBlocks, butterflyDIFBlocks, hblock]
  | n + 1, blocks, block, accA, accB, hblocks => by
      have hblock : block < blocks := by omega
      have htail : blocks = block + 1 + n := by omega
      let base := block * blockSize
      have hinner := butterflyDIFPairInner_eq_pair twiddles half half 0 base
        (base + half) accA accB (by simp)
      have ih := butterflyDIFPairBlocks_eq_pair twiddles blockSize half n blocks
        (block + 1)
        (butterflyDIFInner twiddles half 0 base (base + half) accA)
        (butterflyDIFInner twiddles half 0 base (base + half) accB) htail
      rw [butterflyDIFPairBlocks]
      nth_rewrite 1 [butterflyDIFBlocks]
      nth_rewrite 2 [butterflyDIFBlocks]
      simp only [hblock, ↓reduceIte]
      rw [hinner]
      exact ih

private theorem butterflyStageDIFPairWithTwiddles_eq_pair
    (D : NTT.Domain R) (stage : Nat) (twiddles : Array R) (a b : Array R) :
    butterflyStageDIFPairWithTwiddles D stage twiddles a b =
      (butterflyStageDIFWithTwiddles D stage twiddles a,
        butterflyStageDIFWithTwiddles D stage twiddles b) := by
  unfold butterflyStageDIFPairWithTwiddles butterflyStageDIFWithTwiddles
  exact butterflyDIFPairBlocks_eq_pair twiddles (2 ^ (stage + 1)) (2 ^ stage)
    (D.n / 2 ^ (stage + 1)) (D.n / 2 ^ (stage + 1)) 0 a b (by simp)

set_option maxHeartbeats 800000 in
private theorem butterflyDIFRadix4PairInner_eq_pair
    (twiddlesHigh twiddlesLow : Array R) :
    ∀ n limit j i0 i1 i2 i3 (accA accB : Array R),
      limit = j + n →
        butterflyDIFRadix4PairInner twiddlesHigh twiddlesLow limit j i0 i1 i2 i3
            accA accB =
          (butterflyDIFRadix4Inner twiddlesHigh twiddlesLow limit j i0 i1 i2 i3 accA,
            butterflyDIFRadix4Inner twiddlesHigh twiddlesLow limit j i0 i1 i2 i3 accB)
  | 0, limit, j, i0, i1, i2, i3, accA, accB, hlimit => by
      have hj : ¬ j < limit := by omega
      simp [butterflyDIFRadix4PairInner, butterflyDIFRadix4Inner, hj]
  | n + 1, limit, j, i0, i1, i2, i3, accA, accB, hlimit => by
      have hj : j < limit := by omega
      have htail : limit = j + 1 + n := by omega
      let wHigh0 := twiddlesHigh.getD j 0
      let wHigh1 := twiddlesHigh.getD (j + limit) 0
      let wLow := twiddlesLow.getD j 0
      let x0A := accA.getD i0 0
      let x1A := accA.getD i1 0
      let x2A := accA.getD i2 0
      let x3A := accA.getD i3 0
      let a0A := x0A + x2A
      let a2A := wHigh0 * (x0A - x2A)
      let a1A := x1A + x3A
      let a3A := wHigh1 * (x1A - x3A)
      let nextA := (((accA.set! i0 (a0A + a1A)).set! i1 (wLow * (a0A - a1A))).set!
        i2 (a2A + a3A)).set! i3 (wLow * (a2A - a3A))
      let x0B := accB.getD i0 0
      let x1B := accB.getD i1 0
      let x2B := accB.getD i2 0
      let x3B := accB.getD i3 0
      let a0B := x0B + x2B
      let a2B := wHigh0 * (x0B - x2B)
      let a1B := x1B + x3B
      let a3B := wHigh1 * (x1B - x3B)
      let nextB := (((accB.set! i0 (a0B + a1B)).set! i1 (wLow * (a0B - a1B))).set!
        i2 (a2B + a3B)).set! i3 (wLow * (a2B - a3B))
      have ih := butterflyDIFRadix4PairInner_eq_pair twiddlesHigh twiddlesLow n
        limit (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1) nextA nextB htail
      rw [butterflyDIFRadix4PairInner]
      nth_rewrite 1 [butterflyDIFRadix4Inner]
      nth_rewrite 2 [butterflyDIFRadix4Inner]
      simp only [hj, ↓reduceIte]
      change
        butterflyDIFRadix4PairInner twiddlesHigh twiddlesLow limit (j + 1) (i0 + 1)
            (i1 + 1) (i2 + 1) (i3 + 1) nextA nextB =
          (butterflyDIFRadix4Inner twiddlesHigh twiddlesLow limit (j + 1) (i0 + 1)
              (i1 + 1) (i2 + 1) (i3 + 1) nextA,
            butterflyDIFRadix4Inner twiddlesHigh twiddlesLow limit (j + 1) (i0 + 1)
              (i1 + 1) (i2 + 1) (i3 + 1) nextB)
      exact ih

set_option maxHeartbeats 800000 in
private theorem butterflyDIFRadix4PairBlocks_eq_pair
    (twiddlesHigh twiddlesLow : Array R) (blockSize quarter : Nat) :
    ∀ n blocks block (accA accB : Array R),
      blocks = block + n →
        butterflyDIFRadix4PairBlocks twiddlesHigh twiddlesLow blockSize quarter blocks block
            accA accB =
          (butterflyDIFRadix4Blocks twiddlesHigh twiddlesLow blockSize quarter blocks block accA,
            butterflyDIFRadix4Blocks twiddlesHigh twiddlesLow blockSize quarter blocks block accB)
  | 0, blocks, block, accA, accB, hblocks => by
      have hblock : ¬ block < blocks := by omega
      simp [butterflyDIFRadix4PairBlocks, butterflyDIFRadix4Blocks, hblock]
  | n + 1, blocks, block, accA, accB, hblocks => by
      have hblock : block < blocks := by omega
      have htail : blocks = block + 1 + n := by omega
      let base := block * blockSize
      have hinner := butterflyDIFRadix4PairInner_eq_pair twiddlesHigh twiddlesLow
        quarter quarter 0 base (base + quarter) (base + 2 * quarter)
        (base + 3 * quarter) accA accB (by simp)
      have ih := butterflyDIFRadix4PairBlocks_eq_pair twiddlesHigh twiddlesLow
        blockSize quarter n blocks (block + 1)
        (butterflyDIFRadix4Inner twiddlesHigh twiddlesLow quarter 0 base
          (base + quarter) (base + 2 * quarter) (base + 3 * quarter) accA)
        (butterflyDIFRadix4Inner twiddlesHigh twiddlesLow quarter 0 base
          (base + quarter) (base + 2 * quarter) (base + 3 * quarter) accB) htail
      rw [butterflyDIFRadix4PairBlocks]
      nth_rewrite 1 [butterflyDIFRadix4Blocks]
      nth_rewrite 2 [butterflyDIFRadix4Blocks]
      simp only [hblock, ↓reduceIte]
      rw [hinner]
      exact ih

private theorem butterflyRadix4StageDIFPairWithTwiddles_eq_pair
    (D : NTT.Domain R) (lowStage : Nat) (twiddlesHigh twiddlesLow : Array R)
    (a b : Array R) :
    butterflyRadix4StageDIFPairWithTwiddles D lowStage twiddlesHigh twiddlesLow a b =
      (butterflyRadix4StageDIFWithTwiddles D lowStage twiddlesHigh twiddlesLow a,
        butterflyRadix4StageDIFWithTwiddles D lowStage twiddlesHigh twiddlesLow b) := by
  unfold butterflyRadix4StageDIFPairWithTwiddles butterflyRadix4StageDIFWithTwiddles
  exact butterflyDIFRadix4PairBlocks_eq_pair twiddlesHigh twiddlesLow
    (2 ^ (lowStage + 2)) (2 ^ lowStage) (D.n / 2 ^ (lowStage + 2))
    (D.n / 2 ^ (lowStage + 2)) 0 a b (by simp)

/-- The paired radix-4 DIF stage loop is extensionally two independent stage loops. -/
theorem runStagesDIFRadix4PairWithTwiddles_eq_pair
    (D : NTT.Domain R) (a b : Array R) :
    runStagesDIFRadix4PairWithTwiddles D (twiddleTable D)
        (loadNatural D a) (loadNatural D b) =
      (runStagesDIFRadix4WithTwiddles D (twiddleTable D) (loadNatural D a),
        runStagesDIFRadix4WithTwiddles D (twiddleTable D) (loadNatural D b)) := by
  have hfoldFst :
      ∀ xs (accA accB : Array R),
        (List.foldl
            (fun (acc : MProd (Array R) (Array R)) pass =>
              ⟨(butterflyRadix4StageDIFPairWithTwiddles D
                    (D.logN - 1 - 2 * pass - 1)
                    ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                    ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[])
                    acc.fst acc.snd).1,
                (butterflyRadix4StageDIFPairWithTwiddles D
                    (D.logN - 1 - 2 * pass - 1)
                    ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                    ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[])
                    acc.fst acc.snd).2⟩)
            (⟨accA, accB⟩ : MProd (Array R) (Array R)) xs).fst =
          List.foldl
            (fun acc pass =>
              butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) acc)
            accA xs := by
    intro xs
    induction xs with
    | nil =>
        intro accA accB
        simp
    | cons pass rest ih =>
        intro accA accB
        simp only [List.foldl_cons]
        rw [show
            (⟨(butterflyRadix4StageDIFPairWithTwiddles D
                (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA accB).1,
              (butterflyRadix4StageDIFPairWithTwiddles D
                (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA accB).2⟩ :
                MProd (Array R) (Array R)) =
            ⟨butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA,
              butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accB⟩ by
          simp [butterflyRadix4StageDIFPairWithTwiddles_eq_pair]]
        exact ih
          (butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
            ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
            ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA)
          (butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
            ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
            ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accB)
  have hfoldSnd :
      ∀ xs (accA accB : Array R),
        (List.foldl
            (fun (acc : MProd (Array R) (Array R)) pass =>
              ⟨(butterflyRadix4StageDIFPairWithTwiddles D
                    (D.logN - 1 - 2 * pass - 1)
                    ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                    ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[])
                    acc.fst acc.snd).1,
                (butterflyRadix4StageDIFPairWithTwiddles D
                    (D.logN - 1 - 2 * pass - 1)
                    ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                    ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[])
                    acc.fst acc.snd).2⟩)
            (⟨accA, accB⟩ : MProd (Array R) (Array R)) xs).snd =
          List.foldl
            (fun acc pass =>
              butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) acc)
            accB xs := by
    intro xs
    induction xs with
    | nil =>
        intro accA accB
        simp
    | cons pass rest ih =>
        intro accA accB
        simp only [List.foldl_cons]
        rw [show
            (⟨(butterflyRadix4StageDIFPairWithTwiddles D
                (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA accB).1,
              (butterflyRadix4StageDIFPairWithTwiddles D
                (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA accB).2⟩ :
                MProd (Array R) (Array R)) =
            ⟨butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA,
              butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accB⟩ by
          simp [butterflyRadix4StageDIFPairWithTwiddles_eq_pair]]
        exact ih
          (butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
            ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
            ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA)
          (butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
            ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
            ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accB)
  by_cases hodd : D.logN % 2 = 1
  · simp [runStagesDIFRadix4PairWithTwiddles, runStagesDIFRadix4WithTwiddles,
      hodd, butterflyStageDIFPairWithTwiddles_eq_pair]
    constructor
    · congr 1
      simpa only [Prod.fst, Prod.snd] using
        hfoldFst (List.range' 0 (D.logN / 2)) (loadNatural D a)
        (loadNatural D b)
    · congr 1
      simpa only [Prod.fst, Prod.snd] using
        hfoldSnd (List.range' 0 (D.logN / 2)) (loadNatural D a)
        (loadNatural D b)
  · simp [runStagesDIFRadix4PairWithTwiddles, runStagesDIFRadix4WithTwiddles, hodd]
    constructor
    · simpa only [Prod.fst, Prod.snd] using
        hfoldFst (List.range' 0 (D.logN / 2)) (loadNatural D a)
        (loadNatural D b)
    · simpa only [Prod.fst, Prod.snd] using
        hfoldSnd (List.range' 0 (D.logN / 2)) (loadNatural D a)
        (loadNatural D b)

end Plan

end NTTFast
end CPolynomial
end CompPoly
