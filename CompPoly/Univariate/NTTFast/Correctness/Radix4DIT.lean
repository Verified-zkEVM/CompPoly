/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTTFast.Correctness.Basic

/-!
# Radix-4 DIT NTTFast correctness

Correctness proofs for the mixed radix-4 decimation-in-time stage loop used by `NTTFast`.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast

open scoped BigOperators

variable {R : Type*} [Field R]

namespace Plan

private def ditButterfly (w : R) (i0 i1 : Nat) (acc : Array R) : Array R :=
  let u := acc.getD i0 0
  let t := w * acc.getD i1 0
  (acc.set! i0 (u + t)).set! i1 (u - t)

private theorem getD_ditButterfly_of_ne
    (w : R) (i0 i1 k : Nat) (acc : Array R) (hk0 : k ≠ i0) (hk1 : k ≠ i1) :
    (ditButterfly w i0 i1 acc).getD k 0 = acc.getD k 0 := by
  have h0 : i0 ≠ k := fun h => hk0 h.symm
  have h1 : i1 ≠ k := fun h => hk1 h.symm
  unfold ditButterfly
  simp only [Array.set!, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_setIfInBounds]
  simp [h1]
  rw [Array.getElem?_setIfInBounds]
  simp [h0]

private theorem ditButterfly_comm
    (acc : Array R) (w v : R) (i0 i1 j0 j1 : Nat)
    (h00 : i0 ≠ j0) (h01 : i0 ≠ j1) (h10 : i1 ≠ j0) (h11 : i1 ≠ j1) :
    ditButterfly w i0 i1 (ditButterfly v j0 j1 acc) =
      ditButterfly v j0 j1 (ditButterfly w i0 i1 acc) := by
  change
    (let u := (ditButterfly v j0 j1 acc).getD i0 0
     let t := w * (ditButterfly v j0 j1 acc).getD i1 0
     (((ditButterfly v j0 j1 acc).set! i0 (u + t)).set! i1 (u - t))) =
      (let u := (ditButterfly w i0 i1 acc).getD j0 0
       let t := v * (ditButterfly w i0 i1 acc).getD j1 0
       (((ditButterfly w i0 i1 acc).set! j0 (u + t)).set! j1 (u - t)))
  rw [getD_ditButterfly_of_ne v j0 j1 i0 acc h00 h01]
  rw [getD_ditButterfly_of_ne v j0 j1 i1 acc h10 h11]
  rw [getD_ditButterfly_of_ne w i0 i1 j0 acc h00.symm h10.symm]
  rw [getD_ditButterfly_of_ne w i0 i1 j1 acc h01.symm h11.symm]
  unfold ditButterfly
  simp only [Array.set!]
  rw [Array.setIfInBounds_comm _ _ h01.symm]
  rw [Array.setIfInBounds_comm _ _ h00.symm]
  rw [Array.setIfInBounds_comm _ _ h11.symm]
  rw [Array.setIfInBounds_comm _ _ h10.symm]

private theorem butterflyDITInner_eq_foldl_dit (twiddles : Array R) :
    ∀ n j i0 i1 (acc : Array R),
      butterflyDITInner twiddles (j + n) j i0 i1 acc =
        List.foldl
          (fun acc t => ditButterfly (twiddles.getD (j + t) 0) (i0 + t) (i1 + t) acc)
          acc (List.range' 0 n)
  | 0, j, i0, i1, acc => by
      simp [butterflyDITInner]
  | n + 1, j, i0, i1, acc => by
      have hj : j < j + (n + 1) := by omega
      have ih := butterflyDITInner_eq_foldl_dit twiddles n (j + 1) (i0 + 1) (i1 + 1)
        (ditButterfly (twiddles.getD j 0) i0 i1 acc)
      have hshift :
          List.foldl
              (fun acc t =>
                ditButterfly (twiddles.getD (j + 1 + t) 0) (i0 + 1 + t)
                  (i1 + 1 + t) acc)
              (ditButterfly (twiddles.getD j 0) i0 i1 acc) (List.range' 0 n) =
            List.foldl
              (fun acc t => ditButterfly (twiddles.getD (j + t) 0) (i0 + t) (i1 + t) acc)
              (ditButterfly (twiddles.getD j 0) i0 i1 acc) (List.range' 1 n) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (foldl_range'_succ_shift
            (fun t acc => ditButterfly (twiddles.getD (j + t) 0) (i0 + t) (i1 + t) acc)
            n 0 (ditButterfly (twiddles.getD j 0) i0 i1 acc))
      rw [butterflyDITInner]
      simp only [hj, ↓reduceIte]
      simpa [List.range'_succ, ditButterfly, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih.trans hshift

private theorem butterflyDITInner_comm
    (twiddlesA twiddlesB : Array R) (limitA limitB baseA halfA baseB halfB : Nat)
    (hcomm :
      ∀ i, i < limitA → ∀ j, j < limitB →
        baseA + i ≠ baseB + j ∧
        baseA + i ≠ baseB + halfB + j ∧
        baseA + halfA + i ≠ baseB + j ∧
        baseA + halfA + i ≠ baseB + halfB + j) :
    ∀ acc : Array R,
      butterflyDITInner twiddlesA limitA 0 baseA (baseA + halfA)
          (butterflyDITInner twiddlesB limitB 0 baseB (baseB + halfB) acc) =
        butterflyDITInner twiddlesB limitB 0 baseB (baseB + halfB)
          (butterflyDITInner twiddlesA limitA 0 baseA (baseA + halfA) acc) := by
  intro acc
  let foldA : Array R → Array R :=
    fun acc =>
      List.foldl
        (fun acc i => ditButterfly (twiddlesA.getD i 0) (baseA + i)
          (baseA + halfA + i) acc)
        acc (List.range limitA)
  let foldB : Array R → Array R :=
    fun acc =>
      List.foldl
        (fun acc j => ditButterfly (twiddlesB.getD j 0) (baseB + j)
          (baseB + halfB + j) acc)
        acc (List.range limitB)
  have hA (acc' : Array R) :
      butterflyDITInner twiddlesA limitA 0 baseA (baseA + halfA) acc' = foldA acc' := by
    simpa [foldA, List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (butterflyDITInner_eq_foldl_dit twiddlesA limitA 0 baseA (baseA + halfA) acc')
  have hB (acc' : Array R) :
      butterflyDITInner twiddlesB limitB 0 baseB (baseB + halfB) acc' = foldB acc' := by
    simpa [foldB, List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (butterflyDITInner_eq_foldl_dit twiddlesB limitB 0 baseB (baseB + halfB) acc')
  calc
    butterflyDITInner twiddlesA limitA 0 baseA (baseA + halfA)
        (butterflyDITInner twiddlesB limitB 0 baseB (baseB + halfB) acc) =
        foldA (foldB acc) := by
          rw [hB, hA]
    _ = List.foldl
          (fun acc j => ditButterfly (twiddlesB.getD j 0) (baseB + j)
            (baseB + halfB + j) acc)
          (List.foldl
            (fun acc i => ditButterfly (twiddlesA.getD i 0) (baseA + i)
              (baseA + halfA + i) acc)
            acc (List.range limitA))
          (List.range limitB) := by
          apply foldl_commute_foldl
          intro i j hi hj acc
          rcases hcomm i hi j hj with ⟨h00, h01, h10, h11⟩
          exact (ditButterfly_comm acc (twiddlesA.getD i 0) (twiddlesB.getD j 0)
            (baseA + i) (baseA + halfA + i) (baseB + j) (baseB + halfB + j)
            h00 h01 h10 h11).symm
    _ = butterflyDITInner twiddlesB limitB 0 baseB (baseB + halfB)
          (butterflyDITInner twiddlesA limitA 0 baseA (baseA + halfA) acc) := by
          rw [hA, hB]

private theorem butterflyDITBlocks_eq_foldl_inner
    (twiddles : Array R) (blockSize half blocks : Nat) :
    ∀ n block (acc : Array R),
      blocks = block + n →
      butterflyDITBlocks twiddles blockSize half blocks block acc =
        List.foldl
          (fun acc block =>
            butterflyDITInner twiddles half 0 (block * blockSize) (block * blockSize + half)
              acc)
          acc (List.range' block n)
  | 0, block, acc, hblocks => by
      have hnot : ¬block < blocks := by omega
      simp [butterflyDITBlocks, hnot]
  | n + 1, block, acc, hblocks => by
      have hblock : block < blocks := by omega
      have htail : blocks = block + 1 + n := by omega
      have ih := butterflyDITBlocks_eq_foldl_inner twiddles blockSize half blocks
        n (block + 1)
          (butterflyDITInner twiddles half 0 (block * blockSize) (block * blockSize + half)
            acc)
        htail
      rw [butterflyDITBlocks]
      simp only [hblock, ↓reduceIte]
      simpa [List.range'_succ] using ih

private def radix4Cell
    (wLow wHigh0 wHigh1 : R) (i0 i1 i2 i3 : Nat) (acc : Array R) : Array R :=
  let x0 := acc.getD i0 0
  let x1 := acc.getD i1 0
  let x2 := acc.getD i2 0
  let x3 := acc.getD i3 0
  let t1 := wLow * x1
  let t3 := wLow * x3
  let a0 := x0 + t1
  let a1 := x0 - t1
  let a2 := x2 + t3
  let a3 := x2 - t3
  let u2 := wHigh0 * a2
  let u3 := wHigh1 * a3
  (((acc.set! i0 (a0 + u2)).set! i1 (a1 + u3)).set! i2 (a0 - u2)).set! i3 (a1 - u3)

@[simp] private theorem size_radix4Cell
    (wLow wHigh0 wHigh1 : R) (i0 i1 i2 i3 : Nat) (acc : Array R) :
    (radix4Cell wLow wHigh0 wHigh1 i0 i1 i2 i3 acc).size = acc.size := by
  simp [radix4Cell, Array.set!, Array.size_setIfInBounds]

private theorem setIfInBounds_discard_four {α : Type*}
    (acc : Array α) (i0 i1 i2 i3 : Nat) (v0 v1 v2 v3 w0 w1 w2 w3 : α)
    (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h03 : i0 ≠ i3)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3) :
    (((((((acc.setIfInBounds i0 v0).setIfInBounds i1 v1).setIfInBounds i2 v2).setIfInBounds
          i3 v3).setIfInBounds i0 w0).setIfInBounds i2 w1).setIfInBounds i1
        w2).setIfInBounds i3 w3 =
      (((acc.setIfInBounds i0 w0).setIfInBounds i1 w2).setIfInBounds i2 w1).setIfInBounds
        i3 w3 := by
  rw [Array.setIfInBounds_comm v3 w0 h03.symm]
  rw [Array.setIfInBounds_comm v2 w0 h02.symm]
  rw [Array.setIfInBounds_comm v1 w0 h01.symm]
  rw [Array.setIfInBounds_setIfInBounds]
  rw [Array.setIfInBounds_comm v3 w1 h23.symm]
  rw [Array.setIfInBounds_setIfInBounds]
  rw [Array.setIfInBounds_comm v3 w2 h13.symm]
  rw [Array.setIfInBounds_comm w1 w2 h12.symm]
  rw [Array.setIfInBounds_setIfInBounds]
  rw [Array.setIfInBounds_setIfInBounds]

private theorem radix4Cell_eq_two_stage_cells
    (wLow wHigh0 wHigh1 : R) (i0 i1 i2 i3 : Nat) (acc : Array R)
    (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h03 : i0 ≠ i3)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3)
    (hi0 : i0 < acc.size) (hi1 : i1 < acc.size)
    (hi2 : i2 < acc.size) (hi3 : i3 < acc.size) :
    ditButterfly wHigh1 i1 i3
        (ditButterfly wHigh0 i0 i2
          (ditButterfly wLow i2 i3 (ditButterfly wLow i0 i1 acc))) =
      radix4Cell wLow wHigh0 wHigh1 i0 i1 i2 i3 acc := by
  unfold ditButterfly radix4Cell
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
    Array.size_setIfInBounds]
  simp [hi0, hi1, hi2, hi3, h01, h01.symm, h02, h02.symm, h03, h03.symm,
    h12, h12.symm, h13, h13.symm, h23, h23.symm]
  exact setIfInBounds_discard_four acc i0 i1 i2 i3 _ _ _ _ _ _ _ _
    h01 h02 h03 h12 h13 h23

private theorem butterflyDITRadix4Inner_eq_foldl_cell
    (twiddlesLow twiddlesHigh : Array R) :
    ∀ n j i0 i1 i2 i3 (acc : Array R),
      butterflyDITRadix4Inner twiddlesLow twiddlesHigh (j + n) j i0 i1 i2 i3 acc =
        List.foldl
          (fun acc t =>
            radix4Cell (twiddlesLow.getD (j + t) 0) (twiddlesHigh.getD (j + t) 0)
              (twiddlesHigh.getD (j + t + (j + n)) 0) (i0 + t) (i1 + t) (i2 + t)
              (i3 + t) acc)
          acc (List.range' 0 n)
  | 0, j, _i0, _i1, _i2, _i3, _acc => by
      simp [butterflyDITRadix4Inner]
  | n + 1, j, i0, i1, i2, i3, acc => by
      have hj : j < j + (n + 1) := by omega
      have ih := butterflyDITRadix4Inner_eq_foldl_cell twiddlesLow twiddlesHigh n
        (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1)
        (radix4Cell (twiddlesLow.getD j 0) (twiddlesHigh.getD j 0)
          (twiddlesHigh.getD (j + (j + (n + 1))) 0) i0 i1 i2 i3 acc)
      have hshift :
          List.foldl
              (fun acc t =>
                radix4Cell (twiddlesLow.getD (j + 1 + t) 0)
                  (twiddlesHigh.getD (j + 1 + t) 0)
                  (twiddlesHigh.getD (j + 1 + t + (j + 1 + n)) 0) (i0 + 1 + t)
                  (i1 + 1 + t) (i2 + 1 + t) (i3 + 1 + t) acc)
              (radix4Cell (twiddlesLow.getD j 0) (twiddlesHigh.getD j 0)
                (twiddlesHigh.getD (j + (j + (n + 1))) 0) i0 i1 i2 i3 acc)
              (List.range' 0 n) =
            List.foldl
              (fun acc t =>
                radix4Cell (twiddlesLow.getD (j + t) 0) (twiddlesHigh.getD (j + t) 0)
                  (twiddlesHigh.getD (j + t + (j + (n + 1))) 0) (i0 + t) (i1 + t)
                  (i2 + t) (i3 + t) acc)
              (radix4Cell (twiddlesLow.getD j 0) (twiddlesHigh.getD j 0)
                (twiddlesHigh.getD (j + (j + (n + 1))) 0) i0 i1 i2 i3 acc)
              (List.range' 1 n) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (foldl_range'_succ_shift
            (fun t acc =>
              radix4Cell (twiddlesLow.getD (j + t) 0) (twiddlesHigh.getD (j + t) 0)
                (twiddlesHigh.getD (j + t + (j + (n + 1))) 0) (i0 + t) (i1 + t)
                (i2 + t) (i3 + t) acc)
            n 0
            (radix4Cell (twiddlesLow.getD j 0) (twiddlesHigh.getD j 0)
              (twiddlesHigh.getD (j + (j + (n + 1))) 0) i0 i1 i2 i3 acc))
      rw [butterflyDITRadix4Inner]
      simp only [hj, ↓reduceIte]
      simpa [List.range'_succ, radix4Cell, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih.trans hshift

private theorem butterflyDITRadix4Blocks_eq_foldl_inner
    (twiddlesLow twiddlesHigh : Array R) (blockSize quarter blocks : Nat) :
    ∀ n block (acc : Array R),
      blocks = block + n →
      butterflyDITRadix4Blocks twiddlesLow twiddlesHigh blockSize quarter blocks block acc =
        List.foldl
          (fun acc block =>
            butterflyDITRadix4Inner twiddlesLow twiddlesHigh quarter 0 (block * blockSize)
              (block * blockSize + quarter) (block * blockSize + 2 * quarter)
              (block * blockSize + 3 * quarter) acc)
          acc (List.range' block n)
  | 0, block, _acc, hblocks => by
      have hnot : ¬block < blocks := by omega
      simp [butterflyDITRadix4Blocks, hnot]
  | n + 1, block, acc, hblocks => by
      have hblock : block < blocks := by omega
      have htail : blocks = block + 1 + n := by omega
      have ih := butterflyDITRadix4Blocks_eq_foldl_inner twiddlesLow twiddlesHigh blockSize
        quarter blocks n (block + 1)
        (butterflyDITRadix4Inner twiddlesLow twiddlesHigh quarter 0 (block * blockSize)
          (block * blockSize + quarter) (block * blockSize + 2 * quarter)
          (block * blockSize + 3 * quarter) acc)
        htail
      rw [butterflyDITRadix4Blocks]
      simp only [hblock, ↓reduceIte]
      simpa [List.range'_succ] using ih

set_option maxHeartbeats 800000 in
private theorem butterflyDITRadix4Inner_eq_two_dit_inners
    (twiddlesLow twiddlesHigh : Array R) (q base : Nat) (acc : Array R)
    (hq : 0 < q) (hbound : base + 4 * q ≤ acc.size) :
    butterflyDITRadix4Inner twiddlesLow twiddlesHigh q 0 base (base + q) (base + 2 * q)
        (base + 3 * q) acc =
      butterflyDITInner twiddlesHigh (2 * q) 0 base (base + 2 * q)
        (butterflyDITInner twiddlesLow q 0 (base + 2 * q) (base + 3 * q)
          (butterflyDITInner twiddlesLow q 0 base (base + q) acc)) := by
  calc
    butterflyDITRadix4Inner twiddlesLow twiddlesHigh q 0 base (base + q)
        (base + 2 * q) (base + 3 * q) acc =
        List.foldl
          (fun acc j =>
            radix4Cell (twiddlesLow.getD j 0) (twiddlesHigh.getD j 0)
              (twiddlesHigh.getD (j + q) 0) (base + j) (base + q + j)
              (base + 2 * q + j) (base + 3 * q + j) acc)
          acc (List.range q) := by
          simpa [List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (butterflyDITRadix4Inner_eq_foldl_cell twiddlesLow twiddlesHigh q 0 base
              (base + q) (base + 2 * q) (base + 3 * q) acc)
    _ = List.foldl
          (fun acc j =>
            ditButterfly (twiddlesHigh.getD (j + q) 0) (base + q + j)
              (base + 3 * q + j)
              (ditButterfly (twiddlesHigh.getD j 0) (base + j) (base + 2 * q + j)
                (ditButterfly (twiddlesLow.getD j 0) (base + 2 * q + j)
                  (base + 3 * q + j)
                  (ditButterfly (twiddlesLow.getD j 0) (base + j) (base + q + j) acc))))
          acc (List.range q) := by
          apply foldl_range_congr_inv (p := fun b : Array R => b.size = acc.size)
          · intro j hj acc hacc
            exact (radix4Cell_eq_two_stage_cells (twiddlesLow.getD j 0)
                (twiddlesHigh.getD j 0) (twiddlesHigh.getD (j + q) 0) (base + j)
                (base + q + j) (base + 2 * q + j) (base + 3 * q + j) acc
                (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                (by nlinarith [hacc, hbound]) (by nlinarith [hacc, hbound])
                (by nlinarith [hacc, hbound]) (by nlinarith [hacc, hbound])).symm
          · intro j hj acc hacc
            simp [hacc]
          · rfl
    _ = List.foldl
          (fun acc j =>
            ditButterfly (twiddlesHigh.getD (j + q) 0) (base + q + j)
              (base + 3 * q + j) acc)
          (List.foldl
            (fun acc j => ditButterfly (twiddlesHigh.getD j 0) (base + j)
              (base + 2 * q + j) acc)
            (List.foldl
              (fun acc j => ditButterfly (twiddlesLow.getD j 0) (base + 2 * q + j)
                (base + 3 * q + j) acc)
              (List.foldl
                (fun acc j => ditButterfly (twiddlesLow.getD j 0) (base + j)
                  (base + q + j) acc)
                acc (List.range q)) (List.range q))
            (List.range q))
          (List.range q) := by
          apply foldl_quad
          · intro i j hij hj x
            apply ditButterfly_comm <;> omega
          · intro i j hij hj x
            apply ditButterfly_comm <;> omega
          · intro i j hij hj x
            apply ditButterfly_comm <;> omega
          · intro i j hij hj x
            apply ditButterfly_comm <;> omega
          · intro i j hij hj x
            apply ditButterfly_comm <;> omega
          · intro i j hij hj x
            apply ditButterfly_comm <;> omega
    _ = butterflyDITInner twiddlesHigh (2 * q) 0 base (base + 2 * q)
          (butterflyDITInner twiddlesLow q 0 (base + 2 * q) (base + 3 * q)
            (butterflyDITInner twiddlesLow q 0 base (base + q) acc)) := by
          symm
          have hlow₁ :
              butterflyDITInner twiddlesLow q 0 base (base + q) acc =
                List.foldl
                  (fun acc j => ditButterfly (twiddlesLow.getD j 0) (base + j)
                    (base + q + j) acc)
                  acc (List.range q) := by
            simpa [List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using (butterflyDITInner_eq_foldl_dit twiddlesLow q 0 base (base + q) acc)
          have hlow₂ (acc' : Array R) :
              butterflyDITInner twiddlesLow q 0 (base + 2 * q) (base + 3 * q) acc' =
                List.foldl
                  (fun acc j => ditButterfly (twiddlesLow.getD j 0) (base + 2 * q + j)
                    (base + 3 * q + j) acc)
                  acc' (List.range q) := by
            simpa [List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using (butterflyDITInner_eq_foldl_dit twiddlesLow q 0 (base + 2 * q)
                (base + 3 * q) acc')
          have hhigh (acc' : Array R) :
              butterflyDITInner twiddlesHigh (2 * q) 0 base (base + 2 * q) acc' =
                List.foldl
                  (fun acc j => ditButterfly (twiddlesHigh.getD (j + q) 0) (base + q + j)
                    (base + 3 * q + j) acc)
                  (List.foldl
                    (fun acc j => ditButterfly (twiddlesHigh.getD j 0) (base + j)
                      (base + 2 * q + j) acc)
                    acc' (List.range q))
                  (List.range q) := by
            calc
              butterflyDITInner twiddlesHigh (2 * q) 0 base (base + 2 * q) acc' =
                  List.foldl
                    (fun acc j => ditButterfly (twiddlesHigh.getD j 0) (base + j)
                      (base + 2 * q + j) acc)
                    acc' (List.range' 0 (2 * q)) := by
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                      (butterflyDITInner_eq_foldl_dit twiddlesHigh (2 * q) 0 base
                        (base + 2 * q) acc')
              _ = List.foldl
                    (fun acc j => ditButterfly (twiddlesHigh.getD j 0) (base + j)
                      (base + 2 * q + j) acc)
                    (List.foldl
                      (fun acc j => ditButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc)
                      acc' (List.range' 0 q))
                    (List.range' q q) := by
                    simpa [two_mul] using
                      (foldl_range'_append_split
                      (fun acc j => ditButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc) acc' 0 q q)
              _ = List.foldl
                    (fun acc j =>
                      ditButterfly (twiddlesHigh.getD (j + q) 0) (base + q + j)
                        (base + 3 * q + j) acc)
                    (List.foldl
                      (fun acc j => ditButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc)
                      acc' (List.range q))
                    (List.range q) := by
                    rw [foldl_range'_eq_range_add
                      (fun j acc => ditButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc) q q]
                    rw [← List.range_eq_range']
                    apply foldl_range_congr
                    intro j hj acc
                    simp [Nat.add_comm, Nat.add_left_comm, two_mul]
                    congr 1
                    omega
          rw [hhigh, hlow₂, hlow₁]

set_option maxHeartbeats 1200000 in
private theorem butterflyDITRadix4Blocks_eq_two_dit_blocks
    (twiddlesLow twiddlesHigh : Array R) (q blocks : Nat) (acc : Array R)
    (hq : 0 < q) (hbound : blocks * (4 * q) ≤ acc.size) :
    butterflyDITRadix4Blocks twiddlesLow twiddlesHigh (4 * q) q blocks 0 acc =
      butterflyDITBlocks twiddlesHigh (4 * q) (2 * q) blocks 0
        (butterflyDITBlocks twiddlesLow (2 * q) q (2 * blocks) 0 acc) := by
  let lowBlock : Nat → Array R → Array R :=
    fun block acc =>
      butterflyDITInner twiddlesLow q 0 (2 * q + block * (4 * q))
        (2 * q + (block * (4 * q) + q))
        (butterflyDITInner twiddlesLow q 0 (block * (4 * q)) (q + block * (4 * q))
          acc)
  let highBlock : Nat → Array R → Array R :=
    fun block acc =>
      butterflyDITInner twiddlesHigh (2 * q) 0 (block * (4 * q))
        (block * (4 * q) + 2 * q) acc
  let lowStep : Nat → Array R → Array R :=
    fun block acc =>
      butterflyDITInner twiddlesLow q 0 (block * (2 * q)) (block * (2 * q) + q) acc
  calc
    butterflyDITRadix4Blocks twiddlesLow twiddlesHigh (4 * q) q blocks 0 acc =
        List.foldl
          (fun acc block =>
            butterflyDITRadix4Inner twiddlesLow twiddlesHigh q 0 (block * (4 * q))
              (block * (4 * q) + q) (block * (4 * q) + 2 * q)
              (block * (4 * q) + 3 * q) acc)
          acc (List.range blocks) := by
          simpa [List.range_eq_range'] using
            (butterflyDITRadix4Blocks_eq_foldl_inner twiddlesLow twiddlesHigh (4 * q)
              q blocks blocks 0 acc (by simp))
    _ = List.foldl (fun acc block => highBlock block (lowBlock block acc)) acc
          (List.range blocks) := by
          apply foldl_range_congr_inv (p := fun b : Array R => b.size = acc.size)
          · intro block hblock acc hacc
            simpa [lowBlock, highBlock, three_mul_add_eq_add_two_mul_add, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm]
              using (butterflyDITRadix4Inner_eq_two_dit_inners twiddlesLow twiddlesHigh q
                (block * (4 * q)) acc hq (by nlinarith [hblock, hbound, hacc]))
          · intro block hblock acc hacc
            simp [hacc]
          · rfl
    _ = List.foldl (fun acc block => highBlock block acc)
          (List.foldl (fun acc block => lowBlock block acc) acc (List.range blocks))
          (List.range blocks) := by
          apply foldl_pair
          intro i j hij hj x
          have hlow₁ :
              butterflyDITInner twiddlesLow q 0 (j * (4 * q)) (q + j * (4 * q))
                  (highBlock i x) =
                highBlock i
                  (butterflyDITInner twiddlesLow q 0 (j * (4 * q))
                    (q + j * (4 * q)) x) := by
            simpa [highBlock, three_mul_add_eq_add_two_mul_add, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using
              (butterflyDITInner_comm twiddlesLow twiddlesHigh q (2 * q) (j * (4 * q))
                q (i * (4 * q)) (2 * q) (by
                  intro a ha b hb
                  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith) x)
          have hlow₂ (x' : Array R) :
              butterflyDITInner twiddlesLow q 0 (2 * q + j * (4 * q))
                  (2 * q + (j * (4 * q) + q)) (highBlock i x') =
                highBlock i
                  (butterflyDITInner twiddlesLow q 0 (2 * q + j * (4 * q))
                    (2 * q + (j * (4 * q) + q)) x') := by
            simpa [highBlock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (butterflyDITInner_comm twiddlesLow twiddlesHigh q (2 * q)
                (2 * q + j * (4 * q)) q (i * (4 * q)) (2 * q) (by
                  intro a ha b hb
                  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith) x')
          simp only [lowBlock]
          rw [hlow₁]
          exact hlow₂ _
    _ = List.foldl (fun acc block => highBlock block acc)
          (List.foldl (fun acc block => lowStep block acc) acc (List.range (2 * blocks)))
          (List.range blocks) := by
          congr 1
          calc
            List.foldl (fun acc block => lowBlock block acc) acc (List.range blocks) =
                List.foldl (fun acc block => lowStep (2 * block + 1) (lowStep (2 * block) acc))
                  acc (List.range blocks) := by
                  apply foldl_range_congr
                  intro block hblock acc
                  unfold lowBlock lowStep
                  exact congrArg
                    (fun p : Nat × Nat × Nat × Nat =>
                      butterflyDITInner twiddlesLow q 0 p.1 p.2.1
                        (butterflyDITInner twiddlesLow q 0 p.2.2.1 p.2.2.2 acc))
                    (show
                      ((2 * q + block * (4 * q), 2 * q + (block * (4 * q) + q),
                          block * (4 * q), q + block * (4 * q)) : Nat × Nat × Nat × Nat) =
                        (((2 * block + 1) * (2 * q), (2 * block + 1) * (2 * q) + q,
                          2 * block * (2 * q), 2 * block * (2 * q) + q) :
                          Nat × Nat × Nat × Nat) by
                      ext <;> nlinarith)
            _ = List.foldl (fun acc block => lowStep block acc) acc (List.range (2 * blocks)) := by
                  exact foldl_range_pair lowStep blocks acc
    _ = butterflyDITBlocks twiddlesHigh (4 * q) (2 * q) blocks 0
          (butterflyDITBlocks twiddlesLow (2 * q) q (2 * blocks) 0 acc) := by
          have hlow :
              List.foldl (fun acc block => lowStep block acc) acc (List.range (2 * blocks)) =
                butterflyDITBlocks twiddlesLow (2 * q) q (2 * blocks) 0 acc := by
            symm
            simpa [List.range_eq_range', lowStep] using
              (butterflyDITBlocks_eq_foldl_inner twiddlesLow (2 * q) q (2 * blocks)
                (2 * blocks) 0 acc (by simp))
          rw [hlow]
          symm
          simpa [List.range_eq_range', highBlock] using
            (butterflyDITBlocks_eq_foldl_inner twiddlesHigh (4 * q) (2 * q) blocks
              blocks 0 (butterflyDITBlocks twiddlesLow (2 * q) q (2 * blocks) 0 acc)
              (by simp))

private theorem butterflyRadix4StageWithTwiddles_eq_two_stages
    (D : NTT.Domain R) (lowStage : Nat) (twiddlesLow twiddlesHigh a : Array R)
    (ha : a.size = D.n) (hstage : lowStage + 1 < D.logN) :
    butterflyRadix4StageWithTwiddles D lowStage twiddlesLow twiddlesHigh a =
      butterflyStageWithTwiddles D (lowStage + 1) twiddlesHigh
        (butterflyStageWithTwiddles D lowStage twiddlesLow a) := by
  have hq : 0 < 2 ^ lowStage := Nat.pow_pos (by decide)
  have hblockSize : 2 ^ (lowStage + 2) = 4 * 2 ^ lowStage := by
    rw [show lowStage + 2 = lowStage + 1 + 1 by omega, pow_succ, pow_succ]
    ring
  have hhalf : 2 ^ (lowStage + 1) = 2 * 2 ^ lowStage := by
    rw [pow_succ']
  have hblocks :
      2 * (D.n / 2 ^ (lowStage + 2)) = D.n / 2 ^ (lowStage + 1) := by
    rw [NTT.Domain.n]
    rw [Nat.pow_div (show lowStage + 2 ≤ D.logN by omega) (by decide : 0 < 2)]
    rw [Nat.pow_div (show lowStage + 1 ≤ D.logN by omega) (by decide : 0 < 2)]
    have hsub : D.logN - (lowStage + 1) = (D.logN - (lowStage + 2)) + 1 := by
      omega
    rw [hsub, pow_succ']
  have hbound :
      (D.n / 2 ^ (lowStage + 2)) * (4 * 2 ^ lowStage) ≤ a.size := by
    rw [ha, NTT.Domain.n]
    rw [← hblockSize]
    exact Nat.le_of_eq (Nat.div_mul_cancel
      (Nat.pow_dvd_pow 2 (show lowStage + 2 ≤ D.logN by omega)))
  have hblocks' :
      2 * (2 ^ D.logN / (2 ^ lowStage * 4)) = 2 ^ D.logN / (2 * 2 ^ lowStage) := by
    simpa [NTT.Domain.n, hblockSize, hhalf, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using hblocks
  unfold butterflyRadix4StageWithTwiddles butterflyStageWithTwiddles
  simpa [NTT.Domain.n, hblockSize, hhalf, hblocks', Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (butterflyDITRadix4Blocks_eq_two_dit_blocks twiddlesLow twiddlesHigh
      (2 ^ lowStage) (D.n / 2 ^ (lowStage + 2)) a hq hbound)

/-- A DIT butterfly stage with matching cached twiddles agrees with the `NTT` stage. -/
theorem butterflyStageWithTwiddles_eq_ntt
    (D : NTT.Domain R) (stage : Nat) (twiddles : Array R) (a : Array R)
    (htwiddles :
      ∀ j, j < 2 ^ stage →
        twiddles.getD j 0 = (D.omega ^ (D.n / 2 ^ (stage + 1))) ^ j) :
    butterflyStageWithTwiddles D stage twiddles a =
      NTT.Transform.butterflyStage D stage a := by
  rw [NTT.Transform.butterflyStage_eq_butterflyStageSpec]
  simp [butterflyStageWithTwiddles, NTT.Transform.butterflyStageSpec]
  let wm := D.omega ^ (D.n / 2 ^ (stage + 1))
  have htw : ∀ j, j < 2 ^ stage → twiddles.getD j 0 = wm ^ j := by
    intro j hj
    simpa [wm] using htwiddles j hj
  have hblocks := butterflyDITBlocks_eq_foldl twiddles (2 ^ (stage + 1)) (2 ^ stage) wm htw
    (2 ^ D.logN / 2 ^ (stage + 1)) (2 ^ D.logN / 2 ^ (stage + 1)) 0 a (by simp)
  rw [hblocks]
  simpa [List.range_eq_range', wm, NTT.Domain.n] using
    foldl_range_eq_rec
      (f := fun block acc =>
        NTT.Transform.butterflyBlockStep (2 ^ (stage + 1)) (2 ^ stage)
          (D.omega ^ (2 ^ D.logN / 2 ^ (stage + 1))) block acc)
      (x := a) (2 ^ D.logN / 2 ^ (stage + 1))

/-- The DIT radix-2 stage loop with the full twiddle table agrees with `NTT`. -/
theorem runStagesWithTwiddles_eq_ntt (D : NTT.Domain R) (a : Array R) :
    runStagesWithTwiddles D (twiddleTable D) a = NTT.Transform.runStages D a := by
  simp [runStagesWithTwiddles, NTT.Transform.runStages]
  rw [← List.range_eq_range']
  apply foldl_range_congr
  intro stage hstage acc
  apply butterflyStageWithTwiddles_eq_ntt
  intro j hj
  simpa [twiddleTable, hstage] using twiddlePowers_getD_eq_pow D stage j hj

/--
The mixed radix-4 DIT stage loop agrees with the radix-2 `NTT` stage loop on
domain-sized arrays.
-/
theorem runStagesRadix4WithTwiddles_eq_ntt (D : NTT.Domain R) (a : Array R)
    (ha : a.size = D.n) :
    runStagesRadix4WithTwiddles D (twiddleTable D) a =
      NTT.Transform.runStages D a := by
  rw [← runStagesWithTwiddles_eq_ntt D a]
  let stageStep : Nat → Array R → Array R :=
    fun stage acc => butterflyStageWithTwiddles D stage ((twiddleTable D).getD stage #[]) acc
  let radixStep : Nat → Array R → Array R :=
    fun pass acc =>
      butterflyRadix4StageWithTwiddles D (2 * pass) ((twiddleTable D).getD (2 * pass) #[])
        ((twiddleTable D).getD (2 * pass + 1) #[]) acc
  let pairStep : Nat → Array R → Array R :=
    fun pass acc => stageStep (2 * pass + 1) (stageStep (2 * pass) acc)
  have hpairLoop :
      List.foldl (fun acc pass => radixStep pass acc) a (List.range (D.logN / 2)) =
        List.foldl (fun acc pass => pairStep pass acc) a (List.range (D.logN / 2)) := by
    apply foldl_range_congr_inv (p := fun b : Array R => b.size = D.n)
    · intro pass hpass acc hacc
      exact butterflyRadix4StageWithTwiddles_eq_two_stages D (2 * pass)
        ((twiddleTable D).getD (2 * pass) #[])
        ((twiddleTable D).getD (2 * pass + 1) #[]) acc hacc (by omega)
    · intro pass hpass acc hacc
      simp [radixStep, hacc]
    · exact ha
  have hpairRange :
      List.foldl (fun acc pass => pairStep pass acc) a (List.range (D.logN / 2)) =
        List.foldl (fun acc stage => stageStep stage acc) a
          (List.range (2 * (D.logN / 2))) := by
    simpa [pairStep] using foldl_range_pair stageStep (D.logN / 2) a
  calc
    runStagesRadix4WithTwiddles D (twiddleTable D) a =
        (if D.logN % 2 = 1 then
          stageStep (D.logN - 1)
            (List.foldl (fun acc pass => radixStep pass acc) a (List.range (D.logN / 2)))
        else
          List.foldl (fun acc pass => radixStep pass acc) a (List.range (D.logN / 2))) := by
          by_cases hodd : D.logN % 2 = 1
          · simp [runStagesRadix4WithTwiddles, stageStep, radixStep, List.range_eq_range', hodd]
          · simp [runStagesRadix4WithTwiddles, stageStep, radixStep, List.range_eq_range', hodd]
    _ = (if D.logN % 2 = 1 then
          stageStep (D.logN - 1)
            (List.foldl (fun acc stage => stageStep stage acc) a
              (List.range (2 * (D.logN / 2))))
        else
          List.foldl (fun acc stage => stageStep stage acc) a
            (List.range (2 * (D.logN / 2)))) := by
          rw [hpairLoop, hpairRange]
    _ = List.foldl (fun acc stage => stageStep stage acc) a (List.range D.logN) := by
          by_cases hodd : D.logN % 2 = 1
          · have hlen : D.logN = 2 * (D.logN / 2) + 1 := by omega
            have hlast : D.logN - 1 = 2 * (D.logN / 2) := by omega
            simp only [hodd, ↓reduceIte]
            rw [hlast]
            conv_rhs => rw [hlen]
            simp [List.range_succ, List.foldl_append]
          · have hlen : 2 * (D.logN / 2) = D.logN := by omega
            simp only [hodd, ↓reduceIte]
            rw [hlen]
    _ = runStagesWithTwiddles D (twiddleTable D) a := by
          symm
          simp [runStagesWithTwiddles, stageStep, List.range_eq_range']

end Plan

end NTTFast
end CPolynomial
end CompPoly
