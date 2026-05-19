/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTTFast.Correctness.DIF

/-!
# Radix-4 DIF NTTFast correctness

Correctness proofs for the mixed radix-4 decimation-in-frequency stage loop used by `NTTFast`.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast

open scoped BigOperators

variable {R : Type*} [Field R]

namespace Plan

private def difButterfly (w : R) (i0 i1 : Nat) (acc : Array R) : Array R :=
  let u := acc.getD i0 0
  let v := acc.getD i1 0
  (acc.set! i0 (u + v)).set! i1 (w * (u - v))

private theorem getD_difButterfly_of_ne
    (w : R) (i0 i1 k : Nat) (acc : Array R) (hk0 : k ≠ i0) (hk1 : k ≠ i1) :
    (difButterfly w i0 i1 acc).getD k 0 = acc.getD k 0 := by
  have h0 : i0 ≠ k := fun h ↦ hk0 h.symm
  have h1 : i1 ≠ k := fun h ↦ hk1 h.symm
  unfold difButterfly
  simp only [Array.set!, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_setIfInBounds]
  simp [h1]
  rw [Array.getElem?_setIfInBounds]
  simp [h0]

private theorem difButterfly_comm
    (acc : Array R) (w v : R) (i0 i1 j0 j1 : Nat)
    (h00 : i0 ≠ j0) (h01 : i0 ≠ j1) (h10 : i1 ≠ j0) (h11 : i1 ≠ j1) :
    difButterfly w i0 i1 (difButterfly v j0 j1 acc) =
      difButterfly v j0 j1 (difButterfly w i0 i1 acc) := by
  change
    (let u := (difButterfly v j0 j1 acc).getD i0 0
     let vv := (difButterfly v j0 j1 acc).getD i1 0
     (((difButterfly v j0 j1 acc).set! i0 (u + vv)).set! i1 (w * (u - vv)))) =
      (let u := (difButterfly w i0 i1 acc).getD j0 0
       let vv := (difButterfly w i0 i1 acc).getD j1 0
       (((difButterfly w i0 i1 acc).set! j0 (u + vv)).set! j1 (v * (u - vv))))
  rw [getD_difButterfly_of_ne v j0 j1 i0 acc h00 h01]
  rw [getD_difButterfly_of_ne v j0 j1 i1 acc h10 h11]
  rw [getD_difButterfly_of_ne w i0 i1 j0 acc h00.symm h10.symm]
  rw [getD_difButterfly_of_ne w i0 i1 j1 acc h01.symm h11.symm]
  unfold difButterfly
  simp only [Array.set!]
  rw [Array.setIfInBounds_comm _ _ h01.symm]
  rw [Array.setIfInBounds_comm _ _ h00.symm]
  rw [Array.setIfInBounds_comm _ _ h11.symm]
  rw [Array.setIfInBounds_comm _ _ h10.symm]

private theorem butterflyDIFInner_eq_foldl_dif (twiddles : Array R) :
    ∀ n j i0 i1 (acc : Array R),
      butterflyDIFInner twiddles (j + n) j i0 i1 acc =
        List.foldl
          (fun acc t ↦ difButterfly (twiddles.getD (j + t) 0) (i0 + t) (i1 + t) acc)
          acc (List.range' 0 n)
  | 0, j, i0, i1, acc => by
      simp [butterflyDIFInner]
  | n + 1, j, i0, i1, acc => by
      have hj : j < j + (n + 1) := by omega
      have ih := butterflyDIFInner_eq_foldl_dif twiddles n (j + 1) (i0 + 1) (i1 + 1)
        (difButterfly (twiddles.getD j 0) i0 i1 acc)
      have hshift :
          List.foldl
              (fun acc t ↦
                difButterfly (twiddles.getD (j + 1 + t) 0) (i0 + 1 + t)
                  (i1 + 1 + t) acc)
              (difButterfly (twiddles.getD j 0) i0 i1 acc) (List.range' 0 n) =
            List.foldl
              (fun acc t ↦ difButterfly (twiddles.getD (j + t) 0) (i0 + t) (i1 + t) acc)
              (difButterfly (twiddles.getD j 0) i0 i1 acc) (List.range' 1 n) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (foldl_range'_succ_shift
            (fun t acc ↦ difButterfly (twiddles.getD (j + t) 0) (i0 + t) (i1 + t) acc)
            n 0 (difButterfly (twiddles.getD j 0) i0 i1 acc))
      rw [butterflyDIFInner]
      simp only [hj, ↓reduceIte]
      simpa [List.range'_succ, difButterfly, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih.trans hshift

private theorem butterflyDIFInner_comm
    (twiddlesA twiddlesB : Array R) (limitA limitB baseA halfA baseB halfB : Nat)
    (hcomm :
      ∀ i, i < limitA → ∀ j, j < limitB →
        baseA + i ≠ baseB + j ∧
        baseA + i ≠ baseB + halfB + j ∧
        baseA + halfA + i ≠ baseB + j ∧
        baseA + halfA + i ≠ baseB + halfB + j) :
    ∀ acc : Array R,
      butterflyDIFInner twiddlesA limitA 0 baseA (baseA + halfA)
          (butterflyDIFInner twiddlesB limitB 0 baseB (baseB + halfB) acc) =
        butterflyDIFInner twiddlesB limitB 0 baseB (baseB + halfB)
          (butterflyDIFInner twiddlesA limitA 0 baseA (baseA + halfA) acc) := by
  intro acc
  let foldA : Array R → Array R :=
    fun acc ↦
      List.foldl
        (fun acc i ↦ difButterfly (twiddlesA.getD i 0) (baseA + i)
          (baseA + halfA + i) acc)
        acc (List.range limitA)
  let foldB : Array R → Array R :=
    fun acc ↦
      List.foldl
        (fun acc j ↦ difButterfly (twiddlesB.getD j 0) (baseB + j)
          (baseB + halfB + j) acc)
        acc (List.range limitB)
  have hA (acc' : Array R) :
      butterflyDIFInner twiddlesA limitA 0 baseA (baseA + halfA) acc' = foldA acc' := by
    simpa [foldA, List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (butterflyDIFInner_eq_foldl_dif twiddlesA limitA 0 baseA (baseA + halfA) acc')
  have hB (acc' : Array R) :
      butterflyDIFInner twiddlesB limitB 0 baseB (baseB + halfB) acc' = foldB acc' := by
    simpa [foldB, List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (butterflyDIFInner_eq_foldl_dif twiddlesB limitB 0 baseB (baseB + halfB) acc')
  calc
    butterflyDIFInner twiddlesA limitA 0 baseA (baseA + halfA)
        (butterflyDIFInner twiddlesB limitB 0 baseB (baseB + halfB) acc) =
        foldA (foldB acc) := by
          rw [hB, hA]
    _ = List.foldl
          (fun acc j ↦ difButterfly (twiddlesB.getD j 0) (baseB + j)
            (baseB + halfB + j) acc)
          (List.foldl
            (fun acc i ↦ difButterfly (twiddlesA.getD i 0) (baseA + i)
              (baseA + halfA + i) acc)
            acc (List.range limitA))
          (List.range limitB) := by
          apply foldl_commute_foldl
          intro i j hi hj acc
          rcases hcomm i hi j hj with ⟨h00, h01, h10, h11⟩
          exact (difButterfly_comm acc (twiddlesA.getD i 0) (twiddlesB.getD j 0)
            (baseA + i) (baseA + halfA + i) (baseB + j) (baseB + halfB + j)
            h00 h01 h10 h11).symm
    _ = butterflyDIFInner twiddlesB limitB 0 baseB (baseB + halfB)
          (butterflyDIFInner twiddlesA limitA 0 baseA (baseA + halfA) acc) := by
          rw [hA, hB]

private theorem butterflyDIFBlocks_eq_foldl_inner
    (twiddles : Array R) (blockSize half blocks : Nat) :
    ∀ n block (acc : Array R),
      blocks = block + n →
      butterflyDIFBlocks twiddles blockSize half blocks block acc =
        List.foldl
          (fun acc block ↦
            butterflyDIFInner twiddles half 0 (block * blockSize) (block * blockSize + half)
              acc)
          acc (List.range' block n)
  | 0, block, acc, hblocks => by
      have hnot : ¬block < blocks := by omega
      simp [butterflyDIFBlocks, hnot]
  | n + 1, block, acc, hblocks => by
      have hblock : block < blocks := by omega
      have htail : blocks = block + 1 + n := by omega
      have ih := butterflyDIFBlocks_eq_foldl_inner twiddles blockSize half blocks
        n (block + 1)
          (butterflyDIFInner twiddles half 0 (block * blockSize) (block * blockSize + half)
            acc)
        htail
      rw [butterflyDIFBlocks]
      simp only [hblock, ↓reduceIte]
      simpa [List.range'_succ] using ih

private def radix4DIFCell
    (wHigh0 wHigh1 wLow : R) (i0 i1 i2 i3 : Nat) (acc : Array R) : Array R :=
  let x0 := acc.getD i0 0
  let x1 := acc.getD i1 0
  let x2 := acc.getD i2 0
  let x3 := acc.getD i3 0
  let a0 := x0 + x2
  let a2 := wHigh0 * (x0 - x2)
  let a1 := x1 + x3
  let a3 := wHigh1 * (x1 - x3)
  (((acc.set! i0 (a0 + a1)).set! i1 (wLow * (a0 - a1))).set! i2 (a2 + a3)).set! i3
    (wLow * (a2 - a3))

@[simp] private theorem size_radix4DIFCell
    (wHigh0 wHigh1 wLow : R) (i0 i1 i2 i3 : Nat) (acc : Array R) :
    (radix4DIFCell wHigh0 wHigh1 wLow i0 i1 i2 i3 acc).size = acc.size := by
  simp [radix4DIFCell, Array.set!, Array.size_setIfInBounds]

set_option maxHeartbeats 800000 in
private theorem radix4DIFCell_eq_two_stage_cells
    (wHigh0 wHigh1 wLow : R) (i0 i1 i2 i3 : Nat) (acc : Array R)
    (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h03 : i0 ≠ i3)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3)
    (hi0 : i0 < acc.size) (hi1 : i1 < acc.size)
    (hi2 : i2 < acc.size) (hi3 : i3 < acc.size) :
    difButterfly wLow i2 i3
        (difButterfly wLow i0 i1
          (difButterfly wHigh1 i1 i3 (difButterfly wHigh0 i0 i2 acc))) =
      radix4DIFCell wHigh0 wHigh1 wLow i0 i1 i2 i3 acc := by
  unfold difButterfly radix4DIFCell
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
    Array.size_setIfInBounds]
  simp [hi0, hi1, hi2, hi3, h01, h01.symm, h02, h02.symm, h03, h03.symm,
    h12, h12.symm, h13, h13.symm, h23, h23.symm]
  rw [Array.setIfInBounds_comm _ _ h03.symm]
  rw [Array.setIfInBounds_comm _ _ h01.symm]
  rw [Array.setIfInBounds_comm _ _ h02.symm]
  rw [Array.setIfInBounds_setIfInBounds]
  rw [Array.setIfInBounds_comm _ _ h13.symm]
  rw [Array.setIfInBounds_setIfInBounds]
  rw [Array.setIfInBounds_comm _ _ h23.symm]
  rw [Array.setIfInBounds_setIfInBounds]
  rw [Array.setIfInBounds_comm _ _ h12.symm]
  rw [Array.setIfInBounds_setIfInBounds]

private theorem butterflyDIFRadix4Inner_eq_foldl_cell
    (twiddlesHigh twiddlesLow : Array R) :
    ∀ n j i0 i1 i2 i3 (acc : Array R),
      butterflyDIFRadix4Inner twiddlesHigh twiddlesLow (j + n) j i0 i1 i2 i3 acc =
        List.foldl
          (fun acc t ↦
            radix4DIFCell (twiddlesHigh.getD (j + t) 0)
              (twiddlesHigh.getD (j + t + (j + n)) 0) (twiddlesLow.getD (j + t) 0)
              (i0 + t) (i1 + t) (i2 + t) (i3 + t) acc)
          acc (List.range' 0 n)
  | 0, j, _i0, _i1, _i2, _i3, _acc => by
      simp [butterflyDIFRadix4Inner]
  | n + 1, j, i0, i1, i2, i3, acc => by
      have hj : j < j + (n + 1) := by omega
      have ih := butterflyDIFRadix4Inner_eq_foldl_cell twiddlesHigh twiddlesLow n
        (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1)
        (radix4DIFCell (twiddlesHigh.getD j 0)
          (twiddlesHigh.getD (j + (j + (n + 1))) 0) (twiddlesLow.getD j 0)
          i0 i1 i2 i3 acc)
      have hshift :
          List.foldl
              (fun acc t ↦
                radix4DIFCell (twiddlesHigh.getD (j + 1 + t) 0)
                  (twiddlesHigh.getD (j + 1 + t + (j + 1 + n)) 0)
                  (twiddlesLow.getD (j + 1 + t) 0) (i0 + 1 + t) (i1 + 1 + t)
                  (i2 + 1 + t) (i3 + 1 + t) acc)
              (radix4DIFCell (twiddlesHigh.getD j 0)
                (twiddlesHigh.getD (j + (j + (n + 1))) 0) (twiddlesLow.getD j 0)
                i0 i1 i2 i3 acc)
              (List.range' 0 n) =
            List.foldl
              (fun acc t ↦
                radix4DIFCell (twiddlesHigh.getD (j + t) 0)
                  (twiddlesHigh.getD (j + t + (j + (n + 1))) 0)
                  (twiddlesLow.getD (j + t) 0) (i0 + t) (i1 + t) (i2 + t)
                  (i3 + t) acc)
              (radix4DIFCell (twiddlesHigh.getD j 0)
                (twiddlesHigh.getD (j + (j + (n + 1))) 0) (twiddlesLow.getD j 0)
                i0 i1 i2 i3 acc)
              (List.range' 1 n) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (foldl_range'_succ_shift
            (fun t acc ↦
              radix4DIFCell (twiddlesHigh.getD (j + t) 0)
                (twiddlesHigh.getD (j + t + (j + (n + 1))) 0)
                (twiddlesLow.getD (j + t) 0) (i0 + t) (i1 + t) (i2 + t) (i3 + t)
                acc)
            n 0
            (radix4DIFCell (twiddlesHigh.getD j 0)
              (twiddlesHigh.getD (j + (j + (n + 1))) 0) (twiddlesLow.getD j 0)
              i0 i1 i2 i3 acc))
      rw [butterflyDIFRadix4Inner]
      simp only [hj, ↓reduceIte]
      simpa [List.range'_succ, radix4DIFCell, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih.trans hshift

private theorem butterflyDIFRadix4Blocks_eq_foldl_inner
    (twiddlesHigh twiddlesLow : Array R) (blockSize quarter blocks : Nat) :
    ∀ n block (acc : Array R),
      blocks = block + n →
      butterflyDIFRadix4Blocks twiddlesHigh twiddlesLow blockSize quarter blocks block acc =
        List.foldl
          (fun acc block ↦
            butterflyDIFRadix4Inner twiddlesHigh twiddlesLow quarter 0 (block * blockSize)
              (block * blockSize + quarter) (block * blockSize + 2 * quarter)
              (block * blockSize + 3 * quarter) acc)
          acc (List.range' block n)
  | 0, block, _acc, hblocks => by
      have hnot : ¬block < blocks := by omega
      simp [butterflyDIFRadix4Blocks, hnot]
  | n + 1, block, acc, hblocks => by
      have hblock : block < blocks := by omega
      have htail : blocks = block + 1 + n := by omega
      have ih := butterflyDIFRadix4Blocks_eq_foldl_inner twiddlesHigh twiddlesLow blockSize
        quarter blocks n (block + 1)
        (butterflyDIFRadix4Inner twiddlesHigh twiddlesLow quarter 0 (block * blockSize)
          (block * blockSize + quarter) (block * blockSize + 2 * quarter)
          (block * blockSize + 3 * quarter) acc)
        htail
      rw [butterflyDIFRadix4Blocks]
      simp only [hblock, ↓reduceIte]
      simpa [List.range'_succ] using ih

set_option maxHeartbeats 800000 in
private theorem butterflyDIFRadix4Inner_eq_two_dif_inners
    (twiddlesHigh twiddlesLow : Array R) (q base : Nat) (acc : Array R)
    (hq : 0 < q) (hbound : base + 4 * q ≤ acc.size) :
    butterflyDIFRadix4Inner twiddlesHigh twiddlesLow q 0 base (base + q) (base + 2 * q)
        (base + 3 * q) acc =
      butterflyDIFInner twiddlesLow q 0 (base + 2 * q) (base + 3 * q)
        (butterflyDIFInner twiddlesLow q 0 base (base + q)
          (butterflyDIFInner twiddlesHigh (2 * q) 0 base (base + 2 * q) acc)) := by
  calc
    butterflyDIFRadix4Inner twiddlesHigh twiddlesLow q 0 base (base + q)
        (base + 2 * q) (base + 3 * q) acc =
        List.foldl
          (fun acc j ↦
            radix4DIFCell (twiddlesHigh.getD j 0) (twiddlesHigh.getD (j + q) 0)
              (twiddlesLow.getD j 0) (base + j) (base + q + j) (base + 2 * q + j)
              (base + 3 * q + j) acc)
          acc (List.range q) := by
          simpa [List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (butterflyDIFRadix4Inner_eq_foldl_cell twiddlesHigh twiddlesLow q 0 base
              (base + q) (base + 2 * q) (base + 3 * q) acc)
    _ = List.foldl
          (fun acc j ↦
            difButterfly (twiddlesLow.getD j 0) (base + 2 * q + j)
              (base + 3 * q + j)
              (difButterfly (twiddlesLow.getD j 0) (base + j) (base + q + j)
                (difButterfly (twiddlesHigh.getD (j + q) 0) (base + q + j)
                  (base + 3 * q + j)
                  (difButterfly (twiddlesHigh.getD j 0) (base + j) (base + 2 * q + j)
                    acc))))
          acc (List.range q) := by
          apply foldl_range_congr_inv (p := fun b : Array R ↦ b.size = acc.size)
          · intro j hj acc hacc
            exact (radix4DIFCell_eq_two_stage_cells (twiddlesHigh.getD j 0)
                (twiddlesHigh.getD (j + q) 0) (twiddlesLow.getD j 0) (base + j)
                (base + q + j) (base + 2 * q + j) (base + 3 * q + j) acc
                (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                (by nlinarith [hacc, hbound]) (by nlinarith [hacc, hbound])
                (by nlinarith [hacc, hbound]) (by nlinarith [hacc, hbound])).symm
          · intro j hj acc hacc
            simp [hacc]
          · rfl
    _ = List.foldl
          (fun acc j ↦ difButterfly (twiddlesLow.getD j 0) (base + 2 * q + j)
            (base + 3 * q + j) acc)
          (List.foldl
            (fun acc j ↦ difButterfly (twiddlesLow.getD j 0) (base + j) (base + q + j) acc)
            (List.foldl
              (fun acc j ↦ difButterfly (twiddlesHigh.getD (j + q) 0) (base + q + j)
                (base + 3 * q + j) acc)
              (List.foldl
                (fun acc j ↦ difButterfly (twiddlesHigh.getD j 0) (base + j)
                  (base + 2 * q + j) acc)
                acc (List.range q)) (List.range q))
            (List.range q))
          (List.range q) := by
          apply foldl_quad
          · intro i j hij hj x
            apply difButterfly_comm <;> omega
          · intro i j hij hj x
            apply difButterfly_comm <;> omega
          · intro i j hij hj x
            apply difButterfly_comm <;> omega
          · intro i j hij hj x
            apply difButterfly_comm <;> omega
          · intro i j hij hj x
            apply difButterfly_comm <;> omega
          · intro i j hij hj x
            apply difButterfly_comm <;> omega
    _ = butterflyDIFInner twiddlesLow q 0 (base + 2 * q) (base + 3 * q)
          (butterflyDIFInner twiddlesLow q 0 base (base + q)
            (butterflyDIFInner twiddlesHigh (2 * q) 0 base (base + 2 * q) acc)) := by
          symm
          have hhigh (acc' : Array R) :
              butterflyDIFInner twiddlesHigh (2 * q) 0 base (base + 2 * q) acc' =
                List.foldl
                  (fun acc j ↦ difButterfly (twiddlesHigh.getD (j + q) 0)
                    (base + q + j) (base + 3 * q + j) acc)
                  (List.foldl
                    (fun acc j ↦ difButterfly (twiddlesHigh.getD j 0) (base + j)
                      (base + 2 * q + j) acc)
                    acc' (List.range q))
                  (List.range q) := by
            calc
              butterflyDIFInner twiddlesHigh (2 * q) 0 base (base + 2 * q) acc' =
                  List.foldl
                    (fun acc j ↦ difButterfly (twiddlesHigh.getD j 0) (base + j)
                      (base + 2 * q + j) acc)
                    acc' (List.range' 0 (2 * q)) := by
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                      (butterflyDIFInner_eq_foldl_dif twiddlesHigh (2 * q) 0 base
                        (base + 2 * q) acc')
              _ = List.foldl
                    (fun acc j ↦ difButterfly (twiddlesHigh.getD j 0) (base + j)
                      (base + 2 * q + j) acc)
                    (List.foldl
                      (fun acc j ↦ difButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc)
                      acc' (List.range' 0 q))
                    (List.range' q q) := by
                    simpa [two_mul] using
                      (foldl_range'_append_split
                      (fun acc j ↦ difButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc) acc' 0 q q)
              _ = List.foldl
                    (fun acc j ↦
                      difButterfly (twiddlesHigh.getD (j + q) 0) (base + q + j)
                        (base + 3 * q + j) acc)
                    (List.foldl
                      (fun acc j ↦ difButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc)
                      acc' (List.range q))
                    (List.range q) := by
                    rw [foldl_range'_eq_range_add
                      (fun j acc ↦ difButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc) q q]
                    rw [← List.range_eq_range']
                    apply foldl_range_congr
                    intro j hj acc
                    simp [Nat.add_comm, Nat.add_left_comm, two_mul]
                    congr 1
                    omega
          have hlow₁ (acc' : Array R) :
              butterflyDIFInner twiddlesLow q 0 base (base + q) acc' =
                List.foldl
                  (fun acc j ↦ difButterfly (twiddlesLow.getD j 0) (base + j)
                    (base + q + j) acc)
                  acc' (List.range q) := by
            simpa [List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using (butterflyDIFInner_eq_foldl_dif twiddlesLow q 0 base (base + q) acc')
          have hlow₂ (acc' : Array R) :
              butterflyDIFInner twiddlesLow q 0 (base + 2 * q) (base + 3 * q) acc' =
                List.foldl
                  (fun acc j ↦ difButterfly (twiddlesLow.getD j 0) (base + 2 * q + j)
                    (base + 3 * q + j) acc)
                  acc' (List.range q) := by
            simpa [List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using (butterflyDIFInner_eq_foldl_dif twiddlesLow q 0 (base + 2 * q)
                (base + 3 * q) acc')
          rw [hlow₂, hlow₁, hhigh]

set_option maxHeartbeats 1200000 in
private theorem butterflyDIFRadix4Blocks_eq_two_dif_blocks
    (twiddlesHigh twiddlesLow : Array R) (q blocks : Nat) (acc : Array R)
    (hq : 0 < q) (hbound : blocks * (4 * q) ≤ acc.size) :
    butterflyDIFRadix4Blocks twiddlesHigh twiddlesLow (4 * q) q blocks 0 acc =
      butterflyDIFBlocks twiddlesLow (2 * q) q (2 * blocks) 0
        (butterflyDIFBlocks twiddlesHigh (4 * q) (2 * q) blocks 0 acc) := by
  let highBlock : Nat → Array R → Array R :=
    fun block acc ↦
      butterflyDIFInner twiddlesHigh (2 * q) 0 (block * (4 * q))
        (block * (4 * q) + 2 * q) acc
  let lowBlock : Nat → Array R → Array R :=
    fun block acc ↦
      butterflyDIFInner twiddlesLow q 0 (2 * q + block * (4 * q))
        (2 * q + (block * (4 * q) + q))
        (butterflyDIFInner twiddlesLow q 0 (block * (4 * q)) (q + block * (4 * q))
          acc)
  let lowStep : Nat → Array R → Array R :=
    fun block acc ↦
      butterflyDIFInner twiddlesLow q 0 (block * (2 * q)) (block * (2 * q) + q) acc
  calc
    butterflyDIFRadix4Blocks twiddlesHigh twiddlesLow (4 * q) q blocks 0 acc =
        List.foldl
          (fun acc block ↦
            butterflyDIFRadix4Inner twiddlesHigh twiddlesLow q 0 (block * (4 * q))
              (block * (4 * q) + q) (block * (4 * q) + 2 * q)
              (block * (4 * q) + 3 * q) acc)
          acc (List.range blocks) := by
          simpa [List.range_eq_range'] using
            (butterflyDIFRadix4Blocks_eq_foldl_inner twiddlesHigh twiddlesLow (4 * q)
              q blocks blocks 0 acc (by simp))
    _ = List.foldl (fun acc block ↦ lowBlock block (highBlock block acc)) acc
          (List.range blocks) := by
          apply foldl_range_congr_inv (p := fun b : Array R ↦ b.size = acc.size)
          · intro block hblock acc hacc
            simpa [lowBlock, highBlock, three_mul_add_eq_add_two_mul_add, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm]
              using (butterflyDIFRadix4Inner_eq_two_dif_inners twiddlesHigh twiddlesLow q
                (block * (4 * q)) acc hq (by nlinarith [hblock, hbound, hacc]))
          · intro block hblock acc hacc
            simp [hacc]
          · rfl
    _ = List.foldl (fun acc block ↦ lowBlock block acc)
          (List.foldl (fun acc block ↦ highBlock block acc) acc (List.range blocks))
          (List.range blocks) := by
          apply foldl_pair
          intro i j hij hj x
          have hlow₁ :
              highBlock j
                (butterflyDIFInner twiddlesLow q 0 (i * (4 * q)) (q + i * (4 * q)) x) =
              butterflyDIFInner twiddlesLow q 0 (i * (4 * q)) (q + i * (4 * q))
                (highBlock j x) := by
            simpa [highBlock, three_mul_add_eq_add_two_mul_add, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using
              (butterflyDIFInner_comm twiddlesHigh twiddlesLow (2 * q) q (j * (4 * q))
                (2 * q) (i * (4 * q)) q (by
                  intro a ha b hb
                  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith) x)
          have hlow₂ (x' : Array R) :
              highBlock j
                (butterflyDIFInner twiddlesLow q 0 (2 * q + i * (4 * q))
                  (2 * q + (i * (4 * q) + q)) x') =
              butterflyDIFInner twiddlesLow q 0 (2 * q + i * (4 * q))
                (2 * q + (i * (4 * q) + q)) (highBlock j x') := by
            simpa [highBlock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (butterflyDIFInner_comm twiddlesHigh twiddlesLow (2 * q) q (j * (4 * q))
                (2 * q) (2 * q + i * (4 * q)) q (by
                  intro a ha b hb
                  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith) x')
          simp only [lowBlock]
          rw [← hlow₁]
          rw [← hlow₂]
    _ = List.foldl (fun acc block ↦ lowStep block acc)
          (List.foldl (fun acc block ↦ highBlock block acc) acc (List.range blocks))
          (List.range (2 * blocks)) := by
          calc
            List.foldl (fun acc block ↦ lowBlock block acc)
                (List.foldl (fun acc block ↦ highBlock block acc) acc (List.range blocks))
                (List.range blocks) =
                List.foldl (fun acc block ↦ lowStep (2 * block + 1) (lowStep (2 * block) acc))
                  (List.foldl (fun acc block ↦ highBlock block acc) acc (List.range blocks))
                  (List.range blocks) := by
                  apply foldl_range_congr
                  intro block hblock acc
                  unfold lowBlock lowStep
                  exact congrArg
                    (fun p : Nat × Nat × Nat × Nat ↦
                      butterflyDIFInner twiddlesLow q 0 p.1 p.2.1
                        (butterflyDIFInner twiddlesLow q 0 p.2.2.1 p.2.2.2 acc))
                    (show
                      ((2 * q + block * (4 * q), 2 * q + (block * (4 * q) + q),
                          block * (4 * q), q + block * (4 * q)) : Nat × Nat × Nat × Nat) =
                        (((2 * block + 1) * (2 * q), (2 * block + 1) * (2 * q) + q,
                          2 * block * (2 * q), 2 * block * (2 * q) + q) :
                          Nat × Nat × Nat × Nat) by
                      ext <;> nlinarith)
            _ = List.foldl (fun acc block ↦ lowStep block acc)
                  (List.foldl (fun acc block ↦ highBlock block acc) acc (List.range blocks))
                  (List.range (2 * blocks)) := by
                  exact foldl_range_pair lowStep blocks
                    (List.foldl (fun acc block ↦ highBlock block acc) acc (List.range blocks))
    _ = butterflyDIFBlocks twiddlesLow (2 * q) q (2 * blocks) 0
          (butterflyDIFBlocks twiddlesHigh (4 * q) (2 * q) blocks 0 acc) := by
          have hhigh :
              List.foldl (fun acc block ↦ highBlock block acc) acc (List.range blocks) =
                butterflyDIFBlocks twiddlesHigh (4 * q) (2 * q) blocks 0 acc := by
            symm
            simpa [List.range_eq_range', highBlock] using
              (butterflyDIFBlocks_eq_foldl_inner twiddlesHigh (4 * q) (2 * q) blocks
                blocks 0 acc (by simp))
          rw [hhigh]
          symm
          simpa [List.range_eq_range', lowStep] using
            (butterflyDIFBlocks_eq_foldl_inner twiddlesLow (2 * q) q (2 * blocks)
              (2 * blocks) 0 (butterflyDIFBlocks twiddlesHigh (4 * q) (2 * q) blocks 0 acc)
              (by simp))

private theorem butterflyRadix4StageDIFWithTwiddles_eq_two_stages
    (D : NTT.Domain R) (lowStage : Nat) (twiddlesHigh twiddlesLow a : Array R)
    (ha : a.size = D.n) (hstage : lowStage + 1 < D.logN) :
    butterflyRadix4StageDIFWithTwiddles D lowStage twiddlesHigh twiddlesLow a =
      butterflyStageDIFWithTwiddles D lowStage twiddlesLow
        (butterflyStageDIFWithTwiddles D (lowStage + 1) twiddlesHigh a) := by
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
  unfold butterflyRadix4StageDIFWithTwiddles butterflyStageDIFWithTwiddles
  simpa [NTT.Domain.n, hblockSize, hhalf, hblocks', Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (butterflyDIFRadix4Blocks_eq_two_dif_blocks twiddlesHigh twiddlesLow
      (2 ^ lowStage) (D.n / 2 ^ (lowStage + 2)) a hq hbound)

private theorem runStagesDIFRadix4WithTwiddles_eq_difMathStageSpec
    (D : NTT.Domain R) (a : Array R) :
    runStagesDIFRadix4WithTwiddles D (twiddleTable D) (loadNatural D a) =
      difMathStageSpec D D.logN a := by
  let radixStep : Nat → Array R → Array R :=
    fun pass acc ↦
      let highStage := D.logN - 1 - 2 * pass
      let lowStage := highStage - 1
      butterflyRadix4StageDIFWithTwiddles D lowStage
        ((twiddleTable D).getD highStage #[]) ((twiddleTable D).getD lowStage #[]) acc
  have hloop :
      ∀ n, n ≤ D.logN / 2 →
        List.foldl (fun acc pass ↦ radixStep pass acc) (loadNatural D a) (List.range n) =
          difMathStageSpec D (2 * n) a := by
    intro n hn
    induction n with
    | zero =>
        rw [difMathStageSpec_zero]
        simp
    | succ n ih =>
        have hnle : n ≤ D.logN / 2 := Nat.le_of_succ_le hn
        have hnlt : n < D.logN / 2 := Nat.lt_of_succ_le hn
        let highStage := D.logN - 1 - 2 * n
        let lowStage := highStage - 1
        have hhigh : highStage < D.logN := by
          dsimp [highStage]
          omega
        have hlowPair : lowStage + 1 = highStage := by
          dsimp [lowStage, highStage]
          omega
        have hlowStage : lowStage + 1 < D.logN := by
          rw [hlowPair]
          exact hhigh
        have hprev : D.logN - (highStage + 1) = 2 * n := by
          dsimp [highStage]
          omega
        have hmid : D.logN - (lowStage + 1) = 2 * n + 1 := by
          rw [hlowPair]
          dsimp [highStage]
          omega
        have hfinal : D.logN - lowStage = 2 * (n + 1) := by
          dsimp [lowStage, highStage]
          omega
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ih hnle]
        change radixStep n (difMathStageSpec D (2 * n) a) =
          difMathStageSpec D (2 * (n + 1)) a
        simp only [radixStep]
        change butterflyRadix4StageDIFWithTwiddles D lowStage
            ((twiddleTable D).getD highStage #[]) ((twiddleTable D).getD lowStage #[])
            (difMathStageSpec D (2 * n) a) =
          difMathStageSpec D (2 * (n + 1)) a
        rw [butterflyRadix4StageDIFWithTwiddles_eq_two_stages D lowStage
          ((twiddleTable D).getD highStage #[]) ((twiddleTable D).getD lowStage #[])
          (difMathStageSpec D (2 * n) a) (by simp [difMathStageSpec]) hlowStage]
        have hhighStep :
            butterflyStageDIFWithTwiddles D highStage ((twiddleTable D).getD highStage #[])
                (difMathStageSpec D (2 * n) a) =
              difMathStageSpec D (2 * n + 1) a := by
          convert butterflyStageDIFWithTwiddles_difMathStageSpec_succ D highStage
            ((twiddleTable D).getD highStage #[]) a hhigh ?_ using 1
          · rw [hprev]
          · rw [show D.logN - highStage = 2 * n + 1 by
              dsimp [highStage]
              omega]
          · intro j hj
            rw [twiddleTable_getD_eq_twiddlePowers D highStage hhigh]
            exact twiddlePowers_getD_eq_pow D highStage j hj
        rw [hlowPair]
        rw [hhighStep]
        have hlow : lowStage < D.logN := by omega
        have hlowStep :
            butterflyStageDIFWithTwiddles D lowStage ((twiddleTable D).getD lowStage #[])
                (difMathStageSpec D (2 * n + 1) a) =
              difMathStageSpec D (2 * (n + 1)) a := by
          convert butterflyStageDIFWithTwiddles_difMathStageSpec_succ D lowStage
            ((twiddleTable D).getD lowStage #[]) a hlow ?_ using 1
          · rw [hmid]
          · rw [hfinal]
          · intro j hj
            rw [twiddleTable_getD_eq_twiddlePowers D lowStage hlow]
            exact twiddlePowers_getD_eq_pow D lowStage j hj
        exact hlowStep
  have hpairs := hloop (D.logN / 2) le_rfl
  let stageZero : Array R → Array R :=
    fun acc ↦ butterflyStageDIFWithTwiddles D 0 ((twiddleTable D).getD 0 #[]) acc
  calc
    runStagesDIFRadix4WithTwiddles D (twiddleTable D) (loadNatural D a) =
        (if D.logN % 2 = 1 then
          stageZero (List.foldl (fun acc pass ↦ radixStep pass acc) (loadNatural D a)
            (List.range (D.logN / 2)))
        else
          List.foldl (fun acc pass ↦ radixStep pass acc) (loadNatural D a)
            (List.range (D.logN / 2))) := by
          by_cases hodd : D.logN % 2 = 1
          · simp [runStagesDIFRadix4WithTwiddles, radixStep, stageZero, List.range_eq_range',
              hodd]
          · simp [runStagesDIFRadix4WithTwiddles, radixStep, stageZero, List.range_eq_range',
              hodd]
    _ = (if D.logN % 2 = 1 then
          stageZero (difMathStageSpec D (2 * (D.logN / 2)) a)
        else
          difMathStageSpec D (2 * (D.logN / 2)) a) := by
          rw [hpairs]
    _ = difMathStageSpec D D.logN a := by
          by_cases hodd : D.logN % 2 = 1
          · have hcompleted : 2 * (D.logN / 2) = D.logN - 1 := by omega
            have hlog : 0 < D.logN := by omega
            simp only [hodd, ↓reduceIte]
            rw [hcompleted]
            dsimp [stageZero]
            apply butterflyStageDIFWithTwiddles_difMathStageSpec_succ
            · exact hlog
            · intro j hj
              rw [twiddleTable_getD_eq_twiddlePowers D 0 hlog]
              exact twiddlePowers_getD_eq_pow D 0 j hj
          · have hcompleted : 2 * (D.logN / 2) = D.logN := by omega
            simp [hodd, hcompleted]

/-- The mixed radix-4 DIF stage loop computes the bit-reversed forward NTT output. -/
theorem runStagesDIFRadix4WithTwiddles_correct (D : NTT.Domain R) (a : Array R) :
    runStagesDIFRadix4WithTwiddles D (twiddleTable D) (loadNatural D a) =
      NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D a) := by
  rw [runStagesDIFRadix4WithTwiddles_eq_difMathStageSpec, difMathStageSpec_final]

end Plan

end NTTFast
end CPolynomial
end CompPoly
