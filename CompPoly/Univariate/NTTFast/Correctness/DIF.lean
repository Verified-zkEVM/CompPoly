/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTTFast.Correctness.Basic

/-!
# DIF NTTFast correctness

Correctness proofs for the decimation-in-frequency stage loop used by `NTTFast`.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast

open scoped BigOperators

variable {R : Type*} [Field R]

namespace Plan
private def difMathValueAt (D : NTT.Domain R) (completed : Nat) (a : Array R)
    (idx : Nat) : R :=
  let blockSize : Nat := 2 ^ (D.logN - completed)
  let block := idx / blockSize
  let offset := idx % blockSize
  ∑ t : Fin (2 ^ completed),
    a.getD (offset + t.1 * blockSize) 0 *
      D.omega ^ (NTT.Transform.bitRevNat completed block * (offset + t.1 * blockSize))

/-- Mathematical state after completing `completed` descending DIF stages. -/
def difMathStageSpec (D : NTT.Domain R) (completed : Nat) (a : Array R) : Array R :=
  Array.ofFn (fun i : D.Idx ↦ difMathValueAt D completed a i.1)

private def difMathBlocksSpec
    (D : NTT.Domain R) (stage doneBlocks : Nat) (a : Array R) : Array R :=
  let oldCompleted : Nat := D.logN - (stage + 1)
  let newCompleted : Nat := D.logN - stage
  let blockSize : Nat := 2 ^ (stage + 1)
  Array.ofFn (fun i : D.Idx ↦
    if i.1 / blockSize < doneBlocks then
      difMathValueAt D newCompleted a i.1
    else
      difMathValueAt D oldCompleted a i.1)

private def difMathPairsSpec
    (D : NTT.Domain R) (stage block donePairs : Nat) (a : Array R) : Array R :=
  let oldCompleted : Nat := D.logN - (stage + 1)
  let newCompleted : Nat := D.logN - stage
  let half : Nat := 2 ^ stage
  let blockSize : Nat := 2 ^ (stage + 1)
  Array.ofFn (fun i : D.Idx ↦
    let bigBlock := i.1 / blockSize
    let pair := i.1 % half
    if bigBlock < block then
      difMathValueAt D newCompleted a i.1
    else if bigBlock = block then
      if pair < donePairs then
        difMathValueAt D newCompleted a i.1
      else
        difMathValueAt D oldCompleted a i.1
      else
        difMathValueAt D oldCompleted a i.1)

/-- The initial DIF mathematical state is the naturally ordered input. -/
theorem difMathStageSpec_zero (D : NTT.Domain R) (a : Array R) :
    difMathStageSpec D 0 a = NTT.loadNaturalArray D a := by
  apply Array.ext
  · simp [difMathStageSpec, NTT.loadNaturalArray]
  · intro i hi₁ hi₂
    have hi : i < 2 ^ D.logN := by
      simpa [difMathStageSpec, NTT.Domain.n] using hi₁
    have himod : i % 2 ^ D.logN = i := Nat.mod_eq_of_lt hi
    simp [difMathStageSpec, difMathValueAt, NTT.loadNaturalArray, NTT.Domain.n, himod,
      NTT.Transform.bitRevNat]

/-- The final DIF mathematical state is the bit-reversed forward NTT output. -/
theorem difMathStageSpec_final (D : NTT.Domain R) (a : Array R) :
    difMathStageSpec D D.logN a =
      NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D a) := by
  apply Array.ext
  · simp [difMathStageSpec, NTT.Transform.bitRevPermute]
  · intro i hi₁ hi₂
    have hbr : NTT.Transform.bitRevNat D.logN i < D.n := by
      simpa [NTT.Domain.n] using NTT.Transform.bitRevNat_lt D.logN i
    rw [show (NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D a))[i] =
        (NTT.Forward.forwardSpec D a).getD (NTT.Transform.bitRevNat D.logN i) 0 by
      simp [NTT.Transform.bitRevPermute]]
    have hbr' : NTT.Transform.bitRevNat D.logN i < (NTT.Forward.forwardSpec D a).size := by
      simpa [NTT.Forward.forwardSpec] using hbr
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hbr']
    simp [difMathStageSpec, difMathValueAt, NTT.Forward.forwardSpec, NTT.Forward.nttAt,
      NTT.Domain.n, Nat.mod_one]
    rfl

private theorem dif_lower_div_block (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j) / 2 ^ (stage + 1) = block := by
  rw [Nat.mul_comm block (2 ^ (stage + 1))]
  rw [Nat.mul_add_div (Nat.two_pow_pos (stage + 1))]
  have hlt : j < 2 ^ (stage + 1) :=
    Nat.lt_trans hj (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self stage))
  rw [Nat.div_eq_of_lt hlt]
  simp

private theorem dif_upper_div_block (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j + 2 ^ stage) / 2 ^ (stage + 1) = block := by
  rw [show block * 2 ^ (stage + 1) + j + 2 ^ stage =
      block * 2 ^ (stage + 1) + (j + 2 ^ stage) by omega]
  rw [Nat.mul_comm block (2 ^ (stage + 1))]
  rw [Nat.mul_add_div (Nat.two_pow_pos (stage + 1))]
  have hlt : j + 2 ^ stage < 2 ^ (stage + 1) := by
    rw [pow_succ]
    omega
  rw [Nat.div_eq_of_lt hlt]
  simp

private theorem dif_lower_mod_half (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j) % 2 ^ stage = j := by
  rw [show block * 2 ^ (stage + 1) + j = (block * 2) * 2 ^ stage + j by
    rw [pow_succ]
    ring]
  rw [Nat.mul_add_mod_self_right]
  exact Nat.mod_eq_of_lt hj

private theorem dif_upper_mod_half (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j + 2 ^ stage) % 2 ^ stage = j := by
  rw [show block * 2 ^ (stage + 1) + j + 2 ^ stage =
      (block * 2 + 1) * 2 ^ stage + j by
    rw [pow_succ]
    ring]
  rw [Nat.mul_add_mod_self_right]
  exact Nat.mod_eq_of_lt hj

private theorem dif_lower_div_half (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j) / 2 ^ stage = block * 2 := by
  rw [show block * 2 ^ (stage + 1) + j = (block * 2) * 2 ^ stage + j by
    rw [pow_succ]
    ring]
  rw [Nat.mul_comm (block * 2) (2 ^ stage)]
  rw [Nat.mul_add_div (Nat.two_pow_pos stage)]
  rw [Nat.div_eq_of_lt hj]
  simp

private theorem dif_upper_div_half (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j + 2 ^ stage) / 2 ^ stage = block * 2 + 1 := by
  rw [show block * 2 ^ (stage + 1) + j + 2 ^ stage =
      (block * 2 + 1) * 2 ^ stage + j by
    rw [pow_succ]
    ring]
  rw [Nat.mul_comm (block * 2 + 1) (2 ^ stage)]
  rw [Nat.mul_add_div (Nat.two_pow_pos stage)]
  rw [Nat.div_eq_of_lt hj]

private theorem dif_lower_mod_blockSize (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j) % 2 ^ (stage + 1) = j := by
  rw [Nat.mul_add_mod_self_right block (2 ^ (stage + 1)) j]
  exact Nat.mod_eq_of_lt
    (Nat.lt_trans hj (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self stage)))

private theorem dif_upper_mod_blockSize (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j + 2 ^ stage) % 2 ^ (stage + 1) =
      j + 2 ^ stage := by
  rw [show block * 2 ^ (stage + 1) + j + 2 ^ stage =
      block * 2 ^ (stage + 1) + (j + 2 ^ stage) by omega]
  rw [Nat.mul_add_mod_self_right block (2 ^ (stage + 1)) (j + 2 ^ stage)]
  exact Nat.mod_eq_of_lt (by
    rw [pow_succ]
    omega)

private theorem omega_pow_domain_mul (D : NTT.Domain R) (k : Nat) :
    D.omega ^ (D.n * k) = 1 := by
  have h : D.omega ^ D.n = 1 := by
    simpa [NTT.Domain.n] using D.primitive.pow_eq_one
  rw [pow_mul, h, one_pow]

private theorem omega_pow_add_domain_mul (D : NTT.Domain R) (e k : Nat) :
    D.omega ^ (e + D.n * k) = D.omega ^ e := by
  rw [pow_add, omega_pow_domain_mul D k]
  simp

private theorem omega_pow_domain_half_eq_neg_one
    (D : NTT.Domain R) (hlog : 0 < D.logN) :
    D.omega ^ (D.n / 2) = -1 := by
  have hdiv : 2 ∣ D.n := by
    simpa [NTT.Domain.n] using Nat.pow_dvd_pow 2 (show 1 ≤ D.logN by omega)
  have hprod : D.n = D.n / 2 * 2 := by
    exact (Nat.div_mul_cancel hdiv).symm
  have hprim2 : IsPrimitiveRoot (D.omega ^ (D.n / 2)) 2 := by
    exact IsPrimitiveRoot.pow D.n_pos D.primitive hprod
  exact IsPrimitiveRoot.eq_neg_one_of_two_right hprim2

private theorem difMathBlocksSpec_zero
    (D : NTT.Domain R) (stage : Nat) (a : Array R) :
    difMathBlocksSpec D stage 0 a = difMathStageSpec D (D.logN - (stage + 1)) a := by
  apply Array.ext
  · simp [difMathBlocksSpec, difMathStageSpec]
  · intro i hi₁ hi₂
    simp [difMathBlocksSpec, difMathStageSpec]

private theorem difMathPairsSpec_zero
    (D : NTT.Domain R) (stage block : Nat) (a : Array R) :
    difMathPairsSpec D stage block 0 a = difMathBlocksSpec D stage block a := by
  apply Array.ext
  · simp [difMathPairsSpec, difMathBlocksSpec]
  · intro i hi₁ hi₂
    simp [difMathPairsSpec, difMathBlocksSpec]

private theorem difMathPairsSpec_half
    (D : NTT.Domain R) (stage block : Nat) (a : Array R) :
    difMathPairsSpec D stage block (2 ^ stage) a =
      difMathBlocksSpec D stage (block + 1) a := by
  apply Array.ext
  · simp [difMathPairsSpec, difMathBlocksSpec]
  · intro i hi₁ hi₂
    let bb : Nat := i / 2 ^ (stage + 1)
    let v1 : R := difMathValueAt D (D.logN - stage) a i
    let v0 : R := difMathValueAt D (D.logN - (stage + 1)) a i
    have hpair : i % 2 ^ stage < 2 ^ stage :=
      Nat.mod_lt _ (Nat.two_pow_pos stage)
    have hcase :
        (if bb < block then
          v1
        else if bb = block then
          if i % 2 ^ stage < 2 ^ stage then v1 else v0
        else
          v0)
          = (if bb < block + 1 then v1 else v0) := by
      by_cases hlt : bb < block
      · have hlt' : bb < block + 1 := Nat.lt_trans hlt (Nat.lt_succ_self _)
        rw [if_pos hlt, if_pos hlt']
      · by_cases hEq : bb = block
        · have hlt' : bb < block + 1 := by simp [hEq]
          rw [if_neg hlt, if_pos hEq, if_pos hpair, if_pos hlt']
        · have hnot : ¬bb < block + 1 := by
            exact not_lt_of_ge
              (Nat.succ_le_of_lt
                (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hEq)))
          rw [if_neg hlt, if_neg hEq, if_neg hnot]
    simpa [difMathPairsSpec, difMathBlocksSpec, bb, v1, v0] using hcase

private theorem difMathBlocksSpec_final
    (D : NTT.Domain R) (stage : Nat) (a : Array R) (hstage : stage < D.logN) :
    difMathBlocksSpec D stage (D.n / 2 ^ (stage + 1)) a =
      difMathStageSpec D (D.logN - stage) a := by
  apply Array.ext
  · simp [difMathBlocksSpec, difMathStageSpec]
  · intro i hi₁ hi₂
    let blockSize : Nat := 2 ^ (stage + 1)
    let bb : Nat := i / blockSize
    let v1 : R := difMathValueAt D (D.logN - stage) a i
    let v0 : R := difMathValueAt D (D.logN - (stage + 1)) a i
    have hi : i < D.n := by
      simpa [difMathStageSpec] using hi₂
    have hdiv : blockSize ∣ D.n := by
      dsimp [blockSize]
      simpa [NTT.Domain.n] using Nat.pow_dvd_pow 2 (Nat.succ_le_of_lt hstage)
    have hmul : blockSize * (D.n / blockSize) = D.n := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hdiv
    have hmul' : blockSize * (2 ^ D.logN / blockSize) = 2 ^ D.logN := by
      simpa [NTT.Domain.n] using hmul
    have hblock : bb < D.n / blockSize := by
      dsimp [bb]
      apply Nat.div_lt_of_lt_mul
      rw [hmul']
      simpa [NTT.Domain.n] using hi
    have hcase : (if bb < D.n / blockSize then v1 else v0) = v1 := by
      rw [if_pos hblock]
    simpa [difMathBlocksSpec, difMathStageSpec, blockSize, bb, v1, v0] using hcase

private theorem eq_lower_or_upper_of_block_pair
    (stage block j i : Nat)
    (hblock : i / 2 ^ (stage + 1) = block) (hpair : i % 2 ^ stage = j) :
    i = block * 2 ^ (stage + 1) + j ∨
      i = block * 2 ^ (stage + 1) + j + 2 ^ stage := by
  let half : Nat := 2 ^ stage
  let r : Nat := i % 2 ^ (stage + 1)
  have hblockSize : 2 ^ (stage + 1) = 2 * half := by
    simp [half, pow_succ, Nat.mul_comm]
  have hi_decomp : i = block * 2 ^ (stage + 1) + r := by
    calc
      i = 2 ^ (stage + 1) * (i / 2 ^ (stage + 1)) + i % 2 ^ (stage + 1) := by
        exact (Nat.div_add_mod i (2 ^ (stage + 1))).symm
      _ = i / 2 ^ (stage + 1) * 2 ^ (stage + 1) + i % 2 ^ (stage + 1) := by
        ring
      _ = block * 2 ^ (stage + 1) + r := by
        simp [hblock, r]
  have hr_lt : r < 2 * half := by
    simpa [r, hblockSize] using Nat.mod_lt i (Nat.two_pow_pos (stage + 1))
  have hhalf_dvd : half ∣ 2 ^ (stage + 1) := by
    rw [hblockSize]
    exact ⟨2, by ring⟩
  have hr_mod : r % half = j := by
    simpa [r, half, hpair] using (Nat.mod_mod_of_dvd i hhalf_dvd)
  have hr_decomp : r = (r / half) * half + j := by
    calc
      r = half * (r / half) + r % half := by
        exact (Nat.div_add_mod r half).symm
      _ = r / half * half + r % half := by
        ring
      _ = r / half * half + j := by rw [hr_mod]
  have hq_lt : r / half < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos stage)]
    simpa [half, Nat.mul_comm] using hr_lt
  interval_cases hq : r / half
  · left
    rw [hi_decomp, hr_decomp]
    simp
  · right
    rw [hi_decomp, hr_decomp]
    simp [half]
    omega

private theorem difMathPairsSpec_get_lower_current
    (D : NTT.Domain R) (stage block j : Nat) (a : Array R) (hj : j < 2 ^ stage)
    (hi : block * 2 ^ (stage + 1) + j < (difMathPairsSpec D stage block j a).size) :
    (difMathPairsSpec D stage block j a)[block * 2 ^ (stage + 1) + j] =
      difMathValueAt D (D.logN - (stage + 1)) a (block * 2 ^ (stage + 1) + j) := by
  simp [difMathPairsSpec, dif_lower_div_block stage block j hj,
    dif_lower_mod_half stage block j hj]

private theorem difMathPairsSpec_get_upper_current
    (D : NTT.Domain R) (stage block j : Nat) (a : Array R) (hj : j < 2 ^ stage)
    (hi : block * 2 ^ (stage + 1) + j + 2 ^ stage <
      (difMathPairsSpec D stage block j a).size) :
    (difMathPairsSpec D stage block j a)[block * 2 ^ (stage + 1) + j + 2 ^ stage] =
      difMathValueAt D (D.logN - (stage + 1)) a
        (block * 2 ^ (stage + 1) + j + 2 ^ stage) := by
  simp [difMathPairsSpec, dif_upper_div_block stage block j hj,
    dif_upper_mod_half stage block j hj]

private theorem difMathPairsSpec_get_lower_next
    (D : NTT.Domain R) (stage block j : Nat) (a : Array R) (hj : j < 2 ^ stage)
    (hi : block * 2 ^ (stage + 1) + j < (difMathPairsSpec D stage block (j + 1) a).size) :
    (difMathPairsSpec D stage block (j + 1) a)[block * 2 ^ (stage + 1) + j] =
      difMathValueAt D (D.logN - stage) a (block * 2 ^ (stage + 1) + j) := by
  simp [difMathPairsSpec, dif_lower_div_block stage block j hj,
    dif_lower_mod_half stage block j hj]

private theorem difMathPairsSpec_get_upper_next
    (D : NTT.Domain R) (stage block j : Nat) (a : Array R) (hj : j < 2 ^ stage)
    (hi : block * 2 ^ (stage + 1) + j + 2 ^ stage <
      (difMathPairsSpec D stage block (j + 1) a).size) :
    (difMathPairsSpec D stage block (j + 1) a)[block * 2 ^ (stage + 1) + j + 2 ^ stage] =
      difMathValueAt D (D.logN - stage) a
        (block * 2 ^ (stage + 1) + j + 2 ^ stage) := by
  simp [difMathPairsSpec, dif_upper_div_block stage block j hj,
    dif_upper_mod_half stage block j hj]

private theorem difMathPairsSpec_get_unchanged
    (D : NTT.Domain R) (stage block j : Nat) (a : Array R)
    {i : Nat}
    (hiOld : i < (difMathPairsSpec D stage block j a).size)
    (hiNew : i < (difMathPairsSpec D stage block (j + 1) a).size)
    (hneLower : block * 2 ^ (stage + 1) + j ≠ i)
    (hneUpper : block * 2 ^ (stage + 1) + j + 2 ^ stage ≠ i) :
    (difMathPairsSpec D stage block j a)[i] =
      (difMathPairsSpec D stage block (j + 1) a)[i] := by
  simp only [difMathPairsSpec, Array.getElem_ofFn]
  by_cases hltBlock : i / 2 ^ (stage + 1) < block
  · rw [if_pos hltBlock, if_pos hltBlock]
  · rw [if_neg hltBlock, if_neg hltBlock]
    by_cases hEqBlock : i / 2 ^ (stage + 1) = block
    · rw [if_pos hEqBlock, if_pos hEqBlock]
      by_cases hltPair : i % 2 ^ stage < j
      · rw [if_pos hltPair, if_pos (Nat.lt_trans hltPair (Nat.lt_succ_self j))]
      · have hgePair : j ≤ i % 2 ^ stage := Nat.le_of_not_lt hltPair
        rw [if_neg hltPair]
        by_cases hltPairNext : i % 2 ^ stage < j + 1
        · have hpair : i % 2 ^ stage = j := by omega
          rcases eq_lower_or_upper_of_block_pair stage block j i hEqBlock hpair with h | h
          · exact (hneLower h.symm).elim
          · exact (hneUpper h.symm).elim
        · rw [if_neg hltPairNext]
    · rw [if_neg hEqBlock, if_neg hEqBlock]

private theorem dif_upper_lt_of_lower_lt_domain
    (D : NTT.Domain R) (stage block j : Nat) (hstage : stage < D.logN) (hj : j < 2 ^ stage)
    (hlower : block * 2 ^ (stage + 1) + j < D.n) :
    block * 2 ^ (stage + 1) + j + 2 ^ stage < D.n := by
  let blocks : Nat := 2 ^ (D.logN - (stage + 1))
  let blockSize : Nat := 2 ^ (stage + 1)
  have hN : D.n = blocks * blockSize := by
    dsimp [NTT.Domain.n, blocks, blockSize]
    rw [← pow_add]
    congr 1
    omega
  have hlower' : block * blockSize + j < blocks * blockSize := by
    rw [← hN]
    simpa [blockSize] using hlower
  have hblock : block < blocks := by
    by_contra hnot
    have hle : blocks ≤ block := Nat.le_of_not_lt hnot
    have hmul : blocks * blockSize ≤ block * blockSize := Nat.mul_le_mul_right blockSize hle
    have hle' : blocks * blockSize ≤ block * blockSize + j :=
      Nat.le_trans hmul (Nat.le_add_right _ _)
    omega
  have hupperBlock :
      block * blockSize + j + 2 ^ stage < (block + 1) * blockSize := by
    calc
      block * blockSize + j + 2 ^ stage < block * blockSize + blockSize := by
        have hjBlock : j + 2 ^ stage < blockSize := by
          dsimp [blockSize]
          rw [pow_succ]
          omega
        omega
      _ = (block + 1) * blockSize := by ring
  have hnext : block + 1 ≤ blocks := Nat.succ_le_of_lt hblock
  have hnextMul : (block + 1) * blockSize ≤ blocks * blockSize :=
    Nat.mul_le_mul_right blockSize hnext
  rw [hN]
  exact Nat.lt_of_lt_of_le hupperBlock hnextMul

private theorem difMathValueAt_succ_lower
    (D : NTT.Domain R) (stage block j : Nat) (a : Array R)
    (hstage : stage < D.logN) (hj : j < 2 ^ stage) :
    difMathValueAt D (D.logN - stage) a (block * 2 ^ (stage + 1) + j) =
      difMathValueAt D (D.logN - (stage + 1)) a (block * 2 ^ (stage + 1) + j) +
        difMathValueAt D (D.logN - (stage + 1)) a
          (block * 2 ^ (stage + 1) + j + 2 ^ stage) := by
  have hsubNew : D.logN - (D.logN - stage) = stage := by omega
  have hsubOld : D.logN - (D.logN - (stage + 1)) = stage + 1 := by omega
  simp [difMathValueAt,
    hsubNew, hsubOld,
    dif_lower_div_half stage block j hj,
    dif_lower_mod_half stage block j hj,
    dif_lower_div_block stage block j hj,
    dif_lower_mod_blockSize stage block j hj,
    dif_upper_div_block stage block j hj,
    dif_upper_mod_blockSize stage block j hj]
  have hbits : D.logN - stage = (D.logN - (stage + 1)) + 1 := by
    omega
  rw [hbits]
  rw [← Fin.sum_univ_pow_two_even_add_odd
    (n := D.logN - (stage + 1))
    (f := fun x ↦
      a[j + x * 2 ^ stage]?.getD 0 *
        D.omega ^ (NTT.Transform.bitRevNat ((D.logN - (stage + 1)) + 1) (block * 2) *
          (j + x * 2 ^ stage)))]
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    rw [show block * 2 = 2 * block by ring]
    rw [NTT.Transform.bitRevNat_even]
    rw [show j + 2 * ↑x * 2 ^ stage = j + ↑x * 2 ^ (stage + 1) by
      rw [pow_succ]
      ring]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [show block * 2 = 2 * block by ring]
    rw [NTT.Transform.bitRevNat_even]
    rw [show j + (2 * ↑x + 1) * 2 ^ stage = j + 2 ^ stage + ↑x * 2 ^ (stage + 1) by
      rw [pow_succ]
      ring]

private theorem difMathValueAt_succ_upper
    (D : NTT.Domain R) (stage block j : Nat) (a : Array R)
    (hstage : stage < D.logN) (hj : j < 2 ^ stage) :
    difMathValueAt D (D.logN - stage) a
        (block * 2 ^ (stage + 1) + j + 2 ^ stage) =
      (D.omega ^ (D.n / 2 ^ (stage + 1))) ^ j *
        (difMathValueAt D (D.logN - (stage + 1)) a (block * 2 ^ (stage + 1) + j) -
          difMathValueAt D (D.logN - (stage + 1)) a
            (block * 2 ^ (stage + 1) + j + 2 ^ stage)) := by
  have hsubNew : D.logN - (D.logN - stage) = stage := by omega
  have hsubOld : D.logN - (D.logN - (stage + 1)) = stage + 1 := by omega
  simp [difMathValueAt,
    hsubNew, hsubOld,
    dif_upper_div_half stage block j hj,
    dif_upper_mod_half stage block j hj,
    dif_lower_div_block stage block j hj,
    dif_lower_mod_blockSize stage block j hj,
    dif_upper_div_block stage block j hj,
    dif_upper_mod_blockSize stage block j hj]
  have hbits : D.logN - stage = (D.logN - (stage + 1)) + 1 := by
    omega
  have hstride : D.n / 2 ^ (stage + 1) = 2 ^ (D.logN - (stage + 1)) := by
    rw [NTT.Domain.n]
    exact Nat.pow_div (Nat.succ_le_of_lt hstage) (by decide : 0 < 2)
  have hstride' : 2 ^ D.logN / 2 ^ (stage + 1) = 2 ^ (D.logN - (stage + 1)) := by
    simpa [NTT.Domain.n] using hstride
  rw [hstride']
  rw [← pow_mul]
  rw [hbits]
  rw [← Fin.sum_univ_pow_two_even_add_odd
    (n := D.logN - (stage + 1))
    (f := fun x ↦
      a[j + x * 2 ^ stage]?.getD 0 *
        D.omega ^ (NTT.Transform.bitRevNat ((D.logN - (stage + 1)) + 1) (block * 2 + 1) *
          (j + x * 2 ^ stage)))]
  rw [mul_sub]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [sub_eq_add_neg]
  have hN :
      D.n = 2 ^ (D.logN - (stage + 1)) * 2 ^ (stage + 1) := by
    rw [NTT.Domain.n, ← pow_add]
    congr 1
    omega
  have hHalf :
      D.n / 2 = 2 ^ (D.logN - (stage + 1)) * 2 ^ stage := by
    rw [NTT.Domain.n, Nat.pow_div (show 1 ≤ D.logN by omega) (by decide : 0 < 2)]
    rw [← pow_add]
    congr 1
    omega
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    rw [show block * 2 + 1 = 2 * block + 1 by ring]
    rw [NTT.Transform.bitRevNat_odd]
    rw [show j + 2 * ↑x * 2 ^ stage = j + ↑x * 2 ^ (stage + 1) by
      rw [pow_succ]
      ring]
    rw [show (2 ^ (D.logN - (stage + 1)) +
          NTT.Transform.bitRevNat (D.logN - (stage + 1)) block) *
          (j + ↑x * 2 ^ (stage + 1)) =
        2 ^ (D.logN - (stage + 1)) * j +
          NTT.Transform.bitRevNat (D.logN - (stage + 1)) block *
            (j + ↑x * 2 ^ (stage + 1)) +
          D.n * ↑x by
      rw [hN]
      ring]
    rw [omega_pow_add_domain_mul]
    rw [pow_add]
    ring
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show block * 2 + 1 = 2 * block + 1 by ring]
    rw [NTT.Transform.bitRevNat_odd]
    rw [show j + (2 * ↑x + 1) * 2 ^ stage =
        j + 2 ^ stage + ↑x * 2 ^ (stage + 1) by
      rw [pow_succ]
      ring]
    rw [show (2 ^ (D.logN - (stage + 1)) +
          NTT.Transform.bitRevNat (D.logN - (stage + 1)) block) *
          (j + 2 ^ stage + ↑x * 2 ^ (stage + 1)) =
        (D.n / 2 +
          (2 ^ (D.logN - (stage + 1)) * j +
            NTT.Transform.bitRevNat (D.logN - (stage + 1)) block *
              (j + 2 ^ stage + ↑x * 2 ^ (stage + 1)))) +
          D.n * ↑x by
      rw [hHalf, hN]
      ring]
    rw [omega_pow_add_domain_mul]
    rw [show D.omega ^ (D.n / 2 +
          (2 ^ (D.logN - (stage + 1)) * j +
            NTT.Transform.bitRevNat (D.logN - (stage + 1)) block *
              (j + 2 ^ stage + ↑x * 2 ^ (stage + 1)))) =
        -D.omega ^
          (2 ^ (D.logN - (stage + 1)) * j +
            NTT.Transform.bitRevNat (D.logN - (stage + 1)) block *
              (j + 2 ^ stage + ↑x * 2 ^ (stage + 1))) by
      rw [pow_add, omega_pow_domain_half_eq_neg_one D (by omega)]
      ring]
    rw [pow_add]
    ring

private theorem butterflyDIFPairStep_difMathPairsSpec_succ
    (D : NTT.Domain R) (stage block j : Nat) (twiddles : Array R) (a : Array R)
    (hstage : stage < D.logN) (hj : j < 2 ^ stage)
    (htw : twiddles.getD j 0 = (D.omega ^ (D.n / 2 ^ (stage + 1))) ^ j) :
    let lower := block * 2 ^ (stage + 1) + j
    let upper := lower + 2 ^ stage
    let acc := difMathPairsSpec D stage block j a
    let u := acc.getD lower 0
    let v := acc.getD upper 0
    (acc.set! lower (u + v)).set! upper (twiddles.getD j 0 * (u - v)) =
      difMathPairsSpec D stage block (j + 1) a := by
  dsimp only
  apply Array.ext
  · simp [difMathPairsSpec, Array.set!, Array.size_setIfInBounds]
  · intro i hi₁ hi₂
    simp only [Array.set!, Array.size_setIfInBounds] at hi₁
    simp [Array.set!, Array.getElem_setIfInBounds, hi₁]
    by_cases hUpper : block * 2 ^ (stage + 1) + j + 2 ^ stage = i
    · rw [if_pos hUpper]
      subst i
      have hUpperOld :
          block * 2 ^ (stage + 1) + j + 2 ^ stage <
            (difMathPairsSpec D stage block j a).size := by
        simpa [difMathPairsSpec] using hi₁
      have hLowerOld :
          block * 2 ^ (stage + 1) + j <
            (difMathPairsSpec D stage block j a).size := by
        simpa [difMathPairsSpec] using (show
          block * 2 ^ (stage + 1) + j < D.n by
            have h : block * 2 ^ (stage + 1) + j + 2 ^ stage < D.n := by
              simpa [difMathPairsSpec] using hi₁
            omega)
      rw [Array.getElem?_eq_getElem hLowerOld]
      rw [Array.getElem?_eq_getElem hUpperOld]
      simp only [Option.getD_some]
      rw [difMathPairsSpec_get_lower_current D stage block j a hj hLowerOld]
      rw [difMathPairsSpec_get_upper_current D stage block j a hj hUpperOld]
      rw [difMathPairsSpec_get_upper_next D stage block j a hj hi₂]
      rw [← (Array.getD_eq_getD_getElem? (xs := twiddles) (i := j) (d := 0)), htw]
      exact (difMathValueAt_succ_upper D stage block j a hstage hj).symm
    · rw [if_neg hUpper]
      by_cases hLower : block * 2 ^ (stage + 1) + j = i
      · rw [if_pos hLower]
        subst i
        have hLowerDomain : block * 2 ^ (stage + 1) + j < D.n := by
          simpa [difMathPairsSpec] using hi₁
        have hUpperDomain :
            block * 2 ^ (stage + 1) + j + 2 ^ stage < D.n :=
          dif_upper_lt_of_lower_lt_domain D stage block j hstage hj hLowerDomain
        have hUpperOld :
            block * 2 ^ (stage + 1) + j + 2 ^ stage <
              (difMathPairsSpec D stage block j a).size := by
          simpa [difMathPairsSpec] using hUpperDomain
        rw [Array.getElem?_eq_getElem hi₁]
        rw [Array.getElem?_eq_getElem hUpperOld]
        simp only [Option.getD_some]
        rw [difMathPairsSpec_get_lower_current D stage block j a hj hi₁]
        rw [difMathPairsSpec_get_upper_current D stage block j a hj hUpperOld]
        rw [difMathPairsSpec_get_lower_next D stage block j a hj hi₂]
        exact (difMathValueAt_succ_lower D stage block j a hstage hj).symm
      · rw [if_neg hLower]
        exact difMathPairsSpec_get_unchanged D stage block j a hi₁ hi₂ hLower hUpper

private theorem butterflyDIFInner_difMathPairsSpec_final
    (D : NTT.Domain R) (stage block : Nat) (twiddles : Array R) (a : Array R)
    (hstage : stage < D.logN)
    (htw : ∀ j, j < 2 ^ stage →
      twiddles.getD j 0 = (D.omega ^ (D.n / 2 ^ (stage + 1))) ^ j) :
    ∀ n j,
      2 ^ stage = j + n →
        butterflyDIFInner twiddles (2 ^ stage) j
            (block * 2 ^ (stage + 1) + j)
            (block * 2 ^ (stage + 1) + j + 2 ^ stage)
            (difMathPairsSpec D stage block j a) =
          difMathPairsSpec D stage block (2 ^ stage) a
  | 0, j, hlimit => by
      simp [butterflyDIFInner, hlimit]
  | n + 1, j, hlimit => by
      have hj : j < 2 ^ stage := by omega
      have htail : 2 ^ stage = j + 1 + n := by omega
      have hstep := butterflyDIFPairStep_difMathPairsSpec_succ
        D stage block j twiddles a hstage hj (htw j hj)
      rw [butterflyDIFInner]
      simp only [hj, ↓reduceIte]
      rw [show block * 2 ^ (stage + 1) + j + 1 =
          block * 2 ^ (stage + 1) + (j + 1) by omega]
      rw [show block * 2 ^ (stage + 1) + j + 2 ^ stage + 1 =
          block * 2 ^ (stage + 1) + (j + 1) + 2 ^ stage by omega]
      rw [hstep]
      exact butterflyDIFInner_difMathPairsSpec_final D stage block twiddles a hstage htw
        n (j + 1) htail

private theorem butterflyDIFBlocks_difMathBlocksSpec_final
    (D : NTT.Domain R) (stage : Nat) (twiddles : Array R) (a : Array R)
    (hstage : stage < D.logN)
    (htw : ∀ j, j < 2 ^ stage →
      twiddles.getD j 0 = (D.omega ^ (D.n / 2 ^ (stage + 1))) ^ j) :
    ∀ n blocks block,
      blocks = block + n →
        butterflyDIFBlocks twiddles (2 ^ (stage + 1)) (2 ^ stage) blocks block
            (difMathBlocksSpec D stage block a) =
          difMathBlocksSpec D stage blocks a
  | 0, blocks, block, hblocks => by
      simp [butterflyDIFBlocks, hblocks]
  | n + 1, blocks, block, hblocks => by
      have hblock : block < blocks := by omega
      have htail : blocks = block + 1 + n := by omega
      have hinner := butterflyDIFInner_difMathPairsSpec_final D stage block twiddles a hstage htw
        (2 ^ stage) 0 (by simp)
      rw [butterflyDIFBlocks]
      simp only [hblock, ↓reduceIte]
      rw [show block * 2 ^ (stage + 1) + 2 ^ stage =
          block * 2 ^ (stage + 1) + 0 + 2 ^ stage by omega]
      rw [difMathPairsSpec_zero D stage block a] at hinner
      have hinner' :
          butterflyDIFInner twiddles (2 ^ stage) 0 (block * 2 ^ (stage + 1))
              (block * 2 ^ (stage + 1) + 0 + 2 ^ stage)
              (difMathBlocksSpec D stage block a) =
            difMathPairsSpec D stage block (2 ^ stage) a := by
        simpa using hinner
      rw [hinner']
      rw [difMathPairsSpec_half]
      exact butterflyDIFBlocks_difMathBlocksSpec_final D stage twiddles a hstage htw
        n blocks (block + 1) htail

/-- One executable DIF butterfly stage advances the mathematical DIF stage spec. -/
theorem butterflyStageDIFWithTwiddles_difMathStageSpec_succ
    (D : NTT.Domain R) (stage : Nat) (twiddles : Array R) (a : Array R)
    (hstage : stage < D.logN)
    (htw : ∀ j, j < 2 ^ stage →
      twiddles.getD j 0 = (D.omega ^ (D.n / 2 ^ (stage + 1))) ^ j) :
    butterflyStageDIFWithTwiddles D stage twiddles
        (difMathStageSpec D (D.logN - (stage + 1)) a) =
      difMathStageSpec D (D.logN - stage) a := by
  calc
    butterflyStageDIFWithTwiddles D stage twiddles
        (difMathStageSpec D (D.logN - (stage + 1)) a) =
        butterflyDIFBlocks twiddles (2 ^ (stage + 1)) (2 ^ stage)
          (D.n / 2 ^ (stage + 1)) 0 (difMathBlocksSpec D stage 0 a) := by
          simp [butterflyStageDIFWithTwiddles, difMathBlocksSpec_zero]
    _ = difMathBlocksSpec D stage (D.n / 2 ^ (stage + 1)) a := by
          exact butterflyDIFBlocks_difMathBlocksSpec_final D stage twiddles a hstage htw
            (D.n / 2 ^ (stage + 1)) (D.n / 2 ^ (stage + 1)) 0 (by simp)
    _ = difMathStageSpec D (D.logN - stage) a := by
          exact difMathBlocksSpec_final D stage a hstage

private theorem runStagesDIFWithTwiddles_eq_difMathStageSpec
    (D : NTT.Domain R) (a : Array R) :
    runStagesDIFWithTwiddles D (twiddleTable D) (NTT.loadNaturalArray D a) =
      difMathStageSpec D D.logN a := by
  have hloop :
      ∀ n, n ≤ D.logN →
        List.foldl
          (fun acc pass ↦
            butterflyStageDIFWithTwiddles D (D.logN - pass - 1)
              ((twiddleTable D).getD (D.logN - pass - 1) #[]) acc)
          (NTT.loadNaturalArray D a) (List.range n) =
            difMathStageSpec D n a := by
    intro n hn
    induction n with
    | zero =>
        rw [difMathStageSpec_zero]
        simp
    | succ n ih =>
        have hnle : n ≤ D.logN := Nat.le_of_succ_le hn
        have hnlt : n < D.logN := Nat.lt_of_succ_le hn
        have hstage : D.logN - n - 1 < D.logN := by omega
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ih hnle]
        convert butterflyStageDIFWithTwiddles_difMathStageSpec_succ D
          (D.logN - n - 1) ((twiddleTable D).getD (D.logN - n - 1) #[]) a
          hstage ?_ using 1
        · rw [show D.logN - (D.logN - n - 1 + 1) = n by omega]
        · rw [show D.logN - (D.logN - n - 1) = n + 1 by omega]
        · intro j hj
          rw [twiddleTable_getD_eq_twiddlePowers D (D.logN - n - 1) hstage]
          exact twiddlePowers_getD_eq_pow D (D.logN - n - 1) j hj
  simpa [runStagesDIFWithTwiddles, List.range_eq_range'] using hloop D.logN le_rfl

/-- The DIF stage loop computes the bit-reversed forward NTT output. -/
theorem runStagesDIFWithTwiddles_correct (D : NTT.Domain R) (a : Array R) :
    runStagesDIFWithTwiddles D (twiddleTable D) (NTT.loadNaturalArray D a) =
      NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D a) := by
  rw [runStagesDIFWithTwiddles_eq_difMathStageSpec, difMathStageSpec_final]

end Plan

end NTTFast
end CPolynomial
end CompPoly
