/-
Copyright (c) 2025 CompPoly, Elias Judin, Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Aristotle (Harmonic)
-/
import CompPoly.Multilinear.Basic

/-!
# Fast / Spec Equivalence for the Möbius Transform

Proves `lagrangeToMono` equals `lagrangeToMonoSpec`.

## Strategy

Define `partialMobiusSpec n k v` capturing the state
after the butterfly has processed levels k … n−1.

* **Base** (k = n): identity.
* **Step**: one level transitions k+1 → k.
* **Final** (k = 0): equals `lagrangeToMonoSpec`.
* **Fold**: `lagrangeToMono` = partialMobiusSpec 0.
-/

namespace CompPoly
namespace CMlPolynomial

variable {R : Type*} [AddCommGroup R] {n : ℕ}

/-! ### Bitwise helper -/

/-- `testBit` of `m - 2 ^ i` at bit `j` when bit `i` of `m` is set. -/
private lemma testBit_sub_two_pow {m i j : ℕ}
    (hm : m.testBit i = true) :
    (m - 2 ^ i).testBit j =
      if j = i then false
      else m.testBit j := by
  have hg : Nat.getBit i m = 1 := by
    rw [Nat.getBit_eq_testBit]; simp [hm]
  have h :=
    @Nat.getBit_of_sub_two_pow_of_bit_1
      m i j hg
  split_ifs at h ⊢ with heq
  · subst heq
    exact testBit_of_sub_two_pow_of_bit_1 hm
  · have h1 :=
      Nat.getBit_eq_testBit j (m - 2 ^ i)
    have h2 := Nat.getBit_eq_testBit j m
    rw [h, h2] at h1
    by_cases hb : (m - 2 ^ i).testBit j <;>
      by_cases hb2 : m.testBit j <;>
      simp_all

/-! ### Partial Möbius specification -/

/-- Boolean condition: j agrees with i below k,
j ⊆ i at/above k. -/
private def mobiusCondB (n k : ℕ)
    (i j : Fin (2 ^ n)) : Bool :=
  (Finset.univ.filter (fun b : Fin n ↦
    b.val < k ∧
    i.val.testBit b.val ≠
      j.val.testBit b.val)).card == 0 &&
  (Finset.univ.filter (fun b : Fin n ↦
    b.val ≥ k ∧
    j.val.testBit b.val = true ∧
    i.val.testBit b.val = false)).card == 0

/-- Count of bits ≥ k where i=1, j=0. -/
private def mobiusDiffCt (n k : ℕ)
    (i j : Fin (2 ^ n)) : ℕ :=
  (Finset.univ.filter (fun b : Fin n ↦
    b.val ≥ k ∧
    i.val.testBit b.val = true ∧
    j.val.testBit b.val = false)).card

/-- One signed term. -/
private def mobiusTm {R : Type*} [AddCommGroup R]
    (n k : ℕ) (i j : Fin (2 ^ n))
    (v : Vector R (2 ^ n)) : R :=
  if mobiusCondB n k i j then
    if mobiusDiffCt n k i j % 2 = 0
    then v[j] else -v[j]
  else 0

/-- Partial Möbius spec at frontier k. -/
private def partialMobiusSpec (n k : ℕ)
    (v : Vector R (2 ^ n)) : Vector R (2 ^ n) :=
  Vector.ofFn fun i ↦
    ∑ j : Fin (2 ^ n), mobiusTm n k i j v

/-! ### Base case -/

set_option maxHeartbeats 400000 in
/-- At the fully processed frontier, the partial Möbius specification is the identity. -/
private theorem partialMobiusSpec_base
    (v : Vector R (2 ^ n)) :
    partialMobiusSpec n n v = v := by
  have hCB : ∀ i j : Fin (2 ^ n),
      mobiusCondB n n i j ↔ j = i := by
    unfold mobiusCondB
    intro i j
    constructor <;> intro h <;>
      simp_all +decide [Finset.ext_iff]
    refine Fin.ext ?_
    refine Nat.eq_of_testBit_eq fun k ↦ ?_
    by_cases hk : k < n
    · exact Eq.symm (h ⟨k, hk⟩)
    · rw [Nat.testBit_eq_false_of_lt,
        Nat.testBit_eq_false_of_lt] <;>
      linarith [Fin.is_lt i, Fin.is_lt j,
        Nat.pow_le_pow_right two_pos
          (le_of_not_gt hk)]
  refine Vector.ext fun i ↦ ?_
  intro hi
  simp [partialMobiusSpec, mobiusTm, hCB]
  simp +decide [mobiusDiffCt]

/-! ### Sub-lemmas for the step theorem -/

/-- If `i` and `j` agree at the active bit, the Boolean Möbius condition is unchanged. -/
private lemma mobiusCondB_same_bit (k : Fin n)
    (i j : Fin (2 ^ n))
    (h : i.val.testBit k.val =
         j.val.testBit k.val) :
    mobiusCondB n k.val i j =
    mobiusCondB n (k.val + 1) i j := by
  unfold mobiusCondB
  congr! 1
  · congr! 2; grind +extAll
  · rw [Finset.card_filter,
      Finset.card_filter]
    grind

/-- If `i` and `j` agree at the active bit, the parity-counting term is unchanged. -/
private lemma mobiusDiffCt_same_bit (k : Fin n)
    (i j : Fin (2 ^ n))
    (h : i.val.testBit k.val =
         j.val.testBit k.val) :
    mobiusDiffCt n k.val i j =
    mobiusDiffCt n (k.val + 1) i j := by
  refine congr_arg Finset.card
    (Finset.ext fun x ↦ ?_)
  grind

set_option maxHeartbeats 800000 in
/-- Flipping an active `1` bit in `i` shifts the Boolean condition to the next frontier. -/
private lemma mobiusCondB_flip_bit (k : Fin n)
    (i j : Fin (2 ^ n))
    (hi : i.val.testBit k.val = true)
    (hj : j.val.testBit k.val = false) :
    mobiusCondB n k.val i j =
    mobiusCondB n (k.val + 1)
      ⟨i.val - 2 ^ k.val,
       Nat.sub_lt_of_lt i.isLt⟩ j := by
  unfold mobiusCondB
  have hSub :
    ∀ b : Fin n, b.val ≠ k.val →
      (i.val - 2 ^ k.val).testBit b.val =
        i.val.testBit b.val :=
    fun b hne ↦ by
      rw [testBit_sub_two_pow hi, if_neg hne]
  have hSubK :
    (i.val - 2 ^ k.val).testBit k.val =
      false :=
    testBit_of_sub_two_pow_of_bit_1 hi
  congr! 1
  · congr! 2; grind
  · congr! 2; grind

set_option maxHeartbeats 400000 in
/-- Flipping an active `1` bit in `i` decreases the parity count by exactly one. -/
private lemma mobiusDiffCt_flip_bit (k : Fin n)
    (i j : Fin (2 ^ n))
    (hi : i.val.testBit k.val = true)
    (hj : j.val.testBit k.val = false) :
    mobiusDiffCt n k.val i j =
    mobiusDiffCt n (k.val + 1)
      ⟨i.val - 2 ^ k.val,
       Nat.sub_lt_of_lt i.isLt⟩ j + 1 := by
  simp only [mobiusDiffCt]
  rw [Finset.card_filter,
      Finset.card_filter,
      ← Finset.sum_erase_add _ _
        (Finset.mem_univ k),
      add_comm]
  simp +decide [hi, hj, add_comm]
  refine Finset.card_bij
    (fun x _ ↦ x) ?_ ?_ ?_ <;>
    simp +contextual [Finset.mem_filter,
      Finset.mem_erase, Finset.mem_univ]
  · grind +suggestions
  · intro b hb₁ hb₂ hb₃
    exact ⟨ne_of_gt hb₁,
      le_of_lt hb₁,
      by rw [testBit_sub_two_pow] at hb₂ <;>
         aesop⟩

/-- The signed Möbius term is unchanged when `i` and `j` agree at the active bit. -/
private lemma mobiusTm_same_bit (k : Fin n)
    (i j : Fin (2 ^ n))
    (v : Vector R (2 ^ n))
    (h : i.val.testBit k.val =
         j.val.testBit k.val) :
    mobiusTm n k.val i j v =
    mobiusTm n (k.val + 1) i j v := by
  unfold mobiusTm
  rw [mobiusCondB_same_bit k i j h,
      mobiusDiffCt_same_bit k i j h]

/-- The signed Möbius term picks up a minus sign when the active bit flips from `1` to `0`. -/
private lemma mobiusTm_flip_bit (k : Fin n)
    (i j : Fin (2 ^ n))
    (v : Vector R (2 ^ n))
    (hi : i.val.testBit k.val = true)
    (hj : j.val.testBit k.val = false) :
    mobiusTm n k.val i j v =
    -mobiusTm n (k.val + 1)
      ⟨i.val - 2 ^ k.val,
       Nat.sub_lt_of_lt i.isLt⟩ j v := by
  unfold mobiusTm
  rw [mobiusCondB_flip_bit k i j hi hj,
      mobiusDiffCt_flip_bit k i j hi hj]
  split_ifs <;>
    simp_all +decide [Nat.add_mod]

/-! ### Step theorem -/

set_option maxHeartbeats 1600000 in
/-- One butterfly step moves the partial Möbius specification frontier from `k + 1` to `k`. -/
private theorem partialMobiusSpec_step
    (k : Fin n) (v : Vector R (2 ^ n)) :
    lagrangeToMonoLevel k
      (partialMobiusSpec n (k.val + 1) v) =
    partialMobiusSpec n k.val v := by
  ext i; unfold lagrangeToMonoLevel; simp +decide [*]
  unfold partialMobiusSpec; simp +decide
  split_ifs <;> simp_all +decide [sub_eq_add_neg]
  · rw [← neg_inj, ← Finset.sum_neg_distrib]
    rw [← Finset.sum_add_distrib]
    congr with j
    by_cases hj : j.val.testBit k.val <;>
      simp_all +decide [mobiusTm_same_bit, mobiusTm_flip_bit]
    · unfold mobiusTm; simp +decide [*, mobiusCondB]
      intro h₁ h₂; specialize h₁ (show k ≤ k from le_rfl)
      simp_all +decide [Nat.testBit, Nat.shiftRight_eq_div_pow]
      have : (i - 2 ^ (k : ℕ)) / 2 ^ (k : ℕ) = i / 2 ^ (k : ℕ) - 1 := by
        rw [← Nat.sub_add_cancel (show 2 ^ (k : ℕ) ≤ i from ?_), Nat.add_div] <;> norm_num
        · exact Nat.mod_lt _ (by positivity)
        · exact le_of_not_gt <| fun h ↦ by
            rw [Nat.div_eq_of_lt h] at *
            contradiction
      rw [this] at h₁; omega
    · unfold mobiusTm; simp +decide [*, mobiusCondB]
      intro h₁ h₂; specialize h₁ (show k ≤ k from le_rfl); aesop
  · refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    by_cases h : j.val.testBit k.val = i.testBit k.val <;>
      simp_all +decide [mobiusTm_same_bit]
    unfold mobiusTm; simp +decide [*, mobiusCondB, mobiusDiffCt]
    grind +qlia

/-! ### Zero = spec -/

set_option maxHeartbeats 1600000 in
/-- At frontier `0`, the partial Möbius specification is the closed-form Möbius transform. -/
private theorem partialMobiusSpec_zero_eq_spec
    (v : Vector R (2 ^ n)) :
    partialMobiusSpec n 0 v =
      lagrangeToMonoSpec v := by
  -- By definition of `mobiusTm`, we can rewrite the sum in the partialMobiusSpec.
  have h_sum_eq :
      ∀ i j : Fin (2 ^ n),
        mobiusTm n 0 i j v =
          if i.val &&& j.val = j.val then
            if (i.val.popCount - j.val.popCount) % 2 = 0 then
              v[j]
            else
              -v[j]
          else
            0 := by
    intro i j
    unfold mobiusTm mobiusCondB mobiusDiffCt
    simp +decide [Finset.ext_iff, Nat.testBit]
    congr! 2
    · constructor <;> intro h
      · refine Nat.eq_of_testBit_eq ?_
        intro k
        by_cases hk : k < n <;> simp_all +decide [Nat.testBit_and]
        · simp_all +decide [Nat.testBit, Nat.shiftRight_eq_div_pow]
          exact h ⟨k, hk⟩
        · simp_all +decide
            [ Nat.testBit_eq_false_of_lt
                (show (j : ℕ) < 2 ^ k from
                  lt_of_lt_of_le j.2
                    (Nat.pow_le_pow_right (by decide) hk))
            , Nat.testBit_eq_false_of_lt
                (show (i : ℕ) < 2 ^ k from
                  lt_of_lt_of_le i.2
                    (Nat.pow_le_pow_right (by decide) hk))
            ]
      · intro a ha
        replace h := congr_arg (fun x ↦ x.testBit a) h
        simp_all +decide [Nat.testBit_and]
        simp_all +decide [Nat.testBit, Nat.shiftRight_eq_div_pow]
    · have h_popCount :
          ∀ (x : ℕ), x < 2 ^ n →
            (x.popCount : ℕ) =
              ∑ b ∈ Finset.range n, if x.testBit b then 1 else 0 := by
        intro x hx
        have h_popCount :
            ∀ (x : ℕ), x < 2 ^ n →
              (x.popCount : ℕ) =
                ∑ b ∈ Finset.range n, if x.testBit b then 1 else 0 := by
          intro x hx
          have h_popCount_eq :
              ∀ (m : ℕ),
                (x.popCount : ℕ) =
                  ∑ b ∈ Finset.range m, (if x.testBit b then 1 else 0) +
                    (x >>> m).popCount := by
            intro m
            induction m generalizing x with
            | zero =>
                simp +decide [Nat.shiftRight_eq_div_pow]
            | succ m ih =>
                rw [Finset.sum_range_succ, ih x hx]
                rw [Nat.popCount]
                rw [Nat.popCount]
                cases h : x >>> m <;>
                  simp_all +decide [Nat.testBit, Nat.shiftRight_eq_div_pow]
                · rw [Nat.div_eq_of_lt h]
                  norm_num
                  rw
                    [ Nat.div_eq_of_lt
                        (lt_of_lt_of_le h
                          (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))
                    ]
                  norm_num
                · rw
                    [ show x / 2 ^ (m + 1) = (x / 2 ^ m) / 2 by
                        rw [Nat.div_div_eq_div_mul, pow_succ]
                    ]
                  simp +decide [h, Nat.add_div]
                  ring_nf
                  split_ifs <;> omega
          specialize h_popCount_eq n
          simp_all +decide [Nat.shiftRight_eq_div_pow]
          rw [Nat.div_eq_of_lt hx]
          simp +decide
        exact h_popCount x hx
      have h_popCount_eq :
          ∑ b ∈ Finset.range n, (if i.val.testBit b then 1 else 0) =
            ∑ b ∈ Finset.range n, (if j.val.testBit b then 1 else 0) +
              ∑ b ∈ Finset.range n,
                (if i.val.testBit b ∧ ¬j.val.testBit b then 1 else 0) := by
        rw [← Finset.sum_add_distrib]
        grind
      simp_all +decide [Nat.testBit]
      rw [Finset.card_filter, Finset.card_filter]
      rw [Finset.sum_range]
  unfold partialMobiusSpec lagrangeToMonoSpec
  aesop

/-! ### Fold unrolling -/

/-- Unrolling the butterfly fold computes the partial Möbius specification at frontier `0`. -/
private theorem lagrangeToMono_eq_partialSpec
    (v : Vector R (2 ^ n)) :
    lagrangeToMono n v =
      partialMobiusSpec n 0 v := by
  have hInd : ∀ k : Fin (n + 1),
      (List.drop k.val (List.finRange n)).foldr
        (fun h acc ↦ lagrangeToMonoLevel h acc) v =
      partialMobiusSpec n k.val v := by
    intro k
    induction k using Fin.reverseInduction with
    | last =>
      simp +decide [partialMobiusSpec_base]
      rw [List.drop_eq_nil_of_le] <;> simp +decide [List.finRange]
    | cast k ih =>
      convert congr_arg (fun x ↦ lagrangeToMonoLevel k x) ih using 1
      · simp +decide [List.drop_eq_getElem_cons]
      · exact Eq.symm (partialMobiusSpec_step k v)
  simpa using hInd ⟨0, Nat.zero_lt_succ _⟩

/-! ### Main theorem -/

/-- The fast butterfly Möbius transform agrees
with the closed-form specification. -/
theorem lagrangeToMono_eq_lagrangeToMonoSpec
    (v : Vector R (2 ^ n)) :
    lagrangeToMono n v =
      lagrangeToMonoSpec v := by
  rw [lagrangeToMono_eq_partialSpec,
      partialMobiusSpec_zero_eq_spec]

end CMlPolynomial
end CompPoly
