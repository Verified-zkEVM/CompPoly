/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Natalie Klaus
-/
import CompPoly.Multilinear.Basic

/-!
  # Fast ↔ Spec equivalence for the multilinear zeta / Möbius transforms

  This file proves that the $O(n \cdot 2^n)$ butterfly transforms
  `monoToLagrange` and `lagrangeToMono` (defined in `CompPoly.Multilinear.Basic`) coincide
  pointwise with their $O(4^n)$ inclusion-exclusion specifications
  `monoToLagrangeSpec` and `lagrangeToMonoSpec` respectively.

  The proofs use a common pattern: an indexed family of partial subset sums that
  interpolates between the identity and the full spec, with each transform level
  corresponding to exactly one step of the interpolation.

  * `section MobiusEquivalence` proves `lagrangeToMono = lagrangeToMonoSpec`.
  * `section ZetaEquivalence` proves `monoToLagrange = monoToLagrangeSpec`.

  All helper lemmas are `private`; only the two top-level theorems
  `lagrangeToMono_eq_lagrangeToMonoSpec` and `monoToLagrange_eq_monoToLagrangeSpec`
  are exported.
-/

namespace CompPoly

namespace CMlPolynomial

variable {R : Type*} [AddCommGroup R] {n : ℕ}

section MobiusEquivalence

/-! ### Fast ↔ Spec equivalence for the Möbius transform

We prove `lagrangeToMono = lagrangeToMonoSpec` by introducing an indexed family of
"partial Möbius sums" `mobiusPartial k` that interpolates between the identity (at `k = n`)
and the full spec (at `k = 0`). Each step of the fast transform
`lagrangeToMonoLevel (k - 1)` decrements the parameter by exactly one. Combined with the
base case we obtain the result by descending induction on `k`. -/

/-- Partial Möbius sum at index `i` after processing levels `[k, k + 1, …, n - 1]`.

Sums over `j : Fin (2 ^ n)` that are bitwise subsets of `i` and that agree with `i` modulo
`2 ^ k` (i.e. on all bits strictly below `k`), weighted by
`(-1) ^ (popCount i - popCount j)`.

* At `k = n` only `j = i` satisfies the constraints, so the result is `p[i]`.
* At `k = 0` the low-bits constraint is vacuous and the formula is exactly
  `lagrangeToMonoSpec`.
-/
private def mobiusPartial (k : ℕ) (p : Vector R (2 ^ n)) (i : Fin (2 ^ n)) : R :=
  ∑ j : Fin (2 ^ n),
    if (i.val &&& j.val = j.val) ∧ (i.val % 2 ^ k = j.val % 2 ^ k) then
      if (i.val.popCount - j.val.popCount) % 2 = 0 then p.get j else -p.get j
    else 0

/-- Base case: at `k = n` the modular constraint forces `j = i`, so the partial sum
collapses to `p.get i`. -/
private lemma mobiusPartial_n (p : Vector R (2 ^ n)) (i : Fin (2 ^ n)) :
    mobiusPartial n p i = p.get i := by
  unfold mobiusPartial
  rw [Finset.sum_eq_single i]
  · have h1 : i.val &&& i.val = i.val := by simp [Nat.and_self]
    simp only [h1, and_self, if_true, Nat.sub_self, Nat.zero_mod, if_true]
  · intro j _ hji
    have hji' : j.val ≠ i.val := fun h => hji (Fin.ext h)
    have hi_lt : i.val < 2 ^ n := i.isLt
    have hj_lt : j.val < 2 ^ n := j.isLt
    have : i.val % 2 ^ n ≠ j.val % 2 ^ n := by
      rw [Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt hj_lt]
      exact fun h => hji' h.symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The `k = 0` case is (definitionally) equivalent to `lagrangeToMonoSpec`. -/
private lemma mobiusPartial_zero_eq_spec (p : Vector R (2 ^ n)) (i : Fin (2 ^ n)) :
    mobiusPartial 0 p i = (lagrangeToMonoSpec p).get i := by
  unfold mobiusPartial lagrangeToMonoSpec
  simp only [pow_zero, Nat.mod_one, and_true, Vector.get_ofFn]

/-- `Nat.popCount 0 = 0`: the zero-bit count of `0` is `0`. -/
private lemma popCount_zero' :
    Nat.popCount 0 = 0 := by
  unfold Nat.popCount; simp [Nat.digits]

/-- Recursion for `Nat.popCount` on positive arguments: split off the least-significant bit. -/
private lemma popCount_pos' {m : ℕ} (hm : 0 < m) :
    Nat.popCount m =
      m % 2 + Nat.popCount (m / 2) := by
  unfold Nat.popCount
  rw [Nat.digits_def' (by norm_num : 1 < 2) hm]
  simp [List.sum_cons]

/-- `testBit` at index `k + 1` equals `testBit` at index `k` of the half. -/
private lemma testBit_succ_eq_div2 (m k : ℕ) :
    m.testBit (k + 1) = (m / 2).testBit k := by
  have h := @Nat.testBit_div_two_pow 1 m k
  rw [pow_one] at h; exact h.symm

/-- Clearing a set bit at position `k` decreases `popCount` by exactly one. -/
private lemma popCount_sub_two_pow {m k : ℕ}
    (hbit : m.testBit k = true) :
    Nat.popCount m =
      Nat.popCount (m - 2 ^ k) + 1 := by
  induction k generalizing m with
  | zero =>
    have hm_pos : 0 < m := by
      by_contra h; push Not at h
      simp only [Nat.le_zero] at h
      subst h; simp at hbit
    have hm_odd : m % 2 = 1 := by
      rw [Nat.testBit] at hbit
      simp only [Nat.shiftRight_zero,
        Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero,
        beq_iff_eq] at hbit; omega
    rw [popCount_pos' hm_pos, hm_odd, pow_zero]
    by_cases h1 : m = 1
    · subst h1; simp [popCount_zero']
    · rw [popCount_pos' (by omega : 0 < m - 1)]
      have : (m - 1) % 2 = 0 := by omega
      have : (m - 1) / 2 = m / 2 := by omega
      simp_all; ring
  | succ k ih =>
    have h2k_le := Nat.ge_two_pow_of_testBit hbit
    have hm_pos : 0 < m := by
      linarith [Nat.two_pow_pos (k + 1)]
    rw [popCount_pos' hm_pos]
    have hbd : (m / 2).testBit k = true := by
      rwa [← testBit_succ_eq_div2]
    by_cases h_eq : m = 2 ^ (k + 1)
    · subst h_eq
      rw [Nat.sub_self, popCount_zero']
      have hmod : 2 ^ (k + 1) % 2 = 0 :=
        Nat.dvd_iff_mod_eq_zero.mp
          (dvd_pow_self 2 (by omega))
      have hdiv : 2 ^ (k + 1) / 2 = 2 ^ k := by
        have := pow_succ 2 k; omega
      rw [hmod, hdiv, Nat.zero_add]
      have h := @ih (2 ^ k) Nat.testBit_two_pow_self
      rw [Nat.sub_self, popCount_zero'] at h; omega
    · rw [ih hbd, popCount_pos'
        (by omega : 0 < m - 2 ^ (k + 1))]
      have : (m - 2 ^ (k + 1)) % 2 = m % 2 := by
        have : 2 ∣ 2 ^ (k + 1) :=
          dvd_pow_self 2 (by omega); omega
      have : (m - 2 ^ (k + 1)) / 2 =
          m / 2 - 2 ^ k := by
        have := pow_succ 2 k; omega
      simp_all; ring

/-- If `n &&& m = m` (i.e. `m` is a bitwise submask of `n`) and `n` has bit `k` clear,
then so does `m`. -/
private lemma submask_testBit_false {m n k : ℕ}
    (hsub : n &&& m = m)
    (hbit : n.testBit k = false) :
    m.testBit k = false := by
  by_contra hj; simp only [Bool.not_eq_false] at hj
  have h := Nat.testBit_and n m k
  rw [hsub] at h
  simp only [hbit, Bool.false_and] at h
  exact absurd h.symm (by simp [hj])

/-- Transfer `getBit` equality to `testBit` equality. -/
private lemma testBit_eq_of_getBit_eq {m n k : ℕ}
    (h : Nat.getBit k m = Nat.getBit k n) :
    m.testBit k = n.testBit k := by
  rw [Nat.getBit_eq_testBit,
    Nat.getBit_eq_testBit] at h
  cases hm : m.testBit k <;>
    cases hn : n.testBit k <;> simp_all

/-- Clearing bit `k` in a number that has bit `k` set gives a number with bit `k` clear. -/
private lemma testBit_sub_self {m k : ℕ}
    (hbit : m.testBit k = true) :
    (m - 2 ^ k).testBit k = false := by
  rw [Nat.testBit_false_eq_getBit_eq_0]
  have hgb : Nat.getBit k m = 1 := by
    rw [Nat.testBit_true_eq_getBit_eq_1] at hbit
    exact hbit
  have h :=
    Nat.getBit_of_sub_two_pow_of_bit_1 hgb (j := k)
  simp at h; exact h

/-- Bits other than `k` are unchanged when subtracting `2 ^ k` from a number with bit `k` set. -/
private lemma testBit_sub_ne {m k l : ℕ}
    (hbit : m.testBit k = true) (hl : l ≠ k) :
    (m - 2 ^ k).testBit l = m.testBit l := by
  apply testBit_eq_of_getBit_eq
  have hgb : Nat.getBit k m = 1 := by
    rw [Nat.testBit_true_eq_getBit_eq_1] at hbit
    exact hbit
  have h :=
    Nat.getBit_of_sub_two_pow_of_bit_1 hgb (j := l)
  simp only [hl, ite_false] at h; exact h

/-- `(m / 2 ^ k) % 2 = 1` when bit `k` of `m` is set. -/
private lemma div_mod2_of_testBit_true {m k : ℕ}
    (h : m.testBit k = true) :
    (m / 2 ^ k) % 2 = 1 := by
  rw [Nat.testBit] at h
  simp only [Nat.shiftRight_eq_div_pow] at h
  simp only [Nat.one_and_eq_mod_two,
    Nat.mod_two_bne_zero, beq_iff_eq] at h; omega

/-- `(m / 2 ^ k) % 2 = 0` when bit `k` of `m` is clear. -/
private lemma div_mod2_of_testBit_false {m k : ℕ}
    (h : m.testBit k = false) :
    (m / 2 ^ k) % 2 = 0 := by
  rw [Nat.testBit] at h
  simp only [Nat.shiftRight_eq_div_pow] at h
  simp only [Nat.one_and_eq_mod_two,
    Nat.mod_two_bne_zero,
    beq_eq_false_iff_ne, ne_eq] at h; omega

/-- Decomposition for the case `(m / d) % 2 = 1`: express `m` via
`(d * 2) * q + r` with `r = d + m % d`. Useful to read `m % (d * 2)`. -/
private lemma rewrite_odd (m d : ℕ)
    (hodd : (m / d) % 2 = 1) :
    m = d * 2 * (m / d / 2) + (d + m % d) := by
  have hd := Nat.div_add_mod m d
  have : d * (m / d) =
      d * 2 * (m / d / 2) + d := by
    have hq : m / d = 2 * (m / d / 2) + 1 := by
      omega
    conv_lhs => rw [hq]; rw [Nat.mul_add, Nat.mul_one]
    show d * (2 * (m / d / 2)) + d =
      d * 2 * (m / d / 2) + d
    congr 1; ring
  linarith

/-- Decomposition for the case `(m / d) % 2 = 0`: express `m` via
`(d * 2) * q + r` with `r = m % d`. Useful to read `m % (d * 2)`. -/
private lemma rewrite_even (m d : ℕ)
    (heven : (m / d) % 2 = 0) :
    m = d * 2 * (m / d / 2) + m % d := by
  have hd := Nat.div_add_mod m d
  have : d * (m / d) = d * 2 * (m / d / 2) := by
    have hq : m / d = 2 * (m / d / 2) := by omega
    conv_lhs => rw [hq]
    show d * (2 * (m / d / 2)) =
      d * 2 * (m / d / 2)
    ring
  linarith

/-- When `(m / d) % 2 = 1`, the value of `m % (d * 2)` is `d + m % d`. -/
private lemma mod_double_of_odd_div (m d : ℕ)
    (hd : 0 < d) (hodd : (m / d) % 2 = 1) :
    m % (d * 2) = d + m % d := by
  have := Nat.mod_lt m hd
  conv_lhs => rw [rewrite_odd m d hodd]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- When `(m / d) % 2 = 0`, the value of `m % (d * 2)` is `m % d`. -/
private lemma mod_double_of_even_div (m d : ℕ)
    (hd : 0 < d) (heven : (m / d) % 2 = 0) :
    m % (d * 2) = m % d := by
  have := Nat.mod_lt m hd
  conv_lhs => rw [rewrite_even m d heven]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- If bit `k` of `m` is clear then `m % 2 ^ (k + 1) = m % 2 ^ k`. -/
private lemma mod_pow_succ_of_testBit_false
    {m k : ℕ} (hbit : m.testBit k = false) :
    m % 2 ^ (k + 1) = m % 2 ^ k := by
  rw [pow_succ]; exact mod_double_of_even_div m _
    (Nat.two_pow_pos k)
    (div_mod2_of_testBit_false hbit)

/-- If bit `k` of `m` is set then `(m - 2 ^ k) % 2 ^ (k + 1) = m % 2 ^ k`. -/
private lemma mod_pow_succ_sub_of_testBit_true
    {m k : ℕ} (hbit : m.testBit k = true) :
    (m - 2 ^ k) % 2 ^ (k + 1) = m % 2 ^ k := by
  rw [pow_succ, mod_double_of_even_div _ _
    (Nat.two_pow_pos k)
    (div_mod2_of_testBit_false (testBit_sub_self hbit))]
  have : 2 ^ k * 1 ≤ m := by
    have := Nat.ge_two_pow_of_testBit hbit; omega
  have := @Nat.sub_mul_mod m 1 (2 ^ k) this
  simp at this; exact this

/-- Lift equality modulo `2 ^ k` to equality modulo `2 ^ (k + 1)` when bit `k` agrees on
both sides (both set). -/
private lemma mod_succ_of_both_true {m n k : ℕ}
    (hm : m.testBit k = true)
    (hn : n.testBit k = true)
    (hmod : m % 2 ^ k = n % 2 ^ k) :
    m % 2 ^ (k + 1) = n % 2 ^ (k + 1) := by
  rw [pow_succ,
    mod_double_of_odd_div m _ (Nat.two_pow_pos k)
      (div_mod2_of_testBit_true hm),
    mod_double_of_odd_div n _ (Nat.two_pow_pos k)
      (div_mod2_of_testBit_true hn), hmod]

/-- When bit `k` disagrees between `m` and `n` (set vs clear), their residues modulo
`2 ^ (k + 1)` differ. -/
private lemma mod_succ_ne_of_diff {m n k : ℕ}
    (hm : m.testBit k = true)
    (hn : n.testBit k = false) :
    m % 2 ^ (k + 1) ≠ n % 2 ^ (k + 1) := by
  rw [pow_succ,
    mod_double_of_odd_div m _ (Nat.two_pow_pos k)
      (div_mod2_of_testBit_true hm),
    mod_double_of_even_div n _ (Nat.two_pow_pos k)
      (div_mod2_of_testBit_false hn)]
  have := Nat.mod_lt m (Nat.two_pow_pos k); omega

/-- If residues modulo `2 ^ k` disagree, then so do residues modulo `2 ^ (k + 1)`. -/
private lemma mod_ne_lift {m n k : ℕ}
    (h : m % 2 ^ k ≠ n % 2 ^ k) :
    m % 2 ^ (k + 1) ≠ n % 2 ^ (k + 1) := by
  intro heq; apply h
  have hdvd := Nat.pow_dvd_pow 2 (Nat.le_succ k)
  rw [← Nat.mod_mod_of_dvd m hdvd, heq,
    Nat.mod_mod_of_dvd n hdvd]

/-- If `m` has bit `k` set and `n` is a submask of `m` with bit `k` clear, then `n`
remains a submask after clearing bit `k` in `m`. -/
private lemma submask_sub_two_pow {m n k : ℕ}
    (hsub : m &&& n = n)
    (hbit_m : m.testBit k = true)
    (hbit_n : n.testBit k = false) :
    (m - 2 ^ k) &&& n = n := by
  apply Nat.eq_of_testBit_eq; intro l
  rw [Nat.testBit_and]
  have hsub_tb : (m.testBit l && n.testBit l) =
      n.testBit l := by
    have h := Nat.testBit_and m n l
    rw [hsub] at h; exact h.symm
  if hl : l = k then
    subst hl; simp [hbit_n]
  else rw [testBit_sub_ne hbit_m hl, hsub_tb]

/-- A bitwise submask has no more set bits than its supermask. -/
private lemma popCount_le_of_and_eq :
    ∀ {m n : ℕ}, m &&& n = n →
      n.popCount ≤ m.popCount := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro n h
    by_cases hn : n = 0
    · subst hn; simp [popCount_zero']
    · have hm : m > 0 := by
        by_contra h0; push Not at h0
        simp only [Nat.le_zero] at h0; subst h0
        simp at h; exact hn h.symm
      rw [popCount_pos' (by omega : 0 < n),
        popCount_pos' hm]
      have h_div :
          (m / 2) &&& (n / 2) = n / 2 := by
        have := @Nat.and_div_two_pow m n 1
        simp [pow_one] at this; rw [h] at this
        exact this.symm
      have hmod_le : n % 2 ≤ m % 2 := by
        have hmod := @Nat.and_mod_two_pow m n 1
        simp [pow_one] at hmod; rw [h] at hmod
        rw [hmod]; exact Nat.and_le_left
      have := ih (m / 2)
        (Nat.div_lt_self (by omega) (by norm_num))
        h_div
      omega

/-- Step lemma: applying `lagrangeToMonoLevel k` to the partial sum at level `k + 1`
yields the partial sum at level `k`. This is the induction step that chains the fast
transform to the inclusion-exclusion spec one bit at a time. -/
private lemma mobiusPartial_step
    {k : ℕ} (hk : k < n) (p : Vector R (2 ^ n))
    (i : Fin (2 ^ n)) :
    Vector.get
      (lagrangeToMonoLevel ⟨k, hk⟩
        (Vector.ofFn (mobiusPartial (k + 1) p)))
      i =
    mobiusPartial k p i := by
  unfold lagrangeToMonoLevel mobiusPartial
  simp only [Vector.get_eq_getElem,
    Vector.getElem_ofFn, BitVec.getLsb_eq_getElem,
    Fin.getElem_fin, BitVec.getElem_ofFin]
  if hbit : i.val.testBit k = true then
    simp only [hbit, ↓reduceIte]
    have h2k_le := Nat.ge_two_pow_of_testBit hbit
    have hi_sub_lt : i.val - 2 ^ k < 2 ^ n :=
      Nat.sub_lt_of_lt i.isLt
    have hbit' : (i.val - 2 ^ k).testBit k = false :=
      testBit_sub_self hbit
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    by_cases hjbit : j.val.testBit k = true
    · have hnsub' :
          ¬((i.val - 2 ^ k) &&& j.val = j.val) := by
        intro h
        have := submask_testBit_false h hbit'
        simp [this] at hjbit
      simp only [hnsub', false_and, ite_false, sub_zero]
      by_cases hsub : i.val &&& j.val = j.val
      · by_cases hmod :
            i.val % 2 ^ k = j.val % 2 ^ k
        · simp [hsub, mod_succ_of_both_true
            hbit hjbit hmod, hmod]
        · simp [hsub, mod_ne_lift hmod, hmod]
      · simp [hsub]
    · simp only [Bool.not_eq_true] at hjbit
      by_cases hsub : i.val &&& j.val = j.val
      · have hsub' :=
          submask_sub_two_pow hsub hbit hjbit
        have hmod_ne :=
          mod_succ_ne_of_diff hbit hjbit
        simp only [hsub, true_and, hmod_ne,
          ite_false, zero_sub, hsub', true_and]
        have hmod_iff :
            (i.val % 2 ^ k = j.val % 2 ^ k) ↔
            ((i.val - 2 ^ k) % 2 ^ (k + 1) =
              j.val % 2 ^ (k + 1)) := by
          rw [mod_pow_succ_sub_of_testBit_true hbit,
            mod_pow_succ_of_testBit_false hjbit]
        by_cases hmod :
            i.val % 2 ^ k = j.val % 2 ^ k
        · simp only [hmod, ite_true, hmod_iff.mp hmod]
          have hpc := popCount_sub_two_pow hbit
          have hpc_le := popCount_le_of_and_eq hsub'
          by_cases hpar :
            (i.val.popCount -
              j.val.popCount) % 2 = 0
          · have : ((i.val - 2 ^ k).popCount -
                j.val.popCount) % 2 = 1 := by omega
            simp only [hpar, ite_true, this]; norm_num
          · have hp1 : (i.val.popCount -
                j.val.popCount) % 2 = 1 := by omega
            have : ((i.val - 2 ^ k).popCount -
                j.val.popCount) % 2 = 0 := by omega
            simp only [hp1, this]; norm_num
        · simp only [hmod, ite_false]
          have : ¬((i.val - 2 ^ k) % 2 ^ (k + 1) =
              j.val % 2 ^ (k + 1)) :=
            fun h => hmod (hmod_iff.mpr h)
          simp [this]
      · have hnsub' :
            ¬((i.val - 2 ^ k) &&& j.val = j.val) := by
          intro h'; apply hsub
          apply Nat.eq_of_testBit_eq; intro l
          rw [Nat.testBit_and]
          have hh := Nat.testBit_and
            (i.val - 2 ^ k) j.val l
          rw [h'] at hh
          if hl : l = k then
            subst hl; simp [hjbit]
          else
            rw [testBit_sub_ne hbit hl] at hh
            exact hh.symm
        simp [hsub, hnsub']
  else
    simp only [Bool.not_eq_true] at hbit
    simp only [hbit]
    apply Finset.sum_congr rfl; intro j _
    by_cases hsub : i.val &&& j.val = j.val
    · have hjf := submask_testBit_false hsub hbit
      have hmod_eq :
          (i.val % 2 ^ (k + 1) = j.val % 2 ^ (k + 1)) ↔
          (i.val % 2 ^ k = j.val % 2 ^ k) := by
        rw [mod_pow_succ_of_testBit_false hbit,
          mod_pow_succ_of_testBit_false hjf]
      simp only [hsub, true_and]
      by_cases hmod :
          i.val % 2 ^ k = j.val % 2 ^ k
      · simp [hmod_eq.mpr hmod, hmod]
      · have : ¬(i.val % 2 ^ (k + 1) =
            j.val % 2 ^ (k + 1)) :=
          fun h => hmod (hmod_eq.mp h)
        simp [this, hmod]
    · simp [hsub]

/-- Fold lemma: applying all `n` levels of the fast Möbius transform reduces `p` to the
value `Vector.ofFn (mobiusPartial 0 p)`. Proved by descending induction on the number of
remaining levels. -/
private lemma lagrangeToMono_eq_mobiusPartial_zero
    (p : Vector R (2 ^ n)) :
    lagrangeToMono n p =
      Vector.ofFn (mobiusPartial 0 p) := by
  unfold lagrangeToMono
  suffices h : ∀ m ≤ n,
      ((List.finRange n).drop (n - m)).foldr
        (fun h acc => lagrangeToMonoLevel h acc)
        p =
      Vector.ofFn (mobiusPartial (n - m) p) by
    have := h n (le_refl n)
    simp only [Nat.sub_self, List.drop_zero] at this
    exact this
  intro m hm
  induction m with
  | zero =>
    simp only [Nat.sub_zero]
    have hdrop : (List.finRange n).drop n = [] :=
      List.drop_of_length_le (by simp)
    simp only [hdrop, List.foldr_nil]
    ext i hi; simp only [Vector.getElem_ofFn]
    exact (mobiusPartial_n p ⟨i, hi⟩).symm
  | succ m' ih =>
    have hm' : m' ≤ n := by omega
    have hk : n - (m' + 1) < n := by omega
    have hlen : n - m' - 1 <
        (List.finRange n).length := by
      simp [List.length_finRange]; omega
    have hdrop := List.drop_eq_getElem_cons hlen
      (l := List.finRange n)
    simp only [List.getElem_finRange,
      show n - m' - 1 + 1 = n - m' from by omega]
      at hdrop
    rw [show n - (m' + 1) = n - m' - 1 from by
      omega, hdrop, List.foldr_cons, ih hm']
    ext idx hidx
    simp only [Vector.getElem_ofFn]
    have hstep := mobiusPartial_step hk p
      ⟨idx, hidx⟩
    simp only [Vector.get_eq_getElem] at hstep
    have h1 : n - m' - 1 = n - (m' + 1) := by omega
    have h2 : n - m' = n - (m' + 1) + 1 := by omega
    simp only [h2] at *
    convert hstep using 2

/-- The fast Möbius transform `lagrangeToMono` is pointwise equal to the inclusion-exclusion
specification `lagrangeToMonoSpec`. Combines the fold lemma with the `k = 0` base case. -/
theorem lagrangeToMono_eq_lagrangeToMonoSpec
    (p : Vector R (2 ^ n)) :
    lagrangeToMono n p = lagrangeToMonoSpec p := by
  rw [lagrangeToMono_eq_mobiusPartial_zero]
  ext i hi
  simp only [Vector.getElem_ofFn]
  exact mobiusPartial_zero_eq_spec p ⟨i, hi⟩

end MobiusEquivalence

section ZetaEquivalence

/-! ### Fast ↔ Spec equivalence for the zeta transform

Mirror of `MobiusEquivalence`: we prove `monoToLagrange = monoToLagrangeSpec` with an
indexed family `zetaPartial k` of partial subset sums. Instead of the low-bits constraint
used in the Möbius proof, here `k` counts how many leading levels have already been
applied — the constraint is that `j` must agree with `i` on bits **at or above**
position `k` (`i / 2 ^ k = j / 2 ^ k`).

* At `k = 0` only `j = i` matches, so `zetaPartial 0 p i = p[i]`.
* At `k = n` the constraint is vacuous, recovering `monoToLagrangeSpec`.

Each application of `monoToLagrangeLevel k` to `Vector.ofFn (zetaPartial k p)` increments
`k` by one. `monoToLagrange n` is a `foldl`, so applying the levels `0, 1, …, n-1`
transports us from `zetaPartial 0 = id` to `zetaPartial n = spec`. -/

/-- Partial zeta sum at index `i` after processing levels `[0, 1, …, k - 1]`.

Sums `p[j]` over `j : Fin (2 ^ n)` that are bitwise subsets of `i` and that agree with `i`
on all bits at or above position `k` (`i / 2 ^ k = j / 2 ^ k`).

* At `k = 0` only `j = i` satisfies the constraints, so the result is `p[i]`.
* At `k = n` the high-bits constraint is vacuous and the formula coincides with
  `monoToLagrangeSpec`.
-/
private def zetaPartial (k : ℕ) (p : Vector R (2 ^ n)) (i : Fin (2 ^ n)) : R :=
  ∑ j : Fin (2 ^ n),
    if (i.val &&& j.val = j.val) ∧ (i.val / 2 ^ k = j.val / 2 ^ k) then
      p.get j
    else 0

/-- Base case: at `k = 0` the high-bits constraint forces `j = i`, so the partial zeta
sum collapses to `p.get i`. -/
private lemma zetaPartial_zero (p : Vector R (2 ^ n)) (i : Fin (2 ^ n)) :
    zetaPartial 0 p i = p.get i := by
  unfold zetaPartial
  rw [Finset.sum_eq_single i]
  · have h1 : i.val &&& i.val = i.val := by simp [Nat.and_self]
    simp only [h1, pow_zero, Nat.div_one, and_self, if_true]
  · intro j _ hji
    have hji' : j.val ≠ i.val := fun h ↦ hji (Fin.ext h)
    simp only [pow_zero, Nat.div_one]
    have : i.val ≠ j.val := fun h ↦ hji' h.symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- At `k = n` the high-bits constraint is vacuous (both `i / 2 ^ n` and `j / 2 ^ n`
are `0`), so the partial sum equals `monoToLagrangeSpec`. -/
private lemma zetaPartial_n_eq_spec (p : Vector R (2 ^ n)) (i : Fin (2 ^ n)) :
    zetaPartial n p i = (monoToLagrangeSpec p).get i := by
  unfold zetaPartial monoToLagrangeSpec
  simp only [Vector.get_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  have hi : i.val / 2 ^ n = 0 := Nat.div_eq_of_lt i.isLt
  have hj : j.val / 2 ^ n = 0 := Nat.div_eq_of_lt j.isLt
  by_cases hsub : i.val &&& j.val = j.val
  · simp [hsub, hi, hj]
  · simp [hsub]

/-- `m / 2 ^ (k + 1) = (m / 2 ^ k) / 2`: increasing the shift exponent by one is one
extra halving. -/
private lemma div_pow_succ (m k : ℕ) :
    m / 2 ^ (k + 1) = (m / 2 ^ k) / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

/-- If bit `k` of both `m` and `n` is `0`, then equality modulo `2 ^ k` (high-bits sense,
i.e. of the quotients `/ 2 ^ k`) is equivalent to equality modulo `2 ^ (k + 1)`. -/
private lemma div_pow_succ_eq_of_both_false {m n k : ℕ}
    (hm : m.testBit k = false) (hn : n.testBit k = false) :
    m / 2 ^ k = n / 2 ^ k ↔ m / 2 ^ (k + 1) = n / 2 ^ (k + 1) := by
  have hm_even : (m / 2 ^ k) % 2 = 0 := div_mod2_of_testBit_false hm
  have hn_even : (n / 2 ^ k) % 2 = 0 := div_mod2_of_testBit_false hn
  have hm_div : m / 2 ^ (k + 1) = (m / 2 ^ k) / 2 := div_pow_succ m k
  have hn_div : n / 2 ^ (k + 1) = (n / 2 ^ k) / 2 := div_pow_succ n k
  have hm_split := Nat.div_add_mod (m / 2 ^ k) 2
  have hn_split := Nat.div_add_mod (n / 2 ^ k) 2
  omega

/-- If bit `k` of both `m` and `n` is `1`, then equality modulo `2 ^ k` (high-bits sense)
is equivalent to equality modulo `2 ^ (k + 1)`. -/
private lemma div_pow_succ_eq_of_both_true {m n k : ℕ}
    (hm : m.testBit k = true) (hn : n.testBit k = true) :
    m / 2 ^ k = n / 2 ^ k ↔ m / 2 ^ (k + 1) = n / 2 ^ (k + 1) := by
  have hm_odd : (m / 2 ^ k) % 2 = 1 := div_mod2_of_testBit_true hm
  have hn_odd : (n / 2 ^ k) % 2 = 1 := div_mod2_of_testBit_true hn
  have hm_div : m / 2 ^ (k + 1) = (m / 2 ^ k) / 2 := div_pow_succ m k
  have hn_div : n / 2 ^ (k + 1) = (n / 2 ^ k) / 2 := div_pow_succ n k
  have hm_split := Nat.div_add_mod (m / 2 ^ k) 2
  have hn_split := Nat.div_add_mod (n / 2 ^ k) 2
  omega

/-- When bit `k` disagrees between `m` and `n` (set vs clear), the quotients
`m / 2 ^ k` and `n / 2 ^ k` have different parities and are therefore unequal. -/
private lemma div_pow_ne_of_diff {m n k : ℕ}
    (hm : m.testBit k = true) (hn : n.testBit k = false) :
    m / 2 ^ k ≠ n / 2 ^ k := by
  have hm_odd : (m / 2 ^ k) % 2 = 1 := div_mod2_of_testBit_true hm
  have hn_even : (n / 2 ^ k) % 2 = 0 := div_mod2_of_testBit_false hn
  intro h; rw [h] at hm_odd; omega

/-- Clearing bit `k` in `m` (when set) preserves the high-bits quotient at level `k + 1`:
`(m - 2 ^ k) / 2 ^ (k + 1) = m / 2 ^ (k + 1)`. -/
private lemma div_pow_succ_sub_of_testBit_true {m k : ℕ}
    (hbit : m.testBit k = true) :
    (m - 2 ^ k) / 2 ^ (k + 1) = m / 2 ^ (k + 1) := by
  have hm_ge : 2 ^ k ≤ m := Nat.ge_two_pow_of_testBit hbit
  have hpos : 0 < 2 ^ (k + 1) := Nat.two_pow_pos (k + 1)
  have hmod_sub : (m - 2 ^ k) % 2 ^ (k + 1) = m % 2 ^ k :=
    mod_pow_succ_sub_of_testBit_true hbit
  have hmod_m : m % 2 ^ (k + 1) = 2 ^ k + m % 2 ^ k := by
    have := mod_double_of_odd_div m (2 ^ k) (Nat.two_pow_pos k)
      (div_mod2_of_testBit_true hbit)
    rwa [pow_succ]
  have h1 := Nat.div_add_mod m (2 ^ (k + 1))
  have h2 := Nat.div_add_mod (m - 2 ^ k) (2 ^ (k + 1))
  have hstep :
      2 ^ (k + 1) * (m / 2 ^ (k + 1)) =
      2 ^ (k + 1) * ((m - 2 ^ k) / 2 ^ (k + 1)) := by omega
  exact (Nat.eq_of_mul_eq_mul_left hpos hstep).symm

/-- Step lemma (zeta version): applying `monoToLagrangeLevel k` to the partial zeta sum
at level `k` gives the partial sum at level `k + 1`. -/
private lemma zetaPartial_step
    {k : ℕ} (hk : k < n) (p : Vector R (2 ^ n))
    (i : Fin (2 ^ n)) :
    Vector.get
      (monoToLagrangeLevel ⟨k, hk⟩
        (Vector.ofFn (zetaPartial k p)))
      i =
    zetaPartial (k + 1) p i := by
  unfold monoToLagrangeLevel zetaPartial
  simp only [Vector.get_eq_getElem, Vector.getElem_ofFn,
    BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin]
  if hbit : i.val.testBit k = true then
    simp only [hbit, ↓reduceIte]
    have h2k_le := Nat.ge_two_pow_of_testBit hbit
    have hbit' : (i.val - 2 ^ k).testBit k = false := testBit_sub_self hbit
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    by_cases hjbit : j.val.testBit k = true
    · -- bit k of j = 1: contributes to zetaPartial k p i but not to zetaPartial k p (i - 2^k).
      have hnsub' : ¬((i.val - 2 ^ k) &&& j.val = j.val) := by
        intro h; have := submask_testBit_false h hbit'; simp [this] at hjbit
      simp only [hnsub', false_and, ite_false, add_zero]
      by_cases hsub : i.val &&& j.val = j.val
      · simp only [hsub, true_and]
        have hiff := div_pow_succ_eq_of_both_true hbit hjbit
        by_cases heq : i.val / 2 ^ k = j.val / 2 ^ k
        · simp [heq, hiff.mp heq]
        · have : ¬ i.val / 2 ^ (k + 1) = j.val / 2 ^ (k + 1) := fun h ↦ heq (hiff.mpr h)
          simp [heq, this]
      · simp [hsub]
    · -- bit k of j = 0
      simp only [Bool.not_eq_true] at hjbit
      by_cases hsub : i.val &&& j.val = j.val
      · -- j ⊆ i, bit k of i = 1, bit k of j = 0.
        have hne : i.val / 2 ^ k ≠ j.val / 2 ^ k := div_pow_ne_of_diff hbit hjbit
        have hsub' : (i.val - 2 ^ k) &&& j.val = j.val :=
          submask_sub_two_pow hsub hbit hjbit
        have hbit_sub : (i.val - 2 ^ k).testBit k = false := hbit'
        simp only [hsub, hsub', true_and, hne, ite_false, zero_add]
        have hiff := div_pow_succ_eq_of_both_false hbit_sub hjbit
        have hdiv_sub := div_pow_succ_sub_of_testBit_true hbit
        by_cases heq : (i.val - 2 ^ k) / 2 ^ k = j.val / 2 ^ k
        · have hiff_applied := hiff.mp heq
          rw [hdiv_sub] at hiff_applied
          simp [heq, hiff_applied]
        · have : ¬ i.val / 2 ^ (k + 1) = j.val / 2 ^ (k + 1) := by
            intro h; apply heq
            apply hiff.mpr
            rw [hdiv_sub]; exact h
          simp [heq, this]
      · -- j not a subset of i; also not a subset of i - 2^k.
        have hnsub' : ¬((i.val - 2 ^ k) &&& j.val = j.val) := by
          intro h'; apply hsub
          apply Nat.eq_of_testBit_eq; intro l
          rw [Nat.testBit_and]
          have hh := Nat.testBit_and (i.val - 2 ^ k) j.val l
          rw [h'] at hh
          if hl : l = k then
            subst hl; simp [hjbit]
          else
            rw [testBit_sub_ne hbit hl] at hh; exact hh.symm
        simp [hsub, hnsub']
  else
    simp only [Bool.not_eq_true] at hbit
    simp only [hbit]
    apply Finset.sum_congr rfl; intro j _
    by_cases hsub : i.val &&& j.val = j.val
    · have hjf : j.val.testBit k = false := submask_testBit_false hsub hbit
      simp only [hsub, true_and]
      have hiff := div_pow_succ_eq_of_both_false hbit hjf
      by_cases heq : i.val / 2 ^ k = j.val / 2 ^ k
      · simp [heq, hiff.mp heq]
      · have : ¬ i.val / 2 ^ (k + 1) = j.val / 2 ^ (k + 1) := fun h ↦ heq (hiff.mpr h)
        simp [heq, this]
    · simp [hsub]

/-- Fold lemma (zeta version): applying all `n` levels of `monoToLagrange` via `foldl`
yields `Vector.ofFn (zetaPartial n p)`. Proved by induction on the number of levels
already applied, using `zetaPartial_step`. -/
private lemma monoToLagrange_eq_zetaPartial_n
    (p : Vector R (2 ^ n)) :
    monoToLagrange n p = Vector.ofFn (zetaPartial n p) := by
  unfold monoToLagrange
  have htake_full : (List.finRange n).take n = List.finRange n :=
    List.take_of_length_le (by simp)
  suffices h : ∀ m ≤ n,
      ((List.finRange n).take m).foldl
        (fun acc level ↦ monoToLagrangeLevel level acc)
        p =
      Vector.ofFn (zetaPartial m p) by
    have := h n (le_refl n)
    rw [htake_full] at this
    exact this
  intro m hm
  induction m with
  | zero =>
    simp only [List.take_zero, List.foldl_nil]
    ext i hi
    simp only [Vector.getElem_ofFn]
    exact (zetaPartial_zero p ⟨i, hi⟩).symm
  | succ m' ih =>
    have hm' : m' ≤ n := by omega
    have hk : m' < n := by omega
    have hlen : m' < (List.finRange n).length := by
      rw [List.length_finRange]; exact hk
    have hget : (List.finRange n)[m'] = ⟨m', hk⟩ := List.getElem_finRange hlen
    have htake : (List.finRange n).take (m' + 1) =
        (List.finRange n).take m' ++ [⟨m', hk⟩] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlen, hget]
      rfl
    rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil, ih hm']
    ext idx hidx
    simp only [Vector.getElem_ofFn]
    have hstep := zetaPartial_step hk p ⟨idx, hidx⟩
    simp only [Vector.get_eq_getElem] at hstep
    exact hstep

/-- The fast zeta transform `monoToLagrange` is pointwise equal to the naive
`monoToLagrangeSpec`. Mirror of `lagrangeToMono_eq_lagrangeToMonoSpec`. -/
theorem monoToLagrange_eq_monoToLagrangeSpec
    (p : Vector R (2 ^ n)) :
    monoToLagrange n p = monoToLagrangeSpec p := by
  rw [monoToLagrange_eq_zetaPartial_n]
  ext i hi
  simp only [Vector.getElem_ofFn]
  exact zetaPartial_n_eq_spec p ⟨i, hi⟩

end ZetaEquivalence

end CMlPolynomial

end CompPoly
