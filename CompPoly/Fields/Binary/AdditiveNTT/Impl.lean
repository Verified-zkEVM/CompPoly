/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Fields.Binary.AdditiveNTT.Algorithm
import CompPoly.Fields.Binary.Tower.Concrete.Basis
import Mathlib.Data.BitVec

/-!
# Additive NTT Implementation

Concrete implementation of the Additive NTT algorithm.
-/

namespace AdditiveNTT
open ConcreteBinaryTower

section HelperFunctions
/-- Converts an Array to a Fin function of a specific size `n`. -/
def Array.toFinVec {α : Type _} (n : ℕ) (arr : Array α) (h : arr.size = n) : Fin n → α :=
  fun i => arr[i]

/-- Converts an array to a `Fin n` function, using `0` for missing entries. -/
def arrayToFinFunction {α : Type _} [Zero α] (n : ℕ) (arr : Array α) : Fin n → α :=
  fun i => arr.getD i.val 0

/- The product of a function mapped over the list `0..n-1`. -/
lemma List.prod_finRange_eq_finset_prod {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin n → M) :
    ((List.finRange n).map f).prod = ∏ i : Fin n, f i := rfl

end HelperFunctions

universe u

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable {𝔽q : Type} [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
variable [hFq_card : Fact (Fintype.card 𝔽q = 2)]
variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
variable [h_β₀_eq_1 : Fact (β 0 = 1)]

section Algorithm
variable {ℓ R_rate : ℕ} (h_ℓ_add_R_rate : ℓ + R_rate < r)-- ℓ ∈ {1, ..., r-1}

/-- Define the mapping explicitly from the index k to the Submodule U. -/
def bitsToU (i : Fin r) (k : Fin (2 ^ i.val)) :
    AdditiveNTT.U (L := L) (𝔽q := 𝔽q) (β := β) i :=
  let val := (Finset.univ : Finset (Fin i)).sum fun j =>
    if (Nat.getBit (n := k.val) (k := j.val) == 1) then
      β ⟨j, by omega⟩
    else 0

  -- We essentially reuse your existing proof that this value is in the subspace
  ⟨val, by
    apply Submodule.sum_mem
    intro j _
    split
    · apply Submodule.subset_span
      -- refine ⟨j, ?_, rfl⟩
      refine Set.mem_image_of_mem β ?_
      rw [Set.mem_Ico]
      exact ⟨Fin.zero_le _, j.isLt⟩
    · exact Submodule.zero_mem _
  ⟩

/-- Computes the elements of the subspace: `U_i = span({β_0, ..., β_{i-1}})`. -/
def getUElements (i : Fin r) : List L :=
  (List.finRange (2^i.val)).map fun k =>
    (Finset.univ : Finset (Fin i)).sum fun j =>
      if Nat.getBit (n := k.val) (k := j.val) == 1 then
        β ⟨j.val, by omega⟩
      else 0

/-- Evaluates the subspace vanishing polynomial `W_i(x) = ∏_{u ∈ U_i} (x - u).` -/
def evalWAt (i : Fin r) (x : L) : L :=
  ((getUElements (β := β) (ℓ := ℓ) (R_rate := R_rate) i).map (fun u => x - u)).prod

/-- Evaluates the normalized subspace vanishing polynomial `Ŵ_i(x) = W_i(x) / W_i(β_i)`. -/
def evalNormalizedWAt (i : Fin r) (x : L) : L :=
  let W_x := evalWAt (r := r) (L := L) (ℓ := ℓ) (β := β) (R_rate := R_rate) (i := i) x
  let beta_i := β i
  let W_beta := evalWAt (β := β) (ℓ := ℓ) (R_rate := R_rate) (i := i) beta_i
  W_x * W_beta⁻¹

/-- Computes the twiddle factor used in the butterfly operation.
Corresponds to `AdditiveNTT.twiddleFactor`.
-/
def computableTwiddleFactor (i : Fin ℓ) (u : Fin (2 ^ (ℓ + R_rate - i - 1))) : L :=
  -- evalNormalizedWAt L i u
  ∑ (⟨k, hk⟩: Fin (ℓ + R_rate - i - 1)),
  if Nat.getBit k u.val = 1 then
    -- this branch maps to the above Nat.getBit = 1 branch
      -- (of evaluationPointω (i+1)) under (qMap i)(X)
    (evalNormalizedWAt (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (i := ⟨i, by omega⟩) (x := β ⟨i + 1 + k, by omega⟩))
  else 0

/-- Performs one stage of the Additive NTT. This corresponds to `NTTStage` in the abstract
definition: `b` is the array of coefficients. `i` is the stage index (0 to r-1). -/
def computableNTTStage [Fact (LinearIndependent 𝔽q β)]
    (i : Fin ℓ) (b : Fin (2 ^ (ℓ + R_rate)) → L) : Fin (2^(ℓ + R_rate)) → L :=
  have h_2_pow_i_lt_2_pow_ℓ_add_R_rate: 2^i.val < 2^(ℓ + R_rate) := by
    calc
      2^i.val < 2 ^ (ℓ) := by
        have hr := Nat.pow_lt_pow_right (a:=2) (m:=i.val) (n:=ℓ) (ha:=by omega) (by omega)
        exact hr
      _ ≤ 2 ^ (ℓ + R_rate) := by
        exact Nat.pow_le_pow_right (n:=2) (i := ℓ) (j:=ℓ + R_rate) (by omega) (by omega)
  fun (j : Fin (2^(ℓ + R_rate))) =>
    let u_b_v := j.val
    have h_u_b_v : u_b_v = j.val := by rfl
    let v: Fin (2^i.val) := ⟨Nat.getLowBits i.val u_b_v, by
      have res := Nat.getLowBits_lt_two_pow (numLowBits:=i.val) (n:=u_b_v)
      simp only [res]
    ⟩ -- the i LSBs
    let u_b := u_b_v / (2^i.val) -- the high (ℓ + R_rate - i) bits
    have h_u_b : u_b = u_b_v / (2^i.val) := by rfl
    have h_u_b_lt_2_pow : u_b < 2 ^ (ℓ + R_rate - i) := by
      -- {m n k : Nat} (h : m < n * k) : m / n < k :=
      have res := Nat.div_lt_of_lt_mul (m:=u_b_v) (n:=2^i.val) (k:=2^(ℓ + R_rate - i)) (by
        calc _ < 2 ^ (ℓ + R_rate) := by omega
          _ = 2 ^ i.val * 2 ^ (ℓ + R_rate - i.val) := by
            exact Eq.symm (pow_mul_pow_sub (a:=2) (m:=i.val) (n:=ℓ + R_rate) (by omega))
      )
      rw [h_u_b]
      exact res
    let u: ℕ := u_b / 2 -- the remaining high bits
    let b_bit := u_b % 2 -- the LSB of the high bits, i.e. the `i`-th Nat.getBit
    have h_u : u = u_b / 2 := by rfl
    have h_u_lt_2_pow: u < 2 ^ (ℓ + R_rate - (i + 1)) := by
      have h_u_eq: u = j.val / (2 ^ (i.val + 1)) := by
        rw [h_u, h_u_b, h_u_b_v]
        rw [Nat.div_div_eq_div_mul]
        rfl
      rw [h_u_eq]
      -- ⊢ ↑j / 2 ^ (↑i + 1) < 2 ^ (ℓ + R_rate - (↑i + 1))
      exact div_two_pow_lt_two_pow (x:=j.val) (i := ℓ + R_rate - (i.val + 1)) (j:=i.val + 1) (by
        rw [Nat.sub_add_cancel (by omega)]
        omega
      )
    let twiddleFactor: L := computableTwiddleFactor (r := r) (ℓ := ℓ) (β := β) (L := L)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
      (u := ⟨u, by simp only; exact h_u_lt_2_pow⟩)
    let x0 := twiddleFactor -- since the last Nat.getBit of u||0 is 0
    let x1: L := x0 + 1 -- since the last Nat.getBit of u||1 is 1 and 1 * Ŵᵢ(βᵢ) = 1

    have h_b_bit : b_bit = Nat.getBit i.val j.val := by
      simp only [Nat.getBit, Nat.and_one_is_mod, b_bit, u_b, u_b_v]
      rw [←Nat.shiftRight_eq_div_pow (m:=j.val) (n:=i.val)]
    -- b remains unchanged through this whole function cuz we create new buffer
    if h_b_bit_zero: b_bit = 0 then -- This is the `b(u||0||v)` case
      let odd_split_index := u_b_v + 2^i.val
      have h_lt: odd_split_index < 2^(ℓ + R_rate) := by
        have h_exp_eq: (↑i + (ℓ + R_rate - i)) = ℓ + R_rate := by omega
        simp only [gt_iff_lt, odd_split_index, u_b_v]
        -- ⊢ ↑j + 2 ^ ↑i < 2 ^ (ℓ + R_rate)
        exact Nat.add_two_pow_of_getBit_eq_zero_lt_two_pow (n:=j.val) (m:=ℓ + R_rate)
          (i := i.val) (h_n:=by omega) (h_i := by omega) (h_getBit_at_i_eq_zero:=by
          rw [h_b_bit_zero] at h_b_bit
          exact h_b_bit.symm
        )
      b j + x0 * b ⟨odd_split_index, h_lt⟩
    else -- This is the `b(u||1||v)` case
      let even_split_index := u_b_v ^^^ 2^i.val
      have h_lt: even_split_index < 2^(ℓ + R_rate) := by
        have h_exp_eq: (↑i + (ℓ + R_rate - i)) = ℓ + R_rate := by omega
        simp only [even_split_index, u_b_v]
        apply Nat.xor_lt_two_pow (by omega) (by omega)
      -- b j is now the odd refinement P₁,₍₁ᵥ₎⁽ⁱ⁺¹⁾(X),
      -- b (j - 2^i) stores the even refinement P₀,₍₀ᵥ₎⁽ⁱ⁺¹⁾(X)
      b ⟨even_split_index, h_lt⟩ + x1 * b j

/-- The main computable Additive NTT function. `a` is the input array of coefficients.
`r` is the number of stages (dimension of the domain). The input array size must be at least 2^r. -/
def computableAdditiveNTT (a : Fin (2 ^ ℓ) → L) : Fin (2^(ℓ + R_rate)) → L :=
  let b: Fin (2^(ℓ + R_rate)) → L := tileCoeffs a -- Note: can optimize on this
  Fin.foldl (n:=ℓ) (f:= fun current_b i  =>
    computableNTTStage (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨ℓ - 1 - i, by omega⟩) (b:=current_b)
  ) (init:=b)

/-- Array-backed coefficient tiling for the ST fast additive NTT path. -/
def tileCoeffsArray (R_rate : ℕ) (a : Fin (2 ^ ℓ) → L) : Array L :=
  Array.ofFn (n := 2^(ℓ + R_rate)) fun v =>
    a ⟨v.val % (2^ℓ), Nat.mod_lt v.val (pow_pos (zero_lt_two) ℓ)⟩

/-- Evaluate a subspace polynomial using cached constants `W_k(β_k)`.

Starting from `W_0(x) = x`, each cached constant advances the recurrence
`W_{k+1}(x) = W_k(x) * (W_k(x) + W_k(β_k))`. -/
def evalWAtCachedConstants (constants : Array L) (x : L) : L :=
  let rec loop (j : Nat) (acc : L) : L :=
    if _h_j : j < constants.size then
      let c := constants.getD j 0
      loop (j + 1) (acc * (acc + c))
    else
      acc
  termination_by constants.size - j
  loop 0 x

/-- Precompute the constants `W_k(β_k)` needed by the recursive subspace
polynomial evaluator up to stage `i`. -/
def subspacePolynomialConstantsArray (i : Fin r) : Array L :=
  let rec loop (k : Nat) (constants : Array L) : Array L :=
    if h_k : k < i.val then
      let constant := evalWAtCachedConstants constants (β ⟨k, by omega⟩)
      loop (k + 1) (constants.push constant)
    else
      constants
  termination_by i.val - k
  loop 0 #[]

/-- Precompute normalized vanishing evaluations used by one stage's twiddle factors. -/
def computableNormalizedWValuesArray (i : Fin ℓ) : Array L :=
  let stage : Fin r := ⟨i, by omega⟩
  let constants := subspacePolynomialConstantsArray (β := β) (ℓ := ℓ) (R_rate := R_rate)
    (i := stage)
  let denominatorInv := (evalWAtCachedConstants constants (β stage))⁻¹
  Array.ofFn (n := ℓ + R_rate - i - 1) fun k =>
    evalWAtCachedConstants constants (β ⟨i + 1 + k.val, by omega⟩) * denominatorInv

/-- Precompute all twiddle factors for one additive NTT stage.

The table is built as subset sums of the cached normalized values. When bit `k`
is added, the new entries `u + 2^k` are copied from `u` plus the `k`th
normalized value. -/
def computableTwiddleTableArray (i : Fin ℓ) : Array L :=
  let normalizedValues := computableNormalizedWValuesArray (β := β) (ℓ := ℓ)
    (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
  let numBits := ℓ + R_rate - i - 1
  let tableSize := 2 ^ numBits
  let initial : Array L := Array.replicate tableSize 0
  let rec fillBit (k : Nat) (table : Array L) : Array L :=
    if _h_k : k < numBits then
      let bit := 2 ^ k
      let value := normalizedValues.getD k 0
      let rec fillBase (u : Nat) (table : Array L) : Array L :=
        if _h_u : u < bit then
          let baseValue := table.getD u 0
          fillBase (u + 1) (table.set! (u + bit) (baseValue + value))
        else
          table
      termination_by bit - u
      fillBit (k + 1) (fillBase 0 table)
    else
      table
  termination_by numBits - k
  fillBit 0 initial

/-- In-place array update for one additive NTT stage.

The loop visits butterfly pairs directly by block and low-bit offset, avoiding
the odd-index no-op iterations from a full output scan. `Array.set!` updates
destructively when the array is uniquely owned by the runtime, which is the case
targeted by the ST fast path.

The `twiddles` array stores the values of `computableTwiddleFactor` for this
stage, indexed by `u`. -/
def computableNTTStageArrayInPlace (i : Fin ℓ) (twiddles : Array L) (b : Array L) : Array L :=
  let stride := 2^i.val
  let blockSize := 2^(i.val + 1)
  let blockCount := 2^(ℓ + R_rate - (i.val + 1))
  let rec loopV (u v : Nat) (b : Array L) : Array L :=
    if h_v : v < stride then
      let evenIndex := u * blockSize + v
      let oddIndex := evenIndex + stride
      let twiddleFactor: L := twiddles.getD u 0
      let x0 := twiddleFactor
      let x1: L := x0 + 1
      let evenValue := b.getD evenIndex 0
      let oddValue := b.getD oddIndex 0
      let newEven := evenValue + x0 * oddValue
      let newOdd := evenValue + x1 * oddValue
      loopV u (v + 1) ((b.set! evenIndex newEven).set! oddIndex newOdd)
    else
      b
  termination_by stride - v
  let rec loopU (u : Nat) (b : Array L) : Array L :=
    if h_u : u < blockCount then
      loopU (u + 1) (loopV u 0 b)
    else
      b
  termination_by blockCount - u
  loopU 0 b

/-- Fast additive NTT stage driver over an `Array L` state.

The state is expected to contain the initialized output buffer. Each stage
updates that buffer using the array transition from
`computableNTTStageArrayInPlace`. -/
def computableAdditiveNTTFastStages : StateM (Array L) Unit := do
  let _ ← Fin.foldlM (m := StateM (Array L)) (n := ℓ) (f := fun (_ : Unit) i => do
    let stage : Fin ℓ := ⟨ℓ - 1 - i, by omega⟩
    let twiddles := computableTwiddleTableArray (β := β) (ℓ := ℓ)
      (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := stage)
    modifyThe (Array L) fun current =>
      computableNTTStageArrayInPlace (ℓ := ℓ) (R_rate := R_rate)
        (i := stage) (twiddles := twiddles) current
    pure ()) (init := ())
  pure ()

/-- Fast additive NTT array producer as a state action. -/
def computableAdditiveNTTFastAction (a : Fin (2 ^ ℓ) → L) :
    StateM (Array L) (Array L) := do
  set (tileCoeffsArray (ℓ := ℓ) R_rate a)
  computableAdditiveNTTFastStages (β := β) (ℓ := ℓ) (R_rate := R_rate)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  getThe (Array L)

/-- Fast additive NTT array producer. -/
def computableAdditiveNTTFast (a : Fin (2 ^ ℓ) → L) : Array L :=
  ((computableAdditiveNTTFastAction (β := β) (ℓ := ℓ)
    (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) a).run #[]).1

end Algorithm

section ConcreteBTFieldInstances

instance (k : ℕ) : NeZero (2^k) := by
  refine ⟨?_⟩
  have h₂ : (2 : ℕ) ≠ 0 := by decide
  simp only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true]

/-- Computable basis for ConcreteBTField k over ConcreteBTField 0.
This is the explicit product of Z's. -/
def computableBasisExplicit (k : ℕ) (i : Fin (2 ^ k)) : ConcreteBTField k :=
  (Finset.univ : Finset (Fin k)).prod fun j =>
    if Nat.getBit (n := i.val) (k := j.val) == 1 then
      concreteTowerAlgebraMap (j.val + 1) k (by omega) (Z (j.val + 1))
    else
      1

omit [NeZero r] in
theorem hβ_lin_indep_concrete (k : ℕ) :
    letI := ConcreteBTFieldAlgebra (l:=0) (r:=k) (h_le:=by omega)
    LinearIndependent (R := ConcreteBTField 0)
      (v := computableBasisExplicit k) := by
  letI := ConcreteBTFieldAlgebra (l:=0) (r:=k) (h_le:=by omega)
  have h_eq : computableBasisExplicit k = fun i => multilinearBasis 0 k (by omega) i := by
    funext i
    unfold computableBasisExplicit
    rw [multilinearBasis_apply k 0 (by omega) i]
    simp only [beq_iff_eq, Nat.sub_zero, 𝕏, map_pow]
    congr 1
    funext x
    have h_lt := Nat.getBit_lt_2 (n := i) (k := x)
    by_cases h: Nat.getBit (k := x) (n := i) = 1
    · simp only [h, ↓reduceIte, pow_one]
      rw! (castMode := .all) [Nat.zero_add]
      rfl
    · have hBit_eq_0: Nat.getBit (k := x) (n := i) = 0 := by omega
      simp only [hBit_eq_0, zero_ne_one, ↓reduceIte, pow_zero]
  rw [h_eq]
  exact (multilinearBasis 0 k (by omega)).linearIndependent

abbrev BTF₃ := ConcreteBTField 3 -- 8 bits
instance : NeZero (2^3) := ⟨by norm_num⟩
instance : Field BTF₃ := instFieldConcrete
instance : DecidableEq BTF₃ := (inferInstance : DecidableEq (ConcreteBTField 3))
instance : Fintype BTF₃ :=
  Fintype.ofEquiv (Fin (2 ^ (2 ^ 3))) (BitVec.equivFin (m := 2 ^ 3)).symm.toEquiv

/-- Test of the computable additive NTT over BTF₃ (an 8-bit binary tower field `BTF₃`).
**Input polynomial:** p(x) = x (novel coefficients [7, 1, 0, 0]) of size `2^ℓ` in `BTF₃`
- `ℓ = 2`
- `R_rate = 2`: Repetition rate, evaluating at `S₀` of size `2^(ℓ + R_rate) = 16` points
- `r = 2^3 = 8`: Dimension of the basis for `BTF₃` over `GF(2)`
**Output:** A function `Fin 16 → BTF₃` giving the evaluations of `p(x) = x` at 16 points
in the evaluation domain `S₀` defined by the spanning basis elements `{β₀, ..., β_{ℓ + 𝓡 - 1}}`
of `BTF₃` over `GF(2)`. -/
def testNTTBTF₃ : Fin (2 ^ (2 + 2)) → BTF₃ := by
  let a : Fin 4 → BTF₃ := Array.toFinVec 4 #[7, 1, 0, 0] rfl
  letI : Algebra (ConcreteBTField 0) BTF₃ := ConcreteBTFieldAlgebra (l := 0) (r := 3)
    (h_le := by omega)
  haveI : Fact (LinearIndependent (ConcreteBTField 0) (computableBasisExplicit 3)) :=
    { out := hβ_lin_indep_concrete 3 }
  -- r is the size of the basis
  exact computableAdditiveNTT (𝔽q := ConcreteBTField 0) (L := BTF₃) (r := 2^3) (ℓ := 2)
    (R_rate := 2) (h_ℓ_add_R_rate := by omega) (β := computableBasisExplicit (k := 3)) (a := a)

-- #eval testNTTBTF₃
-- ![1#8, 0#8, 3#8, 2#8, 5#8, 4#8, 7#8, 6#8, 9#8, 8#8, 11#8, 10#8, 13#8, 12#8, 15#8, 14#8]

end ConcreteBTFieldInstances
end AdditiveNTT
