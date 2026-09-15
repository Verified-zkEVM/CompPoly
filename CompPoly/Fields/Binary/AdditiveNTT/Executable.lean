/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Algorithm
import CompPoly.Data.Fin.BigOperators

/-!
# Executable additive NTT algorithms

Generic function-backed and array-backed additive NTT implementations over a finite field,
with an explicitly supplied binary-subfield algebra and independent basis vectors. The
function-backed transform mirrors the abstract stages; the array-backed transform caches
subspace-polynomial constants and twiddle tables.

`CompPoly.Fields.Binary.AdditiveNTT.Correctness` relates these implementations to the
abstract algorithm and its evaluation specification. Concrete tower instances and the
compatibility entry point remain in `CompPoly.Fields.Binary.AdditiveNTT.Impl`.
-/

@[expose] public section

namespace AdditiveNTT

section HelperFunctions
/-- Read an array of length `n` as a function on `Fin n`. -/
def Array.toFinVec {α : Type _} (n : ℕ) (arr : Array α) (h : arr.size = n) : Fin n → α :=
  fun i => arr[i]

/-- Converts an array to a `Fin n` function, using `0` for missing entries. -/
def arrayToFinFunction {α : Type _} [Zero α] (n : ℕ) (arr : Array α) : Fin n → α :=
  fun i => arr.getD i.val 0

/-- The product of a function over the list of finite indices equals its finite product. -/
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
variable {ℓ R_rate : ℕ} (h_ℓ_add_R_rate : ℓ + R_rate < r)

/-- Map the numeric mask `k` to the sum of the first `i` basis vectors selected by its bits,
as an element of their linear span. -/
def bitsToU (i : Fin r) (k : Fin (2 ^ i.val)) :
    AdditiveNTT.U (L := L) (𝔽q := 𝔽q) (β := β) i :=
  let val := (Finset.univ : Finset (Fin i)).sum fun j =>
    if (Nat.getBit (n := k.val) (k := j.val) == 1) then
      β ⟨j, by omega⟩
    else 0

  ⟨val, by
    apply Submodule.sum_mem
    intro j _
    split
    · apply Submodule.subset_span
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

/-- Compute the stage-`i` twiddle factor by summing normalized subspace-polynomial
evaluations selected by the bits of `u`. -/
def computableTwiddleFactor (i : Fin ℓ) (u : Fin (2 ^ (ℓ + R_rate - i - 1))) : L :=
  ∑ (⟨k, hk⟩: Fin (ℓ + R_rate - i - 1)),
  if Nat.getBit k u.val = 1 then
    (evalNormalizedWAt (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (i := ⟨i, by omega⟩) (x := β ⟨i + 1 + k, by omega⟩))
  else 0

-- The `Fact` instance is stated explicitly (matching the variable declaration) so that the
-- basis `β` and field `𝔽q` remain named parameters for the `computableAdditiveNTT` call site.
set_option linter.overlappingInstances false in
/-- Perform stage `i` on the coefficient buffer `b`, pairing entries whose indices differ
in bit `i` and applying the corresponding twiddle factor. -/
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
    -- Each output reads from the unchanged input buffer.
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

/-- Transform `2 ^ ℓ` novel-basis coefficients into `2 ^ (ℓ + R_rate)` values by first
tiling the coefficients and then applying stages `ℓ - 1` down to `0`. The basis has length
`r`, and `ℓ + R_rate < r` bounds the evaluation domain. -/
def computableAdditiveNTT (a : Fin (2 ^ ℓ) → L) : Fin (2^(ℓ + R_rate)) → L :=
  let b: Fin (2^(ℓ + R_rate)) → L := tileCoeffs a -- Note: can optimize on this
  Fin.foldl (n:=ℓ) (f:= fun current_b i  =>
    computableNTTStage (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨ℓ - i - 1, by omega⟩) (b:=current_b)
  ) (init:=b)

/-- Array-backed coefficient tiling for the fast additive NTT path. -/
def tileCoeffsArray (R_rate : ℕ) (a : Fin (2 ^ ℓ) → L) : Array L :=
  Array.ofFn (n := 2^(ℓ + R_rate)) fun v =>
    a ⟨v.val % (2^ℓ), Nat.mod_lt v.val (pow_pos (zero_lt_two) ℓ)⟩

/-- Starting from `acc`, iterate `acc ↦ acc * (acc + constants[k])` for indices
`k` from `j` to `constants.size - 1`. Return `acc` unchanged when `constants.size ≤ j`.

For `j ≤ constants.size`, if the initial accumulator is `W_j(x)` and the remaining
constants are `W_k(β_k)`, the result is `W_{constants.size}(x)`. -/
def evalWAtCachedConstantsLoop (constants : Array L) (j : Nat) (acc : L) : L :=
  if _h_j : j < constants.size then
    let c := constants.getD j 0
    evalWAtCachedConstantsLoop constants (j + 1) (acc * (acc + c))
  else
    acc
termination_by constants.size - j

/-- Evaluate a subspace polynomial using cached constants `W_k(β_k)`.

Starting from `W_0(x) = x`, each cached constant advances the recurrence
`W_{k+1}(x) = W_k(x) * (W_k(x) + W_k(β_k))`. -/
def evalWAtCachedConstants (constants : Array L) (x : L) : L :=
  evalWAtCachedConstantsLoop constants 0 x

/-- Extend the supplied `constants` array, starting at index `k` and stopping before `i`.
Each step evaluates the polynomial recurrence encoded by the current array at `β_k`
and appends the result. Return the array unchanged when `i ≤ k`.

If the supplied array has length `k` and entry `j` is `W_j(β_j)` for every `j < k`,
each appended entry has the same interpretation at its index. -/
def subspacePolynomialConstantsArrayLoop (i : Fin r) (k : Nat) (constants : Array L) : Array L :=
  if h_k : k < i.val then
    let constant := evalWAtCachedConstants constants (β ⟨k, by omega⟩)
    subspacePolynomialConstantsArrayLoop i (k + 1) (constants.push constant)
  else
    constants
termination_by i.val - k

/-- Precompute the constants `W_k(β_k)` needed by the recursive subspace
polynomial evaluator up to stage `i`. -/
def subspacePolynomialConstantsArray (i : Fin r) : Array L :=
  subspacePolynomialConstantsArrayLoop (β := β) (ℓ := ℓ) (R_rate := R_rate) i 0 #[]

/-- Precompute normalized vanishing evaluations used by one stage's twiddle factors. -/
def computableNormalizedWValuesArray (i : Fin ℓ) : Array L :=
  let stage : Fin r := ⟨i, by omega⟩
  let constants := subspacePolynomialConstantsArray (β := β) (ℓ := ℓ) (R_rate := R_rate)
    (i := stage)
  let denominatorInv := (evalWAtCachedConstants constants (β stage))⁻¹
  Array.ofFn (n := ℓ + R_rate - i - 1) fun k =>
    evalWAtCachedConstants constants (β ⟨i + 1 + k.val, by omega⟩) * denominatorInv

/-- Precompute all twiddle factors for one additive NTT stage.

The table entry for `u` is the subset sum of the cached normalized values
selected by the set bits of `u`. -/
def computableTwiddleTableArray (i : Fin ℓ) : Array L :=
  let normalizedValues := computableNormalizedWValuesArray (β := β) (ℓ := ℓ)
    (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
  let numBits := ℓ + R_rate - i - 1
  Array.ofFn (n := 2 ^ numBits) fun u =>
    ∑ k : Fin numBits,
      if Nat.getBit k.val u.val = 1 then normalizedValues.getD k.val 0 else 0

/-- Array update for one additive NTT stage.

The `twiddles` array is intended to store the values of `computableTwiddleFactor`
for this stage, indexed by `u`. Missing entries in either input array are read as zero. -/
def computableNTTStageArray (i : Fin ℓ) (twiddles : Array L) (b : Array L) : Array L :=
  let stride := 2^i.val
  Array.ofFn (n := 2^(ℓ + R_rate)) fun j =>
    let u_b_v := j.val
    let u_b := u_b_v / stride
    let u := u_b / 2
    let b_bit := u_b % 2
    let twiddleFactor : L := twiddles.getD u 0
    let x0 := twiddleFactor
    let x1 : L := x0 + 1
    if _h_b_bit_zero : b_bit = 0 then
      let oddIndex := u_b_v + stride
      b.getD u_b_v 0 + x0 * b.getD oddIndex 0
    else
      let evenIndex := u_b_v ^^^ stride
      b.getD evenIndex 0 + x1 * b.getD u_b_v 0

/-- Fast additive NTT stage driver over an `Array L` state.

The state is expected to contain the initialized output buffer. Each stage
updates that buffer using the array transition from
`computableNTTStageArray`. -/
def computableAdditiveNTTFastStages : StateM (Array L) Unit := do
  let _ ← Fin.foldlM (m := StateM (Array L)) (n := ℓ) (f := fun (_ : Unit) i => do
    let stage : Fin ℓ := ⟨ℓ - i - 1, by omega⟩
    let twiddles := computableTwiddleTableArray (β := β) (ℓ := ℓ)
      (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := stage)
    modifyThe (Array L) fun current =>
      computableNTTStageArray (ℓ := ℓ) (R_rate := R_rate)
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

end AdditiveNTT
