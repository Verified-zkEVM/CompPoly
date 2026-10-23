/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith

/-!
# The additive NTT over a coset, and its inverse

The transform of Lin, Chung and Han (FOCS 2014), over any coset shift + S_l.

The other files here follow Diamond and Posen: one transform over S_l, tiled for the rate.

## Main results

- `vanishing_add`: W_i is additive in characteristic 2 (Lemma 1).
- `network_ntt`: the butterfly network evaluates the novel-basis polynomial on the coset.
- `inetwork_network`: the inverse network undoes the network.
- `inetwork_ntt`: the inverse network recovers the coefficients.
- `ntt_pad`: zero-padded coefficients split into one transform per coset of S_m.
- `normalized_eq_sqAddIter`: for a Cantor basis, W^_j is the j-th iterate of x^2 + x.
-/

@[expose] public section

namespace AdditiveNTT.Coset

open Finset

variable {F : Type _} [Field F] {V : Type _} [AddCommGroup V] [Module F V]




/-- Point m of the span of the basis: the sum of beta_r over the set bits r of m. -/
def point (β : ℕ → F) (m : ℕ) : F := ∑ r ∈ range m, if m.testBit r then β r else 0

/-- The subspace polynomial W_i: the product of x - s over the 2^i points s of S_i. -/
def vanishing (β : ℕ → F) (i : ℕ) (x : F) : F := ∏ m ∈ range (2 ^ i), (x - point β m)

/-- The normalised subspace polynomial W_i(x) / W_i(beta_i). -/
def normalized (β : ℕ → F) (i : ℕ) (x : F) : F := vanishing β i x / vanishing β i (β i)

/-- The novel basis polynomial X_k of the first l normalised subspace polynomials. -/
def novel (β : ℕ → F) (l k : ℕ) (x : F) : F :=
  ∏ j ∈ range l, if k.testBit j then normalized β j x else 1

/-- The value at x of sum_(k < 2^l) d_k X_k. -/
def novelEval (β : ℕ → F) (l : ℕ) (d : ℕ → V) (x : F) : V :=
  ∑ k ∈ range (2 ^ l), novel β l k x • d k

/-- The additive NTT over shift + S_l: entry i is sum_k d_k X_k at shift + point(i). -/
def ntt (β : ℕ → F) (l : ℕ) (shift : F) (d : ℕ → V) : ℕ → V :=
  fun i => novelEval β l d (shift + point β i)

/-- No beta_i, for i < n, is a point of the span of the earlier ones. -/
def Independent (β : ℕ → F) (n : ℕ) : Prop := ∀ i < n, ∀ m < 2 ^ i, point β m ≠ β i

/-- A Cantor basis of length n: beta_0 = 1 and beta_i^2 + beta_i = beta_(i-1) for 0 < i < n. -/
def IsCantor (β : ℕ → F) (n : ℕ) : Prop :=
  β 0 = 1 ∧ ∀ i, i + 1 < n → β (i + 1) ^ 2 + β (i + 1) = β i

/-! ## The butterfly network -/

/-- The forward butterfly (u, v) -> (u + t v, u + t v + v). -/
def butterfly (t : F) (u v : V) : V × V := (u + t • v, u + t • v + v)

/-- The inverse butterfly (u, v) -> (u + t (u + v), u + v). -/
def ibutterfly (t : F) (u v : V) : V × V := (u + t • (u + v), u + v)

/-- Stage j of the forward network.

Row i pairs with the row 2^j away, inside its block of 2^(j+1) rows.

Block b uses the twiddle tau(b). -/
def stage (τ : ℕ → F) (j : ℕ) (x : ℕ → V) : ℕ → V := fun i =>
  if i % 2 ^ (j + 1) < 2 ^ j then (butterfly (τ (i / 2 ^ (j + 1))) (x i) (x (i + 2 ^ j))).1
  else (butterfly (τ (i / 2 ^ (j + 1))) (x (i - 2 ^ j)) (x i)).2

/-- Stage j of the inverse network, pairing rows as the forward stage does. -/
def istage (τ : ℕ → F) (j : ℕ) (x : ℕ → V) : ℕ → V := fun i =>
  if i % 2 ^ (j + 1) < 2 ^ j then (ibutterfly (τ (i / 2 ^ (j + 1))) (x i) (x (i + 2 ^ j))).1
  else (ibutterfly (τ (i / 2 ^ (j + 1))) (x (i - 2 ^ j)) (x i)).2

/-- The forward network of l stages, stage l - 1 first, stage j with twiddles tau_j. -/
def network (τ : ℕ → ℕ → F) : ℕ → (ℕ → V) → ℕ → V
  | 0, x => x
  | l + 1, x => network τ l (stage (τ l) l x)

/-- The inverse network of l stages: stage 0 first, up to stage l - 1. -/
def inetwork (τ : ℕ → ℕ → F) : ℕ → (ℕ → V) → ℕ → V
  | 0, x => x
  | l + 1, x => istage (τ l) l (inetwork τ l x)

/-- The twiddle of stage j and block b over shift + S: W^_j at the block's first point. -/
def twiddle (β : ℕ → F) (shift : F) (j b : ℕ) : F :=
  normalized β j (shift + point β (b * 2 ^ (j + 1)))

/-- The iterated map x -> x^2 + x, which is W_j for a Cantor basis. -/
def sqAddIter (j : ℕ) (x : F) : F := (fun y => y ^ 2 + y)^[j] x




/-! ## Points -/

theorem testBit_of_lt {m r n : ℕ} (hm : m < 2 ^ n) (hr : n ≤ r) : m.testBit r = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right two_pos hr))

/-- The sum over the bits of m below a bound stops changing once the bound covers m. -/
theorem sum_bits_eq {M : Type _} [AddCommMonoid M] (f : ℕ → M) {m a b : ℕ} (hab : a ≤ b)
    (ha : m < 2 ^ a) :
    ∑ r ∈ range a, (if m.testBit r then f r else 0) =
      ∑ r ∈ range b, (if m.testBit r then f r else 0) := by
  rw [← sum_range_add_sum_Ico _ hab, sum_eq_zero (s := Ico a b) fun r hr => by
    simp [testBit_of_lt ha (mem_Ico.mp hr).1], add_zero]

/-- Point m as a sum over any range of bits that covers m. -/
theorem point_eq_sum (β : ℕ → F) {m n : ℕ} (hm : m < 2 ^ n) :
    point β m = ∑ r ∈ range n, if m.testBit r then β r else 0 := by
  rcases le_total m n with h | h
  · exact sum_bits_eq β h (Nat.lt_two_pow_self)
  · exact (sum_bits_eq β h hm).symm

@[simp] theorem point_zero (β : ℕ → F) : point β 0 = 0 := by simp [point]

theorem point_two_pow (β : ℕ → F) (j : ℕ) : point β (2 ^ j) = β j := by
  rw [point_eq_sum β (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self j))]
  rw [sum_eq_single j (fun r _ hr => by simp [Ne.symm hr]) (by simp)]
  simp

/-- Bits below 2^k and bits above it contribute separately. -/
theorem point_add_mul (β : ℕ → F) (a k : ℕ) {b : ℕ} (hb : b < 2 ^ k) :
    point β (2 ^ k * a + b) = point β (2 ^ k * a) + point β b := by
  have hlt : ∀ c, c ≤ a → 2 ^ k * c + b < 2 ^ (k + a + 1) := fun c hc => by
    have : c < 2 ^ (a + 1) := lt_of_le_of_lt hc (Nat.lt_two_pow_self.trans
      (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self a)))
    calc 2 ^ k * c + b < 2 ^ k * c + 2 ^ k := by omega
      _ = 2 ^ k * (c + 1) := by ring
      _ ≤ 2 ^ k * 2 ^ (a + 1) := Nat.mul_le_mul_left _ this
      _ = 2 ^ (k + a + 1) := by ring
  have h1 := hlt a le_rfl
  have h2 : 2 ^ k * a < 2 ^ (k + a + 1) := by omega
  have h3 : b < 2 ^ (k + a + 1) := by omega
  rw [point_eq_sum β h1, point_eq_sum β h2, point_eq_sum β h3,
    ← sum_add_distrib]
  refine sum_congr rfl fun r _ => ?_
  rw [Nat.testBit_two_pow_mul_add a hb, Nat.testBit_two_pow_mul]
  by_cases hr : r < k
  · simp [hr, show ¬ k ≤ r by omega]
  · simp [hr, show k ≤ r by omega, testBit_of_lt hb (show k ≤ r by omega)]

theorem point_add_two_pow (β : ℕ → F) {m k : ℕ} (hm : m < 2 ^ k) :
    point β (m + 2 ^ k) = point β m + β k := by
  rw [add_comm, ← mul_one (2 ^ k), point_add_mul β 1 k hm, mul_one, point_two_pow, add_comm]

/-- Point m of a shifted basis is point m 2^s of the basis. -/
theorem point_mul_two_pow (β : ℕ → F) (m s : ℕ) :
    point β (2 ^ s * m) = point (fun r => β (s + r)) m := by
  have hm : m < 2 ^ m := Nat.lt_two_pow_self
  have hsm : 2 ^ s * m < 2 ^ (s + m) := by
    rw [pow_add]; exact Nat.mul_lt_mul_of_pos_left hm (Nat.two_pow_pos s)
  rw [point_eq_sum _ hm, point_eq_sum β hsm, sum_range_add, sum_eq_zero (s := range s), zero_add]
  · refine sum_congr rfl fun r _ => ?_
    rw [Nat.testBit_two_pow_mul]; simp
  · exact fun r hr => by
      rw [Nat.testBit_two_pow_mul]; simp [show ¬ s ≤ r by simpa using hr]

/-- Point m only reads the basis vectors below the bit length of m. -/
theorem point_congr {β β' : ℕ → F} {m n : ℕ} (hm : m < 2 ^ n) (h : ∀ r < n, β r = β' r) :
    point β m = point β' m := by
  rw [point_eq_sum β hm, point_eq_sum β' hm]
  exact sum_congr rfl fun r hr => by rw [h r (mem_range.mp hr)]

/-- An additive map sends point m of a basis to point m of the image basis. -/
theorem map_point (f : F →+ F) (β : ℕ → F) (m : ℕ) : f (point β m) = point (f ∘ β) m := by
  simp only [point, map_sum, Function.comp]
  exact sum_congr rfl fun r _ => by split_ifs <;> simp

/-- With every bit below t set, point (2^t - 1) is the sum of the first t basis vectors. -/
theorem point_two_pow_sub_one (β : ℕ → F) (t : ℕ) :
    point β (2 ^ t - 1) = ∑ q ∈ range t, β q := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h : 2 ^ (t + 1) - 1 = (2 ^ t - 1) + 2 ^ t := by
      rw [pow_succ]; have := Nat.two_pow_pos t; omega
    rw [h, point_add_two_pow β (by have := Nat.two_pow_pos t; omega), ih, sum_range_succ]




section Vanishing

variable (β : ℕ → F)

@[simp] theorem vanishing_zero (x : F) : vanishing β 0 x = x := by simp [vanishing]

theorem vanishing_succ (i : ℕ) (x : F) :
    vanishing β (i + 1) x = vanishing β i x * vanishing β i (x - β i) := by
  simp only [vanishing, pow_succ, mul_two, prod_range_add]
  congr 1
  refine prod_congr rfl fun m hm => ?_
  rw [add_comm, point_add_two_pow β (mem_range.mp hm)]
  ring

theorem vanishing_point {i m : ℕ} (hm : m < 2 ^ i) : vanishing β i (point β m) = 0 :=
  prod_eq_zero (mem_range.mpr hm) (sub_self _)

/-- The scaling factor of the normalisation is nonzero for an independent basis. -/
theorem vanishing_basis_ne_zero {n i : ℕ} (hβ : Independent β n) (hi : i < n) :
    vanishing β i (β i) ≠ 0 :=
  prod_ne_zero_iff.mpr fun m hm => sub_ne_zero.mpr (hβ i hi m (mem_range.mp hm)).symm

section CharTwo

variable [CharP F 2]

/-- Lin, Chung and Han, Lemma 1: W_i is additive in characteristic 2. -/
theorem vanishing_add (i : ℕ) (x y : F) :
    vanishing β i (x + y) = vanishing β i x + vanishing β i y := by
  induction i generalizing x y with
  | zero => simp
  | succ i ih =>
    have hsub : ∀ z, vanishing β i (z - β i) = vanishing β i z + vanishing β i (β i) := by
      intro z; rw [CharTwo.sub_eq_add, ih]
    simp only [vanishing_succ, hsub, ih]
    linear_combination (vanishing β i x * vanishing β i y) * CharTwo.two_eq_zero (R := F)

/-- W_i as an additive map. -/
def vanishingHom (i : ℕ) : F →+ F where
  toFun := vanishing β i
  map_zero' := by
    have := vanishing_add β i 0 0
    rw [add_zero] at this
    linear_combination -this
  map_add' := vanishing_add β i

theorem vanishing_succ' (i : ℕ) (x : F) :
    vanishing β (i + 1) x = vanishing β i x * (vanishing β i x + vanishing β i (β i)) := by
  rw [vanishing_succ, CharTwo.sub_eq_add, vanishing_add]

theorem normalized_add (i : ℕ) (x y : F) :
    normalized β i (x + y) = normalized β i x + normalized β i y := by
  simp [normalized, vanishing_add, add_div]

omit [CharP F 2] in
theorem normalized_basis {n i : ℕ} (hβ : Independent β n) (hi : i < n) :
    normalized β i (β i) = 1 :=
  div_self (vanishing_basis_ne_zero β hβ hi)

omit [CharP F 2] in
theorem normalized_point {i m : ℕ} (hm : m < 2 ^ i) : normalized β i (point β m) = 0 := by
  simp [normalized, vanishing_point β hm]

/-- W^_l is constant on a coset of S_l. -/
theorem normalized_shift_low (l : ℕ) (shift : F) {i : ℕ} (hi : i < 2 ^ l) :
    normalized β l (shift + point β i) = normalized β l shift := by
  rw [normalized_add, normalized_point β hi, add_zero]

/-- W^_l rises by one on the next coset of S_l. -/
theorem normalized_shift_high {n l : ℕ} (hβ : Independent β n) (hl : l < n) (shift : F)
    {i : ℕ} (hi : i < 2 ^ l) :
    normalized β l (shift + point β (i + 2 ^ l)) = normalized β l shift + 1 := by
  rw [point_add_two_pow β hi, normalized_add, normalized_add, normalized_point β hi,
    normalized_basis β hβ hl, zero_add]

end CharTwo

/-! ## The novel basis -/

theorem novel_succ_low (l : ℕ) {k : ℕ} (hk : k < 2 ^ l) (x : F) :
    novel β (l + 1) k x = novel β l k x := by
  rw [novel, prod_range_succ]; simp [testBit_of_lt hk le_rfl]; rfl

theorem novel_succ_high (l : ℕ) {k : ℕ} (hk : k < 2 ^ l) (x : F) :
    novel β (l + 1) (k + 2 ^ l) x = novel β l k x * normalized β l x := by
  rw [novel, prod_range_succ, novel]
  congr 1
  · refine prod_congr rfl fun j hj => ?_
    rw [add_comm, ← mul_one (2 ^ l), Nat.testBit_two_pow_mul_add 1 hk]
    simp [mem_range.mp hj]
  · rw [add_comm, ← mul_one (2 ^ l), Nat.testBit_two_pow_mul_add 1 hk]; simp

/-! ## Cantor bases -/

section Cantor

variable [CharP F 2] {β}

omit [CharP F 2] in
theorem sqAddIter_succ (j : ℕ) (x : F) :
    sqAddIter (j + 1) x = sqAddIter j x ^ 2 + sqAddIter j x :=
  Function.iterate_succ_apply' _ j x

omit [CharP F 2] in
/-- The iterate sends beta_i to beta_(i-j). -/
theorem sqAddIter_basis {n : ℕ} (hβ : IsCantor β n) {i j : ℕ} (hi : i < n) (hj : j ≤ i) :
    sqAddIter j (β i) = β (i - j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [sqAddIter_succ, ih (by omega)]
    have := hβ.2 (i - (j + 1)) (by omega)
    rwa [show i - (j + 1) + 1 = i - j by omega] at this

/-- For a Cantor basis, W_j is the j-th iterate of x^2 + x. -/
theorem vanishing_eq_sqAddIter {n : ℕ} (hβ : IsCantor β n) {j : ℕ} (hj : j ≤ n) (x : F) :
    vanishing β j x = sqAddIter j x := by
  induction j generalizing x with
  | zero => simp [sqAddIter]
  | succ j ih =>
    rw [vanishing_succ', ih (by omega), ih (by omega), sqAddIter_succ,
      sqAddIter_basis hβ (by omega) le_rfl, Nat.sub_self, hβ.1]
    ring

theorem vanishing_basis_cantor {n : ℕ} (hβ : IsCantor β n) {j : ℕ} (hj : j < n) :
    vanishing β j (β j) = 1 := by
  rw [vanishing_eq_sqAddIter hβ hj.le, sqAddIter_basis hβ hj le_rfl, Nat.sub_self, hβ.1]

/-- A Cantor basis is independent. -/
theorem IsCantor.independent {n : ℕ} (hβ : IsCantor β n) : Independent β n := by
  intro i hi m hm h
  have := vanishing_point β hm
  rw [h, vanishing_basis_cantor hβ hi] at this
  exact one_ne_zero this

/-- For a Cantor basis, W^_j = W_j: the normalisation divides by one. -/
theorem normalized_eq_sqAddIter {n : ℕ} (hβ : IsCantor β n) {j : ℕ} (hj : j < n) (x : F) :
    normalized β j x = sqAddIter j x := by
  rw [normalized, vanishing_basis_cantor hβ hj, div_one, vanishing_eq_sqAddIter hβ hj.le]

/-- For a Cantor basis, the twiddle is W_j(shift) plus point(2b). -/
theorem twiddle_cantor {n : ℕ} (hβ : IsCantor β n) (shift : F) {j b : ℕ} (hj : j < n)
    (hb : b * 2 ^ (j + 1) < 2 ^ n) :
    twiddle β shift j b = sqAddIter j shift + point β (2 * b) := by
  have hb' : b < 2 ^ (n - (j + 1)) := by
    by_contra h
    have := Nat.mul_le_mul_right (2 ^ (j + 1)) (not_lt.mp h)
    rw [← pow_add, Nat.sub_add_cancel (by omega)] at this
    omega
  rw [twiddle, normalized_eq_sqAddIter hβ hj, ← vanishing_eq_sqAddIter hβ hj.le,
    ← vanishing_eq_sqAddIter hβ hj.le, vanishing_add, mul_comm, point_mul_two_pow]
  congr 1
  change vanishingHom β j _ = _
  rw [map_point, ← pow_one 2, point_mul_two_pow]
  refine point_congr hb' fun r hr => ?_
  simp only [Function.comp, vanishingHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [vanishing_eq_sqAddIter hβ hj.le, sqAddIter_basis hβ (by omega) (by omega)]
  congr 1; omega

end Cantor

end Vanishing




/-! ## Row arithmetic of one stage -/

theorem two_pow_succ' (j : ℕ) : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; ring

/-- Inside c blocks, a row of a lower half has its partner inside too. -/
theorem partner_lt {i c j : ℕ} (hi : i < c * 2 ^ (j + 1)) (hlo : i % 2 ^ (j + 1) < 2 ^ j) :
    i + 2 ^ j < c * 2 ^ (j + 1) := by
  have hq : i / 2 ^ (j + 1) < c := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
  have h := Nat.div_add_mod i (2 ^ (j + 1))
  have : 2 ^ (j + 1) * (i / 2 ^ (j + 1) + 1) ≤ 2 ^ (j + 1) * c := Nat.mul_le_mul_left _ hq
  rw [two_pow_succ'] at *
  nlinarith

theorem stage_offset (τ : ℕ → F) (j c : ℕ) (x : ℕ → V) (i : ℕ) :
    stage τ j x (i + c * 2 ^ (j + 1)) =
      stage (fun b => τ (b + c)) j (fun r => x (r + c * 2 ^ (j + 1))) i := by
  have hm : (i + c * 2 ^ (j + 1)) % 2 ^ (j + 1) = i % 2 ^ (j + 1) :=
    Nat.add_mul_mod_self_right _ _ _
  have hd : (i + c * 2 ^ (j + 1)) / 2 ^ (j + 1) = i / 2 ^ (j + 1) + c :=
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)
  simp only [stage, hm, hd]
  split_ifs with h
  · rw [show i + c * 2 ^ (j + 1) + 2 ^ j = i + 2 ^ j + c * 2 ^ (j + 1) by ring]
  · have : 2 ^ j ≤ i := le_trans (not_lt.mp h) (Nat.mod_le _ _)
    rw [show i + c * 2 ^ (j + 1) - 2 ^ j = i - 2 ^ j + c * 2 ^ (j + 1) by omega]

theorem istage_offset (τ : ℕ → F) (j c : ℕ) (x : ℕ → V) (i : ℕ) :
    istage τ j x (i + c * 2 ^ (j + 1)) =
      istage (fun b => τ (b + c)) j (fun r => x (r + c * 2 ^ (j + 1))) i := by
  have hm : (i + c * 2 ^ (j + 1)) % 2 ^ (j + 1) = i % 2 ^ (j + 1) :=
    Nat.add_mul_mod_self_right _ _ _
  have hd : (i + c * 2 ^ (j + 1)) / 2 ^ (j + 1) = i / 2 ^ (j + 1) + c :=
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)
  simp only [istage, hm, hd]
  split_ifs with h
  · rw [show i + c * 2 ^ (j + 1) + 2 ^ j = i + 2 ^ j + c * 2 ^ (j + 1) by ring]
  · have : 2 ^ j ≤ i := le_trans (not_lt.mp h) (Nat.mod_le _ _)
    rw [show i + c * 2 ^ (j + 1) - 2 ^ j = i - 2 ^ j + c * 2 ^ (j + 1) by omega]

theorem stage_congr {τ τ' : ℕ → F} {j c : ℕ} {x x' : ℕ → V} (hτ : ∀ b < c, τ b = τ' b)
    (hx : ∀ i < c * 2 ^ (j + 1), x i = x' i) {i : ℕ} (hi : i < c * 2 ^ (j + 1)) :
    stage τ j x i = stage τ' j x' i := by
  have hq : i / 2 ^ (j + 1) < c := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
  simp only [stage, hτ _ hq]
  split_ifs with h
  · rw [hx i hi, hx _ (partner_lt hi h)]
  · rw [hx i hi, hx _ (by omega)]

theorem istage_congr {τ τ' : ℕ → F} {j c : ℕ} {x x' : ℕ → V} (hτ : ∀ b < c, τ b = τ' b)
    (hx : ∀ i < c * 2 ^ (j + 1), x i = x' i) {i : ℕ} (hi : i < c * 2 ^ (j + 1)) :
    istage τ j x i = istage τ' j x' i := by
  have hq : i / 2 ^ (j + 1) < c := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
  simp only [istage, hτ _ hq]
  split_ifs with h
  · rw [hx i hi, hx _ (partner_lt hi h)]
  · rw [hx i hi, hx _ (by omega)]

/-- The partner of a lower-half row sits in the upper half of the same block. -/
theorem partner_up {i j : ℕ} (h : i % 2 ^ (j + 1) < 2 ^ j) :
    ¬ (i + 2 ^ j) % 2 ^ (j + 1) < 2 ^ j ∧ (i + 2 ^ j) / 2 ^ (j + 1) = i / 2 ^ (j + 1) := by
  have hr : i % 2 ^ (j + 1) + 2 ^ j < 2 ^ (j + 1) := by rw [two_pow_succ'] at *; omega
  have e : i + 2 ^ j = 2 ^ (j + 1) * (i / 2 ^ (j + 1)) + (i % 2 ^ (j + 1) + 2 ^ j) := by
    have := Nat.div_add_mod i (2 ^ (j + 1)); omega
  rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt hr, Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hr]
  simp

/-- The partner of an upper-half row sits in the lower half of the same block. -/
theorem partner_down {i j : ℕ} (h : ¬ i % 2 ^ (j + 1) < 2 ^ j) :
    2 ^ j ≤ i ∧ (i - 2 ^ j) % 2 ^ (j + 1) < 2 ^ j ∧
      (i - 2 ^ j) / 2 ^ (j + 1) = i / 2 ^ (j + 1) := by
  have hm := Nat.mod_lt i (Nat.two_pow_pos (j + 1))
  have hr : i % 2 ^ (j + 1) - 2 ^ j < 2 ^ (j + 1) := by omega
  have hle : 2 ^ j ≤ i := le_trans (not_lt.mp h) (Nat.mod_le _ _)
  have e : i - 2 ^ j = 2 ^ (j + 1) * (i / 2 ^ (j + 1)) + (i % 2 ^ (j + 1) - 2 ^ j) := by
    have := Nat.div_add_mod i (2 ^ (j + 1)); omega
  refine ⟨hle, ?_, ?_⟩
  · rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]; rw [two_pow_succ'] at hm; omega
  · rw [e, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hr]; simp

/-! ## The inverse network undoes the forward network -/

section CharTwo

variable [CharP F 2]

theorem istage_stage (τ : ℕ → F) (j : ℕ) (x : ℕ → V) : istage τ j (stage τ j x) = x := by
  funext i
  simp only [istage, stage]
  by_cases h : i % 2 ^ (j + 1) < 2 ^ j
  · obtain ⟨h2, h3⟩ := partner_up h
    simp only [h, h2, h3, ite_true, ite_false, butterfly, ibutterfly, Nat.add_sub_cancel]
    set t := τ (i / 2 ^ (j + 1))
    linear_combination (norm := module) CharTwo.two_eq_zero (R := F) •
      (t • x (i + 2 ^ j) + t • x i + (t * t) • x (i + 2 ^ j))
  · obtain ⟨hle, h2, h3⟩ := partner_down h
    simp only [h, h2, h3, ite_true, ite_false, butterfly, ibutterfly, Nat.sub_add_cancel hle]
    set t := τ (i / 2 ^ (j + 1))
    linear_combination (norm := module) CharTwo.two_eq_zero (R := F) •
      (x (i - 2 ^ j) + t • x i)

theorem stage_istage (τ : ℕ → F) (j : ℕ) (x : ℕ → V) : stage τ j (istage τ j x) = x := by
  funext i
  simp only [istage, stage]
  by_cases h : i % 2 ^ (j + 1) < 2 ^ j
  · obtain ⟨h2, h3⟩ := partner_up h
    simp only [h, h2, h3, ite_true, ite_false, butterfly, ibutterfly, Nat.add_sub_cancel]
    set t := τ (i / 2 ^ (j + 1))
    linear_combination (norm := module) CharTwo.two_eq_zero (R := F) •
      (t • (x i + x (i + 2 ^ j)))
  · obtain ⟨hle, h2, h3⟩ := partner_down h
    simp only [h, h2, h3, ite_true, ite_false, butterfly, ibutterfly, Nat.sub_add_cancel hle]
    set t := τ (i / 2 ^ (j + 1))
    linear_combination (norm := module) CharTwo.two_eq_zero (R := F) •
      (x (i - 2 ^ j) + t • (x (i - 2 ^ j) + x i))

/-- The inverse network undoes the forward network, for any twiddles. -/
theorem inetwork_network (τ : ℕ → ℕ → F) (l : ℕ) (x : ℕ → V) :
    inetwork τ l (network τ l x) = x := by
  induction l generalizing x with
  | zero => rfl
  | succ l ih => simp only [network, inetwork, ih, istage_stage]

/-- The forward network undoes the inverse network, for any twiddles. -/
theorem network_inetwork (τ : ℕ → ℕ → F) (l : ℕ) (x : ℕ → V) :
    network τ l (inetwork τ l x) = x := by
  induction l generalizing x with
  | zero => rfl
  | succ l ih =>
    simp only [network, inetwork, stage_istage]
    exact ih x

end CharTwo

/-! ## Rows a network reads -/

/-- The network only reads the twiddles of its l stages. -/
theorem network_twiddle_congr {τ τ' : ℕ → ℕ → F} {l : ℕ} (h : ∀ j < l, τ j = τ' j)
    (x : ℕ → V) : network τ l x = network τ' l x := by
  induction l generalizing x with
  | zero => rfl
  | succ l ih => simp only [network, h l (Nat.lt_succ_self l), ih fun j hj => h j (by omega)]

theorem blocks_succ {c l j : ℕ} (hj : j < l) :
    c * 2 ^ (l + 1 - 1 - j) = 2 * c * 2 ^ (l - 1 - j) := by
  rw [show l + 1 - 1 - j = l - 1 - j + 1 by omega, pow_succ]; ring

/-- The rows of c whole blocks of 2^l depend only on those rows and their blocks' twiddles. -/
theorem network_congr {τ τ' : ℕ → ℕ → F} {l c : ℕ} {x x' : ℕ → V}
    (hτ : ∀ j < l, ∀ b < c * 2 ^ (l - 1 - j), τ j b = τ' j b)
    (hx : ∀ i < c * 2 ^ l, x i = x' i) {i : ℕ} (hi : i < c * 2 ^ l) :
    network τ l x i = network τ' l x' i := by
  induction l generalizing c x x' with
  | zero => exact hx i hi
  | succ l ih =>
    have e : c * 2 ^ (l + 1) = 2 * c * 2 ^ l := by ring
    refine ih (c := 2 * c) (fun j hj b hb => hτ j (by omega) b ?_) (fun r hr => ?_) (by rwa [← e])
    · rwa [blocks_succ hj]
    · exact stage_congr (c := c) (fun b hb => hτ l (by omega) b (by simpa using hb)) hx
        (by rwa [e])

theorem inetwork_congr {τ τ' : ℕ → ℕ → F} {l c : ℕ} {x x' : ℕ → V}
    (hτ : ∀ j < l, ∀ b < c * 2 ^ (l - 1 - j), τ j b = τ' j b)
    (hx : ∀ i < c * 2 ^ l, x i = x' i) {i : ℕ} (hi : i < c * 2 ^ l) :
    inetwork τ l x i = inetwork τ' l x' i := by
  induction l generalizing c i with
  | zero => exact hx i hi
  | succ l ih =>
    have e : c * 2 ^ (l + 1) = 2 * c * 2 ^ l := by ring
    refine istage_congr (c := c) (fun b hb => hτ l (by omega) b (by simpa using hb))
      (fun r hr => ih (c := 2 * c) (fun j hj b hb => hτ j (by omega) b ?_)
        (fun r hr => hx r (by rwa [e])) (by rwa [← e])) hi
    rwa [blocks_succ hj]

/-- Past c whole blocks of 2^l, the network is that of the rows above.

The blocks are renumbered from zero. -/
theorem network_offset (τ : ℕ → ℕ → F) (l c : ℕ) (x : ℕ → V) (i : ℕ) :
    network τ l x (i + c * 2 ^ l) =
      network (fun j b => τ j (b + c * 2 ^ (l - 1 - j))) l (fun r => x (r + c * 2 ^ l)) i := by
  induction l generalizing c x with
  | zero => rfl
  | succ l ih =>
    simp only [network]
    rw [show c * 2 ^ (l + 1) = 2 * c * 2 ^ l by ring, ih,
      network_twiddle_congr (τ' := fun j b => τ j (b + c * 2 ^ (l + 1 - 1 - j))) (fun j hj => ?_)]
    · congr 1; funext r
      rw [show 2 * c * 2 ^ l = c * 2 ^ (l + 1) by ring, stage_offset]; simp
    · funext b; rw [blocks_succ hj]

theorem inetwork_twiddle_congr {τ τ' : ℕ → ℕ → F} {l : ℕ} (h : ∀ j < l, τ j = τ' j)
    (x : ℕ → V) : inetwork τ l x = inetwork τ' l x := by
  induction l generalizing x with
  | zero => rfl
  | succ l ih => simp only [inetwork, h l (Nat.lt_succ_self l), ih fun j hj => h j (by omega)]

/-- Past c whole blocks of 2^l, the inverse network is that of the rows above.

The blocks are renumbered from zero. -/
theorem inetwork_offset (τ : ℕ → ℕ → F) (l c : ℕ) (x : ℕ → V) (i : ℕ) :
    inetwork τ l x (i + c * 2 ^ l) =
      inetwork (fun j b => τ j (b + c * 2 ^ (l - 1 - j))) l (fun r => x (r + c * 2 ^ l)) i := by
  induction l generalizing c x i with
  | zero => rfl
  | succ l ih =>
    simp only [inetwork]
    rw [istage_offset]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    congr 1
    funext r
    rw [show c * 2 ^ (l + 1) = 2 * c * 2 ^ l by ring, ih,
      inetwork_twiddle_congr (τ' := fun j b => τ j (b + c * 2 ^ (l + 1 - 1 - j))) (fun j hj => ?_)]
    · rfl
    · funext b; rw [blocks_succ hj]

/-! ## The top stage of a network of 2^(l+1) rows -/

theorem stage_top_low (τ : ℕ → F) (l : ℕ) (d : ℕ → V) {k : ℕ} (hk : k < 2 ^ l) :
    stage τ l d k = d k + τ 0 • d (k + 2 ^ l) := by
  have h1 : k < 2 ^ (l + 1) := by rw [two_pow_succ']; omega
  simp [stage, Nat.mod_eq_of_lt h1, Nat.div_eq_of_lt h1, hk, butterfly]

theorem stage_top_high (τ : ℕ → F) (l : ℕ) (d : ℕ → V) {k : ℕ} (hk : k < 2 ^ l) :
    stage τ l d (k + 2 ^ l) = d k + τ 0 • d (k + 2 ^ l) + d (k + 2 ^ l) := by
  have h1 : k + 2 ^ l < 2 ^ (l + 1) := by rw [two_pow_succ']; omega
  simp [stage, Nat.mod_eq_of_lt h1, Nat.div_eq_of_lt h1, butterfly]

/-! ## Evaluations in the novel basis -/

theorem novelEval_congr (β : ℕ → F) (l : ℕ) {d d' : ℕ → V} (h : ∀ k < 2 ^ l, d k = d' k)
    (x : F) : novelEval β l d x = novelEval β l d' x :=
  sum_congr rfl fun k hk => by rw [h k (mem_range.mp hk)]

/-- Splitting the novel basis at bit l: sum_k d_k X_k = P_0 + W^_l P_1. -/
theorem novelEval_succ (β : ℕ → F) (l : ℕ) (d : ℕ → V) (x : F) :
    novelEval β (l + 1) d x =
      novelEval β l d x + normalized β l x • novelEval β l (fun k => d (k + 2 ^ l)) x := by
  rw [novelEval, two_pow_succ', sum_range_add, novelEval, novelEval, smul_sum]
  congr 1
  · exact sum_congr rfl fun k hk => by rw [novel_succ_low β l (mem_range.mp hk)]
  · refine sum_congr rfl fun k hk => ?_
    rw [add_comm (2 ^ l) k, novel_succ_high β l (mem_range.mp hk), smul_smul, mul_comm]

theorem novelEval_add_smul (β : ℕ → F) (l : ℕ) (a b : ℕ → V) (t x : F) :
    novelEval β l (fun k => a k + t • b k) x = novelEval β l a x + t • novelEval β l b x := by
  simp only [novelEval, smul_add, sum_add_distrib, smul_sum, smul_comm t]

/-! ## The network computes the additive NTT -/

section CharTwo

variable [CharP F 2]

omit [CharP F 2] in
/-- The twiddles of the upper half are those of the coset shifted by beta_l. -/
theorem twiddle_upper (β : ℕ → F) (shift : F) {l j b : ℕ} (hj : j < l)
    (hb : b < 2 ^ (l - 1 - j)) :
    twiddle β shift j (b + 1 * 2 ^ (l - 1 - j)) = twiddle β (shift + β l) j b := by
  have e : (b + 1 * 2 ^ (l - 1 - j)) * 2 ^ (j + 1) = b * 2 ^ (j + 1) + 2 ^ l := by
    rw [one_mul, add_mul, ← pow_add, show l - 1 - j + (j + 1) = l by omega]
  have hlt : b * 2 ^ (j + 1) < 2 ^ l := by
    calc b * 2 ^ (j + 1) < 2 ^ (l - 1 - j) * 2 ^ (j + 1) :=
          Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos _)
      _ = 2 ^ l := by rw [← pow_add, show l - 1 - j + (j + 1) = l by omega]
  rw [twiddle, twiddle, e, point_add_two_pow β hlt]
  congr 1; ring

/-- Lin, Chung and Han, section III: the network computes the additive NTT.

The twiddles are W^_j at the block points, and the basis is independent. -/
theorem network_ntt (β : ℕ → F) {n l : ℕ} (hβ : Independent β n) (hl : l ≤ n) (shift : F)
    (d : ℕ → V) {i : ℕ} (hi : i < 2 ^ l) :
    network (twiddle β shift) l d i = ntt β l shift d i := by
  induction l generalizing shift d i with
  | zero =>
    obtain rfl : i = 0 := by simpa using hi
    simp [network, ntt, novelEval, novel]
  | succ l ih =>
    have ht : twiddle β shift l 0 = normalized β l shift := by simp [twiddle]
    simp only [network]
    rw [ntt, novelEval_succ]
    by_cases hlo : i < 2 ^ l
    · rw [ih (by omega) shift _ hlo, ntt, normalized_shift_low β l shift hlo, ← ht,
        ← novelEval_add_smul]
      exact novelEval_congr β l (fun k hk => stage_top_low _ l d hk) _
    · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 2 ^ l := ⟨i - 2 ^ l, by omega⟩
      have hi' : i < 2 ^ l := by rw [two_pow_succ'] at hi; omega
      rw [← one_mul (2 ^ l), network_offset, one_mul,
        network_congr (V := V) (c := 1) (τ' := twiddle β (shift + β l))
          (fun j hj b hb => twiddle_upper β shift hj (by simpa using hb))
          (fun _ _ => rfl) (by simpa using hi'),
        ih (by omega) _ _ hi', ntt, normalized_shift_high β hβ (by omega) shift hi',
        point_add_two_pow β hi', show shift + (point β i + β l) = shift + β l + point β i by ring,
        ← novelEval_add_smul]
      refine novelEval_congr (V := V) β l (fun k hk => ?_) _
      rw [stage_top_high _ l d hk, ht, add_smul, one_smul, add_assoc]

/-- The inverse network recovers the coefficients from the values on the coset. -/
theorem inetwork_ntt (β : ℕ → F) {n l : ℕ} (hβ : Independent β n) (hl : l ≤ n) (shift : F)
    (d y : ℕ → V) (hy : ∀ i < 2 ^ l, y i = ntt β l shift d i) {i : ℕ} (hi : i < 2 ^ l) :
    inetwork (twiddle β shift) l y i = d i := by
  rw [← inetwork_network (twiddle β shift) l d]
  refine inetwork_congr (c := 1) (fun _ _ _ _ => rfl) (fun r hr => ?_) (by simpa using hi)
  rw [hy r (by simpa using hr), network_ntt β hβ hl shift d (by simpa using hr)]

end CharTwo

theorem novelEval_pad (β : ℕ → F) {m : ℕ} (d : ℕ → V) (hd : ∀ k, 2 ^ m ≤ k → d k = 0) (r : ℕ)
    (x : F) : novelEval β (m + r) d x = novelEval β m d x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [← add_assoc, novelEval_succ, ih]
    have h0 : novelEval β (m + r) (fun k => d (k + 2 ^ (m + r))) x = 0 := by
      refine sum_eq_zero fun k _ => ?_
      have : 2 ^ m ≤ k + 2 ^ (m + r) :=
        le_trans (Nat.pow_le_pow_right two_pos (Nat.le_add_right m r)) (Nat.le_add_left _ _)
      simp only [hd _ this, smul_zero]
    rw [h0, smul_zero, add_zero]

/-- Coefficients zero from 2^m on: row c 2^m + i over S_(m+r) is row i over point(c 2^m) + S_m. -/
theorem ntt_pad (β : ℕ → F) {m : ℕ} (r : ℕ) (shift : F) (d : ℕ → V)
    (hd : ∀ k, 2 ^ m ≤ k → d k = 0) (c : ℕ) {i : ℕ} (hi : i < 2 ^ m) :
    ntt β (m + r) shift d (c * 2 ^ m + i) = ntt β m (shift + point β (c * 2 ^ m)) d i := by
  rw [ntt, ntt, novelEval_pad β d hd, mul_comm c, point_add_mul β c m hi, add_assoc]


end AdditiveNTT.Coset
