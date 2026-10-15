/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.GroupWithZero.Basic

/-!
# Batch inversion

Montgomery's trick inverts `n` elements with one inversion and `3 (n - 1)` multiplications: invert
the product of all elements, then walk back through the prefix products, peeling one factor at a
time.

The algorithm only needs `*`, `⁻¹` and `1`, so it runs on carriers without a `Field` instance;
`batchInv_map` transfers it along any map preserving those operations, and `batchInv_eq` proves it
in a commutative group with zero, for inputs without zeros.
-/

@[expose] public section

namespace CompPoly.List

variable {K L : Type*}

section Ops

variable [Mul K]

/-- The products `q, q x₀, q x₀ x₁, …` of all proper prefixes, each times `q`. -/
def prefixProducts (q : K) : List K → List K
  | [] => []
  | x :: l => q :: prefixProducts (q * x) l

/-- `q x₀ x₁ ⋯`. -/
def productFrom (q : K) : List K → K
  | [] => q
  | x :: l => productFrom (q * x) l

/-- Walk the reversed elements and prefix products, peeling one factor off the running inverse at
each step and prepending that element's inverse to `out`. -/
def batchInvGo : List K → List K → K → List K → List K
  | x :: xs, p :: ps, acc, out => batchInvGo xs ps (acc * x) ((acc * p) :: out)
  | _, _, _, out => out

/-- The inverses of all elements, with one inversion. -/
def batchInv [Inv K] [One K] (xs : List K) : List K :=
  batchInvGo xs.reverse (prefixProducts 1 xs).reverse (productFrom 1 xs)⁻¹ []

theorem length_prefixProducts (q : K) (l : List K) :
    (prefixProducts q l).length = l.length := by
  induction l generalizing q with
  | nil => rfl
  | cons x l ih => simp only [prefixProducts, List.length_cons, ih]

theorem length_batchInvGo (xs ps : List K) (hl : xs.length = ps.length) (acc : K)
    (out : List K) : (batchInvGo xs ps acc out).length = xs.length + out.length := by
  induction xs generalizing ps acc out with
  | nil => cases ps <;> simp [batchInvGo]
  | cons x xs ih =>
    cases ps with
    | nil => simp at hl
    | cons p ps =>
      rw [batchInvGo, ih ps (by simpa using hl)]
      simp only [List.length_cons]; omega

@[simp] theorem length_batchInv [Inv K] [One K] (xs : List K) :
    (batchInv xs).length = xs.length := by
  rw [batchInv, length_batchInvGo _ _ (by simp [length_prefixProducts]), List.length_reverse,
    List.length_nil, Nat.add_zero]

end Ops

/-! ### Transfer along structure-preserving maps -/

section Map

variable [Mul K] [Mul L] (f : K → L)

theorem prefixProducts_map (hmul : ∀ a b, f (a * b) = f a * f b) (q : K) (l : List K) :
    prefixProducts (f q) (l.map f) = (prefixProducts q l).map f := by
  induction l generalizing q with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, prefixProducts, ← hmul, ih]

theorem productFrom_map (hmul : ∀ a b, f (a * b) = f a * f b) (q : K) (l : List K) :
    productFrom (f q) (l.map f) = f (productFrom q l) := by
  induction l generalizing q with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, productFrom, ← hmul, ih]

theorem batchInvGo_map (hmul : ∀ a b, f (a * b) = f a * f b) (xs ps : List K) (acc : K)
    (out : List K) :
    batchInvGo (xs.map f) (ps.map f) (f acc) (out.map f) = (batchInvGo xs ps acc out).map f := by
  induction xs generalizing ps acc out with
  | nil => cases ps <;> rfl
  | cons x xs ih =>
    cases ps with
    | nil => rfl
    | cons p ps =>
      simp only [List.map_cons, batchInvGo, ← hmul]
      rw [← ih, List.map_cons, hmul]

/-- Batch inversion commutes with maps preserving `*`, `⁻¹` and `1`. -/
theorem batchInv_map [Inv K] [One K] [Inv L] [One L] (hmul : ∀ a b, f (a * b) = f a * f b)
    (hinv : ∀ a, f a⁻¹ = (f a)⁻¹)
    (hone : f 1 = 1) (xs : List K) :
    batchInv (xs.map f) = (batchInv xs).map f := by
  rw [batchInv, batchInv, ← List.map_reverse, ← hone, prefixProducts_map f hmul,
    productFrom_map f hmul, ← hinv, ← List.map_reverse, ← batchInvGo_map f hmul,
    List.map_nil]

end Map

/-! ### Correctness -/

section Field

variable [CommGroupWithZero K]

theorem productFrom_eq (q : K) (l : List K) : productFrom q l = q * l.prod := by
  induction l generalizing q with
  | nil => simp only [productFrom, List.prod_nil, mul_one]
  | cons x l ih => rw [productFrom, ih, List.prod_cons, mul_assoc]

theorem prefixProducts_append_singleton (q : K) (l : List K) (x : K) :
    prefixProducts q (l ++ [x]) = prefixProducts q l ++ [q * l.prod] := by
  induction l generalizing q with
  | nil => simp only [List.nil_append, prefixProducts, List.prod_nil, mul_one]
  | cons y l ih => rw [List.cons_append, prefixProducts, prefixProducts, ih, List.prod_cons,
      mul_assoc, List.cons_append]

theorem batchInvGo_spec_reverse (r : List K) (hl : ∀ x ∈ r, x ≠ 0) (q : K) (hq : q ≠ 0)
    (out : List K) :
    batchInvGo r.reverse.reverse (prefixProducts q r.reverse).reverse (q * r.reverse.prod)⁻¹ out =
      r.reverse.map (·⁻¹) ++ out := by
  induction r generalizing out with
  | nil => simp only [List.reverse_nil, prefixProducts, List.map_nil, List.nil_append]; rfl
  | cons x r ih =>
    have hx : x ≠ 0 := hl x (by simp)
    have hl' : ∀ y ∈ r, y ≠ 0 := fun y hy ↦ hl y (by simp [hy])
    have hp : q * r.reverse.prod ≠ 0 :=
      mul_ne_zero hq (List.prod_ne_zero (fun h ↦ hl' 0 (List.mem_reverse.mp h) rfl))
    rw [List.reverse_cons, prefixProducts_append_singleton, List.reverse_append,
      List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      batchInvGo, List.prod_append, List.prod_singleton]
    have e1 : (q * (r.reverse.prod * x))⁻¹ * (q * r.reverse.prod) = x⁻¹ := by
      rw [← mul_assoc q, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hp, mul_one]
    have e2 : (q * (r.reverse.prod * x))⁻¹ * x = (q * r.reverse.prod)⁻¹ := by
      rw [← mul_assoc q, mul_inv_rev, mul_comm x⁻¹, mul_assoc, inv_mul_cancel₀ hx, mul_one]
    rw [e1, e2,
      ih hl', List.map_append, List.map_singleton, List.append_assoc, List.singleton_append]

/-- Batch inversion inverts every element of a list without zeros. -/
theorem batchInv_eq (xs : List K) (hxs : ∀ x ∈ xs, x ≠ 0) : batchInv xs = xs.map (·⁻¹) := by
  have h := batchInvGo_spec_reverse xs.reverse (fun x hx ↦ hxs x (List.mem_reverse.mp hx)) 1
    one_ne_zero []
  simp only [List.reverse_reverse] at h
  rw [one_mul, List.append_nil] at h
  rw [batchInv, productFrom_eq, one_mul]
  exact h

end Field

end CompPoly.List
