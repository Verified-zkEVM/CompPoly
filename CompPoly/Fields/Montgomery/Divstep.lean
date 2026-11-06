/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPoly.Fields.Montgomery.DivstepDefs

/-!
# Word-sized divsteps: coefficient bounds

Unfolding lemmas for `gcdInner` of `Montgomery/DivstepDefs`, and the bound on the entries of
its transition matrix. A chunk of at most 31 divsteps keeps `|f| + |g| ≤ 2^31` in each row.
The linear combinations of the multi-limb inversion runtimes require that bound.
-/

@[expose] public section

namespace Montgomery

/-- Unfolding of the empty divstep run. -/
theorem gcdInner_zero (a b : UInt64) (f0 g0 f1 g1 : Int) :
    gcdInner 0 a b f0 g0 f1 g1 = (a, b, f0, g0, f1, g1) := rfl

/-- Unfolding of one divstep. -/
theorem gcdInner_succ (rounds : Nat) (a b : UInt64) (f0 g0 f1 g1 : Int) :
    gcdInner (rounds + 1) a b f0 g0 f1 g1 =
      if a &&& 1 == 0 then
        gcdInner rounds (a >>> 1) b f0 g0 (f1 * 2) (g1 * 2)
      else if a < b then
        gcdInner rounds ((b - a) >>> 1) a (f1 - f0) (g1 - g0) (f0 * 2) (g0 * 2)
      else
        gcdInner rounds ((a - b) >>> 1) b (f0 - f1) (g0 - g1) (f1 * 2) (g1 * 2) := by
  simp only [gcdInner]
  by_cases h1 : a &&& 1 == 0
  · rw [ite_eq_left h1, ite_eq_left h1]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : a < b
    · rw [ite_eq_left h2, ite_eq_left h2]
    · rw [ite_eq_right h2, ite_eq_right h2]

/-- Transition entries at most double per divstep. -/
theorem gcdInner_natAbs_le {rounds : Nat} {a b a' b' : UInt64}
    {f0 g0 f1 g1 f0' g0' f1' g1' : Int} {n : Nat}
    (h0 : f0.natAbs + g0.natAbs ≤ n) (h1 : f1.natAbs + g1.natAbs ≤ n)
    (heq : gcdInner rounds a b f0 g0 f1 g1 = (a', b', f0', g0', f1', g1')) :
    f0'.natAbs + g0'.natAbs ≤ 2 ^ rounds * n ∧
      f1'.natAbs + g1'.natAbs ≤ 2 ^ rounds * n := by
  induction rounds generalizing a b f0 g0 f1 g1 n with
  | zero =>
    rw [gcdInner_zero] at heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨-, -, rfl, rfl, rfl, rfl⟩ := heq
    rw [Nat.pow_zero, Nat.one_mul]
    exact ⟨h0, h1⟩
  | succ k ih =>
    have step : ∀ {A B : UInt64} {F0 G0 F1 G1 : Int},
        F0.natAbs + G0.natAbs ≤ 2 * n → F1.natAbs + G1.natAbs ≤ 2 * n →
        gcdInner k A B F0 G0 F1 G1 = (a', b', f0', g0', f1', g1') →
        f0'.natAbs + g0'.natAbs ≤ 2 ^ (k + 1) * n ∧
          f1'.natAbs + g1'.natAbs ≤ 2 ^ (k + 1) * n := by
      intro A B F0 G0 F1 G1 hF hG hEq
      rw [Nat.pow_succ, Nat.mul_assoc]
      exact ih hF hG hEq
    rw [gcdInner_succ] at heq
    split at heq
    · exact step (by omega) (by omega) heq
    · split at heq
      · exact step (by omega) (by omega) heq
      · exact step (by omega) (by omega) heq

/-- Chunks of at most 31 divsteps satisfy the linear-combination bound. -/
theorem gcdInner_natAbs_le_31 {rounds : Nat} (h31 : rounds ≤ 31) {a b a' b' : UInt64}
    {f0' g0' f1' g1' : Int}
    (heq : gcdInner rounds a b 1 0 0 1 = (a', b', f0', g0', f1', g1')) :
    f0'.natAbs + g0'.natAbs ≤ 2 ^ 31 ∧ f1'.natAbs + g1'.natAbs ≤ 2 ^ 31 := by
  have h := gcdInner_natAbs_le (n := 1) (by decide) (by decide) heq
  have hle : 2 ^ rounds ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) h31
  omega

end Montgomery
