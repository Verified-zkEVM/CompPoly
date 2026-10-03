/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Correctness.Basic
public import CompPoly.Univariate.NTTFast.Packed.Twiddles

/-! # Squared-root domains and shared twiddle prefixes -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- The domain used by each child after splitting the first DIF layer. -/
def halfDomain [Field R] (D : NTT.Domain R) (hlog : 0 < D.logN) : NTT.Domain R where
  logN := D.logN - 1
  omega := D.omega ^ 2
  primitive := by
    apply IsPrimitiveRoot.pow D.n_pos D.primitive
    change 2 ^ D.logN = 2 * 2 ^ (D.logN - 1)
    have he : D.logN = (D.logN - 1) + 1 := by omega
    conv_lhs => rw [he, Nat.pow_succ]
    omega

/-- Each child domain has exactly half its parent's size. -/
theorem halfDomain_size [Field R] (D : NTT.Domain R) (hlog : 0 < D.logN) :
    D.n = 2 * (halfDomain D hlog).n := by
  change 2 ^ D.logN = 2 * 2 ^ (D.logN - 1)
  have he : D.logN = (D.logN - 1) + 1 := by omega
  conv_lhs => rw [he, Nat.pow_succ]
  omega

/-- Squaring the root and halving the domain preserves every lower-stage twiddle root. -/
theorem halfDomain_stageRoot [Field R] (D : NTT.Domain R) (hlog : 0 < D.logN)
    (stage : Nat) (hs : stage < D.logN - 1) :
    (halfDomain D hlog).omega ^ ((halfDomain D hlog).n / 2 ^ (stage + 1)) =
      D.omega ^ (D.n / 2 ^ (stage + 1)) := by
  change (D.omega ^ 2) ^ (2 ^ (D.logN - 1) / 2 ^ (stage + 1)) =
    D.omega ^ (2 ^ D.logN / 2 ^ (stage + 1))
  rw [← pow_mul, Nat.pow_div (by omega : stage + 1 ≤ D.logN - 1) (by decide : 0 < 2),
    Nat.pow_div (by omega : stage + 1 ≤ D.logN) (by decide : 0 < 2)]
  have he : D.logN - (stage + 1) = (D.logN - 1 - (stage + 1)) + 1 := by omega
  rw [he, Nat.pow_succ]
  congr 1
  omega

/-- The complete lower-stage twiddle arrays agree between a parent and its child domain. -/
theorem halfDomain_twiddlePowers [Field R] (D : NTT.Domain R) (hlog : 0 < D.logN)
    (stage : Nat) (hs : stage < D.logN - 1) :
    Plan.twiddlePowers (halfDomain D hlog) stage = Plan.twiddlePowers D stage := by
  apply array_eq_of_getD _ _ (0 : R)
  · rw [Plan.twiddlePowers_size, Plan.twiddlePowers_size]
  · intro k
    by_cases hk : k < 2 ^ stage
    · rw [Plan.twiddlePowers_getD_eq_pow _ _ _ hk,
        Plan.twiddlePowers_getD_eq_pow _ _ _ hk, halfDomain_stageRoot D hlog stage hs]
    · have hl : (Plan.twiddlePowers (halfDomain D hlog) stage)[k]? = none :=
        Array.getElem?_eq_none (by rw [Plan.twiddlePowers_size]; omega)
      have hr : (Plan.twiddlePowers D stage)[k]? = none :=
        Array.getElem?_eq_none (by rw [Plan.twiddlePowers_size]; omega)
      simp only [Array.getD_eq_getD_getElem?, hl, hr, Option.getD_none]

/-- A parent-domain table remains valid for every recursive child transform. -/
theorem TwiddlesFor.half (D : NTT.Domain KoalaBear.Fast.Field) (hlog : 0 < D.logN)
    (tw : Array (Array KoalaBear.Fast.Field)) (ht : TwiddlesFor D tw) :
    TwiddlesFor (halfDomain D hlog) tw := by
  intro stage hs
  have hs' : stage < D.logN - 1 := hs
  rw [ht stage (by omega), Plan.twiddleTable_getD_eq_twiddlePowers _ _ (by omega),
    Plan.twiddleTable_getD_eq_twiddlePowers _ _ hs, halfDomain_twiddlePowers D hlog stage hs']

end CompPoly.CPolynomial.NTTFast.Packed
