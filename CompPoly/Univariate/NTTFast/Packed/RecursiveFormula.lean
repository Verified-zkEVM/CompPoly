/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Correctness.DIF
public import CompPoly.Univariate.NTTFast.Packed.HalfDomain
import Mathlib.Tactic.Ring

/-! # The recursive DIF split computes the even and odd evaluations -/

@[expose] public section
open scoped BigOperators
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- The left first-layer partition holds the sum of corresponding input halves. -/
def splitFieldsLeft [Field R] (D : NTT.Domain R) (a : Array R) : Array R :=
  Array.ofFn (fun i : Fin (2 ^ (D.logN - 1)) ↦
    a.getD i.val 0 + a.getD (i.val + 2 ^ (D.logN - 1)) 0)

/-- The right first-layer partition holds the twiddle-scaled difference of input halves. -/
def splitFieldsRight [Field R] (D : NTT.Domain R) (a : Array R) : Array R :=
  Array.ofFn (fun i : Fin (2 ^ (D.logN - 1)) ↦
    D.omega ^ i.val * (a.getD i.val 0 - a.getD (i.val + 2 ^ (D.logN - 1)) 0))

/-- The DFT formula with a natural-number evaluation index. -/
def dftValue [Field R] (D : NTT.Domain R) (a : Array R) (k : Nat) : R :=
  ∑ i ∈ Finset.range D.n, a.getD i 0 * D.omega ^ (k * i)

/-- Natural-number and bounded-index DFT formulas have the same sum. -/
theorem dftValue_eq_nttAt [Field R] (D : NTT.Domain R) (a : Array R) (k : D.Idx) :
    dftValue D a k.val = NTT.Forward.nttAt D a k := by
  symm
  exact Fin.sum_univ_eq_sum_range (fun i ↦ a.getD i 0 * D.omega ^ (k.val * i)) D.n

/-- The left child evaluates the original polynomial at even-numbered domain points. -/
theorem dftValue_split_left [Field R] (D : NTT.Domain R) (hlog : 0 < D.logN)
    (a : Array R) (k : Nat) :
    dftValue (halfDomain D hlog) (splitFieldsLeft D a) k = dftValue D a (2 * k) := by
  have hn := halfDomain_size D hlog
  have hp (i : Nat) : D.omega ^ (2 * k * ((halfDomain D hlog).n + i)) =
      D.omega ^ (2 * k * i) := by
    have he : 2 * k * ((halfDomain D hlog).n + i) = 2 * k * i + D.n * k := by
      rw [hn]
      ring
    rw [he, Plan.omega_pow_add_domain_mul]
  unfold dftValue
  conv_rhs => rw [hn, two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < 2 ^ (D.logN - 1) := Finset.mem_range.mp hi
  simp only [splitFieldsLeft]
  rw [getD_ofFn_bounded _ i hi' 0]
  change (a.getD i 0 + a.getD (i + (halfDomain D hlog).n) 0) * (D.omega ^ 2) ^ (k * i) = _
  rw [← pow_mul, hp]
  have he : 2 * (k * i) = 2 * k * i := by ring
  rw [he]
  have hc : (halfDomain D hlog).n + i = i + (halfDomain D hlog).n := Nat.add_comm _ _
  rw [hc]
  ring

/-- The right child evaluates the original polynomial at odd-numbered domain points. -/
theorem dftValue_split_right [Field R] (D : NTT.Domain R) (hlog : 0 < D.logN)
    (a : Array R) (k : Nat) :
    dftValue (halfDomain D hlog) (splitFieldsRight D a) k = dftValue D a (2 * k + 1) := by
  have hn := halfDomain_size D hlog
  have hhalf : D.n / 2 = (halfDomain D hlog).n := by omega
  have hp (i : Nat) : D.omega ^ ((2 * k + 1) * ((halfDomain D hlog).n + i)) =
      -D.omega ^ ((2 * k + 1) * i) := by
    have he : (2 * k + 1) * ((halfDomain D hlog).n + i) =
        (halfDomain D hlog).n + (2 * k + 1) * i + D.n * k := by
      rw [hn]
      ring
    rw [he, Plan.omega_pow_add_domain_mul, pow_add,
      ← hhalf, Plan.omega_pow_domain_half_eq_neg_one D hlog]
    ring
  unfold dftValue
  conv_rhs => rw [hn, two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < 2 ^ (D.logN - 1) := Finset.mem_range.mp hi
  simp only [splitFieldsRight]
  rw [getD_ofFn_bounded _ i hi' 0]
  change (D.omega ^ i * (a.getD i 0 - a.getD (i + (halfDomain D hlog).n) 0)) *
    (D.omega ^ 2) ^ (k * i) = _
  rw [hp, ← pow_mul]
  have he : (2 * k + 1) * i = i + 2 * (k * i) := by ring
  rw [he, pow_add, Nat.add_comm (halfDomain D hlog).n i]
  ring

end CompPoly.CPolynomial.NTTFast.Packed
