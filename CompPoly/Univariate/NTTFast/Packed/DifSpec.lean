/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Correctness.DIF
import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas
public import CompPoly.Univariate.NTTFast.Packed.Decoder
import Mathlib.Tactic.Ring

/-! # The bit-reversed DFT

`difSpec` is the output of a DIF transform: the DFT in bit-reversed order. The radix-four plan
computes it, and its natural-order read `decodedFields` is the DFT, scaled for an inverse
transform.
-/

@[expose] public section
open scoped BigOperators
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- The DFT formula with a natural-number evaluation index. -/
def dftValue [Field R] (D : NTT.Domain R) (a : Array R) (k : Nat) : R :=
  ∑ i ∈ Finset.range D.n, a.getD i 0 * D.omega ^ (k * i)

/-- Natural-number and bounded-index DFT formulas have the same sum. -/
theorem dftValue_eq_nttAt [Field R] (D : NTT.Domain R) (a : Array R) (k : D.Idx) :
    dftValue D a k.val = NTT.Forward.nttAt D a k := by
  symm
  exact Fin.sum_univ_eq_sum_range (fun i ↦ a.getD i 0 * D.omega ^ (k.val * i)) D.n

/-- The ordinary bit-reversed mathematical forward output. -/
def difSpec [Field R] (D : NTT.Domain R) (a : Array R) : Array R :=
  NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D a)

/-- The mathematical DIF output has one value per domain point. -/
@[simp] theorem size_difSpec [Field R] (D : NTT.Domain R) (a : Array R) :
    (difSpec D a).size = D.n := by
  simp only [difSpec, NTT.Transform.bitRevPermute, Array.size_ofFn]

/-- Reading a bounded DIF output evaluates the DFT at the reversed index. -/
theorem getD_difSpec [Field R] (D : NTT.Domain R) (a : Array R) (i : Nat) (hi : i < D.n) :
    (difSpec D a).getD i 0 = dftValue D a (NTT.Transform.bitRevNat D.logN i) := by
  have hb : NTT.Transform.bitRevNat D.logN i < D.n := NTT.Transform.bitRevNat_lt _ _
  simp only [difSpec, NTT.Transform.bitRevPermute]
  rw [getD_ofFn_bounded _ i hi 0]
  simp only [NTT.Forward.forwardSpec]
  rw [getD_ofFn_bounded _ _ hb 0]
  exact (dftValue_eq_nttAt D a ⟨_, hb⟩).symm

/-- An already domain-sized array is unchanged by zero-padding. -/
theorem loadNaturalArray_eq_self [Field R] (D : NTT.Domain R) (a : Array R)
    (hs : a.size = D.n) : NTT.loadNaturalArray D a = a := by
  apply Array.ext (by rw [NTT.size_loadNaturalArray, hs])
  intro i hi hj
  rw [NTT.getElem_loadNaturalArray]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]

/-- The ordinary radix-four pipeline computes the mathematical bit-reversed DFT. -/
theorem planStages_eq_difSpec [Field R] (D : NTT.Domain R) (a : Array R) (hs : a.size = D.n) :
    Plan.runStagesDIFRadix4WithTwiddles D (Plan.twiddleTable D) a = difSpec D a := by
  have h := Plan.runStagesDIFRadix4WithTwiddles_correct D a
  rw [loadNaturalArray_eq_self D a hs] at h
  exact h

/-- Decoding an unnormalized DIF result restores natural-order DFT evaluations. -/
theorem decodedFields_difSpec (D : NTT.Domain KoalaBear.Fast.Field)
    (a : Array KoalaBear.Fast.Field) (factor : KoalaBear.Fast.Field) (inverse : Bool) :
    decodedFields D.logN (difSpec D a) factor inverse =
      if inverse then (NTT.Forward.forwardSpec D a).map (fun x ↦ factor * x)
      else NTT.Forward.forwardSpec D a := by
  cases inverse <;>
    simp only [decodedFields, Bool.false_eq_true, ite_false, ite_true,
      NTT.Forward.forwardSpec, Array.map_ofFn]
  all_goals
    apply congrArg Array.ofFn
    funext i
    rw [getD_difSpec D a _ (NTT.Transform.bitRevNat_lt _ _),
      NTT.Transform.bitRevNat_involutive D.logN i.val i.isLt, dftValue_eq_nttAt D a i] <;> rfl

/-- The domain of `2 ^ k`-th powers of the root, `2 ^ k` times smaller. -/
def powDomain [Field R] (D : NTT.Domain R) (k : Nat) (hk : k ≤ D.logN) : NTT.Domain R where
  logN := D.logN - k
  omega := D.omega ^ 2 ^ k
  primitive := by
    apply IsPrimitiveRoot.pow D.n_pos D.primitive
    change 2 ^ D.logN = 2 ^ k * 2 ^ (D.logN - k)
    rw [← Nat.pow_add, Nat.add_sub_cancel' hk]

end CompPoly.CPolynomial.NTTFast.Packed
