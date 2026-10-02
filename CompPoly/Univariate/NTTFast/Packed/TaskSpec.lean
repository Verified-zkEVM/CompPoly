/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.SplitCorrectness

/-! # Parallel packed task-tree correctness -/

@[expose] public section
open scoped BigOperators
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- The mathematical bit-reversed transform with optional global normalization. -/
def normalizedDifSpec [Field R] (D : NTT.Domain R) (a : Array R) (factor : R)
    (normalize : Bool) : Array R :=
  if normalize then (difSpec D a).map (fun x ↦ factor * x) else difSpec D a

/-- Child normalization uses the original transform's factor, so concatenation preserves it. -/
theorem normalizedDifSpec_split [Field R] (D : NTT.Domain R) (hlog : 0 < D.logN)
    (a : Array R) (factor : R) (normalize : Bool) :
    normalizedDifSpec (halfDomain D hlog) (splitFieldsLeft D a) factor normalize ++
      normalizedDifSpec (halfDomain D hlog) (splitFieldsRight D a) factor normalize =
      normalizedDifSpec D a factor normalize := by
  cases normalize with
  | false => exact difSpec_split D hlog a
  | true =>
    simp only [normalizedDifSpec, ite_true, ← Array.map_append, difSpec_split]

/-- A singleton domain's DFT is its already-sized input. -/
theorem difSpec_log_zero [Field R] (D : NTT.Domain R) (a : Array R)
    (hz : D.logN = 0) (hs : a.size = D.n) : difSpec D a = a := by
  apply Array.ext (by rw [size_difSpec, hs])
  intro i hi hj
  have hik : i < D.n := by simpa only [size_difSpec] using hi
  have he : i = 0 := by simp only [NTT.Domain.n, hz, pow_zero] at hik; omega
  subst i
  have hv := getD_difSpec D a 0 hik
  simp only [hz, NTT.Transform.bitRevNat, dftValue, NTT.Domain.n, pow_zero,
    Nat.zero_mul, Finset.range_one, Finset.sum_singleton, MulOneClass.mul_one] at hv
  simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
    Array.getElem?_eq_getElem hj, Option.getD_some] using hv

/-- When normalization is fused, every actual task leaf has four final layers. -/
def ValidLeafNormalization (logN depth : Nat) (normalize : Bool) : Prop :=
  normalize = true → 4 ≤ logN - depth ∧ (logN - depth) % 2 = 0

/-- The recursive packed task tree computes the mathematical DIF output at every split depth. -/
theorem Native.splitTask_correct (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (factor : KoalaBear.Fast.Field) (normalize : Bool) (depth : Nat)
    (ht : TwiddlesFor D tw) (hs : a.size = D.n) (hu : 4 * D.n < USize.size)
    (hn : ValidLeafNormalization D.logN depth normalize) :
    (Native.splitTask (tw.map packFields) D.logN (packFields a) factor.val normalize depth).get =
      packFields (normalizedDifSpec D a factor normalize) := by
  induction depth generalizing D a with
  | zero =>
    simp only [Native.splitTask, Task.spawn]
    exact Native.stages_difSpec D tw a factor normalize ht hs hu
      (by intro h; simpa only [Nat.sub_zero] using hn h)
  | succ depth ih =>
    rw [Native.splitTask]
    split
    · rename_i hz
      have hnorm : normalize = false := by
        cases normalize with
        | false => rfl
        | true => have h := (hn rfl).1; omega
      simp only [hnorm, normalizedDifSpec, Bool.false_eq_true, ite_false,
        difSpec_log_zero D a hz hs]
    · rename_i hz
      have hlog : 0 < D.logN := by omega
      simp only [Task.bind, Task.map, Task.spawn]
      rw [Native.splitLeft_correct D hlog tw a ht hs hu,
        Native.splitRight_correct D hlog tw a ht hs hu]
      have ht' := TwiddlesFor.half D hlog tw ht
      have hu' : 4 * (halfDomain D hlog).n < USize.size := by
        have hh := halfDomain_size D hlog
        omega
      have hn' : ValidLeafNormalization (halfDomain D hlog).logN depth normalize := by
        intro h
        have he : (halfDomain D hlog).logN - depth = D.logN - (depth + 1) := by
          change D.logN - 1 - depth = D.logN - (depth + 1)
          omega
        rw [he]
        exact hn h
      have hl : (splitFieldsLeft D a).size = (halfDomain D hlog).n := Array.size_ofFn
      have hr : (splitFieldsRight D a).size = (halfDomain D hlog).n := Array.size_ofFn
      change (Native.splitTask _ (halfDomain D hlog).logN _ _ _ depth).get ++
        (Native.splitTask _ (halfDomain D hlog).logN _ _ _ depth).get = _
      rw [ih (halfDomain D hlog) (splitFieldsLeft D a) ht' hl hu' hn',
        ih (halfDomain D hlog) (splitFieldsRight D a) ht' hr hu' hn',
        ← packFields_append, normalizedDifSpec_split]

/-- Fusing input conversion into the first task split preserves the complete mathematical output. -/
theorem Native.splitInputTask_correct (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (factor : KoalaBear.Fast.Field) (normalize : Bool) (depth : Nat)
    (ht : TwiddlesFor D tw) (hs : a.size = D.n) (hu : 4 * D.n < USize.size)
    (hn : ValidLeafNormalization D.logN depth normalize) :
    (Native.splitInputTask (tw.map packFields) D.logN a factor.val normalize depth).get =
      packFields (normalizedDifSpec D a factor normalize) := by
  rw [Native.splitInputTask]
  split
  · rw [Native.encode_eq]
    exact Native.splitTask_correct D tw a factor normalize depth ht hs hu hn
  · rename_i hsplit
    have hdepth : 0 < depth := by omega
    have hlog : 0 < D.logN := by omega
    simp only [Task.bind, Task.map, Task.spawn]
    rw [Native.splitInputLeft_correct D hlog tw a ht hs hu,
      Native.splitInputRight_correct D hlog tw a ht hs hu]
    have ht' := TwiddlesFor.half D hlog tw ht
    have hu' : 4 * (halfDomain D hlog).n < USize.size := by
      have hh := halfDomain_size D hlog
      omega
    have hn' : ValidLeafNormalization (halfDomain D hlog).logN (depth - 1) normalize := by
      intro h
      have he : (halfDomain D hlog).logN - (depth - 1) = D.logN - depth := by
        change D.logN - 1 - (depth - 1) = D.logN - depth
        omega
      rw [he]
      exact hn h
    have hl : (splitFieldsLeft D a).size = (halfDomain D hlog).n := Array.size_ofFn
    have hr : (splitFieldsRight D a).size = (halfDomain D hlog).n := Array.size_ofFn
    change (Native.splitTask _ (halfDomain D hlog).logN _ _ _ (depth - 1)).get ++
      (Native.splitTask _ (halfDomain D hlog).logN _ _ _ (depth - 1)).get = _
    rw [Native.splitTask_correct (halfDomain D hlog) tw (splitFieldsLeft D a)
      factor normalize (depth - 1) ht' hl hu' hn',
      Native.splitTask_correct (halfDomain D hlog) tw (splitFieldsRight D a)
      factor normalize (depth - 1) ht' hr hu' hn',
      ← packFields_append, normalizedDifSpec_split]

end CompPoly.CPolynomial.NTTFast.Packed
