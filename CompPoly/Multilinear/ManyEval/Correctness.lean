/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Multilinear.ManyEval.Basic

/-!
# Multilinear Many-Polynomial Evaluation Correctness

Correctness theorem statements for many-polynomial multilinear evaluation.
-/

namespace CompPoly
namespace CMlPolynomialEval

variable {R : Type*} {n : Nat}

private lemma array_foldl_push_toList {α : Type*} (xs acc : Array α) :
    (Array.foldl (fun acc x ↦ acc.push x) acc xs 0 xs.size).toList =
      acc.toList ++ xs.toList := by
  cases xs with
  | mk xs =>
      induction xs generalizing acc with
      | nil => simp
      | cons _ _ _ => simp

private lemma vector_array_foldl_push_toList (p : CMlPolynomialEval R n) (acc : Array R) :
    (Array.foldl (fun acc x ↦ acc.push x) acc p.toArray 0 (2 ^ n)).toList =
      acc.toList ++ p.toArray.toList := by
  convert array_foldl_push_toList p.toArray acc using 1
  simp

private lemma valuesByPolynomialListLoop_toList
    (polys : List (CMlPolynomialEval R n)) (acc : Array R) :
    (polys.foldl
        (fun values p ↦ Array.foldl (fun values value ↦ values.push value)
          values p.toArray 0 (2 ^ n))
        acc).toList =
      acc.toList ++ polys.flatMap (fun p ↦ p.toArray.toList) := by
  induction polys generalizing acc with
  | nil => simp
  | cons p polys ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih]
      rw [vector_array_foldl_push_toList]
      simp [List.append_assoc]

private lemma valuesByPolynomial_toList (polys : Array (CMlPolynomialEval R n)) :
    (valuesByPolynomial polys).toList =
      polys.toList.flatMap (fun p ↦ p.toArray.toList) := by
  cases polys with
  | mk polys =>
      simpa [valuesByPolynomial] using
        (valuesByPolynomialListLoop_toList (R := R) (n := n) polys #[])

private lemma array_getD_toList {α : Type*} (a : Array α) (i : Nat) (d : α) :
    a.getD i d = a.toList.getD i d := by
  cases a
  simp

private lemma List.getD_flatMap_fixed_length {α β : Type*} (xs : List α) (f : α → List β)
    (width : Nat) (d : β)
    (hwidth : ∀ a ∈ xs, (f a).length = width)
    {polyIdx j : Nat} (hpoly : polyIdx < xs.length) (hj : j < width) :
    (xs.flatMap f).getD (polyIdx * width + j) d =
      (f xs[polyIdx]).getD j d := by
  induction xs generalizing polyIdx with
  | nil => simp at hpoly
  | cons a xs ih =>
      cases polyIdx with
      | zero =>
          simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add]
          rw [List.getD_append]
          · simp
          · simpa using hj.trans_eq (hwidth a (by simp)).symm
      | succ polyIdx =>
          simp only [List.flatMap_cons]
          rw [List.getD_append_right]
          · have hwidth_a : (f a).length = width := hwidth a (by simp)
            rw [hwidth_a]
            have hpoly' : polyIdx < xs.length := by
              simpa using hpoly
            have hwidth' : ∀ b ∈ xs, (f b).length = width := by
              intro b hb
              exact hwidth b (by simp [hb])
            simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using ih hwidth' hpoly'
          · rw [hwidth a (by simp)]
            exact (Nat.le_mul_of_pos_left width (Nat.succ_pos polyIdx)).trans
              (Nat.le_add_right _ _)

private lemma valuesByPolynomial_getD [Zero R]
    (polys : Array (CMlPolynomialEval R n)) (polyIdx j : Nat)
    (hpoly : polyIdx < polys.size) (hj : j < 2 ^ n) :
    (valuesByPolynomial polys).getD (polyIdx * (2 ^ n) + j) 0 =
      polys[polyIdx].toArray.toList.getD j 0 := by
  rw [array_getD_toList]
  rw [valuesByPolynomial_toList]
  have hwidth : ∀ p ∈ polys.toList, (p.toArray.toList).length = 2 ^ n := by
    intro p _hp
    simp
  have hpolyList : polyIdx < polys.toList.length := by
    simpa using hpoly
  rw [List.getD_flatMap_fixed_length (xs := polys.toList)
    (f := fun p ↦ p.toArray.toList) (width := 2 ^ n) (d := (0 : R))
    (hwidth := hwidth) hpolyList hj]
  have hget : polys.toList[polyIdx] = polys[polyIdx] := by
    cases polys
    rfl
  rw [hget]

private lemma List.flatMap_singleton {α β : Type*} (xs : List α) (f : α → β) :
    xs.flatMap (fun x ↦ [f x]) = xs.map f := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp [ih]

private lemma List.flatMap_map {α β γ : Type*} (xs : List α) (f : α → β)
    (g : β → List γ) :
    (xs.map f).flatMap g = xs.flatMap (fun x ↦ g (f x)) := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp [ih]

private lemma vector_zero_toArray_toList (p : CMlPolynomialEval R 0) :
    p.toArray.toList = [p.get ⟨0, by norm_num⟩] := by
  apply List.ext_get
  · simp
  · intro i hLeft hRight
    have hRight' : i < 1 := by
      simpa using hRight
    have hi : i = 0 := by omega
    subst i
    rfl

private lemma foldLayeredPolyLoop_valuesByPolynomial_toList [CommRing R]
    (polys : Array (CMlPolynomialEval R (n + 1))) (r : R)
    (polyIdx pairIdx : Nat) (acc : Array R) (hpoly : polyIdx < polys.size) :
    (foldLayeredPolyLoop (valuesByPolynomial polys) (2 ^ (n + 1)) (2 ^ n)
      (1 - r) r polyIdx pairIdx acc).toList =
      acc.toList ++ (evalMleLayer polys[polyIdx] r).toArray.toList.drop pairIdx := by
  fun_induction foldLayeredPolyLoop (valuesByPolynomial polys) (2 ^ (n + 1)) (2 ^ n)
      (1 - r) r polyIdx pairIdx acc with
  | case1 pairIdx acc h base value ih =>
      rw [ih]
      have hdrop :
          (evalMleLayer polys[polyIdx] r).toArray.toList.drop pairIdx =
            value :: (evalMleLayer polys[polyIdx] r).toArray.toList.drop (pairIdx + 1) := by
        have hiList : pairIdx < (evalMleLayer polys[polyIdx] r).toArray.toList.length := by
          simpa using h
        rw [List.drop_eq_getElem_cons hiList]
        have hEven : 2 * pairIdx < 2 ^ (n + 1) := by
          rw [pow_succ]
          omega
        have hOdd : 2 * pairIdx + 1 < 2 ^ (n + 1) := by
          rw [pow_succ]
          omega
        have hLeft :
            (valuesByPolynomial polys).getD (polyIdx * 2 ^ (n + 1) + 2 * pairIdx) 0 =
              polys[polyIdx].toArray.toList.getD (2 * pairIdx) 0 :=
          valuesByPolynomial_getD polys polyIdx (2 * pairIdx) hpoly hEven
        have hRight :
            (valuesByPolynomial polys).getD (polyIdx * 2 ^ (n + 1) + (2 * pairIdx + 1)) 0 =
              polys[polyIdx].toArray.toList.getD (2 * pairIdx + 1) 0 :=
          valuesByPolynomial_getD polys polyIdx (2 * pairIdx + 1) hpoly hOdd
        have hLeftGet :
            polys[polyIdx].toArray.toList.getD (2 * pairIdx) 0 =
              polys[polyIdx].get ⟨2 * pairIdx, hEven⟩ := by
          rw [List.getD_eq_getElem]
          rfl
        have hRightGet :
            polys[polyIdx].toArray.toList.getD (2 * pairIdx + 1) 0 =
              polys[polyIdx].get ⟨2 * pairIdx + 1, hOdd⟩ := by
          rw [List.getD_eq_getElem]
          rfl
        congr
        have hRightBase : base + 1 = polyIdx * 2 ^ (n + 1) + (2 * pairIdx + 1) := by
          omega
        change (evalMleLayer polys[polyIdx] r).get ⟨pairIdx, h⟩ = _
        simp [value, base, hRightBase, hLeft, hRight, hEven, hOdd]
        rfl
      simp [Array.toList_push, hdrop, List.append_assoc]
  | case2 pairIdx acc h =>
      rw [List.drop_eq_nil_of_le]
      · simp
      · simpa using Nat.le_of_not_gt h

private lemma foldLayeredLayerLoop_valuesByPolynomial_toList [CommRing R]
    (polys : Array (CMlPolynomialEval R (n + 1))) (r : R)
    (polyIdx : Nat) (acc : Array R) :
    (foldLayeredLayerLoop (valuesByPolynomial polys) (2 ^ (n + 1)) (2 ^ n) polys.size
      (1 - r) r polyIdx acc).toList =
      acc.toList ++ (polys.toList.drop polyIdx).flatMap
        (fun p ↦ (evalMleLayer p r).toArray.toList) := by
  fun_induction foldLayeredLayerLoop (valuesByPolynomial polys) (2 ^ (n + 1)) (2 ^ n)
      polys.size (1 - r) r polyIdx acc with
  | case1 polyIdx acc h next ih =>
      rw [ih]
      change
        (foldLayeredPolyLoop (valuesByPolynomial polys) (2 ^ (n + 1)) (2 ^ n)
            (1 - r) r polyIdx 0 acc).toList ++
            (polys.toList.drop (polyIdx + 1)).flatMap
              (fun p ↦ (evalMleLayer p r).toArray.toList) =
          acc.toList ++ (polys.toList.drop polyIdx).flatMap
            (fun p ↦ (evalMleLayer p r).toArray.toList)
      rw [foldLayeredPolyLoop_valuesByPolynomial_toList (polys := polys) (r := r)
        (polyIdx := polyIdx) (pairIdx := 0) (acc := acc) h]
      have hdrop :
          (polys.toList.drop polyIdx).flatMap
              (fun p ↦ (evalMleLayer p r).toArray.toList) =
            (evalMleLayer polys[polyIdx] r).toArray.toList ++
              (polys.toList.drop (polyIdx + 1)).flatMap
                (fun p ↦ (evalMleLayer p r).toArray.toList) := by
        have hiList : polyIdx < polys.toList.length := by
          simpa using h
        rw [List.drop_eq_getElem_cons hiList]
        have hget : polys.toList[polyIdx] = polys[polyIdx] := by
          cases polys
          rfl
        simp [hget]
      simp [hdrop, List.append_assoc]
  | case2 polyIdx acc h =>
      rw [List.drop_eq_nil_of_le]
      · simp
      · simpa using Nat.le_of_not_gt h

private lemma evalManyMleLoop_toList [CommRing R]
    (polys : Array (CMlPolynomialEval R n)) (x : Vector R n) (i : Nat) (acc : Array R) :
    (evalManyMleLoop polys x i acc).toList =
      acc.toList ++ (polys.toList.drop i).map (fun p ↦ evalMle p x) := by
  fun_induction evalManyMleLoop polys x i acc with
  | case1 i acc h p ih =>
      rw [ih]
      have hdrop :
          (polys.toList.drop i).map (fun p ↦ evalMle p x) =
            p.evalMle x :: (polys.toList.drop (i + 1)).map (fun p ↦ evalMle p x) := by
        have hiList : i < polys.toList.length := by
          simpa using h
        rw [List.drop_eq_getElem_cons hiList]
        have hget : polys.toList[i] = p := by
          cases polys
          rfl
        simp [hget]
      simp [Array.toList_push, hdrop, List.append_assoc]
  | case2 i acc h =>
      rw [List.drop_eq_nil_of_le]
      · simp
      · simpa using Nat.le_of_not_gt h

/-- Iterated many-MLE evaluation agrees with scalar `evalMle` on each table. -/
theorem evalManyMle_eq_map_evalMle [CommRing R]
    (polys : Array (CMlPolynomialEval R n)) (x : Vector R n) :
    evalManyMle polys x = polys.map (fun p ↦ evalMle p x) := by
  apply Array.toList_inj.mp
  simp [evalManyMle, evalManyMleLoop_toList]

/-- Layer-by-layer many-MLE evaluation agrees with scalar `evalMle` on each table. -/
theorem evalManyMleByLayers_eq_map_evalMle [CommRing R]
    (polys : Array (CMlPolynomialEval R n)) (x : Vector R n) :
    evalManyMleByLayers polys x = polys.map (fun p ↦ evalMle p x) := by
  induction n with
  | zero =>
      apply Array.toList_inj.mp
      simp [evalManyMleByLayers, evalManyMleByLayersLoop, valuesByPolynomial_toList,
        vector_zero_toArray_toList, List.flatMap_singleton]
  | succ n ih =>
      simp [evalManyMleByLayers, evalManyMleByLayersLoop]
      have hWidth : 2 ^ (n + 1) / 2 = 2 ^ n := by
        rw [pow_succ]
        rw [Nat.mul_comm]
        exact Nat.mul_div_right _ (by norm_num : 0 < 2)
      rw [hWidth]
      have hfirst :
          foldLayeredLayerLoop (valuesByPolynomial polys) (2 ^ (n + 1)) (2 ^ n)
              polys.size (1 - x.head) x.head 0 #[] =
            valuesByPolynomial (polys.map (fun p ↦ evalMleLayer p x.head)) := by
        apply Array.toList_inj.mp
        rw [foldLayeredLayerLoop_valuesByPolynomial_toList]
        simp [valuesByPolynomial_toList, List.flatMap_map]
      rw [hfirst]
      simpa [evalManyMleByLayers, List.flatMap_map] using
        ih (polys.map (fun p ↦ evalMleLayer p x.head)) x.tail

/-- Layer-by-layer many-MLE evaluation agrees with iterated many-MLE evaluation. -/
theorem evalManyMleByLayers_eq_evalManyMle [CommRing R]
    (polys : Array (CMlPolynomialEval R n)) (x : Vector R n) :
    evalManyMleByLayers polys x = evalManyMle polys x := by
  rw [evalManyMleByLayers_eq_map_evalMle, evalManyMle_eq_map_evalMle]

end CMlPolynomialEval
end CompPoly
