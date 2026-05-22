/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.ManyEval.Basic

/-!
# Many-Polynomial Evaluation Correctness

Correctness theorem statements for many-polynomial evaluation backends.
-/

namespace CompPoly
namespace CPolynomial

variable {R : Type*}

private lemma le_foldl_max_size [Zero R] (polys : List (CPolynomial R)) (acc : Nat) :
    acc ≤ polys.foldl (fun acc p ↦ Nat.max acc p.size) acc := by
  induction polys generalizing acc with
  | nil => simp
  | cons p polys ih =>
      exact (Nat.le_max_left acc p.size).trans (ih (Nat.max acc p.size))

private lemma size_le_foldl_max_size_of_mem [Zero R]
    (polys : List (CPolynomial R)) (acc : Nat) {p : CPolynomial R} (hp : p ∈ polys) :
    p.size ≤ polys.foldl (fun acc p ↦ Nat.max acc p.size) acc := by
  induction polys generalizing acc with
  | nil => simp at hp
  | cons q polys ih =>
      simp only [List.mem_cons] at hp
      simp only [List.foldl_cons]
      rcases hp with hp | hp
      · subst p
        exact (Nat.le_max_right acc q.size).trans
          (le_foldl_max_size polys (Nat.max acc q.size))
      · exact ih (Nat.max acc q.size) hp

private lemma size_le_maxCoeffSize_of_mem [Zero R]
    (polys : Array (CPolynomial R)) {p : CPolynomial R} (hp : p ∈ polys.toList) :
    p.size ≤ ManyEval.maxCoeffSize polys := by
  cases polys with
  | mk ps =>
      simpa [ManyEval.maxCoeffSize] using
        size_le_foldl_max_size_of_mem (R := R) ps 0 hp

private theorem foldl_push_size [Mul R] (x : R) :
    ∀ xs : List Nat, ∀ (powers : Array R) (pow : R),
      (List.foldl (fun (b : Array R × R) (_ : Nat) ↦ (b.1.push b.2, b.2 * x))
        (powers, pow) xs).1.size = powers.size + xs.length
  | [], powers, _ => by simp
  | _ :: xs, powers, pow => by
      simp [foldl_push_size x xs (powers.push pow) (pow * x), Nat.add_comm,
        Nat.add_left_comm]

private theorem foldl_push_getD [Semiring R] (x : R) :
    ∀ xs : List Nat, ∀ (powers : Array R) (pow base : R) (offset : Nat),
      powers.size = offset →
      (∀ i, i < offset → powers.getD i 0 = base * x ^ i) →
      pow = base * x ^ offset →
      ∀ i, i < offset + xs.length →
        (List.foldl (fun (b : Array R × R) (_ : Nat) ↦ (b.1.push b.2, b.2 * x))
          (powers, pow) xs).1.getD i 0 = base * x ^ i
  | [], powers, _pow, _base, _offset, _hsize, hvals, _hpow, i, hi => by
      exact hvals i (by simpa using hi)
  | _ :: xs, powers, pow, base, offset, hsize, hvals, hpow, i, hi => by
      apply foldl_push_getD x xs (powers.push pow) (pow * x) base (offset + 1)
      · simp [hsize]
      · intro k hk
        by_cases hk0 : k < offset
        · have hkSize : k < powers.size := by simpa [hsize] using hk0
          rw [← hvals k hk0]
          simp [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hkSize,
            Array.getElem?_eq_getElem hkSize]
        · have hkEq : k = offset := by omega
          subst hkEq
          rw [Array.getD_eq_getD_getElem?]
          rw [← hsize, Array.getElem?_push_size]
          simpa [hsize] using hpow
      · rw [hpow]
        rw [pow_succ]
        exact _root_.mul_assoc base (x ^ offset) x
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

private lemma powerTableLoop_eq_foldl [Mul R] (x : R) (limit i : Nat) (pow : R)
    (acc : Array R) :
    ManyEval.powerTableLoop x limit i pow acc =
      (List.foldl (fun (b : Array R × R) (_ : Nat) ↦ (b.1.push b.2, b.2 * x))
        (acc, pow) (List.range' i (limit - i))).1 := by
  fun_induction ManyEval.powerTableLoop x limit i pow acc with
  | case1 i pow acc h ih =>
      rw [ih]
      have hsub : limit - i = (limit - (i + 1)) + 1 := by omega
      simp [hsub, List.range'_succ]
  | case2 i pow acc h =>
      have hsub : limit - i = 0 := by omega
      simp [hsub]

private lemma powerTable_size [Semiring R] (x : R) (limit : Nat) :
    (ManyEval.powerTable x limit).size = limit := by
  unfold ManyEval.powerTable
  rw [powerTableLoop_eq_foldl]
  simpa using foldl_push_size x (List.range' 0 limit) (#[] : Array R) (1 : R)

private lemma powerTable_getD_eq_pow [Semiring R] (x : R) {limit i : Nat}
    (hi : i < limit) :
    (ManyEval.powerTable x limit).getD i 0 = x ^ i := by
  unfold ManyEval.powerTable
  rw [powerTableLoop_eq_foldl]
  have h := foldl_push_getD x (List.range' 0 limit) (#[] : Array R) (1 : R) (1 : R) 0
    (by simp) (by intro i hi; omega) (by simp) i (by simpa using hi)
  simpa using h

private lemma list_foldl_congr {α β : Type*} {f g : α → β → α}
    (xs : List β) (acc : α) (h : ∀ acc' x, x ∈ xs → f acc' x = g acc' x) :
    xs.foldl f acc = xs.foldl g acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h acc x (by simp)]
      apply ih
      intro acc' y hy
      exact h acc' y (by simp [hy])

private lemma evalWithPowersLoop_eq_foldl_range [Semiring R]
    (coeffs powers : Array R) (limit : Nat) (hcoeffs : limit ≤ coeffs.size)
    (hpowers : limit ≤ powers.size) (i : Nat) (acc : R) :
    ManyEval.evalWithPowersLoop coeffs powers limit hcoeffs hpowers i acc =
      List.foldl (fun acc j ↦ acc + coeffs.getD j 0 * powers.getD j 0) acc
        (List.range' i (limit - i)) := by
  fun_induction ManyEval.evalWithPowersLoop coeffs powers limit hcoeffs hpowers i acc with
  | case1 i acc h coeff pow ih =>
      subst coeff
      subst pow
      rw [ih]
      have hsub : limit - i = (limit - (i + 1)) + 1 := by omega
      rw [hsub, List.range'_succ]
      have hci : coeffs[i] = coeffs.getD i 0 := by
        simp [Array.getD]
        omega
      have hpi : powers[i] = powers.getD i 0 := by
        simp [Array.getD]
        omega
      simp [List.foldl_cons, hci, hpi]
  | case2 i acc h =>
      have hsub : limit - i = 0 := by omega
      simp [hsub]

private lemma foldl_zipIdx_eq_range'_getD_aux [Semiring R]
    (xs : List R) (x acc : R) (offset : Nat) :
    List.foldl (fun acc ai ↦ acc + ai.1 * x ^ ai.2) acc (xs.zipIdx offset) =
      List.foldl (fun acc i ↦ acc + xs.getD (i - offset) 0 * x ^ i) acc
        (List.range' offset xs.length) := by
  induction xs generalizing offset acc with
  | nil => simp
  | cons a xs ih =>
      simp only [List.zipIdx_cons, List.foldl_cons, List.length_cons]
      rw [List.range'_succ, List.foldl_cons]
      simp only [Nat.sub_self, List.getD_cons_zero]
      rw [ih]
      apply list_foldl_congr
      intro _acc' j hj
      have hsub : j - offset = (j - (offset + 1)) + 1 := by
        have hjmem := List.mem_range'.mp hj
        omega
      simp [hsub]

private lemma array_getD_toList {α : Type*} (a : Array α) (i : Nat) (d : α) :
    a.getD i d = a.toList.getD i d := by
  cases a
  simp

private lemma array_foldl_zipIdx_eq_list [Semiring R] (coeffs : Array R) (x acc : R) :
    Array.foldl (fun acc ai ↦ acc + ai.1 * x ^ ai.2) acc coeffs.zipIdx 0 coeffs.size =
      List.foldl (fun acc ai ↦ acc + ai.1 * x ^ ai.2) acc coeffs.toList.zipIdx := by
  cases coeffs
  simp

private lemma evalWithPowers_eq_eval [Semiring R] (coeffs powers : Array R) (x : R)
    (hsize : coeffs.size ≤ powers.size)
    (hpowers : ∀ i, i < coeffs.size → powers.getD i 0 = x ^ i) :
    ManyEval.evalWithPowers coeffs powers =
      coeffs.zipIdx.foldl (fun acc ai ↦ acc + ai.1 * x ^ ai.2) 0 := by
  simp [ManyEval.evalWithPowers, Nat.min_eq_left hsize]
  rw [evalWithPowersLoop_eq_foldl_range]
  rw [array_foldl_zipIdx_eq_list]
  rw [foldl_zipIdx_eq_range'_getD_aux]
  apply list_foldl_congr
  intro _acc' i hi
  rw [← array_getD_toList]
  rw [hpowers i]
  · simp
  · rcases List.mem_range'.mp hi with ⟨j, hj, rfl⟩
    simpa using hj

private lemma evalManyWithPowersLoop_toList [Semiring R]
    (polys : Array (CPolynomial R)) (powers : Array R) (i : Nat) (acc : Array R) :
    (ManyEval.evalManyWithPowersLoop polys powers i acc).toList =
      acc.toList ++ (polys.toList.drop i).map
        (fun p ↦ ManyEval.evalWithPowers p.val powers) := by
  fun_induction ManyEval.evalManyWithPowersLoop polys powers i acc with
  | case1 i acc h p ih =>
      rw [ih]
      have hdrop :
          (polys.toList.drop i).map (fun p ↦ ManyEval.evalWithPowers p.val powers) =
            ManyEval.evalWithPowers p.val powers ::
              (polys.toList.drop (i + 1)).map
                (fun p ↦ ManyEval.evalWithPowers p.val powers) := by
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

/-- Many-polynomial Horner evaluation agrees with scalar evaluation. -/
theorem evalManyHorner_eq_map_eval [Semiring R]
    (polys : Array (CPolynomial R)) (x : R) :
    evalManyHorner polys x = polys.map (fun p ↦ p.eval x) := by
  simp [evalManyHorner, eval_horner_eq_eval]

/-- Shared-powers evaluation agrees with scalar evaluation. -/
theorem evalManySharedPowers_eq_map_eval [Semiring R]
    (polys : Array (CPolynomial R)) (x : R) :
    evalManySharedPowers polys x = polys.map (fun p ↦ p.eval x) := by
  apply Array.toList_inj.mp
  simp only [evalManySharedPowers, evalManyWithPowersLoop_toList, Array.toList_map,
    List.drop_zero, List.nil_append]
  apply List.map_congr_left
  intro p hp
  simp only [eval]
  apply evalWithPowers_eq_eval
  · rw [powerTable_size]
    simpa [size] using size_le_maxCoeffSize_of_mem polys hp
  · intro i hi
    apply powerTable_getD_eq_pow
    exact hi.trans_le (by simpa [size] using size_le_maxCoeffSize_of_mem polys hp)

end CPolynomial
end CompPoly
