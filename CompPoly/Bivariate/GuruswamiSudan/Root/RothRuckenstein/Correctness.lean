/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Lemmas

/-!
# Roth-Ruckenstein Root Correctness

Correctness statements for the Roth-Ruckenstein root backend.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Soundness of Roth-Ruckenstein root filtering. -/
theorem rothRuckensteinRootsYDegreeLt_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F} {Q : CBivariate F} {k : Nat}
    {p : CPolynomial F}
    (h : p ∈ (rothRuckensteinRootsYDegreeLt fieldRoots Q k).toList) :
    degreeLt p k ∧ CBivariate.composeY Q p = 0 := by
  unfold rothRuckensteinRootsYDegreeLt transformedRothRuckensteinRootsYDegreeLt at h
  simp [isRootYDegreeLtBool] at h
  exact ⟨degreeLt_of_degreeLtBool h.2.1, composeY_of_composeYHorner_eq_zero h.2.2⟩

/-- Normalizing a nonzero bivariate polynomial exposes a nonzero initial
coefficient equation for the residual-transform RR step. -/
theorem initialCoefficientPolynomial_stripXAdicFactor_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} (hQ : Q ≠ 0) :
    initialCoefficientPolynomial (CBivariate.stripXAdicFactor Q) ≠ 0 := by
  intro hzero
  cases horder : CBivariate.xAdicOrder? Q with
  | none =>
      exact hQ (cbivar_xAdicOrder?_none_eq_zero horder)
  | some order =>
      rcases cbivar_xAdicOrder?_some_exists horder with ⟨y, hy, hcoeff⟩
      have hstripCoeffNe :
          CBivariate.coeff (CBivariate.divXPower Q order) 0 y ≠ 0 := by
        rw [cbivar_coeff_divXPower]
        simpa using hcoeff
      have hyStrip : y < (CBivariate.divXPower Q order).val.size := by
        by_contra hnot
        exact hstripCoeffNe
          (cbivar_coeff_eq_zero_of_y_size_le
            (CBivariate.divXPower Q order) (i := 0) (j := y) (Nat.le_of_not_lt hnot))
      have hcoeffInitial : (initialCoefficientPolynomial Q.stripXAdicFactor).coeff y = 0 := by
        rw [hzero]
        exact CPolynomial.coeff_zero y
      rw [initialCoefficientPolynomial_coeff_of_lt] at hcoeffInitial
      · rw [CBivariate.stripXAdicFactor, horder, cbivar_coeff_divXPower] at hcoeffInitial
        exact hcoeff (by simpa using hcoeffInitial)
      · simpa [CBivariate.stripXAdicFactor, horder] using hyStrip

private theorem stripXAdicFactor_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {Q : CBivariate F} (hQ : Q ≠ 0) :
    CBivariate.stripXAdicFactor Q ≠ 0 := by
  intro hzero
  cases horder : CBivariate.xAdicOrder? Q with
  | none =>
      exact hQ (cbivar_xAdicOrder?_none_eq_zero horder)
  | some order =>
      rcases cbivar_xAdicOrder?_some_exists horder with ⟨y, hy, hcoeff⟩
      have hcoeffStrip : CBivariate.coeff Q.stripXAdicFactor 0 y = 0 := by
        rw [hzero]
        exact CPolynomial.coeff_zero 0
      rw [CBivariate.stripXAdicFactor, horder, cbivar_coeff_divXPower] at hcoeffStrip
      exact hcoeff (by simpa using hcoeffStrip)

private theorem composeY_stripXAdicFactor_eq_zero_of_composeY {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {p : CPolynomial F}
    (hQ : Q ≠ 0) (hroot : CBivariate.composeY Q p = 0) :
    CBivariate.composeY Q.stripXAdicFactor p = 0 := by
  cases horder : CBivariate.xAdicOrder? Q with
  | none =>
      exact (hQ (cbivar_xAdicOrder?_none_eq_zero horder)).elim
  | some order =>
      apply (CPolynomial.toPoly_eq_zero_iff
        (CBivariate.composeY Q.stripXAdicFactor p)).mp
      rw [composeY_toPoly]
      rw [CBivariate.stripXAdicFactor, horder]
      have hrootPoly : (CBivariate.toPoly Q).eval p.toPoly = 0 := by
        rw [← composeY_toPoly Q p, hroot]
        exact CPolynomial.toPoly_zero
      have hfactor :=
        cbivar_toPoly_eq_C_X_pow_mul_divXPower_of_xAdicOrder (Q := Q) horder
      rw [hfactor] at hrootPoly
      rw [Polynomial.eval_mul, Polynomial.eval_C] at hrootPoly
      have hx : (Polynomial.X ^ order : Polynomial F) ≠ 0 :=
        pow_ne_zero order Polynomial.X_ne_zero
      exact (mul_eq_zero.mp hrootPoly).resolve_left hx

private theorem cbivariate_default_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] :
    (default : CBivariate F) = 0 := rfl

private theorem cpoly_default_eq_zero {R : Type*} [Zero R] :
    (default : CPolynomial R) = 0 := rfl

private theorem substituteYRootPlusXY_eq_fold {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (a : F) :
    substituteYRootPlusXY Q a =
      (List.range' 0 Q.val.size).foldl
        (fun out y ↦
          let coeffY := Q.val.coeff y
          (List.range' 0 coeffY.val.size).foldl
            (fun out x ↦
              let coeff := coeffY.coeff x
              (List.range' 0 (y + 1)).foldl
                (fun out t ↦
                  out +
                    CBivariate.monomialXY (x + t) t
                      (coeff * (Nat.choose y t : F) * a ^ (y - t)))
                out)
            out)
        0 := by
  simp [substituteYRootPlusXY, Std.Legacy.Range.forIn_eq_forIn_range',
    cbivariate_default_eq_zero]

private theorem substituteYRootPlusXY_coeff_fold {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (a : F) (i j : Nat) :
    CBivariate.coeff (substituteYRootPlusXY Q a) i j =
      (List.range' 0 Q.val.size).foldl
        (fun acc y ↦
          let coeffY := Q.val.coeff y
          (List.range' 0 coeffY.val.size).foldl
            (fun acc x ↦
              let coeff := coeffY.coeff x
              (List.range' 0 (y + 1)).foldl
                (fun acc t ↦
                  acc +
                    if i = x + t ∧ j = t then
                      coeff * (Nat.choose y t : F) * a ^ (y - t)
                    else 0)
                acc)
            acc)
        0 := by
  rw [substituteYRootPlusXY_eq_fold]
  let outerStep : CBivariate F → Nat → CBivariate F :=
    fun out y ↦
      let coeffY := Q.val.coeff y
      (List.range' 0 coeffY.val.size).foldl
        (fun out x ↦
          let coeff := coeffY.coeff x
          (List.range' 0 (y + 1)).foldl
            (fun out t ↦
              out +
                CBivariate.monomialXY (x + t) t
                  (coeff * (Nat.choose y t : F) * a ^ (y - t)))
            out)
        out
  let coeffOuterStep : F → Nat → F :=
    fun acc y ↦
      let coeffY := Q.val.coeff y
      (List.range' 0 coeffY.val.size).foldl
        (fun acc x ↦
          let coeff := coeffY.coeff x
          (List.range' 0 (y + 1)).foldl
            (fun acc t ↦
              acc +
                if i = x + t ∧ j = t then
                  coeff * (Nat.choose y t : F) * a ^ (y - t)
                else 0)
            acc)
        acc
  change CBivariate.coeff
      (List.foldl outerStep 0 (List.range' 0 Q.val.size)) i j =
    List.foldl coeffOuterStep 0 (List.range' 0 Q.val.size)
  have houter : ∀ (ys : List Nat) (out : CBivariate F) (acc : F),
      CBivariate.coeff out i j = acc →
        CBivariate.coeff (List.foldl outerStep out ys) i j =
          List.foldl coeffOuterStep acc ys := by
    intro ys
    induction ys with
    | nil =>
        intro out acc hacc
        simpa using hacc
    | cons y ys ih =>
        intro out acc hacc
        simp only [List.foldl_cons]
        apply ih
        dsimp [outerStep, coeffOuterStep]
        let coeffY := Q.val.coeff y
        let innerStep : CBivariate F → Nat → CBivariate F :=
          fun out x ↦
            let coeff := coeffY.coeff x
            (List.range' 0 (y + 1)).foldl
              (fun out t ↦
                out +
                  CBivariate.monomialXY (x + t) t
                    (coeff * (Nat.choose y t : F) * a ^ (y - t)))
              out
        let coeffInnerStep : F → Nat → F :=
          fun acc x ↦
            let coeff := coeffY.coeff x
            (List.range' 0 (y + 1)).foldl
              (fun acc t ↦
                acc +
                  if i = x + t ∧ j = t then
                    coeff * (Nat.choose y t : F) * a ^ (y - t)
                  else 0)
              acc
        change CBivariate.coeff
            (List.foldl innerStep out (List.range' 0 coeffY.val.size)) i j =
          List.foldl coeffInnerStep acc (List.range' 0 coeffY.val.size)
        have hinner : ∀ (xs : List Nat) (out : CBivariate F) (acc : F),
            CBivariate.coeff out i j = acc →
              CBivariate.coeff (List.foldl innerStep out xs) i j =
                List.foldl coeffInnerStep acc xs := by
          intro xs
          induction xs with
          | nil =>
              intro out acc hacc
              simpa using hacc
          | cons x xs ihx =>
              intro out acc hacc
              simp only [List.foldl_cons]
              apply ihx
              dsimp [innerStep, coeffInnerStep]
              let coeff := coeffY.coeff x
              let termStep : CBivariate F → Nat → CBivariate F :=
                fun out t ↦
                  out +
                    CBivariate.monomialXY (x + t) t
                      (coeff * (Nat.choose y t : F) * a ^ (y - t))
              let coeffTermStep : F → Nat → F :=
                fun acc t ↦
                  acc +
                    if i = x + t ∧ j = t then
                      coeff * (Nat.choose y t : F) * a ^ (y - t)
                    else 0
              change CBivariate.coeff
                  (List.foldl termStep out (List.range' 0 (y + 1))) i j =
                List.foldl coeffTermStep acc (List.range' 0 (y + 1))
              have hterm : ∀ (ts : List Nat) (out : CBivariate F) (acc : F),
                  CBivariate.coeff out i j = acc →
                    CBivariate.coeff (List.foldl termStep out ts) i j =
                      List.foldl coeffTermStep acc ts := by
                intro ts
                induction ts with
                | nil =>
                    intro out acc hacc
                    simpa using hacc
                | cons t ts iht =>
                    intro out acc hacc
                    simp only [List.foldl_cons]
                    apply iht
                    dsimp [termStep, coeffTermStep]
                    change CBivariate.coeff
                        (out + CBivariate.monomialXY (x + t) t
                          (coeff * ↑(y.choose t) * a ^ (y - t))) i j =
                      acc + if i = x + t ∧ j = t then
                        coeff * ↑(y.choose t) * a ^ (y - t) else 0
                    rw [CBivariate.coeff_add, CBivariate.coeff_monomialXY, hacc]
              exact hterm (List.range' 0 (y + 1)) out acc hacc
        exact hinner (List.range' 0 coeffY.val.size) out acc hacc
  exact houter (List.range' 0 Q.val.size) 0 0 (CBivariate.coeff_zero i j)

private theorem substituteYRootPlusXY_term_fold_target {F : Type*}
    [Field F] (a coeff : F) (x y x₀ : Nat) (acc : F) :
    (List.range' 0 (y + 1)).foldl
        (fun acc t ↦
          acc +
            if x + y = x₀ + t ∧ y = t then
              coeff * (Nat.choose y t : F) * a ^ (y - t)
            else 0)
        acc =
      acc + if x₀ = x then coeff else 0 := by
  rw [List.foldl_congr_of_mem
    (f := fun acc t ↦
      acc +
        if x + y = x₀ + t ∧ y = t then
          coeff * (Nat.choose y t : F) * a ^ (y - t)
        else 0)
    (g := fun acc t ↦ acc + if t = y then (if x₀ = x then coeff else 0) else 0)
    (List.range' 0 (y + 1)) acc]
  · rw [DenseMatrix.foldl_range_one_special
      (F := F) (pivot := y) (if x₀ = x then coeff else 0) 0 (y + 1) acc]
    have hin : 0 ≤ y ∧ y < 0 + (y + 1) := by omega
    simp [hin]
  · intro acc' t ht
    by_cases hty : t = y
    · subst t
      by_cases hx : x₀ = x
      · subst x₀
        simp
      · have hnot : ¬(x + y = x₀ + y ∧ y = y) := by
          rintro ⟨hxy, _⟩
          apply hx
          omega
        have hx' : x ≠ x₀ := fun h ↦ hx h.symm
        simp [hx, hx']
    · have hnot : ¬(x + y = x₀ + t ∧ y = t) := by
        exact fun h ↦ hty h.2.symm
      simp [hnot, hty]

private theorem substituteYRootPlusXY_term_fold_zero_of_y_lt {F : Type*}
    [Field F] (a coeff : F) (x y y₀ x₀ : Nat) (acc : F) (hy₀ : y₀ < y) :
    (List.range' 0 (y₀ + 1)).foldl
        (fun acc t ↦
          acc +
            if x + y = x₀ + t ∧ y = t then
              coeff * (Nat.choose y₀ t : F) * a ^ (y₀ - t)
            else 0)
        acc =
      acc := by
  rw [List.foldl_congr_of_mem
    (f := fun acc t ↦
      acc +
        if x + y = x₀ + t ∧ y = t then
          coeff * (Nat.choose y₀ t : F) * a ^ (y₀ - t)
        else 0)
    (g := fun acc _t ↦ acc)
    (List.range' 0 (y₀ + 1)) acc]
  · induction (List.range' 0 (y₀ + 1)) generalizing acc with
    | nil => rfl
    | cons t ts ih =>
        simp only [List.foldl_cons]
        exact ih acc
  · intro acc' t ht
    have ht_le : t ≤ y₀ := by
      have ht' := (List.mem_range'_1.mp ht).2
      omega
    have hty : y ≠ t := by omega
    have hnot : ¬(x + y = x₀ + t ∧ y = t) := fun h ↦ hty h.2
    simp [hnot]

private theorem substituteYRootPlusXY_inner_fold_target {F : Type*}
    [Field F] (a : F) (coeffY : CPolynomial F) (x y : Nat) (acc : F)
    (hsize : coeffY.val.size = x + 1) :
    (List.range' 0 coeffY.val.size).foldl
        (fun acc x₀ ↦
          let coeff := coeffY.coeff x₀
          (List.range' 0 (y + 1)).foldl
            (fun acc t ↦
              acc +
                if x + y = x₀ + t ∧ y = t then
                  coeff * (Nat.choose y t : F) * a ^ (y - t)
                else 0)
            acc)
        acc =
      acc + coeffY.coeff x := by
  rw [List.foldl_congr_of_mem
    (f := fun acc x₀ ↦
      let coeff := coeffY.coeff x₀
      (List.range' 0 (y + 1)).foldl
        (fun acc t ↦
          acc +
            if x + y = x₀ + t ∧ y = t then
              coeff * (Nat.choose y t : F) * a ^ (y - t)
            else 0)
        acc)
    (g := fun acc x₀ ↦ acc + if x₀ = x then coeffY.coeff x else 0)
    (List.range' 0 coeffY.val.size) acc]
  · rw [hsize]
    rw [DenseMatrix.foldl_range_one_special
      (F := F) (pivot := x) (coeffY.coeff x) 0 (x + 1) acc]
    have hin : 0 ≤ x ∧ x < 0 + (x + 1) := by omega
    simp [hin]
  · intro acc' x₀ _hx₀
    rw [substituteYRootPlusXY_term_fold_target]
    by_cases hx : x₀ = x <;> simp [hx]

private theorem substituteYRootPlusXY_inner_fold_zero_of_y_lt {F : Type*}
    [Field F] (a : F) (coeffY : CPolynomial F) (x y y₀ : Nat) (acc : F)
    (hy₀ : y₀ < y) :
    (List.range' 0 coeffY.val.size).foldl
        (fun acc x₀ ↦
          let coeff := coeffY.coeff x₀
          (List.range' 0 (y₀ + 1)).foldl
            (fun acc t ↦
              acc +
                if x + y = x₀ + t ∧ y = t then
                  coeff * (Nat.choose y₀ t : F) * a ^ (y₀ - t)
                else 0)
            acc)
        acc =
      acc := by
  rw [List.foldl_congr_of_mem
    (f := fun acc x₀ ↦
      let coeff := coeffY.coeff x₀
      (List.range' 0 (y₀ + 1)).foldl
        (fun acc t ↦
          acc +
            if x + y = x₀ + t ∧ y = t then
              coeff * (Nat.choose y₀ t : F) * a ^ (y₀ - t)
            else 0)
        acc)
    (g := fun acc _x₀ ↦ acc)
    (List.range' 0 coeffY.val.size) acc]
  · induction (List.range' 0 coeffY.val.size) generalizing acc with
    | nil => rfl
    | cons x₀ xs ih =>
        simp only [List.foldl_cons]
        exact ih acc
  · intro acc' x₀ _hx₀
    exact substituteYRootPlusXY_term_fold_zero_of_y_lt a (coeffY.coeff x₀) x y y₀ x₀ acc' hy₀

private theorem substituteYRootPlusXY_coeff_top {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (a : F) (y x : Nat)
    (hQsize : Q.val.size = y + 1) (hRowSize : (Q.val.coeff y).val.size = x + 1) :
    CBivariate.coeff (substituteYRootPlusXY Q a) (x + y) y = (Q.val.coeff y).coeff x := by
  rw [substituteYRootPlusXY_coeff_fold]
  rw [hQsize]
  rw [List.foldl_congr_of_mem
    (f := fun acc y₀ ↦
      let coeffY := Q.val.coeff y₀
      (List.range' 0 coeffY.val.size).foldl
        (fun acc x₀ ↦
          let coeff := coeffY.coeff x₀
          (List.range' 0 (y₀ + 1)).foldl
            (fun acc t ↦
              acc +
                if x + y = x₀ + t ∧ y = t then
                  coeff * (Nat.choose y₀ t : F) * a ^ (y₀ - t)
                else 0)
            acc)
        acc)
    (g := fun acc y₀ ↦ acc + if y₀ = y then (Q.val.coeff y).coeff x else 0)
    (List.range' 0 (y + 1)) 0]
  · rw [DenseMatrix.foldl_range_one_special
      (F := F) (pivot := y) ((Q.val.coeff y).coeff x) 0 (y + 1) 0]
    have hin : 0 ≤ y ∧ y < 0 + (y + 1) := by omega
    simp [hin]
  · intro acc y₀ hy₀mem
    have hy₀lt : y₀ < y + 1 := by
      have hy₀lt' := (List.mem_range'_1.mp hy₀mem).2
      omega
    by_cases hy₀ : y₀ = y
    · subst y₀
      rw [substituteYRootPlusXY_inner_fold_target]
      · simp
      · exact hRowSize
    · have hy₀_lt_y : y₀ < y := by omega
      rw [substituteYRootPlusXY_inner_fold_zero_of_y_lt]
      · simp [hy₀]
      · exact hy₀_lt_y

private theorem substituteYRootPlusXY_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} (a : F) (hQ : Q ≠ 0) :
    substituteYRootPlusXY Q a ≠ 0 := by
  intro hzero
  let y := Q.natDegree
  let coeffY := Q.val.coeff y
  have hQsize : Q.val.size = y + 1 := cpoly_size_eq_natDegree_succ_of_ne_zero hQ
  have hcoeffY_ne : coeffY ≠ 0 := by
    dsimp [coeffY, y]
    exact cpoly_coeff_natDegree_ne_zero_of_ne_zero hQ
  let x := coeffY.natDegree
  have hRowSize : coeffY.val.size = x + 1 :=
    cpoly_size_eq_natDegree_succ_of_ne_zero hcoeffY_ne
  have hcoeff_ne : coeffY.coeff x ≠ 0 :=
    cpoly_coeff_natDegree_ne_zero_of_ne_zero hcoeffY_ne
  have htop :
      CBivariate.coeff (substituteYRootPlusXY Q a) (x + y) y = coeffY.coeff x := by
    simpa [coeffY] using substituteYRootPlusXY_coeff_top Q a y x hQsize hRowSize
  have hzeroCoeff : CBivariate.coeff (substituteYRootPlusXY Q a) (x + y) y = 0 := by
    rw [hzero]
    exact CBivariate.coeff_zero (x + y) y
  rw [htop] at hzeroCoeff
  exact hcoeff_ne hzeroCoeff

private theorem list_sum_map_mul_right {R : Type*} [Semiring R]
    (xs : List Nat) (f : Nat → R) (q : R) :
    (xs.map (fun x ↦ f x * q)).sum = (xs.map f).sum * q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, add_mul]

private theorem polynomialPrefix_eq_range_fold {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (p : CPolynomial F) :
    ∀ n : Nat,
      polynomialPrefix p n =
        (List.range n).foldl
          (fun acc i ↦ acc + CPolynomial.monomial i (p.coeff i)) 0
  | 0 => by
      rw [polynomialPrefix_zero]
      rfl
  | n + 1 => by
      rw [polynomialPrefix_succ, polynomialPrefix_eq_range_fold p n]
      unfold extendPrefix
      rw [List.range_succ, List.foldl_append]
      simp

private theorem cpoly_eq_range_fold {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (p : CPolynomial F) :
    p =
      (List.range' 0 p.val.size).foldl
        (fun acc i ↦ acc + CPolynomial.monomial i (p.coeff i)) 0 := by
  have hprefix := polynomialPrefix_eq_range_fold p p.val.size
  have hdegree : degreeLt p p.val.size := by
    unfold degreeLt CPolynomial.degree
    cases hsize : p.val.size with
    | zero =>
        simp
    | succ n =>
        exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self n)
  have hpref : polynomialPrefix p p.val.size = p :=
    polynomialPrefix_eq_self_of_degreeLt hdegree
  rw [hpref] at hprefix
  rw [List.range_eq_range'] at hprefix
  exact hprefix

private theorem cpoly_range_fold_monomial_mul_pow {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (coeffY q : CPolynomial F) (y : Nat) (acc : CPolynomial F) :
    (List.range' 0 coeffY.val.size).foldl
        (fun acc x ↦ acc + CPolynomial.monomial x (coeffY.coeff x) * q ^ y)
        acc =
      acc + coeffY * q ^ y := by
  rw [list_foldl_add_eq_sum]
  rw [list_sum_map_mul_right]
  have hrow := cpoly_eq_range_fold coeffY
  rw [list_foldl_add_eq_sum
    (fun x ↦ CPolynomial.monomial x (coeffY.coeff x))
    (List.range' 0 coeffY.val.size) 0] at hrow
  simp only [zero_add] at hrow
  rw [← hrow]

private theorem composeY_monomialXY {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (p : CPolynomial F) (x y : Nat) (c : F) :
    CBivariate.composeY (CBivariate.monomialXY x y c) p =
      CPolynomial.monomial x c * p ^ y := by
  apply (CPolynomial.ringEquiv (R := F)).injective
  rw [show CPolynomial.ringEquiv (CBivariate.composeY (CBivariate.monomialXY x y c) p) =
      (CBivariate.composeY (CBivariate.monomialXY x y c) p).toPoly by rfl]
  rw [show CPolynomial.ringEquiv (CPolynomial.monomial x c * p ^ y) =
      (CPolynomial.monomial x c * p ^ y).toPoly by rfl]
  rw [composeY_toPoly, CBivariate.monomialXY_toPoly, CPolynomial.toPoly_mul,
    CPolynomial.toPoly_pow, Polynomial.eval_monomial]
  rw [show (CPolynomial.monomial x c : CPolynomial F).toPoly =
      Polynomial.monomial x c from
    CPolynomial.monomial_toPoly (R := F) x c]

private theorem composeY_foldl_add {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (f : Nat → CBivariate F) (p : CPolynomial F) :
    ∀ (xs : List Nat) (out : CBivariate F) (acc : CPolynomial F),
      CBivariate.composeY out p = acc →
        CBivariate.composeY (xs.foldl (fun out x ↦ out + f x) out) p =
          List.foldl (fun acc x ↦ acc + CBivariate.composeY (f x) p) acc xs := by
  intro xs
  induction xs with
  | nil =>
      intro out acc hacc
      simpa using hacc
  | cons x xs ih =>
      intro out acc hacc
      simp only [List.foldl_cons]
      apply ih
      rw [composeY_add, hacc]

private theorem composeY_substituteYRootPlusXY_term_fold {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (a coeff : F) (p : CPolynomial F) (x y : Nat) (out : CBivariate F) :
    CBivariate.composeY
        ((List.range' 0 (y + 1)).foldl
          (fun out t ↦
            out +
              CBivariate.monomialXY (x + t) t
                (coeff * (Nat.choose y t : F) * a ^ (y - t)))
          out)
        p =
      CBivariate.composeY out p +
        CPolynomial.monomial x coeff * (CPolynomial.C a + CPolynomial.X * p) ^ y := by
  rw [composeY_foldl_add
    (fun t ↦
      CBivariate.monomialXY (x + t) t
        (coeff * (Nat.choose y t : F) * a ^ (y - t)))
    p (List.range' 0 (y + 1)) out (CBivariate.composeY out p) rfl]
  rw [List.foldl_congr_of_mem
    (f := fun acc t ↦
      acc + CBivariate.composeY
        (CBivariate.monomialXY (x + t) t
          (coeff * (Nat.choose y t : F) * a ^ (y - t))) p)
    (g := fun acc t ↦
      acc + CPolynomial.monomial (x + t)
        (coeff * (Nat.choose y t : F) * a ^ (y - t)) * p ^ t)
    (List.range' 0 (y + 1)) (CBivariate.composeY out p)]
  · rw [list_foldl_add_eq_sum
      (fun t ↦
        CPolynomial.monomial (x + t)
          (coeff * (Nat.choose y t : F) * a ^ (y - t)) * p ^ t)]
    have hsum := cpoly_monomial_substitution_sum a coeff p x y
    rw [list_foldl_add_eq_sum
      (fun t ↦
        CPolynomial.monomial (x + t)
          (coeff * (Nat.choose y t : F) * a ^ (y - t)) * p ^ t)
      (List.range' 0 (y + 1)) 0] at hsum
    simp only [zero_add] at hsum
    rw [hsum]
  · intro acc t _ht
    rw [composeY_monomialXY]

private theorem composeY_substituteYRootPlusXY_inner_fold {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (a : F) (p : CPolynomial F) (coeffY : CPolynomial F) (y : Nat)
    (out : CBivariate F) :
    CBivariate.composeY
        ((List.range' 0 coeffY.val.size).foldl
          (fun out x ↦
            let coeff := coeffY.coeff x
            (List.range' 0 (y + 1)).foldl
              (fun out t ↦
                out +
                  CBivariate.monomialXY (x + t) t
                    (coeff * (Nat.choose y t : F) * a ^ (y - t)))
              out)
          out)
        p =
      CBivariate.composeY out p +
        coeffY * (CPolynomial.C a + CPolynomial.X * p) ^ y := by
  let q := CPolynomial.C a + CPolynomial.X * p
  let innerStep : CBivariate F → Nat → CBivariate F :=
    fun out x ↦
      let coeff := coeffY.coeff x
      (List.range' 0 (y + 1)).foldl
        (fun out t ↦
          out +
            CBivariate.monomialXY (x + t) t
              (coeff * (Nat.choose y t : F) * a ^ (y - t)))
        out
  let coeffStep : CPolynomial F → Nat → CPolynomial F :=
    fun acc x ↦ acc + CPolynomial.monomial x (coeffY.coeff x) * q ^ y
  change CBivariate.composeY
      (List.foldl innerStep out (List.range' 0 coeffY.val.size)) p =
    CBivariate.composeY out p + coeffY * q ^ y
  have hfold : ∀ (xs : List Nat) (out : CBivariate F) (acc : CPolynomial F),
      CBivariate.composeY out p = acc →
        CBivariate.composeY (List.foldl innerStep out xs) p =
          List.foldl coeffStep acc xs := by
    intro xs
    induction xs with
    | nil =>
        intro out acc hacc
        simpa using hacc
    | cons x xs ih =>
        intro out acc hacc
        simp only [List.foldl_cons]
        apply ih
        dsimp [innerStep, coeffStep, q]
        rw [composeY_substituteYRootPlusXY_term_fold, hacc]
  rw [hfold (List.range' 0 coeffY.val.size) out (CBivariate.composeY out p) rfl]
  exact cpoly_range_fold_monomial_mul_pow coeffY q y (CBivariate.composeY out p)

private theorem composeY_substituteYRootPlusXY_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (a : F) (p : CPolynomial F) :
    CBivariate.composeY (substituteYRootPlusXY Q a) p =
      CBivariate.composeY Q (CPolynomial.C a + CPolynomial.X * p) := by
  rw [substituteYRootPlusXY_eq_fold]
  let q := CPolynomial.C a + CPolynomial.X * p
  let outerStep : CBivariate F → Nat → CBivariate F :=
    fun out y ↦
      let coeffY := Q.val.coeff y
      (List.range' 0 coeffY.val.size).foldl
        (fun out x ↦
          let coeff := coeffY.coeff x
          (List.range' 0 (y + 1)).foldl
            (fun out t ↦
              out +
                CBivariate.monomialXY (x + t) t
                  (coeff * (Nat.choose y t : F) * a ^ (y - t)))
            out)
        out
  let coeffStep : CPolynomial F → Nat → CPolynomial F :=
    fun acc y ↦ acc + Q.val.coeff y * q ^ y
  change CBivariate.composeY
      (List.foldl outerStep 0 (List.range' 0 Q.val.size)) p =
    CBivariate.composeY Q q
  have hfold : ∀ (ys : List Nat) (out : CBivariate F) (acc : CPolynomial F),
      CBivariate.composeY out p = acc →
        CBivariate.composeY (List.foldl outerStep out ys) p =
          List.foldl coeffStep acc ys := by
    intro ys
    induction ys with
    | nil =>
        intro out acc hacc
        simpa using hacc
    | cons y ys ih =>
        intro out acc hacc
        simp only [List.foldl_cons]
        apply ih
        dsimp [outerStep, coeffStep, q]
        rw [composeY_substituteYRootPlusXY_inner_fold, hacc]
  rw [hfold (List.range' 0 Q.val.size) 0 0 (composeY_zero p)]
  rw [← composeY_eq_range_fold Q q]

private theorem transformedRothRuckensteinResidual_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} (a : F) (hQ : Q ≠ 0) :
    transformedRothRuckensteinResidual Q a ≠ 0 := by
  unfold transformedRothRuckensteinResidual
  exact stripXAdicFactor_ne_zero (substituteYRootPlusXY_ne_zero a hQ)

private theorem composeY_transformedRothRuckensteinResidual_dropXPower_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {p : CPolynomial F} {a : F}
    (hQ : Q ≠ 0)
    (hroot : CBivariate.composeY Q (CPolynomial.C a + CPolynomial.X * p) = 0) :
    CBivariate.composeY (transformedRothRuckensteinResidual Q a) p = 0 := by
  unfold transformedRothRuckensteinResidual
  apply composeY_stripXAdicFactor_eq_zero_of_composeY
  · exact substituteYRootPlusXY_ne_zero a hQ
  · rw [composeY_substituteYRootPlusXY_eq]
    exact hroot

private theorem degreeLt_dropXPower_succ_of_degreeLt {F : Type*}
    [Zero F] {p : CPolynomial F} {depth fuel : Nat}
    (hdegree : degreeLt (CPolynomial.dropXPower p depth) (fuel + 1)) :
    degreeLt (CPolynomial.dropXPower p (depth + 1)) fuel := by
  apply degreeLt_of_degreeLtBool
  rw [degreeLtBool]
  have hsizeBool := degreeLtBool_of_degreeLt hdegree
  rw [degreeLtBool] at hsizeBool
  simp at hsizeBool
  let suffix := CPolynomial.dropXPower p depth
  have hsuffixSize : suffix.val.size ≤ fuel + 1 := by
    dsimp [suffix]
    exact hsizeBool
  have htail :
      CPolynomial.dropXPower p (depth + 1) = CPolynomial.divX suffix := by
    dsimp [suffix]
    rw [← cpoly_dropXPower_add p depth 1]
    rfl
  rw [htail]
  cases hs : suffix.val.size with
  | zero =>
      unfold CPolynomial.divX
      simp [suffix, hs]
  | succ n =>
      have hpos : suffix.val.size > 0 := by simp [hs]
      have hlt := CPolynomial.divX_size_lt (p := suffix) hpos
      rw [decide_eq_true_eq]
      omega

private theorem polynomialPrefix_eq_self_of_dropXPower_degreeLt_zero {F : Type*}
    [Zero F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} {depth : Nat}
    (hdegree : degreeLt (CPolynomial.dropXPower p depth) 0) :
    polynomialPrefix p depth = p := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  unfold polynomialPrefix
  rw [cpoly_truncate_coeff]
  by_cases hi : i < depth
  · simp [hi]
  · have hsizeBool := degreeLtBool_of_degreeLt hdegree
    rw [degreeLtBool] at hsizeBool
    simp at hsizeBool
    have hsizeZero : (CPolynomial.dropXPower p depth).val.size = 0 := by
      rw [hsizeBool]
      rfl
    have hsuffixCoeff :
        (CPolynomial.dropXPower p depth).coeff (i - depth) = 0 :=
      cpoly_coeff_eq_zero_of_size_le _ (by rw [hsizeZero]; omega)
    rw [cpoly_coeff_dropXPower] at hsuffixCoeff
    have hidx : i - depth + depth = i := by omega
    rw [hidx] at hsuffixCoeff
    simp [hi, hsuffixCoeff]

private theorem transformedRothRuckensteinRootPrefixesWithFuel_complete_aux {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) :
    ∀ (fuel : Nat) (Q : CBivariate F) (depth : Nat) (pref p : CPolynomial F),
      Q ≠ 0 →
      pref = polynomialPrefix p depth →
      degreeLt (CPolynomial.dropXPower p depth) fuel →
      CBivariate.composeY Q (CPolynomial.dropXPower p depth) = 0 →
      p ∈ (transformedRothRuckensteinRootPrefixesWithFuel fieldRoots fuel Q depth pref).toList := by
  intro fuel
  induction fuel with
  | zero =>
      intro Q depth pref p hQ hpref hdegree hroot
      simp [transformedRothRuckensteinRootPrefixesWithFuel]
      have hpEq : polynomialPrefix p depth = p :=
        polynomialPrefix_eq_self_of_dropXPower_degreeLt_zero hdegree
      rw [hpref, hpEq]
  | succ fuel ih =>
      intro Q depth pref p hQ hpref hdegree hroot
      simp [transformedRothRuckensteinRootPrefixesWithFuel]
      let Qnorm := CBivariate.stripXAdicFactor Q
      have hQnorm : Qnorm ≠ 0 := stripXAdicFactor_ne_zero hQ
      have hrootNorm : CBivariate.composeY Qnorm (CPolynomial.dropXPower p depth) = 0 := by
        dsimp [Qnorm]
        exact composeY_stripXAdicFactor_eq_zero_of_composeY hQ hroot
      have hcoeff0 :
          (CPolynomial.dropXPower p depth).coeff 0 = p.coeff depth := by
        rw [cpoly_coeff_dropXPower]
        rw [show 0 + depth = depth by omega]
      have hinitRoot :
          CPolynomial.eval (p.coeff depth) (initialCoefficientPolynomial Qnorm) = 0 := by
        rw [← hcoeff0]
        rw [initialCoefficientPolynomial_eval_eq_composeY_coeff_zero]
        rw [hrootNorm]
        exact CPolynomial.coeff_zero 0
      have hcoeffMem :
          p.coeff depth ∈
            (rootsInFieldForNonzeroEquation fieldRoots
              (initialCoefficientPolynomial Qnorm)).toList :=
        rootsInFieldForNonzeroEquation_complete fieldRoots
          (initialCoefficientPolynomial_stripXAdicFactor_ne_zero hQ) hinitRoot
      have hprefNext :
          extendPrefix pref depth (p.coeff depth) =
            polynomialPrefix p (depth + 1) := by
        rw [hpref, polynomialPrefix_succ]
      have hdropRoot :
          CBivariate.composeY
              (transformedRothRuckensteinResidual Qnorm (p.coeff depth))
              (CPolynomial.dropXPower p (depth + 1)) = 0 := by
        have hdropEq :
            CPolynomial.dropXPower p depth =
              CPolynomial.C (p.coeff depth) +
                CPolynomial.X * CPolynomial.dropXPower p (depth + 1) :=
          dropXPower_eq_C_add_X_mul_dropXPower_succ p depth
        apply composeY_transformedRothRuckensteinResidual_dropXPower_eq_zero
          (Q := Qnorm) (a := p.coeff depth)
          (p := CPolynomial.dropXPower p (depth + 1)) hQnorm
        rw [← hdropEq]
        exact hrootNorm
      have hdegreeTail :
          degreeLt (CPolynomial.dropXPower p (depth + 1)) fuel :=
        degreeLt_dropXPower_succ_of_degreeLt hdegree
      have hrec :
          p ∈
            (transformedRothRuckensteinRootPrefixesWithFuel fieldRoots fuel
              (transformedRothRuckensteinResidual Qnorm (p.coeff depth))
              (depth + 1) (extendPrefix pref depth (p.coeff depth))).toList :=
        ih (transformedRothRuckensteinResidual Qnorm (p.coeff depth))
          (depth + 1) (extendPrefix pref depth (p.coeff depth)) p
          (transformedRothRuckensteinResidual_ne_zero (p.coeff depth) hQnorm)
          hprefNext hdegreeTail hdropRoot
      refine ⟨?_, ?_⟩
      · simpa [Qnorm] using hQnorm
      · simpa [Qnorm] using
          (Array.mem_flatten_map_of_mem
            (rootsInFieldForNonzeroEquation fieldRoots
              (initialCoefficientPolynomial Qnorm))
            (fun coeff ↦
              transformedRothRuckensteinRootPrefixesWithFuel fieldRoots fuel
                (transformedRothRuckensteinResidual Qnorm coeff)
                (depth + 1) (extendPrefix pref depth coeff))
            hcoeffMem hrec)

/-- Completeness of Roth-Ruckenstein root finding from a complete field-root backend.

The nonzero-input hypothesis matches the backend completeness contract, which
only promises finite output for nonzero bivariate equations.
-/
theorem rothRuckensteinRootsYDegreeLt_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F}
    {Q : CBivariate F} {k : Nat} {p : CPolynomial F}
    (hQ : Q ≠ 0) (hdegree : degreeLt p k) (hroot : CBivariate.composeY Q p = 0) :
    p ∈ (rothRuckensteinRootsYDegreeLt fieldRoots Q k).toList := by
  unfold rothRuckensteinRootsYDegreeLt transformedRothRuckensteinRootsYDegreeLt
    transformedRothRuckensteinRootPrefixes
  have hprefix :
      p ∈ (transformedRothRuckensteinRootPrefixesWithFuel fieldRoots k Q 0 default).toList := by
    exact transformedRothRuckensteinRootPrefixesWithFuel_complete_aux
      fieldRoots k Q 0 default p hQ
      (by rw [polynomialPrefix_zero, cpoly_default_eq_zero])
      (by simpa [CPolynomial.dropXPower] using hdegree)
      (by simpa [CPolynomial.dropXPower] using hroot)
  simp [hprefix, isRootYDegreeLtBool_of_root hdegree hroot]

/-- Roth-Ruckenstein roots packaged with an explicit univariate field-root backend. -/
def rothRuckensteinRootContext (F : Type*)
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) : GSRootContext F where
  rootsYDegreeLt := rothRuckensteinRootsYDegreeLt fieldRoots
  sound := by
    intro Q k p h
    exact rothRuckensteinRootsYDegreeLt_sound h
  complete := by
    intro Q k p hQ hdegree hroot
    exact rothRuckensteinRootsYDegreeLt_complete
      (fieldRoots := fieldRoots) hQ hdegree hroot

/-- Residual-transform Roth-Ruckenstein roots packaged as a backend. -/
def transformedRothRuckensteinRootContext (F : Type*)
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) : GSRootContext F where
  rootsYDegreeLt := transformedRothRuckensteinRootsYDegreeLt fieldRoots
  sound := by
    intro Q k p h
    unfold transformedRothRuckensteinRootsYDegreeLt at h
    simp [isRootYDegreeLtBool] at h
    exact ⟨degreeLt_of_degreeLtBool h.2.1, composeY_of_composeYHorner_eq_zero h.2.2⟩
  complete := by
    intro Q k p hQ hdegree hroot
    simpa [rothRuckensteinRootsYDegreeLt] using
      (rothRuckensteinRootsYDegreeLt_complete
        (fieldRoots := fieldRoots) hQ hdegree hroot)

end GuruswamiSudan

end CompPoly
