/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Algorithm

/-!
# Roth-Ruckenstein Root Correctness

Correctness statements for the Roth-Ruckenstein root backend.
-/

namespace CompPoly

namespace GuruswamiSudan

private theorem cpoly_val_coeff_ofArray {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (coeffs : Array R) (i : Nat) :
    (CPolynomial.ofArray coeffs).val.coeff i = coeffs.getD i 0 := by
  unfold CPolynomial.ofArray
  exact CPolynomial.Raw.Trim.coeff_eq_coeff coeffs i

private theorem cpoly_coeff_eq_zero_of_size_le {R : Type*} [Zero R]
    (p : CPolynomial R) {i : Nat} (h : p.val.size ≤ i) : p.coeff i = 0 := by
  unfold CPolynomial.coeff CPolynomial.Raw.coeff
  rw [Array.getD_eq_getD_getElem?]
  simp [Array.getElem?_eq_none h]

private theorem cpoly_coeff_dropXPower {R : Type*} [Zero R]
    (p : CPolynomial R) (n i : Nat) :
    (CPolynomial.dropXPower p n).coeff i = p.coeff (i + n) := by
  induction n generalizing p i with
  | zero =>
      simp [CPolynomial.dropXPower]
  | succ n ih =>
      rw [CPolynomial.dropXPower, ih, CPolynomial.coeff_divX]
      have h : i + n + 1 = i + (n + 1) := by omega
      rw [h]

private theorem cbivar_coeff_divXPower {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (Q : CBivariate R) (n i j : Nat) :
    CBivariate.coeff (CBivariate.divXPower Q n) i j = CBivariate.coeff Q (i + n) j := by
  unfold CBivariate.coeff CBivariate.divXPower
  rw [cpoly_val_coeff_ofArray]
  by_cases hj : j < Q.val.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hj]
    have hqcoeff : Q.val.coeff j = Q.val[j] := CPolynomial.Raw.Trim.coeff_eq_getElem hj
    change (CPolynomial.dropXPower Q.val[j] n).coeff i = (Q.val.coeff j).coeff (i + n)
    rw [hqcoeff]
    exact cpoly_coeff_dropXPower Q.val[j] n i
  · have hjle : Q.val.size ≤ j := Nat.le_of_not_lt hj
    have hmaple : (Q.val.map fun coeff => CPolynomial.dropXPower coeff n).size ≤ j := by
      simpa using hjle
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hmaple]
    have hqcoeff : Q.val.coeff j = (0 : CPolynomial R) := by
      unfold CPolynomial.Raw.coeff
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hjle]
      rfl
    rw [hqcoeff]
    change (0 : CPolynomial R).coeff i = (0 : CPolynomial R).coeff (i + n)
    rw [CPolynomial.coeff_zero, CPolynomial.coeff_zero]

private theorem cbivar_coeff_eq_zero_of_y_size_le {R : Type*} [Zero R]
    (Q : CBivariate R) {i j : Nat} (hj : Q.val.size ≤ j) :
    CBivariate.coeff Q i j = 0 := by
  unfold CBivariate.coeff
  have hqcoeff : Q.val.coeff j = (0 : CPolynomial R) := by
    unfold CPolynomial.Raw.coeff
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hj]
    rfl
  rw [hqcoeff]
  exact CPolynomial.coeff_zero i

private theorem initialCoefficientPolynomial_coeff_fold {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (Q : CBivariate F) (j : Nat) :
    ∀ (ys : List Nat) (out : CPolynomial F),
      ys.Nodup →
        (List.foldl
          (fun out y => out + CPolynomial.monomial y (CBivariate.coeff Q 0 y))
          out ys).coeff j =
          out.coeff j + if j ∈ ys then CBivariate.coeff Q 0 j else 0 := by
  intro ys
  induction ys with
  | nil =>
      intro out _hys
      simp
  | cons y ys ih =>
      intro out hys
      have hynot : y ∉ ys := (List.nodup_cons.mp hys).1
      have hysNodup : ys.Nodup := (List.nodup_cons.mp hys).2
      simp only [List.foldl_cons]
      rw [ih (out + CPolynomial.monomial y (CBivariate.coeff Q 0 y)) hysNodup]
      rw [CPolynomial.coeff_add, CPolynomial.coeff_monomial]
      by_cases hjy : j = y
      · subst y
        simp [hynot]
      · have hmonomial :
            (if j = y then CBivariate.coeff Q 0 y else 0) = 0 := by
          simp [hjy]
        rw [hmonomial]
        by_cases hjmem : j ∈ ys <;> simp [hjy, hjmem]

private theorem initialCoefficientPolynomial_coeff_of_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) {j : Nat} (hj : j < Q.val.size) :
    (initialCoefficientPolynomial Q).coeff j = CBivariate.coeff Q 0 j := by
  unfold initialCoefficientPolynomial
  rw [initialCoefficientPolynomial_coeff_fold Q j (List.range Q.val.size)
    (0 : CPolynomial F) (List.nodup_range (n := Q.val.size))]
  rw [CPolynomial.coeff_zero]
  simp [hj]

private theorem cpoly_xAdicOrder?_some_coeff_ne {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial R} {i : Nat} (h : CPolynomial.xAdicOrder? p = some i) :
    p.coeff i ≠ 0 := by
  unfold CPolynomial.xAdicOrder? at h
  have hp := List.find?_some h
  simpa using hp

private theorem cpoly_xAdicOrder?_none_eq_zero {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial R} (h : CPolynomial.xAdicOrder? p = none) : p = 0 := by
  rw [CPolynomial.eq_zero_iff_coeff_zero]
  intro i
  by_cases hi : i < p.val.size
  · unfold CPolynomial.xAdicOrder? at h
    have hall := (List.find?_eq_none).mp h i
    have hmem : i ∈ List.range' 0 p.val.size := by
      simpa [List.mem_range'] using Nat.succ_le_of_lt hi
    have hnot := hall hmem
    by_cases hcoeff : p.coeff i = 0
    · exact hcoeff
    · have hbeqFalse : (p.coeff i == 0) = false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        exact hcoeff (by simpa using htrue)
      have hb : (!(p.coeff i == 0)) = true := by
        rw [hbeqFalse]
        rfl
      exact (hnot hb).elim
  · exact cpoly_coeff_eq_zero_of_size_le p (Nat.le_of_not_lt hi)

private def xAdicStep {R : Type*} [Zero R] [BEq R]
    (Q : CBivariate R) (best : Option Nat) (y : Nat) : Option Nat :=
  match CPolynomial.xAdicOrder? (Q.val.coeff y) with
  | none => best
  | some order =>
      match best with
      | none => some order
      | some current => some (min current order)

private def xAdicWitness {R : Type*} [Zero R] (Q : CBivariate R)
    (best : Option Nat) : Prop :=
  ∀ order, best = some order → ∃ y, y < Q.val.size ∧ CBivariate.coeff Q order y ≠ 0

private theorem cbivar_xAdicOrder?_step_witness {R : Type*}
    [Zero R] [BEq R] [LawfulBEq R]
    (Q : CBivariate R) (best : Option Nat) {y : Nat}
    (hw : xAdicWitness Q best) (hy : y < Q.val.size) :
    xAdicWitness Q (xAdicStep Q best y) := by
  intro result hresult
  unfold xAdicStep at hresult
  cases best with
  | none =>
      cases horder : CPolynomial.xAdicOrder? (Q.val.coeff y) with
      | none =>
          rw [horder] at hresult
          simp at hresult
      | some order =>
          rw [horder] at hresult
          have hres : result = order := by simpa using hresult.symm
          subst result
          have hcoeff : CBivariate.coeff Q order y ≠ 0 := by
            unfold CBivariate.coeff
            exact cpoly_xAdicOrder?_some_coeff_ne horder
          exact ⟨y, hy, hcoeff⟩
  | some current =>
      cases horder : CPolynomial.xAdicOrder? (Q.val.coeff y) with
      | none =>
          rw [horder] at hresult
          have hres : result = current := by simpa using hresult.symm
          subst result
          exact hw current rfl
      | some order =>
          rw [horder] at hresult
          have hres : result = min current order := by simpa using hresult.symm
          subst result
          have hcoeff : CBivariate.coeff Q order y ≠ 0 := by
            unfold CBivariate.coeff
            exact cpoly_xAdicOrder?_some_coeff_ne horder
          by_cases hle : current ≤ order
          · have hmin : min current order = current := Nat.min_eq_left hle
            rcases hw current rfl with ⟨w, hwlt, hwcoeff⟩
            exact ⟨w, hwlt, by simpa [hmin] using hwcoeff⟩
          · have hmin : min current order = order :=
              Nat.min_eq_right (Nat.le_of_not_ge hle)
            exact ⟨y, hy, by simpa [hmin] using hcoeff⟩

private theorem cbivar_xAdicOrder?_fold_witness {R : Type*}
    [Zero R] [BEq R] [LawfulBEq R]
    (Q : CBivariate R) :
    ∀ (ys : List Nat) (best : Option Nat),
      xAdicWitness Q best →
        (∀ y, y ∈ ys → y < Q.val.size) →
          xAdicWitness Q (List.foldl (xAdicStep Q) best ys) := by
  intro ys
  induction ys with
  | nil =>
      intro best hw _hys
      exact hw
  | cons y ys ih =>
      intro best hw hys
      simp only [List.foldl_cons]
      apply ih
      · exact cbivar_xAdicOrder?_step_witness Q best hw (hys y (by simp))
      · intro z hz
        exact hys z (by simp [hz])

private theorem cbivar_xAdicOrder?_some_exists {R : Type*}
    [Zero R] [BEq R] [LawfulBEq R]
    {Q : CBivariate R} {order : Nat} (h : CBivariate.xAdicOrder? Q = some order) :
    ∃ y, y < Q.val.size ∧ CBivariate.coeff Q order y ≠ 0 := by
  unfold CBivariate.xAdicOrder? at h
  change List.foldl (xAdicStep Q) none (List.range' 0 Q.val.size) = some order at h
  have hw := cbivar_xAdicOrder?_fold_witness Q (List.range' 0 Q.val.size) none
    (by
      intro order hnone
      simp at hnone)
    (by
      intro y hy
      simpa using (List.mem_range'_1.mp hy).2)
  exact hw order h

private theorem cbivar_xAdicOrder?_fold_none {R : Type*}
    [Zero R] [BEq R] (Q : CBivariate R) :
    ∀ (ys : List Nat) (best : Option Nat),
      List.foldl (xAdicStep Q) best ys = none →
        best = none ∧ ∀ y, y ∈ ys → CPolynomial.xAdicOrder? (Q.val.coeff y) = none := by
  intro ys
  induction ys with
  | nil =>
      intro best h
      exact ⟨h, by simp⟩
  | cons y ys ih =>
      intro best h
      simp only [List.foldl_cons] at h
      have htail := ih (xAdicStep Q best y) h
      have hstep : xAdicStep Q best y = none := htail.1
      unfold xAdicStep at hstep
      cases hrow : CPolynomial.xAdicOrder? (Q.val.coeff y) with
      | some order =>
          rw [hrow] at hstep
          cases best <;> simp at hstep
      | none =>
          rw [hrow] at hstep
          have hbest : best = none := by simpa using hstep
          constructor
          · exact hbest
          · intro z hz
            simp at hz
            cases hz with
            | inl hzy =>
                subst z
                exact hrow
            | inr hzTail =>
                exact htail.2 z hzTail

private theorem cbivar_xAdicOrder?_none_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {Q : CBivariate F} (h : CBivariate.xAdicOrder? Q = none) : Q = 0 := by
  apply (CPolynomial.eq_zero_iff_coeff_zero (p := (Q : CPolynomial (CPolynomial F)))).mpr
  intro y
  by_cases hy : y < Q.val.size
  · unfold CBivariate.xAdicOrder? at h
    change List.foldl (xAdicStep Q) none (List.range' 0 Q.val.size) = none at h
    have hfold := cbivar_xAdicOrder?_fold_none Q (List.range' 0 Q.val.size) none h
    have hmem : y ∈ List.range' 0 Q.val.size := by
      simpa [List.mem_range'] using Nat.succ_le_of_lt hy
    exact cpoly_xAdicOrder?_none_eq_zero (hfold.2 y hmem)
  · have hyle : Q.val.size ≤ y := Nat.le_of_not_lt hy
    unfold CPolynomial.coeff CPolynomial.Raw.coeff
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hyle]
    rfl

private theorem degreeLt_of_degreeLtBool {F : Type*} [Zero F]
    {p : CPolynomial F} {k : Nat} (h : degreeLtBool p k = true) : degreeLt p k := by
  rw [degreeLtBool] at h
  simp at h
  unfold degreeLt CPolynomial.degree
  cases hs : p.val.size with
  | zero => simp
  | succ n =>
      simp
      omega

private theorem degreeLtBool_of_degreeLt {F : Type*} [Zero F]
    {p : CPolynomial F} {k : Nat} (h : degreeLt p k) : degreeLtBool p k = true := by
  rw [degreeLtBool]
  unfold degreeLt CPolynomial.degree at h
  cases hs : p.val.size with
  | zero =>
      simp
  | succ n =>
      rw [hs] at h
      simp at h
      simp
      omega

private theorem composeY_of_composeYHorner_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {Q : CBivariate F} {p : CPolynomial F}
    (h : CBivariate.composeYHorner Q p = 0) : CBivariate.composeY Q p = 0 := by
  simpa [CBivariate.composeY, CBivariate.composeYHorner, CPolynomial.eval_horner_eq_eval] using h

private theorem composeYHorner_eq_zero_of_composeY {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {Q : CBivariate F} {p : CPolynomial F}
    (h : CBivariate.composeY Q p = 0) : CBivariate.composeYHorner Q p = 0 := by
  simpa [CBivariate.composeY, CBivariate.composeYHorner, CPolynomial.eval_horner_eq_eval] using h

private theorem isRootYDegreeLtBool_of_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {Q : CBivariate F} {p : CPolynomial F} {k : Nat}
    (hdegree : degreeLt p k) (hroot : CBivariate.composeY Q p = 0) :
    isRootYDegreeLtBool Q k p = true := by
  unfold isRootYDegreeLtBool
  rw [degreeLtBool_of_degreeLt hdegree, composeYHorner_eq_zero_of_composeY hroot]
  simp

/-- Soundness of Roth-Ruckenstein root filtering. -/
theorem rothRuckensteinRootsYDegreeLt_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootBackend F} {Q : CBivariate F} {k : Nat}
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

/-- Completeness of Roth-Ruckenstein root finding from a complete field-root backend.

The theorem is stated for nonzero bivariate input, matching the finite-output
root contract.
-/
theorem rothRuckensteinRootsYDegreeLt_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootBackend F}
    {Q : CBivariate F} {k : Nat} {p : CPolynomial F}
    (hQ : Q ≠ 0) (hdegree : degreeLt p k) (hroot : CBivariate.composeY Q p = 0) :
    p ∈ (rothRuckensteinRootsYDegreeLt fieldRoots Q k).toList := by
  sorry

/-- Roth-Ruckenstein roots packaged with an explicit univariate field-root backend. -/
def rothRuckensteinRootBackend (F : Type*)
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootBackend F) : GSRootBackend F where
  rootsYDegreeLt := rothRuckensteinRootsYDegreeLt fieldRoots
  sound := by
    intro Q k p h
    exact rothRuckensteinRootsYDegreeLt_sound h
  complete := by
    intro Q k p hQ hdegree hroot
    exact rothRuckensteinRootsYDegreeLt_complete
      (fieldRoots := fieldRoots) hQ hdegree hroot

/-- Residual-transform Roth-Ruckenstein roots packaged as a backend. -/
def transformedRothRuckensteinRootBackend (F : Type*)
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootBackend F) : GSRootBackend F where
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
