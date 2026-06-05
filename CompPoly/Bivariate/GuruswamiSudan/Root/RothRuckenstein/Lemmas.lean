/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Algorithm
import CompPoly.Bivariate.GuruswamiSudan.Root.Common.Lemmas
import CompPoly.Bivariate.GuruswamiSudan.PolynomialCorrectness
import CompPoly.Data.Array.Lemmas

/-!
# Roth-Ruckenstein Correctness Support

Coefficient, composition, and root-filter lemmas used by the Roth-Ruckenstein
correctness proofs.
-/

namespace CompPoly

namespace GuruswamiSudan

theorem cpoly_val_coeff_ofArray {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (coeffs : Array R) (i : Nat) :
    (CPolynomial.ofArray coeffs).val.coeff i = coeffs.getD i 0 := by
  unfold CPolynomial.ofArray
  exact CPolynomial.Raw.Trim.coeff_eq_coeff coeffs i

theorem cpoly_coeff_eq_zero_of_size_le {R : Type*} [Zero R]
    (p : CPolynomial R) {i : Nat} (h : p.val.size ≤ i) : p.coeff i = 0 := by
  unfold CPolynomial.coeff CPolynomial.Raw.coeff
  rw [Array.getD_eq_getD_getElem?]
  simp [Array.getElem?_eq_none h]

theorem cpoly_size_eq_natDegree_succ_of_ne_zero {R : Type*} [Zero R]
    {p : CPolynomial R} (hp : p ≠ 0) :
    p.val.size = p.natDegree + 1 := by
  unfold CPolynomial.natDegree
  cases hs : p.val.size with
  | zero =>
      have hval : p.val = (#[] : CPolynomial.Raw R) := Array.eq_empty_of_size_eq_zero hs
      apply (hp ?_).elim
      apply CPolynomial.ext
      simpa using hval
  | succ n =>
      simp

theorem cpoly_coeff_natDegree_ne_zero_of_ne_zero {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    {p : CPolynomial R} (hp : p ≠ 0) :
    p.coeff p.natDegree ≠ 0 := by
  have htoPoly : p.toPoly ≠ 0 := (CPolynomial.toPoly_eq_zero_iff p).not.mpr hp
  have hlead : p.toPoly.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr htoPoly
  rw [← CPolynomial.leadingCoeff_toPoly p, CPolynomial.leadingCoeff_eq_coeff_natDegree] at hlead
  exact hlead

theorem cpoly_coeff_eq_zero_of_natDegree_lt {R : Type*} [Zero R]
    (p : CPolynomial R) {i : Nat} (hi : p.natDegree < i) :
    p.coeff i = 0 := by
  by_cases hp : p = 0
  · rw [hp]
    exact CPolynomial.coeff_zero i
  · have hsize := cpoly_size_eq_natDegree_succ_of_ne_zero hp
    exact cpoly_coeff_eq_zero_of_size_le p (by omega)

theorem cpoly_coeff_dropXPower {R : Type*} [Zero R]
    (p : CPolynomial R) (n i : Nat) :
    (CPolynomial.dropXPower p n).coeff i = p.coeff (i + n) := by
  induction n generalizing p i with
  | zero =>
      simp [CPolynomial.dropXPower]
  | succ n ih =>
      rw [CPolynomial.dropXPower, ih, CPolynomial.coeff_divX]
      have h : i + n + 1 = i + (n + 1) := by omega
      rw [h]

theorem cpoly_toPoly_eq_X_pow_mul_dropXPower_of_coeff_eq_zero_lt {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) (n : Nat)
    (hzero : ∀ i, i < n → p.coeff i = 0) :
    p.toPoly = Polynomial.X ^ n * (CPolynomial.dropXPower p n).toPoly := by
  ext i
  rw [← CPolynomial.coeff_toPoly (p := p) (i := i)]
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hn : n ≤ i
  · rw [if_pos hn]
    rw [← CPolynomial.coeff_toPoly (p := CPolynomial.dropXPower p n) (i := i - n)]
    rw [cpoly_coeff_dropXPower]
    congr 1
    omega
  · rw [if_neg hn]
    exact hzero i (Nat.lt_of_not_ge hn)

theorem cbivar_coeff_divXPower {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
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
    have hmaple : (Q.val.map fun coeff ↦ CPolynomial.dropXPower coeff n).size ≤ j := by
      simpa using hjle
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hmaple]
    have hqcoeff : Q.val.coeff j = (0 : CPolynomial R) := by
      unfold CPolynomial.Raw.coeff
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hjle]
      rfl
    rw [hqcoeff]
    change (0 : CPolynomial R).coeff i = (0 : CPolynomial R).coeff (i + n)
    rw [CPolynomial.coeff_zero, CPolynomial.coeff_zero]

theorem cbivar_coeffY_divXPower {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (Q : CBivariate R) (n j : Nat) :
    (CBivariate.divXPower Q n).val.coeff j = CPolynomial.dropXPower (Q.val.coeff j) n := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  change CBivariate.coeff (CBivariate.divXPower Q n) i j =
    (CPolynomial.dropXPower (Q.val.coeff j) n).coeff i
  rw [cbivar_coeff_divXPower, cpoly_coeff_dropXPower]
  rfl

theorem cbivar_coeff_eq_zero_of_y_size_le {R : Type*} [Zero R]
    (Q : CBivariate R) {i j : Nat} (hj : Q.val.size ≤ j) :
    CBivariate.coeff Q i j = 0 := by
  unfold CBivariate.coeff
  have hqcoeff : Q.val.coeff j = (0 : CPolynomial R) := by
    unfold CPolynomial.Raw.coeff
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hj]
    rfl
  rw [hqcoeff]
  exact CPolynomial.coeff_zero i

theorem initialCoefficientPolynomial_coeff_fold {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (Q : CBivariate F) (j : Nat) :
    ∀ (ys : List Nat) (out : CPolynomial F),
      ys.Nodup →
        (List.foldl
          (fun out y ↦ out + CPolynomial.monomial y (CBivariate.coeff Q 0 y))
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

theorem initialCoefficientPolynomial_coeff_of_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) {j : Nat} (hj : j < Q.val.size) :
    (initialCoefficientPolynomial Q).coeff j = CBivariate.coeff Q 0 j := by
  unfold initialCoefficientPolynomial
  rw [initialCoefficientPolynomial_coeff_fold Q j (List.range Q.val.size)
    (0 : CPolynomial F) (List.nodup_range (n := Q.val.size))]
  rw [CPolynomial.coeff_zero]
  simp [hj]

theorem cpoly_xAdicOrder?_some_coeff_ne {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial R} {i : Nat} (h : CPolynomial.xAdicOrder? p = some i) :
    p.coeff i ≠ 0 := by
  unfold CPolynomial.xAdicOrder? at h
  have hp := List.find?_some h
  simpa using hp

theorem cpoly_xAdicOrder?_some_coeff_eq_zero_of_lt {R : Type*}
    [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial R} {order i : Nat}
    (h : CPolynomial.xAdicOrder? p = some order) (hi : i < order) :
    p.coeff i = 0 := by
  unfold CPolynomial.xAdicOrder? at h
  rcases (List.find?_eq_some_iff_getElem.mp h) with
    ⟨_horder, idx, hidx, hget, hbefore⟩
  have hidx_eq : idx = order := by
    simpa [List.getElem_range'_1] using hget
  have hiidx : i < idx := by omega
  have hbeq : (p.coeff i == 0) = true := by
    simpa [List.getElem_range'_1] using hbefore i hiidx
  exact beq_iff_eq.mp hbeq

theorem cpoly_xAdicOrder?_none_eq_zero {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
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

def xAdicStep {R : Type*} [Zero R] [BEq R]
    (Q : CBivariate R) (best : Option Nat) (y : Nat) : Option Nat :=
  match CPolynomial.xAdicOrder? (Q.val.coeff y) with
  | none => best
  | some order =>
      match best with
      | none => some order
      | some current => some (min current order)

def xAdicWitness {R : Type*} [Zero R] (Q : CBivariate R)
    (best : Option Nat) : Prop :=
  ∀ order, best = some order → ∃ y, y < Q.val.size ∧ CBivariate.coeff Q order y ≠ 0

theorem cbivar_xAdicOrder?_step_witness {R : Type*}
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

theorem cbivar_xAdicOrder?_fold_witness {R : Type*}
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

theorem cbivar_xAdicOrder?_some_exists {R : Type*}
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

theorem cbivar_xAdicOrder?_step_some_le_best {R : Type*}
    [Zero R] [BEq R] (Q : CBivariate R) {best : Option Nat} {current result y : Nat}
    (hbest : best = some current) (hstep : xAdicStep Q best y = some result) :
    result ≤ current := by
  subst best
  unfold xAdicStep at hstep
  cases hrow : CPolynomial.xAdicOrder? (Q.val.coeff y) with
  | none =>
      rw [hrow] at hstep
      have hresult : result = current := by simpa using hstep.symm
      omega
  | some rowOrder =>
      rw [hrow] at hstep
      have hresult : result = min current rowOrder := by simpa using hstep.symm
      subst result
      exact Nat.min_le_left current rowOrder

theorem cbivar_xAdicOrder?_step_some_le_row {R : Type*}
    [Zero R] [BEq R] (Q : CBivariate R) {best : Option Nat} {rowOrder result y : Nat}
    (hrow : CPolynomial.xAdicOrder? (Q.val.coeff y) = some rowOrder)
    (hstep : xAdicStep Q best y = some result) :
    result ≤ rowOrder := by
  unfold xAdicStep at hstep
  rw [hrow] at hstep
  cases best with
  | none =>
      have hresult : result = rowOrder := by simpa using hstep.symm
      omega
  | some current =>
      have hresult : result = min current rowOrder := by simpa using hstep.symm
      subst result
      exact Nat.min_le_right current rowOrder

theorem cbivar_xAdicOrder?_fold_some_le_best {R : Type*}
    [Zero R] [BEq R] (Q : CBivariate R) :
    ∀ (ys : List Nat) (best : Option Nat) (current result : Nat),
      best = some current →
        List.foldl (xAdicStep Q) best ys = some result →
          result ≤ current := by
  intro ys
  induction ys with
  | nil =>
      intro best current result hbest hfold
      rw [hbest] at hfold
      have hresult : result = current := by simpa using hfold.symm
      omega
  | cons y ys ih =>
      intro best current result hbest hfold
      simp only [List.foldl_cons] at hfold
      cases hstep : xAdicStep Q best y with
      | none =>
          have hnone : False := by
            subst best
            unfold xAdicStep at hstep
            cases hrow : CPolynomial.xAdicOrder? (Q.val.coeff y) <;> rw [hrow] at hstep <;>
              simp at hstep
          exact hnone.elim
      | some next =>
          rw [hstep] at hfold
          have hresult_le_next := ih (some next) next result rfl hfold
          have hnext_le_current :=
            cbivar_xAdicOrder?_step_some_le_best Q hbest hstep
          exact Nat.le_trans hresult_le_next hnext_le_current

theorem cbivar_xAdicOrder?_fold_some_le_row {R : Type*}
    [Zero R] [BEq R] (Q : CBivariate R) :
    ∀ (ys : List Nat) (best : Option Nat) (result y rowOrder : Nat),
      List.foldl (xAdicStep Q) best ys = some result →
        y ∈ ys →
          CPolynomial.xAdicOrder? (Q.val.coeff y) = some rowOrder →
            result ≤ rowOrder := by
  intro ys
  induction ys with
  | nil =>
      intro best result y rowOrder _hfold hmem _hrow
      simp at hmem
  | cons z zs ih =>
      intro best result y rowOrder hfold hmem hrow
      simp only [List.foldl_cons] at hfold
      simp at hmem
      cases hstep : xAdicStep Q best z with
      | none =>
          rw [hstep] at hfold
          cases hmem with
          | inl hyz =>
              subst y
              unfold xAdicStep at hstep
              rw [hrow] at hstep
              cases best <;> simp at hstep
          | inr hyzs =>
              exact ih none result y rowOrder hfold hyzs hrow
      | some next =>
          rw [hstep] at hfold
          cases hmem with
          | inl hyz =>
              subst y
              have hresult_le_next :=
                cbivar_xAdicOrder?_fold_some_le_best Q zs (some next) next result rfl hfold
              have hnext_le_row :=
                cbivar_xAdicOrder?_step_some_le_row Q hrow hstep
              exact Nat.le_trans hresult_le_next hnext_le_row
          | inr hyzs =>
              exact ih (some next) result y rowOrder hfold hyzs hrow

theorem cbivar_xAdicOrder?_some_coeff_eq_zero_of_lt {R : Type*}
    [Zero R] [BEq R] [LawfulBEq R]
    {Q : CBivariate R} {order i y : Nat}
    (h : CBivariate.xAdicOrder? Q = some order) (hi : i < order) :
    CBivariate.coeff Q i y = 0 := by
  by_cases hy : y < Q.val.size
  · cases hrow : CPolynomial.xAdicOrder? (Q.val.coeff y) with
    | none =>
        unfold CBivariate.coeff
        rw [cpoly_xAdicOrder?_none_eq_zero hrow]
        exact CPolynomial.coeff_zero i
    | some rowOrder =>
        have hle : order ≤ rowOrder := by
          unfold CBivariate.xAdicOrder? at h
          change List.foldl (xAdicStep Q) none (List.range' 0 Q.val.size) = some order at h
          have hmem : y ∈ List.range' 0 Q.val.size := by
            simpa [List.mem_range'] using Nat.succ_le_of_lt hy
          exact cbivar_xAdicOrder?_fold_some_le_row Q
            (List.range' 0 Q.val.size) none order y rowOrder h hmem hrow
        unfold CBivariate.coeff
        exact cpoly_xAdicOrder?_some_coeff_eq_zero_of_lt hrow (Nat.lt_of_lt_of_le hi hle)
  · exact cbivar_coeff_eq_zero_of_y_size_le Q (Nat.le_of_not_lt hy)

theorem cbivar_toPoly_eq_C_X_pow_mul_divXPower_of_xAdicOrder {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {order : Nat} (horder : CBivariate.xAdicOrder? Q = some order) :
    CBivariate.toPoly Q =
      Polynomial.C (Polynomial.X ^ order : Polynomial F) *
        CBivariate.toPoly (CBivariate.divXPower Q order) := by
  ext j n
  rw [CBivariate.coeff_toPoly_Y]
  rw [Polynomial.coeff_C_mul]
  rw [CBivariate.coeff_toPoly_Y]
  rw [cbivar_coeffY_divXPower]
  exact congrArg (fun P : Polynomial F ↦ P.coeff n)
    (cpoly_toPoly_eq_X_pow_mul_dropXPower_of_coeff_eq_zero_lt
      (Q.val.coeff j) order (fun i hi ↦
        cbivar_xAdicOrder?_some_coeff_eq_zero_of_lt (Q := Q) (y := j) horder hi))

theorem cbivar_xAdicOrder?_fold_none {R : Type*}
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

theorem cbivar_xAdicOrder?_none_eq_zero {F : Type*}
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

theorem cpoly_dropXPower_add {R : Type*} [Zero R]
    (p : CPolynomial R) (m n : Nat) :
    CPolynomial.dropXPower (CPolynomial.dropXPower p m) n =
      CPolynomial.dropXPower p (m + n) := by
  induction m generalizing p with
  | zero =>
      simp [CPolynomial.dropXPower]
  | succ m ih =>
      rw [CPolynomial.dropXPower]
      rw [ih]
      rw [show m + 1 + n = (m + n) + 1 by omega]
      simp [CPolynomial.dropXPower]

theorem dropXPower_eq_C_add_X_mul_dropXPower_succ {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (p : CPolynomial F) (depth : Nat) :
    CPolynomial.dropXPower p depth =
      CPolynomial.C (p.coeff depth) +
        CPolynomial.X * CPolynomial.dropXPower p (depth + 1) := by
  let suffix := CPolynomial.dropXPower p depth
  have hcoeff : suffix.coeff 0 = p.coeff depth := by
    dsimp [suffix]
    rw [cpoly_coeff_dropXPower]
    rw [show 0 + depth = depth by omega]
  have hdrop : CPolynomial.dropXPower p (depth + 1) = CPolynomial.divX suffix := by
    dsimp [suffix]
    rw [← cpoly_dropXPower_add p depth 1]
    rfl
  calc
    CPolynomial.dropXPower p depth = suffix := rfl
    _ = CPolynomial.divX suffix * CPolynomial.X + CPolynomial.C (suffix.coeff 0) := by
      rw [CPolynomial.divX_mul_X_add]
    _ = CPolynomial.C (p.coeff depth) +
          CPolynomial.X * CPolynomial.dropXPower p (depth + 1) := by
      rw [hcoeff, hdrop]
      ring

theorem polynomial_monomial_substitution_term {F : Type*} [Field F]
    (a coeff : F) (p : Polynomial F) (x y t : Nat) :
    Polynomial.monomial x coeff *
        ((Polynomial.X * p) ^ t * Polynomial.C a ^ (y - t) *
          Polynomial.C (Nat.choose y t : F)) =
      Polynomial.monomial (x + t) (coeff * (Nat.choose y t : F) * a ^ (y - t)) *
        p ^ t := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial (a := coeff) (n := x)]
  rw [← Polynomial.C_mul_X_pow_eq_monomial
    (a := coeff * (Nat.choose y t : F) * a ^ (y - t)) (n := x + t)]
  simp only [mul_pow, Polynomial.C_mul, Polynomial.C_pow]
  rw [show Polynomial.X ^ (x + t) = Polynomial.X ^ x * Polynomial.X ^ t by rw [pow_add]]
  ring_nf

theorem polynomial_monomial_substitution_sum {F : Type*} [Field F]
    (a coeff : F) (p : Polynomial F) (x y : Nat) :
    (∑ t ∈ Finset.range (y + 1),
        Polynomial.monomial (x + t) (coeff * (Nat.choose y t : F) * a ^ (y - t)) *
          p ^ t) =
      Polynomial.monomial x coeff * (Polynomial.C a + Polynomial.X * p) ^ y := by
  rw [show Polynomial.C a + Polynomial.X * p = Polynomial.X * p + Polynomial.C a by ring]
  rw [add_pow]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro t ht
  rw [← polynomial_monomial_substitution_term (a := a) (coeff := coeff)
    (p := p) (x := x) (y := y) (t := t)]
  rw [← Polynomial.C_eq_natCast (R := F) (Nat.choose y t)]

theorem foldl_cpoly_toPoly_add {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (f : Nat → CPolynomial F) :
    ∀ (xs : List Nat) (acc : CPolynomial F) (accPoly : Polynomial F),
      acc.toPoly = accPoly →
        (xs.foldl (fun acc x ↦ acc + f x) acc).toPoly =
          xs.foldl (fun acc x ↦ acc + (f x).toPoly) accPoly := by
  intro xs
  induction xs with
  | nil =>
      intro acc accPoly hacc
      simpa using hacc
  | cons x xs ih =>
      intro acc accPoly hacc
      simp only [List.foldl_cons]
      apply ih
      rw [CPolynomial.toPoly_add, hacc]

theorem cpoly_monomial_substitution_sum {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (a coeff : F) (p : CPolynomial F) (x y : Nat) :
    (List.range' 0 (y + 1)).foldl
        (fun acc t ↦
          acc + CPolynomial.monomial (x + t)
            (coeff * (Nat.choose y t : F) * a ^ (y - t)) * p ^ t)
        0 =
      CPolynomial.monomial x coeff * (CPolynomial.C a + CPolynomial.X * p) ^ y := by
  apply (CPolynomial.ringEquiv (R := F)).injective
  change
    ((List.range' 0 (y + 1)).foldl
        (fun acc t ↦
          acc + CPolynomial.monomial (x + t)
            (coeff * (Nat.choose y t : F) * a ^ (y - t)) * p ^ t)
        0).toPoly =
      (CPolynomial.monomial x coeff * (CPolynomial.C a + CPolynomial.X * p) ^ y).toPoly
  rw [foldl_cpoly_toPoly_add
    (fun t ↦
      CPolynomial.monomial (x + t) (coeff * (Nat.choose y t : F) * a ^ (y - t)) *
        p ^ t)
    (List.range' 0 (y + 1)) 0 0 (CPolynomial.toPoly_zero (R := F))]
  rw [← List.range_eq_range']
  rw [list_foldl_add_eq_sum]
  rw [list_sum_map_range_eq_finset_sum]
  simp only [CPolynomial.toPoly_mul, CPolynomial.toPoly_pow, CPolynomial.toPoly_add,
    CPolynomial.C_toPoly, CPolynomial.X_toPoly, zero_add]
  calc
    ∑ x_1 ∈ Finset.range (y + 1),
        (CPolynomial.monomial (x + x_1)
            (coeff * (Nat.choose y x_1 : F) * a ^ (y - x_1))).toPoly * p.toPoly ^ x_1
        = ∑ x_1 ∈ Finset.range (y + 1),
            (Polynomial.monomial (x + x_1)
              (coeff * (Nat.choose y x_1 : F) * a ^ (y - x_1)) : Polynomial F) *
                p.toPoly ^ x_1 := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact congrArg (fun q : Polynomial F ↦ q * p.toPoly ^ i)
            (CPolynomial.monomial_toPoly (R := F) (x + i)
              (coeff * (Nat.choose y i : F) * a ^ (y - i)))
    _ = Polynomial.monomial x coeff * (Polynomial.C a + Polynomial.X * p.toPoly) ^ y := by
          rw [polynomial_monomial_substitution_sum]
    _ = (CPolynomial.monomial x coeff).toPoly *
          (Polynomial.C a + Polynomial.X * p.toPoly) ^ y := by
          rw [show (CPolynomial.monomial x coeff : CPolynomial F).toPoly =
              Polynomial.monomial x coeff from
            CPolynomial.monomial_toPoly (R := F) x coeff]

end GuruswamiSudan

end CompPoly
