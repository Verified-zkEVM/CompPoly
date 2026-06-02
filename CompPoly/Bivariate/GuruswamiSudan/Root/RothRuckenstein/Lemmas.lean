/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Algorithm
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
  exact congrArg (fun P : Polynomial F => P.coeff n)
    (cpoly_toPoly_eq_X_pow_mul_dropXPower_of_coeff_eq_zero_lt
      (Q.val.coeff j) order (fun i hi =>
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

theorem degreeLt_of_degreeLtBool {F : Type*} [Zero F]
    {p : CPolynomial F} {k : Nat} (h : degreeLtBool p k = true) : degreeLt p k := by
  rw [degreeLtBool] at h
  simp at h
  unfold degreeLt CPolynomial.degree
  cases hs : p.val.size with
  | zero => simp
  | succ n =>
      simp
      omega

theorem degreeLtBool_of_degreeLt {F : Type*} [Zero F]
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

theorem cpoly_truncate_coeff {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) (n i : Nat) :
    (CPolynomial.truncate p n).coeff i = if i < n then p.coeff i else 0 := by
  unfold CPolynomial.truncate CPolynomial.ofArray CPolynomial.coeff
  rw [CPolynomial.Raw.Trim.coeff_eq_coeff]
  unfold CPolynomial.Raw.coeff
  simp [Array.getElem?_extract]
  by_cases hin : i < n
  · by_cases hip : i < p.val.size
    · simp [hin, hip]
    · simp [hin, hip]
  · simp [hin]

def polynomialPrefix {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) (n : Nat) : CPolynomial R :=
  CPolynomial.truncate p n

theorem polynomialPrefix_zero {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) : polynomialPrefix p 0 = 0 := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  unfold polynomialPrefix
  rw [cpoly_truncate_coeff]
  simp
  rfl

theorem polynomialPrefix_succ {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (p : CPolynomial F) (depth : Nat) :
    polynomialPrefix p (depth + 1) =
      extendPrefix (polynomialPrefix p depth) depth (p.coeff depth) := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  unfold polynomialPrefix extendPrefix
  rw [cpoly_truncate_coeff, CPolynomial.coeff_add, cpoly_truncate_coeff,
    CPolynomial.coeff_monomial]
  by_cases hi : i = depth
  · subst i
    simp
  · by_cases hlt : i < depth
    · have hltSucc : i < depth + 1 := by omega
      simp [hi, hlt, hltSucc]
    · have hnotSucc : ¬ i < depth + 1 := by omega
      simp [hi, hlt, hnotSucc]

theorem polynomialPrefix_eq_self_of_degreeLt {F : Type*}
    [Zero F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} {k : Nat} (hdegree : degreeLt p k) :
    polynomialPrefix p k = p := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  unfold polynomialPrefix
  rw [cpoly_truncate_coeff]
  by_cases hi : i < k
  · simp [hi]
  · have hb := degreeLtBool_of_degreeLt hdegree
    rw [degreeLtBool] at hb
    simp at hb
    have hsize : p.val.size ≤ i := by omega
    rw [if_neg hi, cpoly_coeff_eq_zero_of_size_le p hsize]

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

theorem list_foldl_add_eq_sum {R : Type*} [AddMonoid R]
    (f : Nat → R) : ∀ (xs : List Nat) (acc : R),
    List.foldl (fun acc i => acc + f i) acc xs = acc + (xs.map f).sum
  | [], acc => by simp
  | x :: xs, acc => by
      rw [List.foldl_cons, list_foldl_add_eq_sum f xs (acc + f x)]
      exact (_root_.add_assoc acc (f x) ((xs.map f).sum))

theorem list_sum_map_range_eq_finset_sum {R : Type*} [AddCommMonoid R]
    (f : Nat → R) : ∀ n : Nat,
    (List.map f (List.range n)).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
      rw [List.sum_range_succ, Finset.sum_range_succ, list_sum_map_range_eq_finset_sum f n]

theorem cpoly_powCoeff_eq_coeff_pow {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) (k n : Nat) :
    CPolynomial.powCoeff p k n = (p ^ k : CPolynomial R).coeff n := by
  induction k generalizing n with
  | zero =>
      simp only [CPolynomial.powCoeff, pow_zero]
      rw [CPolynomial.coeff_one]
  | succ k ih =>
      unfold CPolynomial.powCoeff
      rw [list_foldl_add_eq_sum]
      rw [pow_succ']
      rw [CPolynomial.coeff_mul]
      rw [list_sum_map_range_eq_finset_sum]
      simp [ih]

theorem cpoly_mulPowCoeff_eq_coeff_mul_pow {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (a p : CPolynomial R) (k n : Nat) :
    CPolynomial.mulPowCoeff a p k n = (a * (p ^ k : CPolynomial R)).coeff n := by
  unfold CPolynomial.mulPowCoeff
  rw [list_foldl_add_eq_sum]
  rw [CPolynomial.coeff_mul]
  rw [list_sum_map_range_eq_finset_sum]
  simp [cpoly_powCoeff_eq_coeff_pow]

theorem cpoly_eval_monomial {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (y : Nat) (a c : F) :
    (CPolynomial.monomial y a).eval c = a * c ^ y := by
  rw [CPolynomial.eval_toPoly]
  rw [show (CPolynomial.monomial y a : CPolynomial F).toPoly =
      Polynomial.monomial y a from CPolynomial.monomial_toPoly (R := F) y a]
  simp [Polynomial.eval_monomial]

theorem cpoly_eval_add {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (p q : CPolynomial F) (c : F) :
    CPolynomial.eval c (p + q) = CPolynomial.eval c p + CPolynomial.eval c q := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_add, Polynomial.eval_add,
    ← CPolynomial.eval_toPoly, ← CPolynomial.eval_toPoly]

theorem cpoly_coeff_zero_mul {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (p q : CPolynomial F) :
    (p * q).coeff 0 = p.coeff 0 * q.coeff 0 := by
  rw [CPolynomial.coeff_mul]
  rw [show Finset.range (0 + 1) = Finset.range 1 by rfl]
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_zero, zero_add, tsub_zero]

theorem cpoly_coeff_zero_pow {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (p : CPolynomial F) :
    ∀ n : Nat, (p ^ n : CPolynomial F).coeff 0 = p.coeff 0 ^ n := by
  intro n
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      rw [CPolynomial.coeff_one]
      simp
  | succ n ih =>
      rw [pow_succ, pow_succ, CPolynomial.coeff_mul]
      rw [show Finset.range (0 + 1) = Finset.range 1 by rfl]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_zero, zero_add, tsub_zero]
      rw [ih]

theorem cpoly_coeff_zero_pow_monomial_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (c : F) :
    ∀ n : Nat, ((CPolynomial.monomial 0 c) ^ n : CPolynomial F).coeff 0 = c ^ n := by
  intro n
  rw [cpoly_coeff_zero_pow]
  rw [CPolynomial.coeff_monomial]
  rfl

theorem cpoly_mulPowCoeff_monomial_zero_depth_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (a : CPolynomial F) (c : F) (y : Nat) :
    CPolynomial.mulPowCoeff a (CPolynomial.monomial 0 c) y 0 = a.coeff 0 * c ^ y := by
  rw [cpoly_mulPowCoeff_eq_coeff_mul_pow]
  rw [CPolynomial.coeff_mul]
  rw [show Finset.range (0 + 1) = Finset.range 1 by rfl]
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_zero, zero_add, tsub_zero]
  rw [cpoly_coeff_zero_pow_monomial_zero]

theorem composeY_coeff_zero_zipIdx_eq_range_aux {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (xs : List (CPolynomial F)) (p accPoly : CPolynomial F) (accCoeff : F)
    (offset : Nat) (hacc : accPoly.coeff 0 = accCoeff) :
    List.foldl
        (fun acc y => acc + (xs.getD (y - offset) 0).coeff 0 * p.coeff 0 ^ y)
        accCoeff (List.range' offset xs.length) =
      (List.foldl (fun acc x => acc + x.1 * p ^ x.2) accPoly
        (xs.zipIdx offset)).coeff 0 := by
  induction xs generalizing accPoly accCoeff offset with
  | nil =>
      simp [hacc]
  | cons x xs ih =>
      simp only [List.length_cons, List.zipIdx_cons, List.foldl_cons]
      rw [List.range'_succ, List.foldl_cons]
      rw [show offset - offset = 0 by omega]
      simp only [List.getD_cons_zero]
      rw [List.foldl_congr_of_mem
        (f := fun acc y =>
          acc + ((x :: xs).getD (y - offset) 0).coeff 0 * p.coeff 0 ^ y)
        (g := fun acc y =>
          acc + (xs.getD (y - (offset + 1)) 0).coeff 0 * p.coeff 0 ^ y)
        (List.range' (offset + 1) xs.length)
        (accCoeff + x.coeff 0 * p.coeff 0 ^ offset)
        (fun acc' y hy => by
          have hsub : y - offset = (y - (offset + 1)) + 1 := by
            have hymem := List.mem_range'.mp hy
            omega
          simp [hsub])]
      apply ih
      rw [CPolynomial.coeff_add, cpoly_coeff_zero_mul, cpoly_coeff_zero_pow, hacc]

theorem composeY_coeff_zero_fold_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (coeffs : Array (CPolynomial F)) (p : CPolynomial F) :
    List.foldl (fun acc y => acc + (coeffs.getD y 0).coeff 0 * p.coeff 0 ^ y) 0
        (List.range' 0 coeffs.size) =
      (Array.foldl (fun acc x => acc + x.1 * p ^ x.2) 0 coeffs.zipIdx).coeff 0 := by
  rw [Array.foldl_zipIdx_eq_foldl_toList_zipIdx]
  simpa using
    (composeY_coeff_zero_zipIdx_eq_range_aux coeffs.toList p (0 : CPolynomial F) 0 0
      (by rw [CPolynomial.coeff_zero]))

theorem composeY_coeff_zipIdx_eq_range_aux {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (xs : List (CPolynomial R)) (p accPoly : CPolynomial R) (accCoeff : R)
    (offset n : Nat) (hacc : accPoly.coeff n = accCoeff) :
    List.foldl
        (fun acc y => acc + ((xs.getD (y - offset) 0) * p ^ y).coeff n)
        accCoeff (List.range' offset xs.length) =
      (List.foldl (fun acc x => acc + x.1 * p ^ x.2) accPoly
        (xs.zipIdx offset)).coeff n := by
  induction xs generalizing accPoly accCoeff offset with
  | nil =>
      simp [hacc]
  | cons x xs ih =>
      simp only [List.length_cons, List.zipIdx_cons, List.foldl_cons]
      rw [List.range'_succ, List.foldl_cons]
      rw [show offset - offset = 0 by omega]
      simp only [List.getD_cons_zero]
      rw [List.foldl_congr_of_mem
        (f := fun acc y =>
          acc + (((x :: xs).getD (y - offset) 0) * p ^ y).coeff n)
        (g := fun acc y =>
          acc + ((xs.getD (y - (offset + 1)) 0) * p ^ y).coeff n)
        (List.range' (offset + 1) xs.length)
        (accCoeff + (x * p ^ offset).coeff n)
        (fun acc' y hy => by
          have hsub : y - offset = (y - (offset + 1)) + 1 := by
            have hymem := List.mem_range'.mp hy
            omega
          simp [hsub])]
      apply ih
      rw [CPolynomial.coeff_add, hacc]

theorem composeY_coeff_fold_eq {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (coeffs : Array (CPolynomial R)) (p : CPolynomial R) (n : Nat) :
    List.foldl (fun acc y => acc + ((coeffs.getD y 0) * p ^ y).coeff n) 0
        (List.range' 0 coeffs.size) =
      (Array.foldl (fun acc x => acc + x.1 * p ^ x.2) 0 coeffs.zipIdx).coeff n := by
  rw [Array.foldl_zipIdx_eq_foldl_toList_zipIdx]
  simpa using
    (composeY_coeff_zipIdx_eq_range_aux coeffs.toList p (0 : CPolynomial R) 0 0 n
      (by rw [CPolynomial.coeff_zero]))

theorem composeYCoeff_eq_composeY_coeff {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (Q : CBivariate R) (p : CPolynomial R) (depth : Nat) :
    CBivariate.composeYCoeff Q p depth = (CBivariate.composeY Q p).coeff depth := by
  unfold CBivariate.composeYCoeff CBivariate.composeY CPolynomial.eval
  simp [cpoly_mulPowCoeff_eq_coeff_mul_pow]
  simpa using (composeY_coeff_fold_eq Q.val p depth)

theorem fold_range_coeff_add_mul_pow {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (coeffs : Array (CPolynomial R)) (p : CPolynomial R) :
    ∀ (ys : List Nat) (acc : CPolynomial R) (accCoeff : R) (n : Nat),
      acc.coeff n = accCoeff →
        (List.foldl (fun acc y => acc + coeffs.getD y 0 * p ^ y) acc ys).coeff n =
          List.foldl
            (fun acc y => acc + ((coeffs.getD y 0) * p ^ y).coeff n)
            accCoeff ys := by
  intro ys
  induction ys with
  | nil =>
      intro acc accCoeff n hacc
      simpa using hacc
  | cons y ys ih =>
      intro acc accCoeff n hacc
      simp only [List.foldl_cons]
      apply ih
      rw [CPolynomial.coeff_add, hacc]

theorem composeY_eq_range_fold {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (Q : CBivariate R) (p : CPolynomial R) :
    CBivariate.composeY Q p =
      (List.range' 0 Q.val.size).foldl
        (fun acc y => acc + Q.val.coeff y * p ^ y) 0 := by
  rw [CPolynomial.eq_iff_coeff]
  intro n
  rw [fold_range_coeff_add_mul_pow Q.val p (List.range' 0 Q.val.size) 0 0 n
    (CPolynomial.coeff_zero n)]
  rw [← composeYCoeff_eq_composeY_coeff]
  unfold CBivariate.composeYCoeff
  simp [cpoly_mulPowCoeff_eq_coeff_mul_pow]

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
        (xs.foldl (fun acc x => acc + f x) acc).toPoly =
          xs.foldl (fun acc x => acc + (f x).toPoly) accPoly := by
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
        (fun acc t =>
          acc + CPolynomial.monomial (x + t)
            (coeff * (Nat.choose y t : F) * a ^ (y - t)) * p ^ t)
        0 =
      CPolynomial.monomial x coeff * (CPolynomial.C a + CPolynomial.X * p) ^ y := by
  apply (CPolynomial.ringEquiv (R := F)).injective
  change
    ((List.range' 0 (y + 1)).foldl
        (fun acc t =>
          acc + CPolynomial.monomial (x + t)
            (coeff * (Nat.choose y t : F) * a ^ (y - t)) * p ^ t)
        0).toPoly =
      (CPolynomial.monomial x coeff * (CPolynomial.C a + CPolynomial.X * p) ^ y).toPoly
  rw [foldl_cpoly_toPoly_add
    (fun t =>
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
          exact congrArg (fun q : Polynomial F => q * p.toPoly ^ i)
            (CPolynomial.monomial_toPoly (R := F) (x + i)
              (coeff * (Nat.choose y i : F) * a ^ (y - i)))
    _ = Polynomial.monomial x coeff * (Polynomial.C a + Polynomial.X * p.toPoly) ^ y := by
          rw [polynomial_monomial_substitution_sum]
    _ = (CPolynomial.monomial x coeff).toPoly *
          (Polynomial.C a + Polynomial.X * p.toPoly) ^ y := by
          rw [show (CPolynomial.monomial x coeff : CPolynomial F).toPoly =
              Polynomial.monomial x coeff from
            CPolynomial.monomial_toPoly (R := F) x coeff]

theorem composeY_toPoly {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (p : CPolynomial F) :
    (CBivariate.composeY Q p).toPoly = (CBivariate.toPoly Q).eval p.toPoly := by
  unfold CBivariate.composeY
  rw [CPolynomial.eval_toPoly]
  rw [CBivariate.toPoly_eq_map]
  rw [Polynomial.eval_map]
  exact (Polynomial.eval₂_hom
    (f := (CPolynomial.ringEquiv (R := F)).toRingHom)
    (p := CPolynomial.toPoly Q) (x := p)).symm

theorem initialCoefficientPolynomial_evalHorner_eq_composeYCoeff_monomial_zero
    {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (Q : CBivariate F) (c : F) :
    (initialCoefficientPolynomial Q).evalHorner c =
      CBivariate.composeYCoeff Q (CPolynomial.monomial 0 c) 0 := by
  rw [CPolynomial.eval_horner_eq_eval]
  unfold initialCoefficientPolynomial CBivariate.composeYCoeff
  rw [List.range_eq_range']
  let polyStep : CPolynomial F → Nat → CPolynomial F :=
    fun out y => out + CPolynomial.monomial y (CBivariate.coeff Q 0 y)
  let coeffStep : F → Nat → F :=
    fun acc y => acc + CPolynomial.mulPowCoeff (Q.val.coeff y)
      (CPolynomial.monomial 0 c) y 0
  change CPolynomial.eval c (List.foldl polyStep 0 (List.range' 0 Q.val.size)) =
    List.foldl coeffStep 0 (List.range' 0 Q.val.size)
  have hfold : ∀ (xs : List Nat) (out : CPolynomial F) (acc : F),
      CPolynomial.eval c out = acc →
      CPolynomial.eval c (List.foldl polyStep out xs) = List.foldl coeffStep acc xs := by
    intro xs
    induction xs with
    | nil =>
        intro out acc hacc
        simpa using hacc
    | cons y ys ih =>
        intro out acc hacc
        simp only [List.foldl_cons]
        apply ih
        dsimp [polyStep, coeffStep]
        rw [cpoly_eval_add, hacc, cpoly_eval_monomial,
          cpoly_mulPowCoeff_monomial_zero_depth_zero]
        rfl
  exact hfold (List.range' 0 Q.val.size) 0 0
    (by simp [CPolynomial.eval_toPoly, CPolynomial.toPoly_zero])

theorem composeYCoeff_monomial_zero_eq_composeY_coeff_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (p : CPolynomial F) :
    CBivariate.composeYCoeff Q (CPolynomial.monomial 0 (p.coeff 0)) 0 =
      (CBivariate.composeY Q p).coeff 0 := by
  unfold CBivariate.composeYCoeff CBivariate.composeY CPolynomial.eval
  simp [cpoly_mulPowCoeff_monomial_zero_depth_zero]
  simpa using (composeY_coeff_zero_fold_eq Q.val p)

theorem initialCoefficientPolynomial_eval_eq_composeY_coeff_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (p : CPolynomial F) :
    CPolynomial.eval (p.coeff 0) (initialCoefficientPolynomial Q) =
      (CBivariate.composeY Q p).coeff 0 := by
  rw [← CPolynomial.eval_horner_eq_eval]
  rw [initialCoefficientPolynomial_evalHorner_eq_composeYCoeff_monomial_zero]
  exact composeYCoeff_monomial_zero_eq_composeY_coeff_zero Q p

theorem rootsInFieldForNonzeroEquation_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (fieldRoots : FieldRootContext F) {p : CPolynomial F} {a : F}
    (hp : p ≠ 0) (ha : CPolynomial.eval a p = 0) :
    a ∈ (rootsInFieldForNonzeroEquation fieldRoots p).toList := by
  unfold rootsInFieldForNonzeroEquation
  rw [if_neg]
  · exact fieldRoots.complete p a hp ha
  · intro hbeq
    exact hp (beq_iff_eq.mp hbeq)

theorem composeY_of_composeYHorner_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {Q : CBivariate F} {p : CPolynomial F}
    (h : CBivariate.composeYHorner Q p = 0) : CBivariate.composeY Q p = 0 := by
  simpa [CBivariate.composeY, CBivariate.composeYHorner, CPolynomial.eval_horner_eq_eval] using h

theorem composeYHorner_eq_zero_of_composeY {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {Q : CBivariate F} {p : CPolynomial F}
    (h : CBivariate.composeY Q p = 0) : CBivariate.composeYHorner Q p = 0 := by
  simpa [CBivariate.composeY, CBivariate.composeYHorner, CPolynomial.eval_horner_eq_eval] using h

theorem isRootYDegreeLtBool_of_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {Q : CBivariate F} {p : CPolynomial F} {k : Nat}
    (hdegree : degreeLt p k) (hroot : CBivariate.composeY Q p = 0) :
    isRootYDegreeLtBool Q k p = true := by
  unfold isRootYDegreeLtBool
  rw [degreeLtBool_of_degreeLt hdegree, composeYHorner_eq_zero_of_composeY hroot]
  simp

end GuruswamiSudan

end CompPoly
