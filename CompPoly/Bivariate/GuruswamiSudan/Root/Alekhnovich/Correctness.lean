/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.Alekhnovich.Lemmas
import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Lemmas

/-!
# Alekhnovich Root Search Correctness

Public correctness surface for the Alekhnovich bounded bivariate root backend
[Ale05].

## References

* [M. Alekhnovich, *Linear Diophantine Equations Over Polynomials and Soft
    Decoding of Reed-Solomon Codes*, IEEE Transactions on Information Theory
    51(7), 2257-2265, 2005][Ale05]
-/

namespace CompPoly

namespace GuruswamiSudan

private theorem cpoly_natDegree_mul_le_of_field {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (P Q : CPolynomial F) :
    (P * Q).natDegree ≤ P.natDegree + Q.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_mul,
    CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly]
  exact Polynomial.natDegree_mul_le

private theorem cpoly_natDegree_pow_le_of_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (P : CPolynomial F) {d : Nat} (hP : P.natDegree ≤ d) :
    ∀ n, (P ^ n).natDegree ≤ n * d
  | 0 => by
      rw [pow_zero, CPolynomial.natDegree_toPoly, CPolynomial.toPoly_one]
      simp
  | n + 1 => by
      have hmul :
          (P ^ (n + 1)).natDegree ≤ P.natDegree + (P ^ n).natDegree := by
        rw [pow_succ']
        exact cpoly_natDegree_mul_le_of_field P (P ^ n)
      have hpow := cpoly_natDegree_pow_le_of_le P hP n
      exact le_trans hmul (by
        calc
          P.natDegree + (P ^ n).natDegree ≤ d + n * d := Nat.add_le_add hP hpow
          _ = (n + 1) * d := by
            rw [Nat.succ_mul, Nat.add_comm])

private theorem cpoly_natDegree_le_pred_of_degreeLt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} {k : Nat} (hp : degreeLt p k) :
    p.natDegree ≤ k - 1 := by
  rw [CPolynomial.natDegree_toPoly]
  unfold degreeLt at hp
  by_cases hpzero : p = 0
  · rw [hpzero]
    have hzero : ((0 : CPolynomial F).toPoly) = 0 :=
      (CPolynomial.toPoly_eq_zero_iff (0 : CPolynomial F)).mpr rfl
    rw [hzero]
    simp
  · have hdegCp := CPolynomial.degree_toPoly p
    have hdeg : p.toPoly.degree < (k : WithBot Nat) := by
      rwa [← hdegCp]
    have hpoly_ne : p.toPoly ≠ 0 := (CPolynomial.toPoly_eq_zero_iff p).not.mpr hpzero
    have hnat_lt : p.toPoly.natDegree < k := by
      exact WithBot.coe_lt_coe.mp
        (by simpa [Polynomial.degree_eq_natDegree hpoly_ne] using hdeg)
    omega

private theorem cpoly_mul_coeff_congr_left_of_coeff_eq_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {P Q R : CPolynomial F} {n : Nat}
    (hcoeff : ∀ i, i ≤ n → P.coeff i = Q.coeff i) :
    (P * R).coeff n = (Q * R).coeff n := by
  rw [CPolynomial.coeff_mul, CPolynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [hcoeff i hile]

private theorem cpoly_mulPowCoeff_zero_left {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (P : CPolynomial F) (y n : Nat) :
    CPolynomial.mulPowCoeff (0 : CPolynomial F) P y n = 0 := by
  rw [cpoly_mulPowCoeff_eq_coeff_mul_pow, CPolynomial.zero_mul,
    CPolynomial.coeff_zero]

private theorem cbivar_coeffY_eq_zero_of_y_size_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (Q : CBivariate F) {y : Nat} (hy : Q.val.size ≤ y) :
    Q.val.coeff y = 0 := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  change CBivariate.coeff Q i y = 0
  exact cbivar_coeff_eq_zero_of_y_size_le Q hy

private theorem list_foldl_add_zero_of_forall {F : Type*} [AddMonoid F]
    {xs : List Nat} {f : Nat → F}
    (hzero : ∀ x, x ∈ xs → f x = 0) (acc : F) :
    xs.foldl (fun acc x ↦ acc + f x) acc = acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, hzero x (by simp)]
      simpa only [add_zero] using ih (by
        intro y hy
        exact hzero y (by simp [hy])) acc

private theorem array_foldl_mem_of_mem_step {α β : Type*}
    (xs : Array α) (step : Array β → α → Array β) {x : α} {y : β}
    (hx : x ∈ xs.toList)
    (hstep : ∀ out, y ∈ (step out x).toList)
    (hpres : ∀ out z, y ∈ out.toList → y ∈ (step out z).toList) :
    y ∈ (xs.foldl step #[]).toList := by
  cases xs with
  | mk data =>
      simp at hx ⊢
      have haux : ∀ (data : List α) (acc : Array β),
          y ∈ acc.toList ∨ x ∈ data →
            y ∈ (data.foldl step acc).toList := by
        intro data
        induction data with
        | nil =>
            intro acc h
            simp at h ⊢
            exact h
        | cons z zs ih =>
            intro acc h
            simp only [List.foldl_cons]
            apply ih
            rcases h with hacc | hxdata
            · exact Or.inl (hpres acc z hacc)
            · simp only [List.mem_cons] at hxdata
              cases hxdata with
              | inl hzx =>
                  subst z
                  exact Or.inl (hstep acc)
              | inr hxzs =>
                  exact Or.inr hxzs
      simpa using haux data #[] (Or.inr hx)

private theorem array_foldl_forall_of_forall_step {α β : Type*}
    (P : β → Prop) (xs : Array α) (step : Array β → α → Array β) (init : Array β)
    (hinit : ∀ y, y ∈ init.toList → P y)
    (hstep : ∀ out x y, (∀ z, z ∈ out.toList → P z) → y ∈ (step out x).toList → P y) :
    ∀ y, y ∈ (xs.foldl step init).toList → P y := by
  cases xs with
  | mk data =>
      rw [← Array.foldl_toList]
      induction data generalizing init with
      | nil =>
          intro y hy
          exact hinit y (by simpa using hy)
      | cons x xs ih =>
          simp only [List.foldl_cons]
          apply ih
          intro y hy
          exact hstep init x y hinit hy

private theorem array_foldl_forall_of_forall_step_with_input {α β : Type*}
    (P : β → Prop) (Q : α → Prop) (xs : Array α)
    (step : Array β → α → Array β) (init : Array β)
    (hinit : ∀ y, y ∈ init.toList → P y)
    (hxs : ∀ x, x ∈ xs.toList → Q x)
    (hstep : ∀ out x y,
      (∀ z, z ∈ out.toList → P z) → Q x → y ∈ (step out x).toList → P y) :
    ∀ y, y ∈ (xs.foldl step init).toList → P y := by
  cases xs with
  | mk data =>
      simp at hxs ⊢
      have hdata : ∀ x, x ∈ data → Q x := hxs
      clear hxs
      induction data generalizing init with
      | nil =>
          intro y hy
          exact hinit y (by simpa using hy)
      | cons x xs ih =>
          simp only [List.foldl_cons]
          apply ih
          · intro y hy
            exact hstep init x y hinit (hdata x (by simp)) hy
          · intro z hz
            exact hdata z (by simp [hz])

private theorem composeYCoeff_eq_fold_range_of_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (Q : CBivariate F) (p : CPolynomial F) (n : Nat) {M : Nat}
    (hM : Q.val.size ≤ M) :
    CBivariate.composeYCoeff Q p n =
      (List.range' 0 M).foldl
        (fun acc y ↦ acc + CPolynomial.mulPowCoeff (Q.val.coeff y) p y n) 0 := by
  unfold CBivariate.composeYCoeff
  have hsplit : List.range' 0 M =
      List.range' 0 Q.val.size ++ List.range' Q.val.size (M - Q.val.size) := by
    have h := List.range'_append (s := 0) (m := Q.val.size)
      (n := M - Q.val.size) (step := 1)
    have hsum : Q.val.size + (M - Q.val.size) = M := Nat.add_sub_of_le hM
    simpa [hsum] using h.symm
  rw [hsplit, List.foldl_append]
  symm
  apply list_foldl_add_zero_of_forall
  intro y hy
  rcases List.mem_range'.mp hy with ⟨offset, _hoffset, rfl⟩
  have hyge : Q.val.size ≤ Q.val.size + 1 * offset := by omega
  rw [cbivar_coeffY_eq_zero_of_y_size_le Q hyge,
    cpoly_mulPowCoeff_zero_left]

private theorem composeY_coeff_congr_of_coeff_eq_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {Q R : CBivariate F} {p : CPolynomial F} {n : Nat}
    (hcoeff : ∀ i j, i ≤ n → CBivariate.coeff Q i j = CBivariate.coeff R i j) :
    (CBivariate.composeY Q p).coeff n = (CBivariate.composeY R p).coeff n := by
  rw [← composeYCoeff_eq_composeY_coeff Q p n,
    ← composeYCoeff_eq_composeY_coeff R p n]
  let M := max Q.val.size R.val.size
  rw [composeYCoeff_eq_fold_range_of_le Q p n
      (Nat.le_max_left Q.val.size R.val.size),
    composeYCoeff_eq_fold_range_of_le R p n
      (Nat.le_max_right Q.val.size R.val.size)]
  apply List.foldl_congr_of_mem
  intro _acc y _hy
  congr 1
  rw [cpoly_mulPowCoeff_eq_coeff_mul_pow, cpoly_mulPowCoeff_eq_coeff_mul_pow]
  apply cpoly_mul_coeff_congr_left_of_coeff_eq_le
  intro i hi
  simpa [CBivariate.coeff] using hcoeff i y hi

private theorem cbivar_coeff_add {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (Q R : CBivariate F) (i j : Nat) :
    CBivariate.coeff (Q + R) i j = CBivariate.coeff Q i j + CBivariate.coeff R i j := by
  have houter :=
    congrArg (fun row : CPolynomial F ↦ CPolynomial.coeff row i)
      (CPolynomial.coeff_add
        (Q : CPolynomial (CPolynomial F)) (R : CPolynomial (CPolynomial F)) j)
  exact houter.trans
    (CPolynomial.coeff_add (CPolynomial.coeff Q j) (CPolynomial.coeff R j) i)

private theorem cbivar_coeff_truncateX_of_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (Q : CBivariate F) {N i j : Nat} (hi : i < N) :
    CBivariate.coeff (CBivariate.truncateX Q N) i j = CBivariate.coeff Q i j := by
  rw [cbivar_coeff_truncateX]
  simp [hi]

private theorem cbivar_coeff_monomial_truncate_of_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (r : Nat) (P : CPolynomial F) {N i j : Nat} (hi : i < N) :
    CBivariate.coeff (CPolynomial.monomial r (CPolynomial.truncate P N) : CBivariate F) i j =
      CBivariate.coeff (CPolynomial.monomial r P : CBivariate F) i j := by
  change (CPolynomial.coeff
      (CPolynomial.monomial r (CPolynomial.truncate P N) : CBivariate F) j).coeff i =
    (CPolynomial.coeff (CPolynomial.monomial r P : CBivariate F) j).coeff i
  rw [CPolynomial.coeff_monomial, CPolynomial.coeff_monomial]
  by_cases hj : j = r
  · subst j
    simp only [eq_self, if_true]
    rw [cpoly_truncate_coeff]
    simp [hi]
  · simp [hj]

private theorem substituteYPolynomialPlusXPowerYTruncated_coeff_eq_of_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (f : CPolynomial F) (t N : Nat) {i j : Nat} (hi : i < N) :
    CBivariate.coeff (substituteYPolynomialPlusXPowerYTruncated Q f t N) i j =
      CBivariate.coeff (substituteYPolynomialPlusXPowerY Q f t) i j := by
  let lowEq : CBivariate F → CBivariate F → Prop :=
    fun A B ↦ ∀ x y, x < N → CBivariate.coeff A x y = CBivariate.coeff B x y
  have hzero : lowEq 0 0 := by
    intro x y _hx
    simp [CBivariate.coeff]
  have hinner :
      ∀ (coeffY : CPolynomial F) (y : Nat) (rs : List Nat)
        (outT outE accE : CBivariate F),
        lowEq outT (outE + accE) →
          lowEq
            (rs.foldl
              (fun out r ↦
                let term := CPolynomial.truncate
                  (shiftedSubstitutionCoeffTerm coeffY f t y r) N
                let contribution : CBivariate F := CPolynomial.monomial r term
                CBivariate.truncateX (out + contribution) N)
              outT)
            (outE +
              rs.foldl
                (fun out r ↦
                  let contribution : CBivariate F := CPolynomial.monomial r
                    (shiftedSubstitutionCoeffTerm coeffY f t y r)
                  out + contribution)
                accE) := by
    intro coeffY y rs
    induction rs with
    | nil =>
        intro outT outE accE h
        simpa using h
    | cons r rs ih =>
        intro outT outE accE h
        simp only [List.foldl_cons]
        apply ih
        intro x z hx
        rw [cbivar_coeff_truncateX_of_lt _ hx]
        rw [cbivar_coeff_add, h x z hx, cbivar_coeff_add, cbivar_coeff_add]
        rw [cbivar_coeff_monomial_truncate_of_lt r
          (shiftedSubstitutionCoeffTerm coeffY f t y r) hx]
        rw [cbivar_coeff_add]
        ring
  have houter :
      ∀ (ys : List Nat) (outT outE : CBivariate F),
        lowEq outT outE →
          lowEq
            (ys.foldl
              (fun out y ↦
                let coeffY := Q.val.coeff y
                (List.range (y + 1)).foldl
                  (fun out r ↦
                    let term := CPolynomial.truncate
                      (shiftedSubstitutionCoeffTerm coeffY f t y r) N
                    let contribution : CBivariate F := CPolynomial.monomial r term
                    CBivariate.truncateX (out + contribution) N)
                  out)
              outT)
            (ys.foldl
              (fun out y ↦
                let coeffY := Q.val.coeff y
                out + (List.range (y + 1)).foldl
                  (fun out r ↦
                    let contribution : CBivariate F := CPolynomial.monomial r
                      (shiftedSubstitutionCoeffTerm coeffY f t y r)
                    out + contribution)
                  0)
              outE) := by
    intro ys
    induction ys with
    | nil =>
        intro outT outE h
        simpa using h
    | cons y ys ih =>
        intro outT outE h
        simp only [List.foldl_cons]
        apply ih
        apply hinner
        intro x z hx
        rw [cbivar_coeff_add]
        have hzeroCoeff : CBivariate.coeff (0 : CBivariate F) x z = 0 := by
          change CPolynomial.coeff (CPolynomial.coeff (0 : CBivariate F) z) x = 0
          have hrow : CPolynomial.coeff (0 : CBivariate F) z = (0 : CPolynomial F) :=
            CPolynomial.coeff_zero z
          rw [hrow]
          exact CPolynomial.coeff_zero x
        rw [hzeroCoeff, add_zero]
        exact h x z hx
  unfold substituteYPolynomialPlusXPowerYTruncated substituteYPolynomialPlusXPowerY
  exact houter (List.range' 0 Q.val.size) 0 0 hzero i j hi

private theorem cpoly_coeff_mul_X_pow {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (q : CPolynomial F) (n x : Nat) :
    (q * CPolynomial.X ^ n).coeff (x + n) = q.coeff x := by
  rw [CPolynomial.coeff_toPoly]
  rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
  rw [mul_comm]
  rw [Polynomial.coeff_X_pow_mul]
  rw [← CPolynomial.coeff_toPoly]

private theorem cpoly_coeff_mul_X_pow_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (q : CPolynomial F) {n : Nat} (hn : 0 < n) :
    (q * CPolynomial.X ^ n).coeff 0 = 0 := by
  rw [CPolynomial.coeff_toPoly]
  rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
  rw [mul_comm]
  have hne : ¬ 0 = n := by omega
  simp [hne]

private theorem cpoly_C_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] :
    CPolynomial.C (1 : F) = 1 := by
  apply CPolynomial.ringEquiv.injective
  change (CPolynomial.C (1 : F)).toPoly = (1 : CPolynomial F).toPoly
  rw [CPolynomial.C_toPoly, CPolynomial.toPoly_one, Polynomial.C_1]

private theorem shiftedSubstitutionCoeffTerm_top_coeff {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (coeffY f : CPolynomial F) (t y x : Nat) :
    (shiftedSubstitutionCoeffTerm coeffY f t y y).coeff (x + t * y) =
      coeffY.coeff x := by
  unfold shiftedSubstitutionCoeffTerm
  rw [Nat.sub_self]
  simp only [Nat.choose_self, Nat.cast_one, pow_zero]
  rw [cpoly_C_one]
  simpa [mul_assoc] using cpoly_coeff_mul_X_pow coeffY (t * y) x

private theorem shiftedSubstitutionCoeffTerm_coeff_zero_of_r_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (coeffY f : CPolynomial F) (t y r : Nat)
    (ht : 0 < t) (hr : 0 < r) :
    (shiftedSubstitutionCoeffTerm coeffY f t y r).coeff 0 = 0 := by
  unfold shiftedSubstitutionCoeffTerm
  have hpow : 0 < t * r := Nat.mul_pos ht hr
  simpa [mul_assoc] using
    cpoly_coeff_mul_X_pow_zero
      (coeffY * CPolynomial.C (Nat.choose y r : F) * f ^ (y - r)) hpow

private theorem shiftedSubstitution_inner_coeff_target {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (coeffY f : CPolynomial F) (t y x : Nat) (out : CBivariate F) :
    CBivariate.coeff
        ((List.range (y + 1)).foldl
          (fun (out : CBivariate F) r ↦
            let contribution : CBivariate F := CPolynomial.monomial r
              (shiftedSubstitutionCoeffTerm coeffY f t y r)
            out + contribution)
          out)
        (x + t * y) y =
      CBivariate.coeff out (x + t * y) y + coeffY.coeff x := by
  let step : CBivariate F → Nat → CBivariate F :=
    fun out r ↦
      let contribution : CBivariate F := CPolynomial.monomial r
        (shiftedSubstitutionCoeffTerm coeffY f t y r)
      out + contribution
  let coeffStep : F → Nat → F :=
    fun acc r ↦ acc + if r = y then coeffY.coeff x else 0
  change CBivariate.coeff (List.foldl step out (List.range (y + 1))) (x + t * y) y =
    CBivariate.coeff out (x + t * y) y + coeffY.coeff x
  have hfold : ∀ rs out acc,
      CBivariate.coeff out (x + t * y) y = acc →
      CBivariate.coeff (List.foldl step out rs) (x + t * y) y =
        List.foldl coeffStep acc rs := by
    intro rs
    induction rs with
    | nil => intro out acc h; simpa using h
    | cons r rs ih =>
        intro out acc h
        simp only [List.foldl_cons]
        apply ih
        dsimp [step, coeffStep]
        let contribution : CBivariate F := CPolynomial.monomial r
          (shiftedSubstitutionCoeffTerm coeffY f t y r)
        change CBivariate.coeff (out + contribution) (x + t * y) y =
          acc + if r = y then coeffY.coeff x else 0
        rw [CBivariate.coeff_add]
        change CBivariate.coeff out (x + t * y) y +
            CPolynomial.coeff
              (CPolynomial.coeff
                (CPolynomial.monomial r
                  (shiftedSubstitutionCoeffTerm coeffY f t y r) : CBivariate F) y)
              (x + t * y) =
          acc + if r = y then coeffY.coeff x else 0
        rw [CPolynomial.coeff_monomial]
        rw [h]
        by_cases hry : r = y
        · subst r
          rw [if_pos rfl, if_pos rfl]
          rw [shiftedSubstitutionCoeffTerm_top_coeff]
        · have hyr : y ≠ r := fun h ↦ hry h.symm
          simp [hyr, hry]
          change (0 : CPolynomial F).coeff (x + t * y) = 0
          rw [CPolynomial.coeff_zero]
  rw [hfold (List.range (y + 1)) out (CBivariate.coeff out (x + t * y) y) rfl]
  rw [List.range_eq_range']
  rw [DenseMatrix.foldl_range_one_special
      (F := F) (pivot := y) (coeffY.coeff x) 0 (y + 1)
      (CBivariate.coeff out (x + t * y) y)]
  have hin : 0 ≤ y ∧ y < 0 + (y + 1) := by omega
  simp [hin]

private theorem shiftedSubstitution_inner_coeff_zero_of_y_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (coeffY f : CPolynomial F) (t y y₀ i : Nat) (out : CBivariate F)
    (hy₀ : y₀ < y) :
    CBivariate.coeff
        ((List.range (y₀ + 1)).foldl
          (fun (out : CBivariate F) r ↦
            let contribution : CBivariate F := CPolynomial.monomial r
              (shiftedSubstitutionCoeffTerm coeffY f t y₀ r)
            out + contribution)
          out)
        i y =
      CBivariate.coeff out i y := by
  let step : CBivariate F → Nat → CBivariate F :=
    fun out r ↦
      let contribution : CBivariate F := CPolynomial.monomial r
        (shiftedSubstitutionCoeffTerm coeffY f t y₀ r)
      out + contribution
  change CBivariate.coeff (List.foldl step out (List.range (y₀ + 1))) i y =
    CBivariate.coeff out i y
  have hfold : ∀ rs out,
      (∀ r, r ∈ rs → r < y) →
      CBivariate.coeff (List.foldl step out rs) i y =
        CBivariate.coeff out i y := by
    intro rs
    induction rs with
    | nil => intro out _hrs; rfl
    | cons r rs ih =>
        intro out hrs
        simp only [List.foldl_cons]
        rw [ih]
        · dsimp [step]
          let contribution : CBivariate F := CPolynomial.monomial r
            (shiftedSubstitutionCoeffTerm coeffY f t y₀ r)
          change CBivariate.coeff (out + contribution) i y =
            CBivariate.coeff out i y
          rw [CBivariate.coeff_add]
          change CBivariate.coeff out i y +
              CPolynomial.coeff
                (CPolynomial.coeff
                  (CPolynomial.monomial r
                    (shiftedSubstitutionCoeffTerm coeffY f t y₀ r) : CBivariate F) y)
                i =
            CBivariate.coeff out i y
          rw [CPolynomial.coeff_monomial]
          have hyr : y ≠ r := by
            have hrt : r < y := hrs r (by simp)
            omega
          simp [hyr]
          change (0 : CPolynomial F).coeff i = 0
          rw [CPolynomial.coeff_zero]
        · intro z hz
          exact hrs z (by simp [hz])
  apply hfold
  intro r hr
  have hrlt : r < y₀ + 1 := List.mem_range.mp hr
  omega

private theorem shiftedSubstitution_inner_coeff_zero_of_x_zero_y_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (coeffY f : CPolynomial F) (t y₀ y : Nat) (out : CBivariate F)
    (ht : 0 < t) (hy : 0 < y) :
    CBivariate.coeff
        ((List.range (y₀ + 1)).foldl
          (fun (out : CBivariate F) r ↦
            let contribution : CBivariate F := CPolynomial.monomial r
              (shiftedSubstitutionCoeffTerm coeffY f t y₀ r)
            out + contribution)
          out)
        0 y =
      CBivariate.coeff out 0 y := by
  let step : CBivariate F → Nat → CBivariate F :=
    fun out r ↦
      let contribution : CBivariate F := CPolynomial.monomial r
        (shiftedSubstitutionCoeffTerm coeffY f t y₀ r)
      out + contribution
  change CBivariate.coeff (List.foldl step out (List.range (y₀ + 1))) 0 y =
    CBivariate.coeff out 0 y
  have hfold : ∀ rs out,
      CBivariate.coeff (List.foldl step out rs) 0 y =
        CBivariate.coeff out 0 y := by
    intro rs
    induction rs with
    | nil => intro out; rfl
    | cons r rs ih =>
        intro out
        simp only [List.foldl_cons]
        rw [ih]
        dsimp [step]
        let contribution : CBivariate F := CPolynomial.monomial r
          (shiftedSubstitutionCoeffTerm coeffY f t y₀ r)
        change CBivariate.coeff (out + contribution) 0 y =
          CBivariate.coeff out 0 y
        rw [CBivariate.coeff_add]
        change CBivariate.coeff out 0 y +
            CPolynomial.coeff
              (CPolynomial.coeff
                (CPolynomial.monomial r
                  (shiftedSubstitutionCoeffTerm coeffY f t y₀ r) : CBivariate F) y)
              0 =
          CBivariate.coeff out 0 y
        rw [CPolynomial.coeff_monomial]
        by_cases hyr : y = r
        · subst r
          simp [shiftedSubstitutionCoeffTerm_coeff_zero_of_r_pos coeffY f t y₀ y ht hy]
        · rw [if_neg hyr]
          rw [CPolynomial.coeff_zero, add_zero]
  exact hfold (List.range (y₀ + 1)) out

private theorem substituteYPolynomialPlusXPowerY_coeff_top {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (f : CPolynomial F) (t y x : Nat)
    (hQsize : Q.val.size = y + 1) :
    CBivariate.coeff (substituteYPolynomialPlusXPowerY Q f t) (x + t * y) y =
      (Q.val.coeff y).coeff x := by
  unfold substituteYPolynomialPlusXPowerY
  rw [hQsize]
  let outerStep : CBivariate F → Nat → CBivariate F :=
    fun out y₀ ↦
      let coeffY := Q.val.coeff y₀
      out + (List.range (y₀ + 1)).foldl
        (fun (out : CBivariate F) r ↦
          let contribution : CBivariate F := CPolynomial.monomial r
            (shiftedSubstitutionCoeffTerm coeffY f t y₀ r)
          out + contribution)
        0
  let coeffStep : F → Nat → F :=
    fun acc y₀ ↦ acc + if y₀ = y then (Q.val.coeff y).coeff x else 0
  change CBivariate.coeff (List.foldl outerStep 0 (List.range' 0 (y + 1)))
      (x + t * y) y = (Q.val.coeff y).coeff x
  have hfold : ∀ ys out acc,
      (∀ y₀, y₀ ∈ ys → y₀ < y + 1) →
      CBivariate.coeff out (x + t * y) y = acc →
      CBivariate.coeff (List.foldl outerStep out ys) (x + t * y) y =
        List.foldl coeffStep acc ys := by
    intro ys
    induction ys with
    | nil => intro out acc _hys h; simpa using h
    | cons y₀ ys ih =>
        intro out acc hys h
        simp only [List.foldl_cons]
        apply ih
        · intro z hz
          exact hys z (by simp [hz])
        dsimp [outerStep, coeffStep]
        let inner : CBivariate F :=
          (List.range (y₀ + 1)).foldl
            (fun (out : CBivariate F) r ↦
              let contribution : CBivariate F := CPolynomial.monomial r
                (shiftedSubstitutionCoeffTerm (Q.val.coeff y₀) f t y₀ r)
              out + contribution)
            0
        change CBivariate.coeff (out + inner) (x + t * y) y =
          acc + if y₀ = y then (Q.val.coeff y).coeff x else 0
        rw [CBivariate.coeff_add]
        rw [h]
        have hy₀lt : y₀ < y + 1 := hys y₀ (by simp)
        by_cases hy₀ : y₀ = y
        · subst y₀
          rw [shiftedSubstitution_inner_coeff_target]
          rw [CBivariate.coeff_zero]
          simp
        · have hy₀_lt_y : y₀ < y := by omega
          rw [shiftedSubstitution_inner_coeff_zero_of_y_lt
            (Q.val.coeff y₀) f t y y₀ (x + t * y) (0 : CBivariate F) hy₀_lt_y]
          rw [CBivariate.coeff_zero]
          simp [hy₀]
  rw [hfold (List.range' 0 (y + 1)) 0 0
    (by
      intro z hz
      have hzlt := (List.mem_range'_1.mp hz).2
      omega)
    (CBivariate.coeff_zero (x + t * y) y)]
  rw [DenseMatrix.foldl_range_one_special
      (F := F) (pivot := y) ((Q.val.coeff y).coeff x) 0 (y + 1) 0]
  have hin : 0 ≤ y ∧ y < 0 + (y + 1) := by omega
  simp [hin]

private theorem substituteYPolynomialPlusXPowerY_coeff_zero_of_y_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (f : CPolynomial F) (t y : Nat)
    (ht : 0 < t) (hy : 0 < y) :
    CBivariate.coeff (substituteYPolynomialPlusXPowerY Q f t) 0 y = 0 := by
  unfold substituteYPolynomialPlusXPowerY
  let outerStep : CBivariate F → Nat → CBivariate F :=
    fun out y₀ ↦
      let coeffY := Q.val.coeff y₀
      out + (List.range (y₀ + 1)).foldl
        (fun (out : CBivariate F) r ↦
          let contribution : CBivariate F := CPolynomial.monomial r
            (shiftedSubstitutionCoeffTerm coeffY f t y₀ r)
          out + contribution)
        0
  change CBivariate.coeff (List.foldl outerStep 0 (List.range' 0 Q.val.size)) 0 y = 0
  have hfold : ∀ ys out,
      CBivariate.coeff out 0 y = 0 →
        CBivariate.coeff (List.foldl outerStep out ys) 0 y = 0 := by
    intro ys
    induction ys with
    | nil =>
        intro out h
        simpa using h
    | cons y₀ ys ih =>
        intro out h
        simp only [List.foldl_cons]
        apply ih
        dsimp [outerStep]
        let inner : CBivariate F :=
          (List.range (y₀ + 1)).foldl
            (fun (out : CBivariate F) r ↦
              let contribution : CBivariate F := CPolynomial.monomial r
                (shiftedSubstitutionCoeffTerm (Q.val.coeff y₀) f t y₀ r)
              out + contribution)
            0
        change CBivariate.coeff (out + inner) 0 y = 0
        rw [CBivariate.coeff_add, h]
        have hinner : CBivariate.coeff inner 0 y = 0 := by
          dsimp [inner]
          change CBivariate.coeff
            ((List.range (y₀ + 1)).foldl
              (fun (out : CBivariate F) r ↦
                let contribution : CBivariate F := CPolynomial.monomial r
                  (shiftedSubstitutionCoeffTerm (Q.val.coeff y₀) f t y₀ r)
                out + contribution)
              0) 0 y = 0
          rw [shiftedSubstitution_inner_coeff_zero_of_x_zero_y_pos
            (Q.val.coeff y₀) f t y₀ y (0 : CBivariate F) ht hy]
          exact CBivariate.coeff_zero 0 y
        rw [hinner]
        simp
  exact hfold (List.range' 0 Q.val.size) 0 (CBivariate.coeff_zero 0 y)

private theorem substituteYPolynomialPlusXPowerYTruncated_coeff_zero_of_y_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (f : CPolynomial F) {t N y : Nat}
    (hN : 0 < N) (ht : 0 < t) (hy : 0 < y) :
    CBivariate.coeff (substituteYPolynomialPlusXPowerYTruncated Q f t N) 0 y = 0 := by
  rw [substituteYPolynomialPlusXPowerYTruncated_coeff_eq_of_lt Q f t N hN]
  exact substituteYPolynomialPlusXPowerY_coeff_zero_of_y_pos Q f t y ht hy

private theorem substituteYPolynomialPlusXPowerY_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} (f : CPolynomial F) (t : Nat) (hQ : Q ≠ 0) :
    substituteYPolynomialPlusXPowerY Q f t ≠ 0 := by
  intro hzero
  let y := Q.natDegree
  let coeffY := Q.val.coeff y
  have hQsize : Q.val.size = y + 1 := cpoly_size_eq_natDegree_succ_of_ne_zero hQ
  have hcoeffY_ne : coeffY ≠ 0 := by
    dsimp [coeffY, y]
    exact cpoly_coeff_natDegree_ne_zero_of_ne_zero hQ
  let x := coeffY.natDegree
  have hcoeff_ne : coeffY.coeff x ≠ 0 :=
    cpoly_coeff_natDegree_ne_zero_of_ne_zero hcoeffY_ne
  have htop :
      CBivariate.coeff (substituteYPolynomialPlusXPowerY Q f t) (x + t * y) y =
        coeffY.coeff x := by
    simpa [coeffY] using substituteYPolynomialPlusXPowerY_coeff_top Q f t y x hQsize
  have hzeroCoeff :
      CBivariate.coeff (substituteYPolynomialPlusXPowerY Q f t) (x + t * y) y = 0 := by
    rw [hzero]
    exact CBivariate.coeff_zero (x + t * y) y
  rw [htop] at hzeroCoeff
  exact hcoeff_ne hzeroCoeff

private theorem shiftPolynomialByXPower_coeff {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (q : CPolynomial F) (t i : Nat) :
    (shiftPolynomialByXPower q t).coeff i = if t ≤ i then q.coeff (i - t) else 0 := by
  unfold shiftPolynomialByXPower
  rw [CPolynomial.coeff_toPoly]
  rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hti : t ≤ i
  · rw [if_pos hti]
    rw [← CPolynomial.coeff_toPoly]
    simp [hti]
  · rw [if_neg hti]
    simp [hti]

private theorem polynomialPrefix_add_shift_dropXPower {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (p : CPolynomial F) (t : Nat) :
    polynomialPrefix p t + shiftPolynomialByXPower (CPolynomial.dropXPower p t) t = p := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  rw [CPolynomial.coeff_add, shiftPolynomialByXPower_coeff]
  unfold polynomialPrefix
  rw [cpoly_truncate_coeff]
  by_cases hit : i < t
  · rw [if_pos hit]
    have hnot : ¬ t ≤ i := Nat.not_le_of_gt hit
    rw [if_neg hnot]
    simp
  · rw [if_neg hit]
    have hle : t ≤ i := Nat.le_of_not_lt hit
    rw [if_pos hle]
    rw [cpoly_coeff_dropXPower]
    rw [show i - t + t = i by omega]
    simp

private theorem rootPrefix_add_shift_dropXPower_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {p : CPolynomial F} {rootPrefix : RootPrefix F}
    (hmatch : MatchesRootPrefix p rootPrefix) :
    rootPrefix.prefixPoly +
        shiftPolynomialByXPower (CPolynomial.dropXPower p rootPrefix.precision)
          rootPrefix.precision =
      p := by
  unfold MatchesRootPrefix MatchesPrefix at hmatch
  rw [← hmatch]
  exact polynomialPrefix_add_shift_dropXPower p rootPrefix.precision

private theorem polynomialPrefix_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (p : CPolynomial F) :
    polynomialPrefix p 1 = CPolynomial.C (p.coeff 0) := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  unfold polynomialPrefix
  rw [cpoly_truncate_coeff]
  rw [CPolynomial.coeff_C]
  cases i with
  | zero => simp
  | succ i => simp

private theorem dropXPower_size_le {F : Type*} [Zero F]
    (p : CPolynomial F) (t : Nat) :
    (CPolynomial.dropXPower p t).val.size ≤ p.val.size - t := by
  induction t generalizing p with
  | zero => simp [CPolynomial.dropXPower]
  | succ t ih =>
      rw [CPolynomial.dropXPower]
      by_cases hp : p.val.size = 0
      · have hdivSize : (CPolynomial.divX p).val.size = 0 := by
          unfold CPolynomial.divX
          simp [hp]
        have h := ih (CPolynomial.divX p)
        rw [hdivSize] at h
        omega
      · have hpos : p.val.size > 0 := Nat.pos_of_ne_zero hp
        have hdivlt := CPolynomial.divX_size_lt (p := p) hpos
        have h := ih (CPolynomial.divX p)
        omega

private theorem cpoly_natDegree_dropXPower_add_le_of_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (p : CPolynomial F) (t : Nat)
    (hdrop : CPolynomial.dropXPower p t ≠ 0) :
    (CPolynomial.dropXPower p t).natDegree + t ≤ p.natDegree := by
  have hcoeffDrop :
      (CPolynomial.dropXPower p t).coeff
        (CPolynomial.dropXPower p t).natDegree ≠ 0 :=
    cpoly_coeff_natDegree_ne_zero_of_ne_zero hdrop
  have hcoeff :
      p.coeff ((CPolynomial.dropXPower p t).natDegree + t) ≠ 0 := by
    rwa [← cpoly_coeff_dropXPower p t (CPolynomial.dropXPower p t).natDegree]
  exact CPolynomial.le_natDegree_of_ne_zero hcoeff

private theorem degreeLt_dropXPower_of_degreeLt_of_le {F : Type*}
    [Zero F] {p : CPolynomial F} {k t : Nat}
    (hdegree : degreeLt p k) (htk : t ≤ k) :
    degreeLt (CPolynomial.dropXPower p t) (k - t) := by
  apply degreeLt_of_degreeLtBool
  rw [degreeLtBool]
  have hb := degreeLtBool_of_degreeLt hdegree
  rw [degreeLtBool] at hb
  simp at hb ⊢
  have hs := dropXPower_size_le p t
  omega

private theorem polynomialPrefix_add_shift_prefix_dropXPower {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (p : CPolynomial F) (t u : Nat) :
    polynomialPrefix p (t + u) =
      polynomialPrefix p t +
        shiftPolynomialByXPower (polynomialPrefix (CPolynomial.dropXPower p t) u) t := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  rw [CPolynomial.coeff_add, shiftPolynomialByXPower_coeff]
  unfold polynomialPrefix
  rw [cpoly_truncate_coeff]
  by_cases hi_tu : i < t + u
  · rw [if_pos hi_tu]
    by_cases hti : t ≤ i
    · rw [if_pos hti]
      rw [cpoly_truncate_coeff (CPolynomial.dropXPower p t) u (i - t)]
      have hi_sub : i - t < u := by omega
      rw [if_pos hi_sub]
      rw [cpoly_coeff_dropXPower]
      rw [show i - t + t = i by omega]
      by_cases hit : i < t
      · exact False.elim ((Nat.not_lt_of_ge hti) hit)
      · rw [cpoly_truncate_coeff p t i, if_neg hit]
        simp
    · rw [if_neg hti]
      have hit : i < t := Nat.lt_of_not_ge hti
      rw [cpoly_truncate_coeff, if_pos hit]
      simp
  · rw [if_neg hi_tu]
    by_cases hti : t ≤ i
    · rw [if_pos hti]
      rw [cpoly_truncate_coeff (CPolynomial.dropXPower p t) u (i - t)]
      have hi_sub_not : ¬ i - t < u := by omega
      rw [if_neg hi_sub_not]
      by_cases hit : i < t
      · exact False.elim ((Nat.not_lt_of_ge hti) hit)
      · rw [cpoly_truncate_coeff p t i, if_neg hit]
        simp
    · rw [if_neg hti]
      have hit : i < t := Nat.lt_of_not_ge hti
      rw [cpoly_truncate_coeff, if_pos hit]
      omega

private theorem MatchesRootPrefix.compose {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {p : CPolynomial F} {outer suffix : RootPrefix F}
    (houter : MatchesRootPrefix p outer)
    (hsuffix : MatchesRootPrefix (CPolynomial.dropXPower p outer.precision) suffix) :
    MatchesRootPrefix p (composeRootPrefixes outer suffix) := by
  unfold MatchesRootPrefix MatchesPrefix at houter hsuffix ⊢
  unfold composeRootPrefixes
  dsimp
  rw [polynomialPrefix_add_shift_prefix_dropXPower]
  rw [houter, hsuffix]

private theorem polynomialPrefix_prefix_of_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (p : CPolynomial F) {k t : Nat} (hkt : k ≤ t) :
    polynomialPrefix (polynomialPrefix p t) k = polynomialPrefix p k := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  unfold polynomialPrefix
  rw [cpoly_truncate_coeff, cpoly_truncate_coeff]
  by_cases hik : i < k
  · rw [if_pos hik]
    have hit : i < t := Nat.lt_of_lt_of_le hik hkt
    rw [cpoly_truncate_coeff, if_pos hit]
    rw [if_pos hik]
  · rw [if_neg hik]
    rw [cpoly_truncate_coeff p k i, if_neg hik]

private theorem polynomialPrefix_rootPrefix_eq_of_degreeLt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {p : CPolynomial F} {rootPrefix : RootPrefix F} {k : Nat}
    (hmatch : MatchesRootPrefix p rootPrefix)
    (hprec : k ≤ rootPrefix.precision)
    (hdegree : degreeLt p k) :
    polynomialPrefix rootPrefix.prefixPoly k = p := by
  unfold MatchesRootPrefix MatchesPrefix at hmatch
  rw [← hmatch]
  rw [polynomialPrefix_prefix_of_le p hprec]
  exact polynomialPrefix_eq_self_of_degreeLt hdegree

private theorem finishAlekhnovichPrefixWithFuel_complete_of_precision {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F} {Q : CBivariate F} {k fuel : Nat}
    {p : CPolynomial F} {rootPrefix : RootPrefix F}
    (hmatch : MatchesRootPrefix p rootPrefix)
    (hprec : k ≤ rootPrefix.precision)
    (hdegree : degreeLt p k) :
    p ∈ (finishAlekhnovichPrefixWithAlekhnovichWithFuel fieldRoots fuel Q k rootPrefix).toList := by
  cases fuel with
  | zero =>
      simp [finishAlekhnovichPrefixWithAlekhnovichWithFuel, Nat.not_lt.mpr hprec,
        polynomialPrefix_rootPrefix_eq_of_degreeLt hmatch hprec hdegree]
  | succ fuel =>
      simp [finishAlekhnovichPrefixWithAlekhnovichWithFuel, Nat.not_lt.mpr hprec,
        polynomialPrefix_rootPrefix_eq_of_degreeLt hmatch hprec hdegree]

/-- Soundness of Alekhnovich root filtering. -/
theorem alekhnovichRootsYDegreeLt_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F} {Q : CBivariate F} {k : Nat}
    {p : CPolynomial F}
    (h : p ∈ (alekhnovichRootsYDegreeLt fieldRoots Q k).toList) :
    degreeLt p k ∧ CBivariate.composeY Q p = 0 := by
  rw [alekhnovichRootsYDegreeLt] at h
  by_cases hzero : Q == 0
  · simp [hzero] at h
  · exact rootsYDegreeLtFromCandidates_eraseDups_sound (by
      simpa [hzero] using h)

/-- The exact final filter keeps any true bounded root that the Alekhnovich
candidate generator has already produced. -/
theorem alekhnovichRootsYDegreeLt_complete_of_candidate_mem {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F} {Q : CBivariate F} {k : Nat}
    {p : CPolynomial F}
    (hQ : Q ≠ 0)
    (hmem : p ∈ (alekhnovichRootCandidates fieldRoots Q k).toList)
    (hdegree : degreeLt p k) (hroot : CBivariate.composeY Q p = 0) :
    p ∈ (alekhnovichRootsYDegreeLt fieldRoots Q k).toList := by
  rw [alekhnovichRootsYDegreeLt]
  have hzero : (Q == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact hQ (beq_iff_eq.mp htrue)
  rw [hzero]
  exact rootsYDegreeLtFromCandidates_eraseDups_complete_of_mem
    hmem hdegree hroot

/-- Shifted substitution preserves modular roots below `N` before truncation. -/
theorem RootMod.substituteYPolynomialPlusXPowerY {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {f g : CPolynomial F} {t N : Nat}
    (hroot : RootMod Q (f + shiftPolynomialByXPower g t) N) :
    RootMod (substituteYPolynomialPlusXPowerY Q f t) g N := by
  intro i hi
  rw [composeY_substituteYPolynomialPlusXPowerY]
  simpa [shiftPolynomialByXPower] using hroot i hi

/-- Truncated shifted substitution has the same coefficients below `N` as exact
shifted substitution, so it preserves modular roots below `N`. -/
theorem RootMod.substituteYPolynomialPlusXPowerYTruncated {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {f g : CPolynomial F} {t N : Nat}
    (hroot : RootMod Q (f + shiftPolynomialByXPower g t) N) :
    RootMod (substituteYPolynomialPlusXPowerYTruncated Q f t N) g N := by
  unfold RootMod
  intro i hi
  have hcoeff :
      (CBivariate.composeY
        (GuruswamiSudan.substituteYPolynomialPlusXPowerYTruncated Q f t N) g).coeff i =
        (CBivariate.composeY
          (GuruswamiSudan.substituteYPolynomialPlusXPowerY Q f t) g).coeff i := by
    apply composeY_coeff_congr_of_coeff_eq_le
    intro x y hx
    exact substituteYPolynomialPlusXPowerYTruncated_coeff_eq_of_lt Q f t N
      (Nat.lt_of_le_of_lt hx hi)
  rw [hcoeff]
  exact (RootMod.substituteYPolynomialPlusXPowerY
    (Q := Q) (f := f) (g := g) (t := t) (N := N) hroot) i hi

/-- Stripping a visible `X`-adic valuation transports a modular root of `Q` to
a shorter modular root of the stripped residual. -/
theorem RootMod.stripXAdicFactor {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {p : CPolynomial F} {s N : Nat}
    (horder : CBivariate.xAdicOrder? Q = some s)
    (hroot : RootMod Q p (s + N)) :
    RootMod (CBivariate.stripXAdicFactor Q) p N := by
  unfold RootMod
  intro i hi
  rw [CBivariate.stripXAdicFactor, horder]
  have hfactor := cbivar_toPoly_eq_C_X_pow_mul_divXPower_of_xAdicOrder
    (Q := Q) horder
  have hfactorEval : (CBivariate.composeY Q p).toPoly =
      Polynomial.X ^ s * (CBivariate.composeY (CBivariate.divXPower Q s) p).toPoly := by
    rw [composeY_toPoly, composeY_toPoly]
    rw [hfactor, Polynomial.eval_mul, Polynomial.eval_C]
  have hrootCoeff : ((CBivariate.composeY Q p).toPoly).coeff (i + s) = 0 := by
    rw [← CPolynomial.coeff_toPoly (CBivariate.composeY Q p) (i + s)]
    exact hroot (i + s) (by omega)
  have hcoeff : ((CBivariate.composeY Q p).toPoly).coeff (i + s) =
      ((CBivariate.composeY (CBivariate.divXPower Q s) p).toPoly).coeff i := by
    simpa [Polynomial.coeff_X_pow_mul] using
      congrArg (fun P : Polynomial F ↦ P.coeff (i + s)) hfactorEval
  change (CBivariate.composeY (CBivariate.divXPower Q s) p).coeff i = 0
  rw [CPolynomial.coeff_toPoly]
  exact hcoeff.symm.trans hrootCoeff

private theorem RootMod.of_shiftedResidualUpTo {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {f g : CPolynomial F} {t N : Nat}
    (hroot : RootMod Q (f + shiftPolynomialByXPower g t) N)
    (hval : (shiftedResidualUpTo Q f t N).valuation < N) :
    RootMod (shiftedResidualUpTo Q f t N).residual g
      (N - (shiftedResidualUpTo Q f t N).valuation) := by
  unfold _root_.CompPoly.GuruswamiSudan.shiftedResidualUpTo at hval ⊢
  let T := _root_.CompPoly.GuruswamiSudan.substituteYPolynomialPlusXPowerYTruncated Q f t N
  have hrootT : RootMod T g N := by
    dsimp [T]
    exact RootMod.substituteYPolynomialPlusXPowerYTruncated hroot
  cases horder : CBivariate.xAdicOrder? T with
  | none =>
      simp [T, horder] at hval
  | some s =>
      by_cases hs : s < N
      · simp [T, horder, hs] at hval ⊢
        have hsum : s + (N - s) = N := Nat.add_sub_of_le (Nat.le_of_lt hs)
        have hstrip := RootMod.stripXAdicFactor (Q := T) (p := g) (s := s)
          (N := N - s) horder (by simpa [hsum] using hrootT)
        simpa [CBivariate.stripXAdicFactor, horder] using hstrip
      · simp [T, horder, hs] at hval

private theorem RootMod.of_composeY_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {Q : CBivariate F} {p : CPolynomial F} {N : Nat}
    (hroot : CBivariate.composeY Q p = 0) :
    RootMod Q p N := by
  intro i _hi
  rw [hroot]
  exact CPolynomial.coeff_zero i

private theorem normalizeAlekhnovichInput_eq_some {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {Q Qnorm : CBivariate F} {N Nnorm : Nat}
    (hnorm : normalizeAlekhnovichInput Q N = some (Qnorm, Nnorm)) :
    ∃ s, CBivariate.xAdicOrder? Q = some s ∧ s < N ∧
      Qnorm = CBivariate.divXPower Q s ∧ Nnorm = N - s := by
  unfold normalizeAlekhnovichInput at hnorm
  cases horder : CBivariate.xAdicOrder? Q with
  | none => simp [horder] at hnorm
  | some s =>
      by_cases hs : s < N
      · simp [horder, hs] at hnorm
        rcases hnorm with ⟨rfl, rfl⟩
        exact ⟨s, by simp, hs, rfl, rfl⟩
      · simp [horder, hs] at hnorm

private theorem RootMod.normalizeAlekhnovichInput {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q Qnorm : CBivariate F} {N Nnorm : Nat} {p : CPolynomial F}
    (hnorm : normalizeAlekhnovichInput Q N = some (Qnorm, Nnorm))
    (hroot : RootMod Q p N) :
    RootMod Qnorm p Nnorm := by
  rcases normalizeAlekhnovichInput_eq_some hnorm with ⟨s, horder, hs, rfl, rfl⟩
  have hsum : s + (N - s) = N := Nat.add_sub_of_le (Nat.le_of_lt hs)
  have hstrip := RootMod.stripXAdicFactor (Q := Q) (p := p) (s := s)
    (N := N - s) horder (by simpa [hsum] using hroot)
  simpa [CBivariate.stripXAdicFactor, horder] using hstrip

private theorem stripXAdicFactor_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {Q : CBivariate F} (hQ : Q ≠ 0) :
    CBivariate.stripXAdicFactor Q ≠ 0 := by
  intro hzero
  cases horder : CBivariate.xAdicOrder? Q with
  | none =>
      exact hQ (cbivar_xAdicOrder?_none_eq_zero horder)
  | some order =>
      rcases cbivar_xAdicOrder?_some_exists horder with ⟨y, _hy, hcoeff⟩
      have hcoeffStrip : CBivariate.coeff Q.stripXAdicFactor 0 y = 0 := by
        rw [hzero]
        exact CPolynomial.coeff_zero 0
      rw [CBivariate.stripXAdicFactor, horder, cbivar_coeff_divXPower] at hcoeffStrip
      exact hcoeff (by simpa using hcoeffStrip)

private theorem initialCoefficientPolynomial_stripXAdicFactor_ne_zero {F : Type*}
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

private theorem initialCoefficientPolynomial_coeff_eq_zero_of_size_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) {j : Nat} (hj : Q.val.size ≤ j) :
    (initialCoefficientPolynomial Q).coeff j = 0 := by
  unfold initialCoefficientPolynomial
  rw [initialCoefficientPolynomial_coeff_fold Q j (List.range Q.val.size)
    (0 : CPolynomial F) (List.nodup_range (n := Q.val.size))]
  rw [CPolynomial.coeff_zero]
  simp [hj]

private theorem initialCoefficientPolynomial_exists_coeff_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F}
    (hinit : initialCoefficientPolynomial Q ≠ 0) :
    ∃ y, y < Q.val.size ∧ CBivariate.coeff Q 0 y ≠ 0 := by
  let P := initialCoefficientPolynomial Q
  let y := P.natDegree
  have hcoeff : P.coeff y ≠ 0 := by
    dsimp [P, y]
    exact cpoly_coeff_natDegree_ne_zero_of_ne_zero hinit
  have hy : y < Q.val.size := by
    by_contra hnot
    exact hcoeff (by
      dsimp [P]
      exact initialCoefficientPolynomial_coeff_eq_zero_of_size_le Q
        (Nat.le_of_not_lt hnot))
  exact ⟨y, hy, by
    have h := initialCoefficientPolynomial_coeff_of_lt Q hy
    dsimp [P] at hcoeff
    rw [h] at hcoeff
    exact hcoeff⟩

private theorem initialCoefficientPolynomial_coeff_zero_eq_cbivar_coeff_zero_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) :
    (initialCoefficientPolynomial Q).coeff 0 = CBivariate.coeff Q 0 0 := by
  by_cases hsize : 0 < Q.val.size
  · exact initialCoefficientPolynomial_coeff_of_lt Q hsize
  · have hle : Q.val.size ≤ 0 := Nat.le_of_not_lt hsize
    rw [initialCoefficientPolynomial_coeff_eq_zero_of_size_le Q hle]
    symm
    exact cbivar_coeff_eq_zero_of_y_size_le Q hle

private theorem rootPrefix_coeff_zero_eq_of_matches_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {p : CPolynomial F} {rootPrefix : RootPrefix F}
    (hmatch : MatchesRootPrefix p rootPrefix)
    (hprec : 0 < rootPrefix.precision) :
    rootPrefix.prefixPoly.coeff 0 = p.coeff 0 := by
  unfold MatchesRootPrefix MatchesPrefix at hmatch
  rw [← hmatch]
  unfold polynomialPrefix
  rw [cpoly_truncate_coeff]
  simp [hprec]

private theorem composeY_coeff_zero_eq_of_coeff_zero_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) {f p : CPolynomial F}
    (hcoeff : f.coeff 0 = p.coeff 0) :
    (CBivariate.composeY Q f).coeff 0 = (CBivariate.composeY Q p).coeff 0 := by
  rw [← initialCoefficientPolynomial_eval_eq_composeY_coeff_zero Q f]
  rw [← initialCoefficientPolynomial_eval_eq_composeY_coeff_zero Q p]
  rw [hcoeff]

private theorem substituteYPolynomialPlusXPowerYTruncated_coeff_zero_zero_of_matches_root
    {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {p : CPolynomial F} {rootPrefix : RootPrefix F} {N : Nat}
    (hN : 0 < N)
    (hmatch : MatchesRootPrefix p rootPrefix)
    (hprec : 0 < rootPrefix.precision)
    (hroot : RootMod Q p N) :
    CBivariate.coeff
      (substituteYPolynomialPlusXPowerYTruncated Q rootPrefix.prefixPoly
        rootPrefix.precision N)
      0 0 = 0 := by
  rw [substituteYPolynomialPlusXPowerYTruncated_coeff_eq_of_lt
    Q rootPrefix.prefixPoly rootPrefix.precision N hN]
  let T := substituteYPolynomialPlusXPowerY Q rootPrefix.prefixPoly rootPrefix.precision
  change CBivariate.coeff T 0 0 = 0
  rw [← initialCoefficientPolynomial_coeff_zero_eq_cbivar_coeff_zero_zero T]
  rw [← CPolynomial.eval_zero_eq_coeff_zero (initialCoefficientPolynomial T)]
  change CPolynomial.eval ((0 : CPolynomial F).coeff 0) (initialCoefficientPolynomial T) = 0
  rw [initialCoefficientPolynomial_eval_eq_composeY_coeff_zero T (0 : CPolynomial F)]
  have hcompose :
      (CBivariate.composeY T (0 : CPolynomial F)).coeff 0 =
        (CBivariate.composeY Q rootPrefix.prefixPoly).coeff 0 := by
    dsimp [T]
    rw [composeY_substituteYPolynomialPlusXPowerY]
    simp
  rw [hcompose]
  rw [composeY_coeff_zero_eq_of_coeff_zero_eq Q
    (rootPrefix_coeff_zero_eq_of_matches_pos hmatch hprec)]
  exact hroot 0 hN

private theorem substituteYPolynomialPlusXPowerYTruncated_coeff_zero_of_matches_root
    {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {p : CPolynomial F} {rootPrefix : RootPrefix F} {N y : Nat}
    (hN : 0 < N)
    (hmatch : MatchesRootPrefix p rootPrefix)
    (hprec : 0 < rootPrefix.precision)
    (hroot : RootMod Q p N) :
    CBivariate.coeff
      (substituteYPolynomialPlusXPowerYTruncated Q rootPrefix.prefixPoly
        rootPrefix.precision N)
      0 y = 0 := by
  cases y with
  | zero =>
      exact substituteYPolynomialPlusXPowerYTruncated_coeff_zero_zero_of_matches_root
        hN hmatch hprec hroot
  | succ y =>
      exact substituteYPolynomialPlusXPowerYTruncated_coeff_zero_of_y_pos
        Q rootPrefix.prefixPoly hN hprec (Nat.succ_pos y)

private theorem shiftedResidualUpTo_valuation_pos_of_matches_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {p : CPolynomial F} {rootPrefix : RootPrefix F} {N : Nat}
    (hN : 0 < N)
    (hmatch : MatchesRootPrefix p rootPrefix)
    (hprec : 0 < rootPrefix.precision)
    (hroot : RootMod Q p N)
    (hval : (shiftedResidualUpTo Q rootPrefix.prefixPoly rootPrefix.precision N).valuation < N) :
    0 < (shiftedResidualUpTo Q rootPrefix.prefixPoly rootPrefix.precision N).valuation := by
  unfold shiftedResidualUpTo at hval ⊢
  let T := substituteYPolynomialPlusXPowerYTruncated Q rootPrefix.prefixPoly
    rootPrefix.precision N
  cases horder : CBivariate.xAdicOrder? T with
  | none =>
      simp [T, horder] at hval
  | some s =>
      by_cases hs : s < N
      · simp [T, horder, hs] at hval ⊢
        by_contra hnot
        have hs0 : s = 0 := Nat.eq_zero_of_not_pos hnot
        subst s
        rcases cbivar_xAdicOrder?_some_exists horder with ⟨y, _hy, hcoeff⟩
        exact hcoeff
          (substituteYPolynomialPlusXPowerYTruncated_coeff_zero_of_matches_root
            (Q := Q) (p := p) (rootPrefix := rootPrefix) (N := N) (y := y)
            hN hmatch hprec hroot)
      · simp [T, horder, hs] at hval

private theorem cbivar_xAdicOrder?_eq_zero_of_initial_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F}
    (hinit : initialCoefficientPolynomial Q ≠ 0) :
    CBivariate.xAdicOrder? Q = some 0 := by
  rcases initialCoefficientPolynomial_exists_coeff_ne_zero hinit with ⟨y, _hy, hcoeff⟩
  cases horder : CBivariate.xAdicOrder? Q with
  | none =>
      have hQzero := cbivar_xAdicOrder?_none_eq_zero horder
      rw [hQzero] at hcoeff
      exact (hcoeff (CBivariate.coeff_zero 0 y)).elim
  | some order =>
      have horder_zero : order = 0 := by
        by_contra hne
        have hpos : 0 < order := Nat.pos_of_ne_zero hne
        exact hcoeff (cbivar_xAdicOrder?_some_coeff_eq_zero_of_lt
          (Q := Q) (order := order) (i := 0) (y := y) horder hpos)
      subst order
      simp

private theorem cbivar_divXPower_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (Q : CBivariate F) :
    CBivariate.divXPower Q 0 = Q := by
  rw [CBivariate.eq_iff_coeff]
  intro i j
  rw [cbivar_coeff_divXPower]
  simp

private theorem alekhnovichRootPrefixesWithFuel_precision_pos_of_initial_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) :
    ∀ {fuel : Nat} {Q : CBivariate F} {N : Nat} {rootPrefix : RootPrefix F},
      N < fuel →
      0 < N →
      initialCoefficientPolynomial Q ≠ 0 →
      rootPrefix ∈ (alekhnovichRootPrefixesWithFuel fieldRoots fuel Q N).toList →
      0 < rootPrefix.precision := by
  intro fuel
  induction fuel with
  | zero =>
      intro Q N rootPrefix hfuel _hNpos _hinit _hmem
      omega
  | succ fuel ih =>
      intro Q N rootPrefix hfuel hNpos hinit hmem
      have horder0 : CBivariate.xAdicOrder? Q = some 0 :=
        cbivar_xAdicOrder?_eq_zero_of_initial_ne_zero hinit
      have hnorm : normalizeAlekhnovichInput Q N = some (Q, N) := by
        unfold normalizeAlekhnovichInput
        simp [horder0, hNpos, cbivar_divXPower_zero]
      by_cases hN1 : N = 1
      · subst N
        simp [alekhnovichRootPrefixesWithFuel, hnorm] at hmem
        rcases hmem with ⟨a, _ha, hroot⟩
        subst rootPrefix
        simp
      · have hN0 : ¬ N = 0 := by omega
        simp [alekhnovichRootPrefixesWithFuel, hN0, hnorm, hN1] at hmem
        let halfPrecision := (N + 1) / 2
        have hhalf_pos : 0 < halfPrecision := by omega
        have hhalf_lt_fuel : halfPrecision < fuel := by omega
        let prefixes := alekhnovichRootPrefixesWithFuel fieldRoots fuel Q halfPrecision
        let step : Array (RootPrefix F) → RootPrefix F → Array (RootPrefix F) :=
          fun out rootPrefix ↦
            let residual :=
              shiftedResidualUpTo Q rootPrefix.prefixPoly rootPrefix.precision N
            if residual.valuation < N then
              out ++
                (alekhnovichRootPrefixesWithFuel fieldRoots fuel residual.residual
                  (N - residual.valuation)).map
                  (fun suffix ↦ composeRootPrefixes rootPrefix suffix)
            else
              out.push rootPrefix
        change rootPrefix ∈ prefixes.foldl step #[] at hmem
        have hmemList : rootPrefix ∈ (prefixes.foldl step #[]).toList :=
          Array.mem_def.mp hmem
        exact array_foldl_forall_of_forall_step_with_input
          (fun rootPrefix : RootPrefix F ↦ 0 < rootPrefix.precision)
          (fun rootPrefix : RootPrefix F ↦ 0 < rootPrefix.precision)
          prefixes step #[] (by simp)
          (by
            intro outer houter
            exact ih hhalf_lt_fuel hhalf_pos hinit (by
              dsimp [prefixes] at houter
              exact houter))
          (by
            intro out outer y hout houter_pos hy
            by_cases hval :
        (shiftedResidualUpTo Q outer.prefixPoly outer.precision N).valuation < N
            · simp [step, hval] at hy
              rcases hy with hy | ⟨suffix, _hsuffixMem, hyEq⟩
              · exact hout y (Array.mem_def.mp hy)
              · subst y
                unfold composeRootPrefixes
                dsimp
                omega
            · simp [step, hval] at hy
              rcases hy with hy | rfl
              · exact hout y (Array.mem_def.mp hy)
              · exact houter_pos)
          rootPrefix hmemList

private theorem initialCoefficientPolynomial_normalizeAlekhnovichInput_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q Qnorm : CBivariate F} {N Nnorm : Nat}
    (hnorm : normalizeAlekhnovichInput Q N = some (Qnorm, Nnorm)) :
    initialCoefficientPolynomial Qnorm ≠ 0 := by
  rcases normalizeAlekhnovichInput_eq_some hnorm with ⟨s, horder, _hs, rfl, rfl⟩
  have hQ : Q ≠ 0 := by
    intro hzero
    rcases cbivar_xAdicOrder?_some_exists horder with ⟨y, _hy, hcoeff⟩
    rw [hzero] at hcoeff
    exact hcoeff (CBivariate.coeff_zero s y)
  simpa [CBivariate.stripXAdicFactor, horder] using
    initialCoefficientPolynomial_stripXAdicFactor_ne_zero hQ

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

private theorem composeY_shiftedResidual_dropXPower_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {p : CPolynomial F} {rootPrefix : RootPrefix F}
    (hQ : Q ≠ 0)
    (hmatch : MatchesRootPrefix p rootPrefix)
    (hroot : CBivariate.composeY Q p = 0) :
    CBivariate.composeY
        (CBivariate.stripXAdicFactor
          (substituteYPolynomialPlusXPowerY Q rootPrefix.prefixPoly
            rootPrefix.precision))
        (CPolynomial.dropXPower p rootPrefix.precision) = 0 := by
  apply composeY_stripXAdicFactor_eq_zero_of_composeY
  · exact substituteYPolynomialPlusXPowerY_ne_zero rootPrefix.prefixPoly
      rootPrefix.precision hQ
  · rw [composeY_substituteYPolynomialPlusXPowerY]
    have hpEq := rootPrefix_add_shift_dropXPower_eq hmatch
    rw [← hpEq] at hroot
    simpa [shiftPolynomialByXPower] using hroot

/-- Recursive Alekhnovich prefix coverage for modular roots. -/
theorem alekhnovichRootPrefixesWithFuel_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F} {Q : CBivariate F} {N fuel : Nat}
    {p : CPolynomial F}
    (hfuel : N < fuel)
    (hroot : RootMod Q p N) :
    ∃ rootPrefix,
      rootPrefix ∈ (alekhnovichRootPrefixesWithFuel fieldRoots fuel Q N).toList ∧
        MatchesRootPrefix p rootPrefix := by
  revert Q N p
  induction fuel with
  | zero =>
      intro Q N p hfuel _hroot
      omega
  | succ fuel ih =>
      intro Q N p hfuel hroot
      by_cases hN : N = 0
      · refine ⟨{ prefixPoly := 0, precision := 0 }, ?_, ?_⟩
        · simp [alekhnovichRootPrefixesWithFuel, hN]
        · simp [MatchesRootPrefix, MatchesPrefix, polynomialPrefix_zero]
      · cases hnorm : normalizeAlekhnovichInput Q N with
        | none =>
            refine ⟨{ prefixPoly := 0, precision := 0 }, ?_, ?_⟩
            · simp [alekhnovichRootPrefixesWithFuel, hN, hnorm]
            · simp [MatchesRootPrefix, MatchesPrefix, polynomialPrefix_zero]
        | some normalized =>
            rcases normalized with ⟨Qnorm, Nnorm⟩
            have hrootNorm : RootMod Qnorm p Nnorm :=
              RootMod.normalizeAlekhnovichInput hnorm hroot
            by_cases hNnorm0 : Nnorm = 0
            · refine ⟨{ prefixPoly := 0, precision := 0 }, ?_, ?_⟩
              · simp [alekhnovichRootPrefixesWithFuel, hN, hnorm, hNnorm0]
              · simp [MatchesRootPrefix, MatchesPrefix, polynomialPrefix_zero]
            · by_cases hNnorm1 : Nnorm = 1
              · have hinitRoot :
                    CPolynomial.eval (p.coeff 0) (initialCoefficientPolynomial Qnorm) = 0 := by
                  rw [initialCoefficientPolynomial_eval_eq_composeY_coeff_zero]
                  exact hrootNorm 0 (by omega)
                have hcoeffMem :
                    p.coeff 0 ∈
                      (rootsInFieldForNonzeroEquation fieldRoots
                        (initialCoefficientPolynomial Qnorm)).toList :=
                  rootsInFieldForNonzeroEquation_complete fieldRoots
                    (initialCoefficientPolynomial_normalizeAlekhnovichInput_ne_zero hnorm)
                    hinitRoot
                refine ⟨{ prefixPoly := CPolynomial.C (p.coeff 0), precision := 1 }, ?_, ?_⟩
                · simp [alekhnovichRootPrefixesWithFuel, hN, hnorm, hNnorm1]
                  exact ⟨p.coeff 0, Array.mem_def.mpr hcoeffMem, by simp [CPolynomial.coeff]⟩
                · simp [MatchesRootPrefix, MatchesPrefix, polynomialPrefix_one]
              · have hNnorm_pos : 0 < Nnorm := Nat.pos_of_ne_zero hNnorm0
                have hNnorm_gt_one : 1 < Nnorm := by omega
                let halfPrecision := (Nnorm + 1) / 2
                have hhalf_pos : 0 < halfPrecision := by omega
                have hhalf_le : halfPrecision ≤ Nnorm := by omega
                have hhalf_lt_Nnorm : halfPrecision < Nnorm := by omega
                have hNnorm_le_N : Nnorm ≤ N := by
                  rcases normalizeAlekhnovichInput_eq_some hnorm with
                    ⟨s, _horder, hs, _hQnorm, hNnormEq⟩
                  rw [hNnormEq]
                  omega
                have hN_le_fuel : N ≤ fuel := by omega
                have hhalf_lt_fuel : halfPrecision < fuel := by omega
                have hrootHalf : RootMod Qnorm p halfPrecision := by
                  intro i hi
                  exact hrootNorm i (Nat.lt_of_lt_of_le hi hhalf_le)
                rcases ih (Q := Qnorm) (N := halfPrecision) (p := p)
                    hhalf_lt_fuel hrootHalf with
                  ⟨outer, houterMem, houterMatch⟩
                have hinitNorm :
                    initialCoefficientPolynomial Qnorm ≠ 0 :=
                  initialCoefficientPolynomial_normalizeAlekhnovichInput_ne_zero hnorm
                have houterPrecPos : 0 < outer.precision :=
                  alekhnovichRootPrefixesWithFuel_precision_pos_of_initial_ne_zero
                    fieldRoots hhalf_lt_fuel hhalf_pos hinitNorm houterMem
                let residual :=
                  shiftedResidualUpTo Qnorm outer.prefixPoly outer.precision Nnorm
                let prefixes :=
                  alekhnovichRootPrefixesWithFuel fieldRoots fuel Qnorm halfPrecision
                let step : Array (RootPrefix F) → RootPrefix F → Array (RootPrefix F) :=
                  fun out rootPrefix ↦
                    if (shiftedResidualUpTo Qnorm rootPrefix.prefixPoly rootPrefix.precision
                        Nnorm).valuation < Nnorm then
                      out ++
                        (alekhnovichRootPrefixesWithFuel fieldRoots fuel
                          (shiftedResidualUpTo Qnorm rootPrefix.prefixPoly
                            rootPrefix.precision Nnorm).residual
                          (Nnorm -
                            (shiftedResidualUpTo Qnorm rootPrefix.prefixPoly
                              rootPrefix.precision Nnorm).valuation)).map
                          (fun suffix ↦ composeRootPrefixes rootPrefix suffix)
                    else
                      out.push rootPrefix
                by_cases hval : residual.valuation < Nnorm
                · let suffixPoly := CPolynomial.dropXPower p outer.precision
                  have hrootForResidualInput :
                      RootMod Qnorm
                        (outer.prefixPoly +
                          shiftPolynomialByXPower suffixPoly outer.precision)
                        Nnorm := by
                    have hpEq := rootPrefix_add_shift_dropXPower_eq houterMatch
                    simpa [suffixPoly, hpEq] using hrootNorm
                  have hrootResidual :
                      RootMod residual.residual suffixPoly
                        (Nnorm - residual.valuation) := by
                    dsimp [residual]
                    exact RootMod.of_shiftedResidualUpTo hrootForResidualInput hval
                  have hval_pos : 0 < residual.valuation := by
                    dsimp [residual] at hval ⊢
                    exact shiftedResidualUpTo_valuation_pos_of_matches_root
                      hNnorm_pos houterMatch houterPrecPos hrootNorm hval
                  have hfuelSuffix : Nnorm - residual.valuation < fuel := by
                    omega
                  rcases ih (Q := residual.residual)
                      (N := Nnorm - residual.valuation) (p := suffixPoly)
                      hfuelSuffix hrootResidual with
                    ⟨suffix, hsuffixMem, hsuffixMatch⟩
                  refine ⟨composeRootPrefixes outer suffix, ?_, ?_⟩
                  · simp [alekhnovichRootPrefixesWithFuel, hN, hnorm, hNnorm0,
                      hNnorm1]
                    apply Array.mem_def.mpr
                    have hstepOuter :
                        ∀ out,
                          composeRootPrefixes outer suffix ∈ (step out outer).toList := by
                      intro out
                      dsimp [step, residual] at hval ⊢
                      simp [hval]
                      have hsuffixMemArray := Array.mem_def.mpr hsuffixMem
                      dsimp [residual] at hsuffixMemArray
                      exact Or.inr ⟨suffix, hsuffixMemArray, rfl⟩
                    have hpres :
                        ∀ out z,
                          composeRootPrefixes outer suffix ∈ out.toList →
                            composeRootPrefixes outer suffix ∈ (step out z).toList := by
                      intro out z hz
                      dsimp [step]
                      by_cases hzval :
                          (shiftedResidualUpTo Qnorm z.prefixPoly z.precision Nnorm).valuation <
                            Nnorm
                      · simp [hzval, hz]
                      · simp [hzval, hz]
                    exact array_foldl_mem_of_mem_step prefixes step houterMem hstepOuter hpres
                  · exact MatchesRootPrefix.compose houterMatch hsuffixMatch
                · refine ⟨outer, ?_, houterMatch⟩
                  · simp [alekhnovichRootPrefixesWithFuel, hN, hnorm, hNnorm0,
                      hNnorm1]
                    apply Array.mem_def.mpr
                    have hstepOuter : ∀ out, outer ∈ (step out outer).toList := by
                      intro out
                      dsimp [step, residual] at hval ⊢
                      simp [hval]
                    have hpres : ∀ out z, outer ∈ out.toList → outer ∈ (step out z).toList := by
                      intro out z hz
                      dsimp [step]
                      by_cases hzval :
                          (shiftedResidualUpTo Qnorm z.prefixPoly z.precision Nnorm).valuation <
                            Nnorm
                      · simp [hzval, hz]
                      · simp [hzval, hz]
                    exact array_foldl_mem_of_mem_step prefixes step houterMem hstepOuter hpres

private theorem list_foldl_max_ge_acc {α : Type*} (f : α → Nat) :
    ∀ (xs : List α) (acc : Nat),
      acc ≤ xs.foldl (fun bound x ↦ Nat.max bound (f x)) acc := by
  intro xs
  induction xs with
  | nil =>
      intro acc
      simp
  | cons x xs ih =>
      intro acc
      exact (Nat.le_max_left acc (f x)).trans
        (ih (Nat.max acc (f x)))

private theorem list_foldl_max_ge_of_mem {α : Type*} (f : α → Nat)
    {xs : List α} {x : α} (hx : x ∈ xs) (acc : Nat) :
    f x ≤ xs.foldl (fun bound x ↦ Nat.max bound (f x)) acc := by
  induction xs generalizing acc with
  | nil =>
      simp at hx
  | cons y ys ih =>
      simp at hx
      cases hx with
      | inl h =>
          subst y
          exact (Nat.le_max_right acc (f x)).trans
            (list_foldl_max_ge_acc f ys (Nat.max acc (f x)))
      | inr hx =>
          exact ih hx (Nat.max acc (f y))

private theorem list_foldl_max_le_of_forall {α : Type*} (f : α → Nat)
    {xs : List α} {bound acc : Nat}
    (hacc : acc ≤ bound) (hxs : ∀ x, x ∈ xs → f x ≤ bound) :
    xs.foldl (fun bound x ↦ Nat.max bound (f x)) acc ≤ bound := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact max_le hacc (hxs x (by simp))
      · intro y hy
        exact hxs y (by simp [hy])

private theorem cbivar_divXPower_size_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (Q : CBivariate F) (n : Nat) :
    (CBivariate.divXPower Q n).val.size ≤ Q.val.size := by
  unfold CBivariate.divXPower CPolynomial.ofArray
  simpa using
    (CPolynomial.Raw.Trim.size_le_size
      (Q.val.map fun coeff ↦ CPolynomial.dropXPower coeff n))

private theorem cbivar_xAdicOrder?_some_le_of_coeff_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {Q : CBivariate F} {i y : Nat}
    (hcoeff : CBivariate.coeff Q i y ≠ 0) :
    ∃ order, CBivariate.xAdicOrder? Q = some order ∧ order ≤ i := by
  cases horder : CBivariate.xAdicOrder? Q with
  | none =>
      have hzero := cbivar_xAdicOrder?_none_eq_zero horder
      rw [hzero] at hcoeff
      exact (hcoeff (CBivariate.coeff_zero i y)).elim
  | some order =>
      refine ⟨order, rfl, ?_⟩
      by_contra hnot
      have hi : i < order := Nat.lt_of_not_ge hnot
      exact hcoeff
        (cbivar_xAdicOrder?_some_coeff_eq_zero_of_lt
          (Q := Q) (order := order) (i := i) (y := y) horder hi)

private theorem shiftedResidualUpTo_valuation_lt_of_alekhnovichPrecisionBound_le
    {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} (f : CPolynomial F) {t k N : Nat}
    (hQ : Q ≠ 0) (ht : t < k)
    (hNbound : alekhnovichPrecisionBound Q k ≤ N) :
    (shiftedResidualUpTo Q f t N).valuation < N := by
  let y := Q.natDegree
  let coeffY := Q.val.coeff y
  have hQsize : Q.val.size = y + 1 := by
    dsimp [y]
    exact cpoly_size_eq_natDegree_succ_of_ne_zero hQ
  have hcoeffY_ne : coeffY ≠ 0 := by
    dsimp [coeffY, y]
    exact cpoly_coeff_natDegree_ne_zero_of_ne_zero hQ
  let x := coeffY.natDegree
  have hcoeff_ne : coeffY.coeff x ≠ 0 := by
    dsimp [x]
    exact cpoly_coeff_natDegree_ne_zero_of_ne_zero hcoeffY_ne
  let B := alekhnovichPrecisionBound Q k
  have hcoeffTop :
      CBivariate.coeff (substituteYPolynomialPlusXPowerY Q f t) (x + t * y) y =
        coeffY.coeff x := by
    simpa [coeffY] using substituteYPolynomialPlusXPowerY_coeff_top Q f t y x hQsize
  have hidx_lt_bound : x + t * y < B := by
    dsimp [B, x, coeffY]
    unfold alekhnovichPrecisionBound
    have hyMem : y ∈ List.range' 0 Q.val.size := by
      rw [hQsize]
      simp [List.mem_range', y]
    have hterm_le :
        (Q.val.coeff y).natDegree + y * (k - 1) ≤
          (List.range' 0 Q.val.size).foldl
            (fun bound y ↦ max bound ((Q.val.coeff y).natDegree + y * (k - 1))) 0 :=
      list_foldl_max_ge_of_mem
        (fun y ↦ (Q.val.coeff y).natDegree + y * (k - 1)) hyMem 0
    have ht_le : t ≤ k - 1 := by omega
    have hmul_le : t * y ≤ y * (k - 1) := by
      rw [Nat.mul_comm t y]
      exact Nat.mul_le_mul_left y ht_le
    omega
  have hidx_lt : x + t * y < N :=
    Nat.lt_of_lt_of_le hidx_lt_bound hNbound
  let T := substituteYPolynomialPlusXPowerYTruncated Q f t N
  have hcoeffT : CBivariate.coeff T (x + t * y) y ≠ 0 := by
    dsimp [T]
    change CBivariate.coeff
        (substituteYPolynomialPlusXPowerYTruncated Q f t N) (x + t * y) y ≠ 0
    rw [substituteYPolynomialPlusXPowerYTruncated_coeff_eq_of_lt Q f t N hidx_lt]
    rw [hcoeffTop]
    exact hcoeff_ne
  rcases cbivar_xAdicOrder?_some_le_of_coeff_ne_zero hcoeffT with
    ⟨order, horder, horder_le⟩
  change (shiftedResidualUpTo Q f t N).valuation < N
  have horder_lt : order < N := Nat.lt_of_le_of_lt horder_le hidx_lt
  dsimp [T] at horder
  simp [shiftedResidualUpTo, horder, horder_lt]

private theorem shiftedResidualUpTo_valuation_lt_alekhnovichPrecisionBound
    {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} (f : CPolynomial F) {t k : Nat}
    (hQ : Q ≠ 0) (ht : t < k) :
    (shiftedResidualUpTo Q f t (alekhnovichPrecisionBound Q k)).valuation <
      alekhnovichPrecisionBound Q k :=
  shiftedResidualUpTo_valuation_lt_of_alekhnovichPrecisionBound_le
    (Q := Q) f hQ ht le_rfl

private theorem shiftedResidualUpTo_initialCoefficientPolynomial_ne_zero_of_valuation_lt
    {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {f : CPolynomial F} {t N : Nat}
    (hval : (shiftedResidualUpTo Q f t N).valuation < N) :
    initialCoefficientPolynomial (shiftedResidualUpTo Q f t N).residual ≠ 0 := by
  unfold shiftedResidualUpTo at hval ⊢
  let T := substituteYPolynomialPlusXPowerYTruncated Q f t N
  cases horder : CBivariate.xAdicOrder? T with
  | none =>
      simp [T, horder] at hval
  | some s =>
      by_cases hs : s < N
      · simp [T, horder, hs] at hval ⊢
        have hTne : T ≠ 0 := by
          intro hzero
          rcases cbivar_xAdicOrder?_some_exists horder with ⟨y, _hy, hcoeff⟩
          rw [hzero] at hcoeff
          exact hcoeff (CBivariate.coeff_zero s y)
        simpa [CBivariate.stripXAdicFactor, horder] using
          initialCoefficientPolynomial_stripXAdicFactor_ne_zero hTne
      · simp [T, horder, hs] at hval

private theorem alekhnovichRootPrefixesWithFuel_precision_pos_of_initial_ne_zero_any
    {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) :
    ∀ {fuel : Nat} {Q : CBivariate F} {N : Nat} {rootPrefix : RootPrefix F},
      0 < N →
      initialCoefficientPolynomial Q ≠ 0 →
      rootPrefix ∈ (alekhnovichRootPrefixesWithFuel fieldRoots fuel Q N).toList →
      0 < rootPrefix.precision := by
  intro fuel
  induction fuel with
  | zero =>
      intro Q N rootPrefix _hNpos _hinit hmem
      simp [alekhnovichRootPrefixesWithFuel] at hmem
  | succ fuel ih =>
      intro Q N rootPrefix hNpos hinit hmem
      have horder0 : CBivariate.xAdicOrder? Q = some 0 :=
        cbivar_xAdicOrder?_eq_zero_of_initial_ne_zero hinit
      have hnorm : normalizeAlekhnovichInput Q N = some (Q, N) := by
        unfold normalizeAlekhnovichInput
        simp [horder0, hNpos, cbivar_divXPower_zero]
      by_cases hN1 : N = 1
      · subst N
        simp [alekhnovichRootPrefixesWithFuel, hnorm] at hmem
        rcases hmem with ⟨a, _ha, hroot⟩
        subst rootPrefix
        simp
      · have hN0 : ¬ N = 0 := by omega
        simp [alekhnovichRootPrefixesWithFuel, hN0, hnorm, hN1] at hmem
        let halfPrecision := (N + 1) / 2
        have hhalf_pos : 0 < halfPrecision := by omega
        let prefixes := alekhnovichRootPrefixesWithFuel fieldRoots fuel Q halfPrecision
        let step : Array (RootPrefix F) → RootPrefix F → Array (RootPrefix F) :=
          fun out rootPrefix ↦
            let residual :=
              shiftedResidualUpTo Q rootPrefix.prefixPoly rootPrefix.precision N
            if residual.valuation < N then
              out ++
                (alekhnovichRootPrefixesWithFuel fieldRoots fuel residual.residual
                  (N - residual.valuation)).map
                  (fun suffix ↦ composeRootPrefixes rootPrefix suffix)
            else
              out.push rootPrefix
        change rootPrefix ∈ prefixes.foldl step #[] at hmem
        have hmemList : rootPrefix ∈ (prefixes.foldl step #[]).toList :=
          Array.mem_def.mp hmem
        exact array_foldl_forall_of_forall_step_with_input
          (fun rootPrefix : RootPrefix F ↦ 0 < rootPrefix.precision)
          (fun rootPrefix : RootPrefix F ↦ 0 < rootPrefix.precision)
          prefixes step #[] (by simp)
          (by
            intro outer houter
            exact ih hhalf_pos hinit (by
              dsimp [prefixes] at houter
              exact houter))
          (by
            intro out outer y hout houter_pos hy
            by_cases hval :
                (shiftedResidualUpTo Q outer.prefixPoly outer.precision N).valuation < N
            · simp [step, hval] at hy
              rcases hy with hy | ⟨suffix, hsuffixMem, hyEq⟩
              · exact hout y (Array.mem_def.mp hy)
              · subst y
                unfold composeRootPrefixes
                dsimp
                have hNdiff_pos :
                    0 < N -
                      (shiftedResidualUpTo Q outer.prefixPoly outer.precision N).valuation := by
                  omega
                have hinitResidual :
                    initialCoefficientPolynomial
                        (shiftedResidualUpTo Q outer.prefixPoly outer.precision N).residual ≠ 0 :=
                  shiftedResidualUpTo_initialCoefficientPolynomial_ne_zero_of_valuation_lt hval
                have hsuffix_pos : 0 < suffix.precision :=
                  ih hNdiff_pos hinitResidual (by
                    exact Array.mem_def.mp hsuffixMem)
                omega
            · simp [step, hval] at hy
              rcases hy with hy | rfl
              · exact hout y (Array.mem_def.mp hy)
              · exact houter_pos)
          rootPrefix hmemList

private theorem alekhnovichRootPrefixesWithFuel_precision_gt_one_of_initial_ne_zero_bound
    {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) :
    ∀ {fuel : Nat} {Q : CBivariate F} {N k : Nat} {rootPrefix : RootPrefix F},
      initialCoefficientPolynomial Q ≠ 0 →
      alekhnovichPrecisionBound Q k ≤ N →
      rootPrefix ∈ (alekhnovichRootPrefixesWithFuel fieldRoots fuel Q N).toList →
      rootPrefix.precision < k →
      1 < rootPrefix.precision := by
  intro fuel
  induction fuel with
  | zero =>
      intro Q N k rootPrefix _hinit _hbound hmem _hprec
      simp [alekhnovichRootPrefixesWithFuel] at hmem
  | succ fuel ih =>
      intro Q N k rootPrefix hinit hbound hmem hprec
      have hbound_pos : 0 < alekhnovichPrecisionBound Q k := by
        unfold alekhnovichPrecisionBound
        omega
      have hNpos : 0 < N := by omega
      have horder0 : CBivariate.xAdicOrder? Q = some 0 :=
        cbivar_xAdicOrder?_eq_zero_of_initial_ne_zero hinit
      have hQne : Q ≠ 0 := by
        intro hzero
        have hinit_zero : initialCoefficientPolynomial (0 : CBivariate F) = 0 := by
          unfold initialCoefficientPolynomial
          change (List.foldl
            (fun out y ↦ out + CPolynomial.monomial y
              (CBivariate.coeff (0 : CBivariate F) 0 y)) 0 (List.range 0)) = 0
          simp
        have hQinit_zero : initialCoefficientPolynomial Q = 0 := by
          rw [hzero]
          exact hinit_zero
        exact hinit hQinit_zero
      have hnorm : normalizeAlekhnovichInput Q N = some (Q, N) := by
        unfold normalizeAlekhnovichInput
        simp [horder0, hNpos, cbivar_divXPower_zero]
      by_cases hN1 : N = 1
      · subst N
        simp [alekhnovichRootPrefixesWithFuel, hnorm] at hmem
        rcases hmem with ⟨a, _ha, hroot⟩
        subst rootPrefix
        have hk_lt_bound : k < alekhnovichPrecisionBound Q k := by
          unfold alekhnovichPrecisionBound
          omega
        simp at hprec ⊢
        omega
      · have hN0 : ¬ N = 0 := by omega
        simp [alekhnovichRootPrefixesWithFuel, hN0, hnorm, hN1] at hmem
        let halfPrecision := (N + 1) / 2
        have hhalf_pos : 0 < halfPrecision := by omega
        let prefixes := alekhnovichRootPrefixesWithFuel fieldRoots fuel Q halfPrecision
        let step : Array (RootPrefix F) → RootPrefix F → Array (RootPrefix F) :=
          fun out rootPrefix ↦
            let residual :=
              shiftedResidualUpTo Q rootPrefix.prefixPoly rootPrefix.precision N
            if residual.valuation < N then
              out ++
                (alekhnovichRootPrefixesWithFuel fieldRoots fuel residual.residual
                  (N - residual.valuation)).map
                  (fun suffix ↦ composeRootPrefixes rootPrefix suffix)
            else
              out.push rootPrefix
        change rootPrefix ∈ prefixes.foldl step #[] at hmem
        have hmemList : rootPrefix ∈ (prefixes.foldl step #[]).toList :=
          Array.mem_def.mp hmem
        have hprop :
            ∀ y, y ∈ (prefixes.foldl step #[]).toList →
              y.precision < k → 1 < y.precision :=
          array_foldl_forall_of_forall_step_with_input
            (fun rootPrefix : RootPrefix F ↦ rootPrefix.precision < k →
              1 < rootPrefix.precision)
            (fun rootPrefix : RootPrefix F ↦ 0 < rootPrefix.precision)
            prefixes step #[] (by simp)
            (by
              intro outer houter
              exact alekhnovichRootPrefixesWithFuel_precision_pos_of_initial_ne_zero_any
                fieldRoots hhalf_pos hinit (by
                  dsimp [prefixes] at houter
                  exact houter))
            (by
              intro out outer y hout houter_pos hy hylt
              by_cases hval :
                  (shiftedResidualUpTo Q outer.prefixPoly outer.precision N).valuation < N
              · simp [step, hval] at hy
                rcases hy with hy | ⟨suffix, hsuffixMem, hyEq⟩
                · exact hout y (Array.mem_def.mp hy) hylt
                · subst y
                  unfold composeRootPrefixes
                  dsimp
                  have hNdiff_pos :
                      0 < N -
                        (shiftedResidualUpTo Q outer.prefixPoly outer.precision N).valuation := by
                    omega
                  have hinitResidual :
                      initialCoefficientPolynomial
                          (shiftedResidualUpTo Q outer.prefixPoly outer.precision N).residual ≠
                        0 :=
                    shiftedResidualUpTo_initialCoefficientPolynomial_ne_zero_of_valuation_lt hval
                  have hsuffix_pos : 0 < suffix.precision :=
                    alekhnovichRootPrefixesWithFuel_precision_pos_of_initial_ne_zero_any
                      fieldRoots hNdiff_pos hinitResidual (by
                        exact Array.mem_def.mp hsuffixMem)
                  omega
              · simp [step, hval] at hy
                rcases hy with hy | hyEq
                · exact hout y (Array.mem_def.mp hy) hylt
                · have hval_lt :
                      (shiftedResidualUpTo Q y.prefixPoly y.precision N).valuation < N :=
                    shiftedResidualUpTo_valuation_lt_of_alekhnovichPrecisionBound_le
                      y.prefixPoly hQne hylt hbound
                  have hval_y :
                      ¬(shiftedResidualUpTo Q y.prefixPoly y.precision N).valuation < N := by
                    simpa [hyEq] using hval
                  exact False.elim (hval_y hval_lt))
        exact hprop rootPrefix hmemList hprec

private theorem cbivar_xAdicOrder?_some_lt_alekhnovichPrecisionBound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {Q : CBivariate F} {k order : Nat}
    (horder : CBivariate.xAdicOrder? Q = some order) :
    order < alekhnovichPrecisionBound Q k := by
  rcases cbivar_xAdicOrder?_some_exists horder with ⟨y, hy, hcoeff⟩
  have hcoeffRow : (Q.val.coeff y).coeff order ≠ 0 := by
    simpa [CBivariate.coeff] using hcoeff
  have horder_le : order ≤ (Q.val.coeff y).natDegree :=
    CPolynomial.le_natDegree_of_ne_zero hcoeffRow
  unfold alekhnovichPrecisionBound
  have hmem : y ∈ List.range' 0 Q.val.size := by
    simpa [List.mem_range'] using Nat.succ_le_of_lt hy
  have hterm_le :
      (Q.val.coeff y).natDegree + y * (k - 1) ≤
        (List.range' 0 Q.val.size).foldl
          (fun bound y ↦ max bound ((Q.val.coeff y).natDegree + y * (k - 1))) 0 :=
    list_foldl_max_ge_of_mem
      (fun y ↦ (Q.val.coeff y).natDegree + y * (k - 1)) hmem 0
  omega

private theorem alekhnovichPrecisionBound_divXPower_le_sub_xAdicOrder
    {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {k order : Nat}
    (horder : CBivariate.xAdicOrder? Q = some order) :
    alekhnovichPrecisionBound (CBivariate.divXPower Q order) k ≤
      alekhnovichPrecisionBound Q k - order := by
  let M : Nat :=
    (List.range' 0 Q.val.size).foldl
      (fun bound y ↦ max bound ((Q.val.coeff y).natDegree + y * (k - 1))) 0
  let Qnorm : CBivariate F := CBivariate.divXPower Q order
  let Mnorm : Nat :=
    (List.range' 0 Qnorm.val.size).foldl
      (fun bound y ↦ max bound ((Qnorm.val.coeff y).natDegree + y * (k - 1))) 0
  have horder_le_M : order ≤ M := by
    rcases cbivar_xAdicOrder?_some_exists horder with ⟨y, hy, hcoeff⟩
    have hcoeffRow : (Q.val.coeff y).coeff order ≠ 0 := by
      simpa [CBivariate.coeff] using hcoeff
    have horder_le_row : order ≤ (Q.val.coeff y).natDegree :=
      CPolynomial.le_natDegree_of_ne_zero hcoeffRow
    have hmem : y ∈ List.range' 0 Q.val.size := by
      simpa [List.mem_range'] using Nat.succ_le_of_lt hy
    have hterm_le : (Q.val.coeff y).natDegree + y * (k - 1) ≤ M := by
      dsimp [M]
      exact list_foldl_max_ge_of_mem
        (fun y ↦ (Q.val.coeff y).natDegree + y * (k - 1)) hmem 0
    omega
  have hQnorm_ne : Qnorm ≠ 0 := by
    intro hzero
    rcases cbivar_xAdicOrder?_some_exists horder with ⟨y, _hy, hcoeff⟩
    have hcoeffNorm : CBivariate.coeff Qnorm 0 y ≠ 0 := by
      change CBivariate.coeff (CBivariate.divXPower Q order) 0 y ≠ 0
      rw [cbivar_coeff_divXPower Q order 0 y]
      simpa using hcoeff
    rw [hzero] at hcoeffNorm
    exact hcoeffNorm (CBivariate.coeff_zero 0 y)
  have hQnorm_size : Qnorm.val.size = Qnorm.natDegree + 1 := by
    dsimp [Qnorm]
    exact cpoly_size_eq_natDegree_succ_of_ne_zero hQnorm_ne
  have hQnorm_size_le : Qnorm.val.size ≤ Q.val.size := by
    dsimp [Qnorm]
    exact cbivar_divXPower_size_le Q order
  have htop_ne : Qnorm.val.coeff Qnorm.natDegree ≠ 0 :=
    cpoly_coeff_natDegree_ne_zero_of_ne_zero hQnorm_ne
  have htop_term_le :
      (Qnorm.val.coeff Qnorm.natDegree).natDegree +
          Qnorm.natDegree * (k - 1) ≤ M - order := by
    have htop_lt_norm : Qnorm.natDegree < Qnorm.val.size := by
      rw [hQnorm_size]
      omega
    have htop_lt_Q : Qnorm.natDegree < Q.val.size := by
      exact Nat.lt_of_lt_of_le htop_lt_norm hQnorm_size_le
    have hdrop_nonzero :
        CPolynomial.dropXPower (Q.val.coeff Qnorm.natDegree) order ≠ 0 := by
      have htop_ne' :
          (CBivariate.divXPower Q order).val.coeff Qnorm.natDegree ≠ 0 := by
        simpa [Qnorm] using htop_ne
      simpa [cbivar_coeffY_divXPower Q order Qnorm.natDegree] using htop_ne'
    have hdrop_le :
        (Qnorm.val.coeff Qnorm.natDegree).natDegree + order ≤
          (Q.val.coeff Qnorm.natDegree).natDegree := by
      have h :=
        cpoly_natDegree_dropXPower_add_le_of_ne_zero
          (Q.val.coeff Qnorm.natDegree) order hdrop_nonzero
      rwa [← cbivar_coeffY_divXPower Q order Qnorm.natDegree] at h
    have hmemTop : Qnorm.natDegree ∈ List.range' 0 Q.val.size := by
      simpa [List.mem_range'] using Nat.succ_le_of_lt htop_lt_Q
    have horig_term_le :
        (Q.val.coeff Qnorm.natDegree).natDegree +
            Qnorm.natDegree * (k - 1) ≤ M := by
      dsimp [M]
      exact list_foldl_max_ge_of_mem
        (fun y ↦ (Q.val.coeff y).natDegree + y * (k - 1)) hmemTop 0
    omega
  have hterm_norm_le :
      ∀ y, y ∈ List.range' 0 Qnorm.val.size →
        (Qnorm.val.coeff y).natDegree + y * (k - 1) ≤ M - order := by
    intro y hy
    have hylt_norm : y < Qnorm.val.size := by
      simpa using (List.mem_range'_1.mp hy).2
    have hyle_top : y ≤ Qnorm.natDegree := by
      rw [hQnorm_size] at hylt_norm
      omega
    by_cases hrow : Qnorm.val.coeff y = 0
    · have hnat_zero : (Qnorm.val.coeff y).natDegree = 0 := by
        rw [hrow]
        rfl
      rw [hnat_zero]
      have hy_mul_le : y * (k - 1) ≤ Qnorm.natDegree * (k - 1) :=
        Nat.mul_le_mul_right (k - 1) hyle_top
      omega
    · have hylt_Q : y < Q.val.size := Nat.lt_of_lt_of_le hylt_norm hQnorm_size_le
      have hdrop_nonzero :
          CPolynomial.dropXPower (Q.val.coeff y) order ≠ 0 := by
        have hrow' : (CBivariate.divXPower Q order).val.coeff y ≠ 0 := by
          simpa [Qnorm] using hrow
        simpa [cbivar_coeffY_divXPower Q order y] using hrow'
      have hdrop_le :
          (Qnorm.val.coeff y).natDegree + order ≤ (Q.val.coeff y).natDegree := by
        have h :=
          cpoly_natDegree_dropXPower_add_le_of_ne_zero
            (Q.val.coeff y) order hdrop_nonzero
        rwa [← cbivar_coeffY_divXPower Q order y] at h
      have hmem : y ∈ List.range' 0 Q.val.size := by
        simpa [List.mem_range'] using Nat.succ_le_of_lt hylt_Q
      have horig_term_le :
          (Q.val.coeff y).natDegree + y * (k - 1) ≤ M := by
        dsimp [M]
        exact list_foldl_max_ge_of_mem
          (fun y ↦ (Q.val.coeff y).natDegree + y * (k - 1)) hmem 0
      omega
  have hMnorm_le : Mnorm ≤ M - order := by
    dsimp [Mnorm]
    apply list_foldl_max_le_of_forall
    · omega
    · exact hterm_norm_le
  unfold alekhnovichPrecisionBound
  dsimp [M, Qnorm, Mnorm] at hMnorm_le horder_le_M ⊢
  omega

private theorem normalizeAlekhnovichInput_precisionBound_some {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {k : Nat}
    (hQ : Q ≠ 0) :
    ∃ Qnorm Nnorm,
      normalizeAlekhnovichInput Q (alekhnovichPrecisionBound Q k) =
          some (Qnorm, Nnorm) ∧
        0 < Nnorm ∧ Nnorm ≤ alekhnovichPrecisionBound Q k ∧
        alekhnovichPrecisionBound Qnorm k ≤ Nnorm ∧
        initialCoefficientPolynomial Qnorm ≠ 0 := by
  cases horder : CBivariate.xAdicOrder? Q with
  | none =>
      exact (hQ (cbivar_xAdicOrder?_none_eq_zero horder)).elim
  | some order =>
      have horder_lt :
          order < alekhnovichPrecisionBound Q k :=
        cbivar_xAdicOrder?_some_lt_alekhnovichPrecisionBound horder
      refine ⟨CBivariate.divXPower Q order,
        alekhnovichPrecisionBound Q k - order, ?_, ?_, ?_, ?_, ?_⟩
      · unfold normalizeAlekhnovichInput
        simp [horder, horder_lt]
      · omega
      · omega
      · exact alekhnovichPrecisionBound_divXPower_le_sub_xAdicOrder horder
      · simpa [CBivariate.stripXAdicFactor, horder] using
          initialCoefficientPolynomial_stripXAdicFactor_ne_zero hQ

private theorem alekhnovichRootPrefixesWithFuel_precision_pos_of_ne_zero_precisionBound
    {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) {Q : CBivariate F} {k : Nat}
    {rootPrefix : RootPrefix F}
    (hQ : Q ≠ 0)
    (hmem :
      rootPrefix ∈
        (alekhnovichRootPrefixesWithFuel fieldRoots
          (alekhnovichPrecisionBound Q k + 1) Q
          (alekhnovichPrecisionBound Q k)).toList) :
    0 < rootPrefix.precision := by
  let N := alekhnovichPrecisionBound Q k
  have hNpos : 0 < N := by
    dsimp [N]
    unfold alekhnovichPrecisionBound
    omega
  rcases normalizeAlekhnovichInput_precisionBound_some (Q := Q) (k := k) hQ with
    ⟨Qnorm, Nnorm, hnorm, hNnormpos, hNnormle, _hNnormBound, hinit⟩
  have horder0 : CBivariate.xAdicOrder? Qnorm = some 0 :=
    cbivar_xAdicOrder?_eq_zero_of_initial_ne_zero hinit
  have hnormId : normalizeAlekhnovichInput Qnorm Nnorm = some (Qnorm, Nnorm) := by
    unfold normalizeAlekhnovichInput
    simp [horder0, hNnormpos, cbivar_divXPower_zero]
  have hNne : ¬ N = 0 := by omega
  have hNneExpr : ¬ alekhnovichPrecisionBound Q k = 0 := by
    dsimp [N] at hNne
    exact hNne
  have hNnormne : ¬ Nnorm = 0 := by omega
  have hmemNorm :
      rootPrefix ∈
        (alekhnovichRootPrefixesWithFuel fieldRoots (N + 1) Qnorm Nnorm).toList := by
    simpa [N, alekhnovichRootPrefixesWithFuel, hNneExpr, hNnormne, hnorm, hnormId] using hmem
  exact alekhnovichRootPrefixesWithFuel_precision_pos_of_initial_ne_zero
    fieldRoots (fuel := N + 1) (Q := Qnorm) (N := Nnorm)
    (rootPrefix := rootPrefix) (by omega) hNnormpos hinit hmemNorm

private theorem alekhnovichRootPrefixesWithFuel_precision_gt_one_of_ne_zero_precisionBound
    {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) {Q : CBivariate F} {k : Nat}
    {rootPrefix : RootPrefix F}
    (hQ : Q ≠ 0)
    (hmem :
      rootPrefix ∈
        (alekhnovichRootPrefixesWithFuel fieldRoots
          (alekhnovichPrecisionBound Q k + 1) Q
          (alekhnovichPrecisionBound Q k)).toList)
    (hprec : rootPrefix.precision < k) :
    1 < rootPrefix.precision := by
  let N := alekhnovichPrecisionBound Q k
  have hNpos : 0 < N := by
    dsimp [N]
    unfold alekhnovichPrecisionBound
    omega
  rcases normalizeAlekhnovichInput_precisionBound_some (Q := Q) (k := k) hQ with
    ⟨Qnorm, Nnorm, hnorm, hNnormpos, _hNnormle, hNnormBound, hinit⟩
  have horder0 : CBivariate.xAdicOrder? Qnorm = some 0 :=
    cbivar_xAdicOrder?_eq_zero_of_initial_ne_zero hinit
  have hnormId : normalizeAlekhnovichInput Qnorm Nnorm = some (Qnorm, Nnorm) := by
    unfold normalizeAlekhnovichInput
    simp [horder0, hNnormpos, cbivar_divXPower_zero]
  have hNne : ¬ N = 0 := by omega
  have hNneExpr : ¬ alekhnovichPrecisionBound Q k = 0 := by
    dsimp [N] at hNne
    exact hNne
  have hNnormne : ¬ Nnorm = 0 := by omega
  have hmemNorm :
      rootPrefix ∈
        (alekhnovichRootPrefixesWithFuel fieldRoots (N + 1) Qnorm Nnorm).toList := by
    simpa [N, alekhnovichRootPrefixesWithFuel, hNneExpr, hNnormne, hnorm, hnormId] using hmem
  exact alekhnovichRootPrefixesWithFuel_precision_gt_one_of_initial_ne_zero_bound
    fieldRoots hinit hNnormBound hmemNorm hprec

private theorem finishAlekhnovichPrefixWithFuel_complete_of_candidate_ih {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F} {fuel : Nat}
    (ih : ∀ {fuel' : Nat} {Q : CBivariate F} {k : Nat} {p : CPolynomial F},
      fuel' < fuel →
        k < fuel' →
        Q ≠ 0 →
          degreeLt p k →
            CBivariate.composeY Q p = 0 →
              p ∈ (alekhnovichRootCandidatesWithFuel fieldRoots fuel' Q k).toList)
    {Q : CBivariate F} {k : Nat} {p : CPolynomial F}
    {rootPrefix : RootPrefix F}
    (hfuel : k - rootPrefix.precision < fuel - 1)
    (hQ : Q ≠ 0)
    (hmatch : MatchesRootPrefix p rootPrefix)
    (hdegree : degreeLt p k)
    (hroot : CBivariate.composeY Q p = 0) :
    p ∈
      (finishAlekhnovichPrefixWithAlekhnovichWithFuel fieldRoots fuel Q k
        rootPrefix).toList := by
  by_cases hprec : rootPrefix.precision < k
  · let suffixPoly := CPolynomial.dropXPower p rootPrefix.precision
    let residual :=
      CBivariate.stripXAdicFactor
        (substituteYPolynomialPlusXPowerY Q rootPrefix.prefixPoly
          rootPrefix.precision)
    cases fuel with
    | zero =>
        omega
    | succ fuel =>
    have hfuel' : k - rootPrefix.precision < fuel := by
      simpa using hfuel
    have hprec_le : rootPrefix.precision ≤ k := Nat.le_of_lt hprec
    have hresidual_ne : residual ≠ 0 := by
      dsimp [residual]
      exact stripXAdicFactor_ne_zero
        (substituteYPolynomialPlusXPowerY_ne_zero rootPrefix.prefixPoly
          rootPrefix.precision hQ)
    have hdegreeSuffix : degreeLt suffixPoly (k - rootPrefix.precision) := by
      dsimp [suffixPoly]
      exact degreeLt_dropXPower_of_degreeLt_of_le hdegree hprec_le
    have hrootSuffix : CBivariate.composeY residual suffixPoly = 0 := by
      dsimp [residual, suffixPoly]
      exact composeY_shiftedResidual_dropXPower_eq_zero hQ hmatch hroot
    have hsuffixMem :
        suffixPoly ∈
          (alekhnovichRootCandidatesWithFuel fieldRoots fuel residual
            (k - rootPrefix.precision)).toList :=
      ih (fuel' := fuel) (by omega) hfuel' hresidual_ne hdegreeSuffix hrootSuffix
    simp [finishAlekhnovichPrefixWithAlekhnovichWithFuel, hprec]
    have hpEq := rootPrefix_add_shift_dropXPower_eq hmatch
    exact ⟨suffixPoly, Array.mem_def.mpr hsuffixMem, by
      dsimp [suffixPoly]
      exact hpEq⟩
  · exact finishAlekhnovichPrefixWithFuel_complete_of_precision
      (fieldRoots := fieldRoots) (Q := Q) (k := k) (fuel := fuel)
      (p := p) (rootPrefix := rootPrefix) hmatch (Nat.le_of_not_lt hprec) hdegree

/-- Candidate generation coverage for the Alekhnovich-only recursive suffix
completion. -/
theorem alekhnovichRootCandidatesWithFuel_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F} {Q : CBivariate F} {k fuel : Nat}
    {p : CPolynomial F}
    (hfuel : k < fuel)
    (hQ : Q ≠ 0)
    (hdegree : degreeLt p k)
    (hroot : CBivariate.composeY Q p = 0) :
    p ∈ (alekhnovichRootCandidatesWithFuel fieldRoots fuel Q k).toList := by
  induction fuel using Nat.strong_induction_on generalizing Q k p with
  | h fuel ih =>
    cases fuel with
    | zero =>
      omega
    | succ fuel =>
      have hzero : (Q == 0) = false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        exact hQ (beq_iff_eq.mp htrue)
      let N := alekhnovichPrecisionBound Q k
      have hrootMod : RootMod Q p N := RootMod.of_composeY_eq_zero hroot
      rcases alekhnovichRootPrefixesWithFuel_complete
          (fieldRoots := fieldRoots) (Q := Q) (N := N) (fuel := N + 1)
          (p := p) (by omega) hrootMod with
        ⟨rootPrefix, hprefixMem, hmatch⟩
      have hprecPos : 0 < rootPrefix.precision :=
        alekhnovichRootPrefixesWithFuel_precision_pos_of_ne_zero_precisionBound
          fieldRoots hQ (by simpa [N] using hprefixMem)
      let prefixes := alekhnovichRootPrefixesWithFuel fieldRoots (N + 1) Q N
      let step : Array (CPolynomial F) → RootPrefix F → Array (CPolynomial F) :=
        fun out rootPrefix ↦
          out ++ finishAlekhnovichPrefixWithAlekhnovichWithFuel fieldRoots fuel Q k
            rootPrefix
      have hfinish :
          p ∈
            (finishAlekhnovichPrefixWithAlekhnovichWithFuel fieldRoots fuel Q k
              rootPrefix).toList := by
        by_cases hprec : rootPrefix.precision < k
        · have hk_le_fuel : k ≤ fuel := by omega
          have hfuelFinish : k - rootPrefix.precision < fuel - 1 := by
            by_cases hklt : k < fuel
            · omega
            · have hprec_gt_one : 1 < rootPrefix.precision := by
                exact
                  alekhnovichRootPrefixesWithFuel_precision_gt_one_of_ne_zero_precisionBound
                    fieldRoots hQ (by simpa [N] using hprefixMem) hprec
              omega
          have ihFinish :
              ∀ {fuel' : Nat} {Q : CBivariate F} {k : Nat} {p : CPolynomial F},
                fuel' < fuel →
                  k < fuel' →
                    Q ≠ 0 →
                      degreeLt p k →
                        CBivariate.composeY Q p = 0 →
                          p ∈
                            (alekhnovichRootCandidatesWithFuel fieldRoots fuel' Q k).toList := by
            intro fuel' Q' k' p' hfuel' hk' hQ' hdegree' hroot'
            exact ih fuel' (Nat.lt_trans hfuel' (Nat.lt_succ_self fuel))
              hk' hQ' hdegree' hroot'
          exact finishAlekhnovichPrefixWithFuel_complete_of_candidate_ih
            (fieldRoots := fieldRoots) (fuel := fuel) ihFinish hfuelFinish hQ
            hmatch hdegree hroot
        · exact finishAlekhnovichPrefixWithFuel_complete_of_precision
            (fieldRoots := fieldRoots) (Q := Q) (k := k) (fuel := fuel)
            (p := p) (rootPrefix := rootPrefix) hmatch
            (Nat.le_of_not_lt hprec) hdegree
      have hprefixMem' : rootPrefix ∈ prefixes.toList := by
        simpa [prefixes, N] using hprefixMem
      have hstep : ∀ out, p ∈ (step out rootPrefix).toList := by
        intro out
        dsimp [step]
        simp [hfinish]
      have hpres : ∀ out z, p ∈ out.toList → p ∈ (step out z).toList := by
        intro out z hp
        dsimp [step]
        simp [hp]
      have hfold :
          p ∈ (prefixes.foldl step #[]).toList :=
        array_foldl_mem_of_mem_step prefixes step hprefixMem' hstep hpres
      simpa [alekhnovichRootCandidatesWithFuel, hzero, N, prefixes, step] using hfold

/-- The finite modular-root predicate is exact once the substitution degree is
bounded below the checked precision. -/
theorem composeY_eq_zero_of_rootMod_of_substitutionDegreeBound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {Q : CBivariate F} {p : CPolynomial F} {k N : Nat}
    (hbound : SubstitutionDegreeBound Q k N)
    (hdegree : degreeLt p k)
    (hroot : RootMod Q p N) :
    CBivariate.composeY Q p = 0 := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  by_cases hi : i < N
  · exact hroot i hi
  · have hNle : N ≤ i := Nat.le_of_not_lt hi
    rw [← composeYCoeff_eq_composeY_coeff Q p i]
    unfold CBivariate.composeYCoeff
    have hpdeg : p.natDegree ≤ k - 1 := cpoly_natDegree_le_pred_of_degreeLt hdegree
    have hterm : ∀ y, y ∈ List.range' 0 Q.val.size →
        CPolynomial.mulPowCoeff (Q.val.coeff y) p y i = 0 := by
      intro y hy
      rw [cpoly_mulPowCoeff_eq_coeff_mul_pow]
      apply cpoly_coeff_eq_zero_of_natDegree_lt
      have hylt : y < Q.val.size := by
        simpa using (List.mem_range'_1.mp hy).2
      have hpow : (p ^ y).natDegree ≤ y * (k - 1) :=
        cpoly_natDegree_pow_le_of_le p hpdeg y
      have hmul : ((Q.val.coeff y) * p ^ y).natDegree ≤
          (Q.val.coeff y).natDegree + (p ^ y).natDegree :=
        cpoly_natDegree_mul_le_of_field (Q.val.coeff y) (p ^ y)
      have hboundY := hbound y hylt
      omega
    have hfold : ∀ ys : List Nat,
        (∀ y, y ∈ ys → y ∈ List.range' 0 Q.val.size) →
        ys.foldl (fun acc y ↦ acc + CPolynomial.mulPowCoeff (Q.val.coeff y) p y i)
          0 = 0 := by
      intro ys hys
      induction ys with
      | nil => simp
      | cons y ys ih =>
          rw [List.foldl_cons]
          rw [hterm y (hys y (by simp))]
          simpa only [zero_add] using ih (by
            intro z hz
            exact hys z (by simp [hz]))
    exact hfold (List.range' 0 Q.val.size) (by intro y hy; exact hy)

/-- Completeness of Alekhnovich candidate generation for exact bounded roots. -/
theorem alekhnovichRootCandidates_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F} {Q : CBivariate F} {k : Nat}
    {p : CPolynomial F}
    (hQ : Q ≠ 0)
    (hdegree : degreeLt p k)
    (hroot : CBivariate.composeY Q p = 0) :
    p ∈ (alekhnovichRootCandidates fieldRoots Q k).toList := by
  unfold alekhnovichRootCandidates
  exact alekhnovichRootCandidatesWithFuel_complete
    (fieldRoots := fieldRoots) (Q := Q) (k := k) (fuel := k + 1) (p := p)
    (by omega) hQ hdegree hroot

/-- Completeness of Alekhnovich bounded-degree root finding from a complete
field-root backend. -/
theorem alekhnovichRootsYDegreeLt_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F}
    {Q : CBivariate F} {k : Nat} {p : CPolynomial F}
    (hQ : Q ≠ 0) (hdegree : degreeLt p k) (hroot : CBivariate.composeY Q p = 0) :
    p ∈ (alekhnovichRootsYDegreeLt fieldRoots Q k).toList :=
  alekhnovichRootsYDegreeLt_complete_of_candidate_mem hQ
    (alekhnovichRootCandidates_complete
      (fieldRoots := fieldRoots) hQ hdegree hroot)
    hdegree hroot

/-- Alekhnovich roots packaged with an explicit univariate field-root backend. -/
def alekhnovichRootContext (F : Type*)
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) : GSRootContext F where
  rootsYDegreeLt := alekhnovichRootsYDegreeLt fieldRoots
  sound := by
    intro Q k p h
    exact alekhnovichRootsYDegreeLt_sound h
  complete := by
    intro Q k p hQ hdegree hroot
    exact alekhnovichRootsYDegreeLt_complete
      (fieldRoots := fieldRoots) hQ hdegree hroot

end GuruswamiSudan

end CompPoly
