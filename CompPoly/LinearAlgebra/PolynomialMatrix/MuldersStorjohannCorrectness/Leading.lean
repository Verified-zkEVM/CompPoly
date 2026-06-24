/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Conflict

/-!
# Mulders-Storjohann Correctness Shifted Leading Term Helpers

Shifted leading-position data and cancellation degree bounds.
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

omit [LawfulBEq F] [DecidableEq F] in
theorem rowShiftedLeadingPosition?_lt
    {row : PolynomialRow F} {shift : Array Nat} {pos : Nat}
    (hpos : rowShiftedLeadingPosition? row shift = some pos) :
    pos < row.size := by
  unfold rowShiftedLeadingPosition? at hpos
  cases hdeg : rowShiftedDegree? row shift with
  | none =>
      simp [hdeg] at hpos
  | some d =>
      simp [hdeg] at hpos
      have hmemReverse :
          pos ∈ (List.range row.size).reverse :=
        List.mem_of_find?_eq_some hpos
      have hmem : pos ∈ List.range row.size := by
        simpa using (List.mem_reverse.mp hmemReverse)
      exact List.mem_range.mp hmem

omit [LawfulBEq F] [DecidableEq F] in
theorem rowShiftedLeadingPosition?_no_larger_tie
    {row : PolynomialRow F} {shift : Array Nat} {degree pos k : Nat}
    (hdeg : rowShiftedDegree? row shift = some degree)
    (hpos : rowShiftedLeadingPosition? row shift = some pos)
    (hk : k < row.size) (hposk : pos < k) :
    shiftedEntryDegree? row shift k ≠ some degree := by
  have hposBound : pos < row.size := rowShiftedLeadingPosition?_lt hpos
  unfold rowShiftedLeadingPosition? at hpos
  rw [hdeg] at hpos
  set pred : Nat → Bool :=
    fun j ↦
      match shiftedEntryDegree? row shift j with
      | some dj => dj == degree
      | none => false
  change (List.range row.size).reverse.find? pred = some pos at hpos
  rcases (List.find?_eq_some_iff_getElem.mp hpos) with
    ⟨_, idx, hidx, hget, hbefore⟩
  have hidxLen : idx < row.size := by
    simpa [List.length_reverse] using hidx
  have hindexLt :
      (List.range row.size).length - 1 - idx < (List.range row.size).length := by
    simp only [List.length_range]
    omega
  have hgetIndex :
      (List.range row.size)[(List.range row.size).length - 1 - idx]'hindexLt = pos := by
    simpa [List.getElem_reverse hidx] using hget
  have hidxEq : idx = row.size - 1 - pos := by
    rw [List.getElem_range hindexLt] at hgetIndex
    simp only [List.length_range] at hgetIndex
    omega
  intro hentry
  let kidx := row.size - 1 - k
  have hkidxLen : kidx < (List.range row.size).reverse.length := by
    simp [kidx, List.length_reverse]
    omega
  have hgetK : (List.range row.size).reverse[kidx] = k := by
    rw [List.getElem_reverse hkidxLen]
    have hindexLt :
        (List.range row.size).length - 1 - kidx < (List.range row.size).length := by
      simp only [List.length_range]
      omega
    rw [List.getElem_range hindexLt]
    simp [kidx]
    omega
  have hkidx_lt_idx : kidx < idx := by
    simp [kidx, hidxEq]
    omega
  have hnot := hbefore kidx hkidx_lt_idx
  simp [pred, hgetK, hentry] at hnot

omit [Field F] [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem list_find?_some_of_exists
    {α : Type*} (xs : List α) (pred : α → Bool)
    (hexists : ∃ x ∈ xs, pred x = true) :
    ∃ x, xs.find? pred = some x := by
  induction xs with
  | nil =>
      rcases hexists with ⟨_, hx, _⟩
      simp at hx
  | cons x xs ih =>
      by_cases hx : pred x = true
      · exact ⟨x, by simp [List.find?, hx]⟩
      · have htail : ∃ y ∈ xs, pred y = true := by
          rcases hexists with ⟨y, hy, hpred⟩
          simp at hy
          rcases hy with rfl | hy
          · contradiction
          · exact ⟨y, hy, hpred⟩
        rcases ih htail with ⟨y, hyfind⟩
        exact ⟨y, by simp [List.find?, hx, hyfind]⟩

omit [LawfulBEq F] [DecidableEq F] in
theorem rowShiftedLeadingPosition?_some_of_degree
    {row : PolynomialRow F} {shift : Array Nat} {degree : Nat}
    (hdeg : rowShiftedDegree? row shift = some degree) :
    ∃ pos, rowShiftedLeadingPosition? row shift = some pos := by
  unfold rowShiftedLeadingPosition?
  rw [hdeg]
  rcases exists_shiftedEntryDegree?_eq_of_rowShiftedDegree?_eq_some hdeg with
    ⟨j, hj, hentry⟩
  let pred : Nat → Bool :=
    fun j ↦
      match shiftedEntryDegree? row shift j with
      | some dj => dj == degree
      | none => false
  change ∃ pos, (List.range row.size).reverse.find? pred = some pos
  have hexists : ∃ x ∈ (List.range row.size).reverse, pred x = true := by
    refine ⟨j, ?_, ?_⟩
    · simpa using (List.mem_reverse.mpr (List.mem_range.mpr hj))
    · simp [pred, hentry]
  exact list_find?_some_of_exists (List.range row.size).reverse pred hexists

omit [LawfulBEq F] [DecidableEq F] in
theorem rowShiftedLeadingPosition?_le_of_entry_eq_degree
    {row : PolynomialRow F} {shift : Array Nat} {degree pos k : Nat}
    (hdeg : rowShiftedDegree? row shift = some degree)
    (hpos : rowShiftedLeadingPosition? row shift = some pos)
    (hk : k < row.size)
    (hentry : shiftedEntryDegree? row shift k = some degree) :
    k ≤ pos := by
  by_contra hnot
  have hposk : pos < k := by omega
  exact rowShiftedLeadingPosition?_no_larger_tie hdeg hpos hk hposk hentry

omit [DecidableEq F] in
theorem shiftedEntryDegree?_eq_some_of_rowGet_ne_zero
    {row : PolynomialRow F} {shift : Array Nat} {j : Nat}
    (hne : rowGet row j ≠ 0) :
    shiftedEntryDegree? row shift j =
      some ((rowGet row j).natDegree + shift.getD j 0) := by
  have hbeq : (rowGet row j == 0) = false := by
    rw [Bool.eq_false_iff]
    intro htrue
    exact hne (LawfulBEq.eq_of_beq htrue)
  simp [shiftedEntryDegree?, hbeq, Array.getD_eq_getD_getElem?]

omit [DecidableEq F] in
theorem shiftedEntryDegree?_eq_some_iff_data
    {row : PolynomialRow F} {shift : Array Nat} {j d : Nat} :
    shiftedEntryDegree? row shift j = some d ↔
      rowGet row j ≠ 0 ∧
        (rowGet row j).natDegree + shift.getD j 0 = d := by
  constructor
  · intro h
    unfold shiftedEntryDegree? at h
    by_cases hzero : rowGet row j = 0
    · have hbeq : (rowGet row j == 0) = true := by
        rwa [beq_iff_eq]
      simp [hbeq] at h
    · have hbeq : (rowGet row j == 0) = false := by
        rw [Bool.eq_false_iff]
        intro htrue
        exact hzero (LawfulBEq.eq_of_beq htrue)
      simp [hbeq] at h
      exact ⟨hzero, by simpa [Array.getD_eq_getD_getElem?] using h⟩
  · rintro ⟨hne, rfl⟩
    exact shiftedEntryDegree?_eq_some_of_rowGet_ne_zero hne

omit [DecidableEq F] in
theorem rowShiftedDegree?_entry_bound
    {row : PolynomialRow F} {shift : Array Nat} {degree j : Nat}
    (hdeg : rowShiftedDegree? row shift = some degree)
    (hj : j < row.size) (hne : rowGet row j ≠ 0) :
    (rowGet row j).natDegree + shift.getD j 0 ≤ degree := by
  exact shiftedEntryDegree?_le_of_rowShiftedDegree?_eq_some hdeg hj
    (shiftedEntryDegree?_eq_some_of_rowGet_ne_zero hne)

omit [LawfulBEq F] [DecidableEq F] in
theorem rowShiftedLeadingPosition?_entry_eq
    {row : PolynomialRow F} {shift : Array Nat} {degree pos : Nat}
    (hdeg : rowShiftedDegree? row shift = some degree)
    (hpos : rowShiftedLeadingPosition? row shift = some pos) :
    shiftedEntryDegree? row shift pos = some degree := by
  unfold rowShiftedLeadingPosition? at hpos
  rw [hdeg] at hpos
  have hpred := List.find?_some hpos
  cases hentry : shiftedEntryDegree? row shift pos with
  | none =>
      simp [hentry] at hpred
  | some entryDegree =>
      simp [hentry] at hpred
      simp [hpred]

omit [DecidableEq F] in
theorem rowShiftedLeadingTerm?_some_of_position
    {row : PolynomialRow F} {shift : Array Nat} {pos : Nat}
    (hpos : rowShiftedLeadingPosition? row shift = some pos) :
    ∃ term : ShiftedLeadingTerm F,
      rowShiftedLeadingTerm? row shift = some term ∧ term.position = pos := by
  have hposOrig := hpos
  unfold rowShiftedLeadingPosition? at hpos
  cases hdeg : rowShiftedDegree? row shift with
  | none =>
      simp [hdeg] at hpos
  | some shiftedDegree =>
      simp [hdeg] at hpos
      have hentry := rowShiftedLeadingPosition?_entry_eq hdeg hposOrig
      rcases shiftedEntryDegree?_eq_some_iff_data.1 hentry with ⟨hne, _⟩
      have hbeq : (rowGet row pos == 0) = false := by
        rw [Bool.eq_false_iff]
        intro htrue
        exact hne (LawfulBEq.eq_of_beq htrue)
      refine ⟨
        { position := pos
          degree := (rowGet row pos).natDegree
          shiftedDegree := shiftedDegree
          coeff := (rowGet row pos).coeff (rowGet row pos).natDegree },
        ?_, rfl⟩
      simp [rowShiftedLeadingTerm?, hdeg, hposOrig, hbeq]

omit [DecidableEq F] in
theorem rowShiftedLeadingTerm?_some_data
    {row : PolynomialRow F} {shift : Array Nat} {term : ShiftedLeadingTerm F}
    (hterm : rowShiftedLeadingTerm? row shift = some term) :
    rowShiftedDegree? row shift = some term.shiftedDegree ∧
      rowShiftedLeadingPosition? row shift = some term.position ∧
      rowGet row term.position ≠ 0 ∧
      term.degree = (rowGet row term.position).natDegree ∧
      term.shiftedDegree = term.degree + shift.getD term.position 0 ∧
      term.coeff = (rowGet row term.position).coeff term.degree := by
  unfold rowShiftedLeadingTerm? at hterm
  cases hdeg : rowShiftedDegree? row shift with
  | none =>
      simp [hdeg] at hterm
  | some shiftedDegree =>
      cases hpos : rowShiftedLeadingPosition? row shift with
      | none =>
          simp [hdeg, hpos] at hterm
      | some pos =>
          simp [hdeg, hpos] at hterm
          by_cases hzero : rowGet row pos = 0
          · exact False.elim (hterm.1 hzero)
          · have htermEq := hterm.2
            subst term
            have hentry := rowShiftedLeadingPosition?_entry_eq hdeg hpos
            have hentryData := shiftedEntryDegree?_eq_some_iff_data.1 hentry
            rcases hentryData with ⟨_, hshifted⟩
            simpa [hdeg, hpos, hzero, Array.getD_eq_getD_getElem?] using hshifted.symm

omit [DecidableEq F] in
theorem rowShiftedLeadingTerm?_coeff_ne_zero
    {row : PolynomialRow F} {shift : Array Nat} {term : ShiftedLeadingTerm F}
    (hterm : rowShiftedLeadingTerm? row shift = some term) :
    term.coeff ≠ 0 := by
  rcases rowShiftedLeadingTerm?_some_data hterm with
    ⟨_, _, hrow, hdegree, _, hcoeff⟩
  intro hzero
  have hlead := CPolynomial.leadingCoeff_ne_zero hrow
  apply hlead
  rw [CPolynomial.leadingCoeff_eq_coeff_natDegree, ← hdegree, ← hcoeff]
  exact hzero

omit [DecidableEq F] in
theorem cpoly_natDegree_mul_le (P Q : CPolynomial F) :
    (P * Q).natDegree ≤ P.natDegree + Q.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_mul,
    CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly]
  exact Polynomial.natDegree_mul_le

omit [DecidableEq F] in
theorem cpoly_natDegree_mul
    {P Q : CPolynomial F} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (P * Q).natDegree = P.natDegree + Q.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_mul,
    CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly]
  exact Polynomial.natDegree_mul
    ((CPolynomial.toPoly_eq_zero_iff P).not.mpr hP)
    ((CPolynomial.toPoly_eq_zero_iff Q).not.mpr hQ)

omit [DecidableEq F] in
theorem cpoly_coeff_mul_natDegree_add_ne_zero
    {P Q : CPolynomial F} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (P * Q).coeff (P.natDegree + Q.natDegree) ≠ 0 := by
  have hprod : P * Q ≠ 0 := by
    intro hzero
    have htoProd : (P * Q).toPoly ≠ 0 := by
      rw [CPolynomial.toPoly_mul]
      exact mul_ne_zero
        ((CPolynomial.toPoly_eq_zero_iff P).not.mpr hP)
        ((CPolynomial.toPoly_eq_zero_iff Q).not.mpr hQ)
    exact htoProd (by rw [hzero, CPolynomial.toPoly_zero])
  have hlead := CPolynomial.leadingCoeff_ne_zero hprod
  rw [CPolynomial.leadingCoeff_eq_coeff_natDegree,
    cpoly_natDegree_mul hP hQ] at hlead
  exact hlead

omit [DecidableEq F] in
theorem cpoly_natDegree_sub_le (P Q : CPolynomial F) :
    (P - Q).natDegree ≤ max P.natDegree Q.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_sub,
    CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly]
  exact Polynomial.natDegree_sub_le P.toPoly Q.toPoly

omit [DecidableEq F] in
theorem cpoly_natDegree_neg (P : CPolynomial F) :
    (-P).natDegree = P.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_neg,
    CPolynomial.natDegree_toPoly, Polynomial.natDegree_neg]

theorem cpoly_natDegree_monomial_le (d : Nat) (c : F) :
    (CPolynomial.monomial d c).natDegree ≤ d := by
  by_cases hc : c = 0
  · subst c
    simp [CPolynomial.monomial, CPolynomial.Raw.monomial, CPolynomial.natDegree]
  · rw [CPolynomial.natDegree_monomial hc]

theorem cpoly_natDegree_monomial_mul_le
    (d : Nat) (c : F) (P : CPolynomial F) :
    (CPolynomial.monomial d c * P).natDegree ≤ d + P.natDegree := by
  have hmul := cpoly_natDegree_mul_le (CPolynomial.monomial d c) P
  have hmono := cpoly_natDegree_monomial_le d c
  omega

theorem cpoly_coeff_monomial_mul
    (n d : Nat) (c : F) (P : CPolynomial F) :
    (CPolynomial.monomial n c * P).coeff (d + n) =
      c * P.coeff d := by
  rw [CPolynomial.coeff_toPoly, CPolynomial.toPoly_mul]
  have hmono :
      (CPolynomial.monomial n c).toPoly = Polynomial.monomial n c :=
    CPolynomial.monomial_toPoly n c
  rw [hmono]
  rw [Polynomial.coeff_monomial_mul]
  rw [← CPolynomial.coeff_toPoly]

omit [DecidableEq F] in
theorem cpoly_natDegree_sub_shift_le
    {P Q : CPolynomial F} {shiftDegree bound : Nat}
    (hP : P ≠ 0 → P.natDegree + shiftDegree ≤ bound)
    (hQ : Q ≠ 0 → Q.natDegree + shiftDegree ≤ bound)
    (hne : P - Q ≠ 0) :
    (P - Q).natDegree + shiftDegree ≤ bound := by
  have hsub := cpoly_natDegree_sub_le P Q
  by_cases hPzero : P = 0
  · by_cases hQzero : Q = 0
    · subst P
      subst Q
      simp at hne
    · have hQbound := hQ hQzero
      simpa [hPzero, cpoly_natDegree_neg] using hQbound
  · by_cases hQzero : Q = 0
    · have hPbound := hP hPzero
      simpa [hQzero] using hPbound
    · have hPbound := hP hPzero
      have hQbound := hQ hQzero
      omega

omit [DecidableEq F] in
theorem cpoly_natDegree_sub_shift_lt
    {P Q : CPolynomial F} {shiftDegree bound : Nat}
    (hP : P ≠ 0 → P.natDegree + shiftDegree < bound)
    (hQ : Q ≠ 0 → Q.natDegree + shiftDegree < bound)
    (hne : P - Q ≠ 0) :
    (P - Q).natDegree + shiftDegree < bound := by
  have hsub := cpoly_natDegree_sub_le P Q
  by_cases hPzero : P = 0
  · by_cases hQzero : Q = 0
    · subst P
      subst Q
      simp at hne
    · have hQbound := hQ hQzero
      simpa [hPzero, cpoly_natDegree_neg] using hQbound
  · by_cases hQzero : Q = 0
    · have hPbound := hP hPzero
      simpa [hQzero] using hPbound
    · have hPbound := hP hPzero
      have hQbound := hQ hQzero
      omega

omit [DecidableEq F] in
theorem rowShiftedDegree?_le_of_entry_bound
    {row : PolynomialRow F} {shift : Array Nat} {degree bound : Nat}
    (hbound : ∀ k, k < row.size → rowGet row k ≠ 0 →
      (rowGet row k).natDegree + shift.getD k 0 ≤ bound)
    (hdeg : rowShiftedDegree? row shift = some degree) :
    degree ≤ bound := by
  rcases exists_shiftedEntryDegree?_eq_of_rowShiftedDegree?_eq_some hdeg with
    ⟨k, hk, hentry⟩
  rcases shiftedEntryDegree?_eq_some_iff_data.1 hentry with ⟨hne, hentryEq⟩
  have hkBound := hbound k hk hne
  omega

omit [DecidableEq F] in
theorem rowShiftedLeadingTerm?_entry_bound
    {row : PolynomialRow F} {shift : Array Nat} {term : ShiftedLeadingTerm F}
    (hterm : rowShiftedLeadingTerm? row shift = some term)
    {k : Nat} (hk : k < row.size) (hne : rowGet row k ≠ 0) :
    (rowGet row k).natDegree + shift.getD k 0 ≤ term.shiftedDegree := by
  rcases rowShiftedLeadingTerm?_some_data hterm with
    ⟨hdeg, _, _, _, _, _⟩
  exact rowShiftedDegree?_entry_bound hdeg hk hne

omit [DecidableEq F] in
theorem rowShiftedLeadingTerm?_entry_strict_of_pos_lt
    {row : PolynomialRow F} {shift : Array Nat} {term : ShiftedLeadingTerm F}
    (hterm : rowShiftedLeadingTerm? row shift = some term)
    {k : Nat} (hk : k < row.size) (hposlt : term.position < k)
    (hne : rowGet row k ≠ 0) :
    (rowGet row k).natDegree + shift.getD k 0 < term.shiftedDegree := by
  rcases rowShiftedLeadingTerm?_some_data hterm with
    ⟨hdeg, hpos, _, _, _, _⟩
  have hle := rowShiftedDegree?_entry_bound hdeg hk hne
  have hnot :=
    rowShiftedLeadingPosition?_no_larger_tie hdeg hpos hk hposlt
  have hentry := shiftedEntryDegree?_eq_some_of_rowGet_ne_zero (shift := shift) hne
  have hneEq :
      (rowGet row k).natDegree + shift.getD k 0 ≠ term.shiftedDegree := by
    intro heq
    have heq' :
        (rowGet row k).natDegree + shift[k]?.getD 0 = term.shiftedDegree := by
      simpa [Array.getD_eq_getD_getElem?] using heq
    exact hnot (by simpa [heq'] using hentry)
  omega

theorem rowScaleMonomial_entry_bound_of_leading_terms
    {target reducer : PolynomialRow F} {shift : Array Nat}
    {t r : ShiftedLeadingTerm F}
    (ht : rowShiftedLeadingTerm? target shift = some t)
    (hr : rowShiftedLeadingTerm? reducer shift = some r)
    (hpos : t.position = r.position)
    (hle : r.shiftedDegree ≤ t.shiftedDegree)
    {k : Nat} (hk : k < reducer.size)
    (hne : rowGet
      (rowScaleMonomial (t.coeff / r.coeff) (t.degree - r.degree) reducer) k ≠ 0) :
    (rowGet
      (rowScaleMonomial (t.coeff / r.coeff) (t.degree - r.degree) reducer) k).natDegree +
        shift.getD k 0 ≤ t.shiftedDegree := by
  rcases rowShiftedLeadingTerm?_some_data ht with
    ⟨_, _, _, _, htShifted, _⟩
  rcases rowShiftedLeadingTerm?_some_data hr with
    ⟨hrRowDegree, _, _, _, hrShifted, _⟩
  have hdegLe : r.degree ≤ t.degree := by
    have hrShiftedAtTarget :
        r.shiftedDegree = r.degree + shift.getD t.position 0 := by
      simpa [← hpos] using hrShifted
    omega
  have hdelta : (t.degree - r.degree) + r.shiftedDegree = t.shiftedDegree := by
    have hrShiftedAtTarget :
        r.shiftedDegree = r.degree + shift.getD t.position 0 := by
      simpa [← hpos] using hrShifted
    omega
  have hscaledNatDegree :=
    cpoly_natDegree_monomial_mul_le (t.degree - r.degree)
      (t.coeff / r.coeff) (rowGet reducer k)
  have hreducerNonzero : rowGet reducer k ≠ 0 := by
    intro hzero
    apply hne
    simp [rowGet_rowScaleMonomial, hzero]
  have hreducerBound :
      (rowGet reducer k).natDegree + shift.getD k 0 ≤ r.shiftedDegree :=
    rowShiftedDegree?_entry_bound hrRowDegree hk hreducerNonzero
  rw [rowGet_rowScaleMonomial] at hne ⊢
  omega

theorem rowScaleMonomial_entry_strict_of_pos_lt
    {target reducer : PolynomialRow F} {shift : Array Nat}
    {t r : ShiftedLeadingTerm F}
    (ht : rowShiftedLeadingTerm? target shift = some t)
    (hr : rowShiftedLeadingTerm? reducer shift = some r)
    (hpos : t.position = r.position)
    (hle : r.shiftedDegree ≤ t.shiftedDegree)
    {k : Nat} (hk : k < reducer.size) (hposlt : t.position < k)
    (hne : rowGet
      (rowScaleMonomial (t.coeff / r.coeff) (t.degree - r.degree) reducer) k ≠ 0) :
    (rowGet
      (rowScaleMonomial (t.coeff / r.coeff) (t.degree - r.degree) reducer) k).natDegree +
        shift.getD k 0 < t.shiftedDegree := by
  rcases rowShiftedLeadingTerm?_some_data ht with
    ⟨_, _, _, _, htShifted, _⟩
  rcases rowShiftedLeadingTerm?_some_data hr with
    ⟨_, _, _, _, hrShifted, _⟩
  have hdelta : (t.degree - r.degree) + r.shiftedDegree = t.shiftedDegree := by
    have hrShiftedAtTarget :
        r.shiftedDegree = r.degree + shift.getD t.position 0 := by
      simpa [← hpos] using hrShifted
    omega
  have hreducerNonzero : rowGet reducer k ≠ 0 := by
    intro hzero
    apply hne
    simp [rowGet_rowScaleMonomial, hzero]
  have hreducerStrict :
      (rowGet reducer k).natDegree + shift.getD k 0 < r.shiftedDegree := by
    apply rowShiftedLeadingTerm?_entry_strict_of_pos_lt hr hk
    · simpa [← hpos] using hposlt
    · exact hreducerNonzero
  have hscaledNatDegree :=
    cpoly_natDegree_monomial_mul_le (t.degree - r.degree)
      (t.coeff / r.coeff) (rowGet reducer k)
  rw [rowGet_rowScaleMonomial] at hne ⊢
  omega

theorem cancelShiftedLeadingTerm_coeff_cancel
    {target reducer : PolynomialRow F} {shift : Array Nat}
    {t r : ShiftedLeadingTerm F}
    (ht : rowShiftedLeadingTerm? target shift = some t)
    (hr : rowShiftedLeadingTerm? reducer shift = some r)
    (hpos : t.position = r.position)
    (hle : r.shiftedDegree ≤ t.shiftedDegree)
    (hrcoeff : r.coeff ≠ 0) :
    (rowGet (cancelShiftedLeadingTerm target reducer shift) t.position).coeff t.degree = 0 := by
  rcases rowShiftedLeadingTerm?_some_data ht with
    ⟨_, _, _, htDegree, htShifted, htCoeff⟩
  rcases rowShiftedLeadingTerm?_some_data hr with
    ⟨_, _, _, hrDegree, hrShifted, hrCoeff⟩
  have hdegLe : r.degree ≤ t.degree := by
    have hrShiftedAtTarget :
        r.shiftedDegree = r.degree + shift.getD t.position 0 := by
      simpa [← hpos] using hrShifted
    omega
  have hposBeq : (t.position == r.position) = true := by
    rwa [beq_iff_eq]
  have hrcoeffBeq : (r.coeff == 0) = false := by
    rw [Bool.eq_false_iff]
    intro htrue
    exact hrcoeff (LawfulBEq.eq_of_beq htrue)
  unfold cancelShiftedLeadingTerm
  rw [ht, hr]
  simp [hposBeq, hrcoeffBeq, rowGet_rowSub, rowGet_rowScaleMonomial]
  rw [← Array.getD_eq_getD_getElem?]
  change
    (rowGet target t.position -
        CPolynomial.monomial (t.degree - r.degree) (t.coeff / r.coeff) *
          rowGet reducer t.position).coeff t.degree = 0
  rw [CPolynomial.coeff_sub]
  have hreducerCoeff :
      (rowGet reducer t.position).coeff r.degree = r.coeff := by
    have hrCoeffAtTarget :
        r.coeff = (rowGet reducer t.position).coeff r.degree := by
      simpa [← hpos] using hrCoeff
    exact hrCoeffAtTarget.symm
  have hscaled :
      (CPolynomial.monomial (t.degree - r.degree) (t.coeff / r.coeff) *
          rowGet reducer t.position).coeff t.degree = t.coeff := by
    have hsum : r.degree + (t.degree - r.degree) = t.degree := by omega
    have hcoeff := cpoly_coeff_monomial_mul
      (n := t.degree - r.degree) (d := r.degree)
      (c := t.coeff / r.coeff) (P := rowGet reducer t.position)
    rw [hsum, hreducerCoeff] at hcoeff
    simpa [div_mul_cancel₀ t.coeff hrcoeff] using hcoeff
  rw [hscaled]
  simp [htCoeff]

theorem cancelShiftedLeadingTerm_no_target_shifted_entry
    {target reducer : PolynomialRow F} {shift : Array Nat}
    {t r : ShiftedLeadingTerm F}
    (ht : rowShiftedLeadingTerm? target shift = some t)
    (hr : rowShiftedLeadingTerm? reducer shift = some r)
    (hpos : t.position = r.position)
    (hle : r.shiftedDegree ≤ t.shiftedDegree) :
    shiftedEntryDegree? (cancelShiftedLeadingTerm target reducer shift) shift t.position ≠
      some t.shiftedDegree := by
  have hrcoeff : r.coeff ≠ 0 := rowShiftedLeadingTerm?_coeff_ne_zero hr
  have hcancelCoeff :=
    cancelShiftedLeadingTerm_coeff_cancel ht hr hpos hle hrcoeff
  rcases rowShiftedLeadingTerm?_some_data ht with
    ⟨_, _, _, _, htShifted, _⟩
  intro hentry
  rcases shiftedEntryDegree?_eq_some_iff_data.1 hentry with
    ⟨hrow, hentryEq⟩
  have hnatDegree :
      (rowGet (cancelShiftedLeadingTerm target reducer shift) t.position).natDegree =
        t.degree := by
    omega
  have hlead :=
    CPolynomial.leadingCoeff_ne_zero hrow
  have hcoeffNonzero :
      (rowGet (cancelShiftedLeadingTerm target reducer shift) t.position).coeff
        t.degree ≠ 0 := by
    rw [← hnatDegree]
    simpa [CPolynomial.leadingCoeff_eq_coeff_natDegree] using hlead
  exact hcoeffNonzero hcancelCoeff

theorem cancelShiftedLeadingTerm_entry_bound
    {target reducer : PolynomialRow F} {shift : Array Nat}
    {t r : ShiftedLeadingTerm F}
    (ht : rowShiftedLeadingTerm? target shift = some t)
    (hr : rowShiftedLeadingTerm? reducer shift = some r)
    (hpos : t.position = r.position)
    (hle : r.shiftedDegree ≤ t.shiftedDegree)
    (hsize : reducer.size = target.size)
    {k : Nat} (hk : k < target.size)
    (hne : rowGet (cancelShiftedLeadingTerm target reducer shift) k ≠ 0) :
    (rowGet (cancelShiftedLeadingTerm target reducer shift) k).natDegree +
        shift.getD k 0 ≤ t.shiftedDegree := by
  have hrcoeff : r.coeff ≠ 0 := rowShiftedLeadingTerm?_coeff_ne_zero hr
  have hposBeq : (t.position == r.position) = true := by
    rwa [beq_iff_eq]
  have hrcoeffBeq : (r.coeff == 0) = false := by
    rw [Bool.eq_false_iff]
    intro htrue
    exact hrcoeff (LawfulBEq.eq_of_beq htrue)
  unfold cancelShiftedLeadingTerm at hne ⊢
  rw [ht, hr] at hne ⊢
  simp [hposBeq, hrcoeffBeq, rowGet_rowSub, rowGet_rowScaleMonomial] at hne ⊢
  apply cpoly_natDegree_sub_shift_le
  · intro htargetNonzero
    simpa [Array.getD_eq_getD_getElem?] using
      rowShiftedLeadingTerm?_entry_bound ht hk htargetNonzero
  · intro hscaledNonzero
    have hkReducer : k < reducer.size := by omega
    have hscaledRowNonzero :
        rowGet
          (rowScaleMonomial (t.coeff / r.coeff) (t.degree - r.degree) reducer) k ≠ 0 := by
      simpa [rowGet_rowScaleMonomial] using hscaledNonzero
    have hbound :=
      rowScaleMonomial_entry_bound_of_leading_terms ht hr hpos hle hkReducer
        hscaledRowNonzero
    simpa [rowGet_rowScaleMonomial, Array.getD_eq_getD_getElem?] using hbound
  · exact hne

theorem cancelShiftedLeadingTerm_entry_strict_of_pos_lt
    {target reducer : PolynomialRow F} {shift : Array Nat}
    {t r : ShiftedLeadingTerm F}
    (ht : rowShiftedLeadingTerm? target shift = some t)
    (hr : rowShiftedLeadingTerm? reducer shift = some r)
    (hpos : t.position = r.position)
    (hle : r.shiftedDegree ≤ t.shiftedDegree)
    (hsize : reducer.size = target.size)
    {k : Nat} (hk : k < target.size) (hposlt : t.position < k)
    (hne : rowGet (cancelShiftedLeadingTerm target reducer shift) k ≠ 0) :
    (rowGet (cancelShiftedLeadingTerm target reducer shift) k).natDegree +
        shift.getD k 0 < t.shiftedDegree := by
  have hrcoeff : r.coeff ≠ 0 := rowShiftedLeadingTerm?_coeff_ne_zero hr
  have hposBeq : (t.position == r.position) = true := by
    rwa [beq_iff_eq]
  have hrcoeffBeq : (r.coeff == 0) = false := by
    rw [Bool.eq_false_iff]
    intro htrue
    exact hrcoeff (LawfulBEq.eq_of_beq htrue)
  unfold cancelShiftedLeadingTerm at hne ⊢
  rw [ht, hr] at hne ⊢
  simp [hposBeq, hrcoeffBeq, rowGet_rowSub, rowGet_rowScaleMonomial] at hne ⊢
  apply cpoly_natDegree_sub_shift_lt
  · intro htargetNonzero
    simpa [Array.getD_eq_getD_getElem?] using
      rowShiftedLeadingTerm?_entry_strict_of_pos_lt ht hk hposlt htargetNonzero
  · intro hscaledNonzero
    have hkReducer : k < reducer.size := by omega
    have hscaledRowNonzero :
        rowGet
          (rowScaleMonomial (t.coeff / r.coeff) (t.degree - r.degree) reducer) k ≠ 0 := by
      simpa [rowGet_rowScaleMonomial] using hscaledNonzero
    have hbound :=
      rowScaleMonomial_entry_strict_of_pos_lt ht hr hpos hle hkReducer hposlt
        hscaledRowNonzero
    simpa [rowGet_rowScaleMonomial, Array.getD_eq_getD_getElem?] using hbound
  · exact hne

end PolynomialMatrix

end CompPoly
