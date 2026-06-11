/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.Common
import CompPoly.Bivariate.GuruswamiSudan.PolynomialCorrectness

/-!
# Common Guruswami-Sudan Root Helper Lemmas

Reusable proof facts for bounded bivariate root backends.
-/

namespace CompPoly

theorem array_mem_eraseDups_fold {α : Type*} [BEq α] [LawfulBEq α]
    (a : α) : ∀ (xs : List α) (out : Array α),
      a ∈ List.foldl (fun out x ↦ if x ∈ out then out else out.push x) out xs →
        a ∈ out ∨ a ∈ xs := by
  intro xs
  induction xs with
  | nil =>
      intro out h
      exact Or.inl h
  | cons x xs ih =>
      intro out h
      simp only [List.foldl_cons] at h
      by_cases hx : x ∈ out
      · have h' := ih out (by simpa [hx] using h)
        cases h' with
        | inl hout => exact Or.inl hout
        | inr hxs => exact Or.inr (by simp [hxs])
      · have h' := ih (out.push x) (by simpa [hx] using h)
        cases h' with
        | inl hout =>
            simp at hout
            cases hout with
            | inl hout => exact Or.inl hout
            | inr hax => exact Or.inr (by simp [hax])
        | inr hxs => exact Or.inr (by simp [hxs])

theorem array_mem_of_mem_eraseDups {α : Type*} [BEq α] [LawfulBEq α]
    {xs : Array α} {a : α} (h : a ∈ xs.eraseDups) : a ∈ xs := by
  unfold Array.eraseDups at h
  rcases xs with ⟨l⟩
  simp at h ⊢
  have hh := array_mem_eraseDups_fold a l #[] h
  simpa using hh

theorem array_mem_eraseDups_fold_of_mem {α : Type*} [BEq α] [LawfulBEq α]
    (a : α) : ∀ (xs : List α) (out : Array α),
      a ∈ out ∨ a ∈ xs →
        a ∈ List.foldl (fun out x ↦ if x ∈ out then out else out.push x) out xs
  | [], out, h => by
      rcases h with h | h
      · exact h
      · simp at h
  | x :: xs, out, h => by
      rw [List.foldl_cons]
      by_cases hx : x ∈ out
      · rw [if_pos hx]
        apply array_mem_eraseDups_fold_of_mem a xs out
        rcases h with h | h
        · exact Or.inl h
        · simp at h
          rcases h with rfl | h
          · exact Or.inl hx
          · exact Or.inr h
      · rw [if_neg hx]
        apply array_mem_eraseDups_fold_of_mem a xs (out.push x)
        rcases h with h | h
        · exact Or.inl (by simp [h])
        · simp at h
          rcases h with rfl | h
          · exact Or.inl (by simp)
          · exact Or.inr h

theorem array_mem_eraseDups_of_mem {α : Type*} [BEq α] [LawfulBEq α]
    {xs : Array α} {a : α} (h : a ∈ xs) : a ∈ xs.eraseDups := by
  unfold Array.eraseDups
  rcases xs with ⟨l⟩
  simp at h ⊢
  exact array_mem_eraseDups_fold_of_mem a l #[] (Or.inr h)

namespace GuruswamiSudan

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

theorem cbivar_coeff_truncateX {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (Q : CBivariate R) (n i j : Nat) :
    CBivariate.coeff (CBivariate.truncateX Q n) i j =
      if i < n then CBivariate.coeff Q i j else 0 := by
  unfold CBivariate.coeff CBivariate.truncateX
  unfold CPolynomial.ofArray
  rw [CPolynomial.Raw.Trim.coeff_eq_coeff]
  unfold CPolynomial.Raw.coeff
  by_cases hj : j < Q.val.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hj]
    simpa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj] using
      cpoly_truncate_coeff Q.val[j] n i
  · have hjle : Q.val.size ≤ j := Nat.le_of_not_lt hj
    have hmaple : (Q.val.map fun coeff ↦ CPolynomial.truncate coeff n).size ≤ j := by
      simpa using hjle
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hmaple]
    change (0 : CPolynomial R).coeff i =
      if i < n then (Array.getD Q.val j 0).coeff i else 0
    rw [CPolynomial.coeff_zero]
    by_cases hi : i < n
    · rw [if_pos hi]
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hjle]
      change 0 = (0 : CPolynomial R).coeff i
      rw [CPolynomial.coeff_zero]
    · rw [if_neg hi]

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
    rw [if_neg hi, CPolynomial.coeff_eq_zero_of_size_le p hsize]

theorem list_foldl_add_eq_sum {R : Type*} [AddMonoid R]
    (f : Nat → R) : ∀ (xs : List Nat) (acc : R),
    List.foldl (fun acc i ↦ acc + f i) acc xs = acc + (xs.map f).sum
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

theorem cpoly_eval_add {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) (c : R) :
    CPolynomial.eval c (p + q) = CPolynomial.eval c p + CPolynomial.eval c q := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_add, Polynomial.eval_add,
    ← CPolynomial.eval_toPoly, ← CPolynomial.eval_toPoly]

theorem cpoly_eval_monomial {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (y : Nat) (a c : R) :
    (CPolynomial.monomial y a).eval c = a * c ^ y := by
  rw [CPolynomial.eval_toPoly]
  rw [show (CPolynomial.monomial y a : CPolynomial R).toPoly =
      Polynomial.monomial y a from CPolynomial.monomial_toPoly (R := R) y a]
  simp [Polynomial.eval_monomial]

theorem composeY_add {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (P Q : CBivariate R) (p : CPolynomial R) :
    CBivariate.composeY (P + Q) p = CBivariate.composeY P p + CBivariate.composeY Q p := by
  unfold CBivariate.composeY
  exact cpoly_eval_add P Q p

theorem composeY_outer_monomial {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (c p : CPolynomial R) (y : Nat) :
    CBivariate.composeY (CPolynomial.monomial y c : CBivariate R) p = c * p ^ y := by
  unfold CBivariate.composeY
  exact cpoly_eval_monomial y c p

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
        (fun acc y ↦ acc + (xs.getD (y - offset) 0).coeff 0 * p.coeff 0 ^ y)
        accCoeff (List.range' offset xs.length) =
      (List.foldl (fun acc x ↦ acc + x.1 * p ^ x.2) accPoly
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
        (f := fun acc y ↦
          acc + ((x :: xs).getD (y - offset) 0).coeff 0 * p.coeff 0 ^ y)
        (g := fun acc y ↦
          acc + (xs.getD (y - (offset + 1)) 0).coeff 0 * p.coeff 0 ^ y)
        (List.range' (offset + 1) xs.length)
        (accCoeff + x.coeff 0 * p.coeff 0 ^ offset)
        (fun _acc y hy ↦ by
          have hsub : y - offset = (y - (offset + 1)) + 1 := by
            have hymem := List.mem_range'.mp hy
            omega
          simp [hsub])]
      apply ih
      rw [CPolynomial.coeff_add, cpoly_coeff_zero_mul, cpoly_coeff_zero_pow, hacc]

theorem composeY_coeff_zero_fold_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (coeffs : Array (CPolynomial F)) (p : CPolynomial F) :
    List.foldl (fun acc y ↦ acc + (coeffs.getD y 0).coeff 0 * p.coeff 0 ^ y) 0
        (List.range' 0 coeffs.size) =
      (Array.foldl (fun acc x ↦ acc + x.1 * p ^ x.2) 0 coeffs.zipIdx).coeff 0 := by
  rw [Array.foldl_zipIdx_eq_foldl_toList_zipIdx]
  simpa using
    (composeY_coeff_zero_zipIdx_eq_range_aux coeffs.toList p (0 : CPolynomial F) 0 0
      (by rw [CPolynomial.coeff_zero]))

theorem composeY_coeff_zipIdx_eq_range_aux {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (xs : List (CPolynomial R)) (p accPoly : CPolynomial R) (accCoeff : R)
    (offset n : Nat) (hacc : accPoly.coeff n = accCoeff) :
    List.foldl
        (fun acc y ↦ acc + ((xs.getD (y - offset) 0) * p ^ y).coeff n)
        accCoeff (List.range' offset xs.length) =
      (List.foldl (fun acc x ↦ acc + x.1 * p ^ x.2) accPoly
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
        (f := fun acc y ↦
          acc + (((x :: xs).getD (y - offset) 0) * p ^ y).coeff n)
        (g := fun acc y ↦
          acc + ((xs.getD (y - (offset + 1)) 0) * p ^ y).coeff n)
        (List.range' (offset + 1) xs.length)
        (accCoeff + (x * p ^ offset).coeff n)
        (fun _acc y hy ↦ by
          have hsub : y - offset = (y - (offset + 1)) + 1 := by
            have hymem := List.mem_range'.mp hy
            omega
          simp [hsub])]
      apply ih
      rw [CPolynomial.coeff_add, hacc]

theorem composeY_coeff_fold_eq {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (coeffs : Array (CPolynomial R)) (p : CPolynomial R) (n : Nat) :
    List.foldl (fun acc y ↦ acc + ((coeffs.getD y 0) * p ^ y).coeff n) 0
        (List.range' 0 coeffs.size) =
      (Array.foldl (fun acc x ↦ acc + x.1 * p ^ x.2) 0 coeffs.zipIdx).coeff n := by
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
        (List.foldl (fun acc y ↦ acc + coeffs.getD y 0 * p ^ y) acc ys).coeff n =
          List.foldl
            (fun acc y ↦ acc + ((coeffs.getD y 0) * p ^ y).coeff n)
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
        (fun acc y ↦ acc + Q.val.coeff y * p ^ y) 0 := by
  rw [CPolynomial.eq_iff_coeff]
  intro n
  rw [fold_range_coeff_add_mul_pow Q.val p (List.range' 0 Q.val.size) 0 0 n
    (CPolynomial.coeff_zero n)]
  rw [← composeYCoeff_eq_composeY_coeff]
  unfold CBivariate.composeYCoeff
  simp [cpoly_mulPowCoeff_eq_coeff_mul_pow]

theorem composeY_zero {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) :
    CBivariate.composeY (0 : CBivariate R) p = 0 := by
  rw [composeY_eq_range_fold]
  rfl

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
    fun out y ↦ out + CPolynomial.monomial y (CBivariate.coeff Q 0 y)
  let coeffStep : F → Nat → F :=
    fun acc y ↦ acc + CPolynomial.mulPowCoeff (Q.val.coeff y)
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

theorem rootsYDegreeLtFromCandidates_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {candidates : Array (CPolynomial F)} {Q : CBivariate F} {k : Nat}
    {p : CPolynomial F}
    (h : p ∈ (rootsYDegreeLtFromCandidates candidates Q k).toList) :
    degreeLt p k ∧ CBivariate.composeY Q p = 0 := by
  unfold rootsYDegreeLtFromCandidates at h
  simp [isRootYDegreeLtBool] at h
  exact ⟨degreeLt_of_degreeLtBool h.2.1, composeY_of_composeYHorner_eq_zero h.2.2⟩

theorem rootsYDegreeLtFromCandidates_eraseDups_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {candidates : Array (CPolynomial F)} {Q : CBivariate F} {k : Nat}
    {p : CPolynomial F}
    (h : p ∈ (rootsYDegreeLtFromCandidates candidates Q k).eraseDups.toList) :
    degreeLt p k ∧ CBivariate.composeY Q p = 0 := by
  have hmem : p ∈ rootsYDegreeLtFromCandidates candidates Q k :=
    array_mem_of_mem_eraseDups (by simpa using h)
  exact rootsYDegreeLtFromCandidates_sound (by simpa using hmem)

theorem rootsYDegreeLtFromCandidates_complete_of_mem {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {candidates : Array (CPolynomial F)} {Q : CBivariate F} {k : Nat}
    {p : CPolynomial F}
    (hmem : p ∈ candidates.toList)
    (hdegree : degreeLt p k) (hroot : CBivariate.composeY Q p = 0) :
    p ∈ (rootsYDegreeLtFromCandidates candidates Q k).toList := by
  unfold rootsYDegreeLtFromCandidates
  simp [hmem, isRootYDegreeLtBool_of_root hdegree hroot]

theorem rootsYDegreeLtFromCandidates_eraseDups_complete_of_mem {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {candidates : Array (CPolynomial F)} {Q : CBivariate F} {k : Nat}
    {p : CPolynomial F}
    (hmem : p ∈ candidates.toList)
    (hdegree : degreeLt p k) (hroot : CBivariate.composeY Q p = 0) :
    p ∈ (rootsYDegreeLtFromCandidates candidates Q k).eraseDups.toList := by
  have hfilterList :
      p ∈ (rootsYDegreeLtFromCandidates candidates Q k).toList :=
    rootsYDegreeLtFromCandidates_complete_of_mem hmem hdegree hroot
  have hfilterArray :
      p ∈ rootsYDegreeLtFromCandidates candidates Q k := by
    simpa using hfilterList
  have herase : p ∈ (rootsYDegreeLtFromCandidates candidates Q k).eraseDups :=
    array_mem_eraseDups_of_mem hfilterArray
  simpa using herase

end GuruswamiSudan

end CompPoly
