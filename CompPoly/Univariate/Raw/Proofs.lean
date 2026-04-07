/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Desmond Coles, Natalie Klaus
-/
import CompPoly.Univariate.Raw.Ops

/-!
# Raw Univariate Polynomial Proofs

Proofs about operations on raw computable univariate polynomials.
-/

namespace CompPoly

namespace CPolynomial.Raw

variable {R : Type*}
variable {Q : Type*}

section Operations

section Semiring

variable [Semiring R] [BEq R]
variable [Semiring Q]

variable {S : Type*}
variable (p q r : CPolynomial.Raw R)

lemma pow_zero (p : CPolynomial.Raw R) :
    p ^ 0 = C 1 := by
      exact rfl

lemma pow_succ (p : CPolynomial.Raw R) (n : ℕ) :
    p ^ (n + 1) = p * (p ^ n) := by
      convert ( Function.iterate_succ_apply' ( mul p ) n ( C 1 ) )
           using 1

section AddDefs

lemma matchSize_size_eq {p q : CPolynomial.Raw Q} :
    let (p', q') := Array.matchSize p q 0
    p'.size = q'.size := by
  change (Array.rightpad _ _ _).size = (Array.rightpad _ _ _).size
  rw [Array.size_rightpad, Array.size_rightpad]
  omega

lemma matchSize_size {p q : CPolynomial.Raw Q} :
    let (p', _) := Array.matchSize p q 0
    p'.size = max p.size q.size := by
  change (Array.rightpad _ _ _).size = max (Array.size _) (Array.size _)
  rw [Array.size_rightpad]
  omega

lemma zipWith_size {R} {f : R → R → R} {a b : Array R} (h : a.size = b.size) :
    (Array.zipWith f a b).size = a.size := by
  simp; omega

omit [BEq R] in
lemma concat_coeff₁ (i : ℕ) : i < p.size →
    (p ++ q).coeff i = p.coeff i := by simp; grind

omit [BEq R] in
lemma concat_coeff₂ (i : ℕ) : i ≥ p.size →
    (p ++ q).coeff i = q.coeff (i - p.size) := by simp; grind

theorem add_size {p q : CPolynomial.Raw Q} : (addRaw p q).size = max p.size q.size := by
  change (Array.zipWith _ _ _ ).size = max p.size q.size
  rw [zipWith_size matchSize_size_eq, matchSize_size]

theorem add_coeff {p q : CPolynomial.Raw Q} {i : ℕ} (hi : i < (addRaw p q).size) :
    (addRaw p q)[i] = p.coeff i + q.coeff i := by
  simp [addRaw]
  by_cases hi' : i < p.size <;> by_cases hi'' : i < q.size <;> simp_all

theorem add_coeff? (p q : CPolynomial.Raw Q) (i : ℕ) :
    (addRaw p q).coeff i = p.coeff i + q.coeff i := by
  rcases (Nat.lt_or_ge i (addRaw p q).size) with h_lt | h_ge
  · rw [← add_coeff h_lt]; simp [h_lt]
  have h_lt' : i ≥ max p.size q.size := by rwa [← add_size]
  have h_p : i ≥ p.size := by omega
  have h_q : i ≥ q.size := by omega
  simp [h_ge, h_p, h_q]

lemma add_coeff_trimmed [LawfulBEq R] (p q : CPolynomial.Raw R) (i : ℕ) :
    (p + q).coeff i = p.coeff i + q.coeff i := by
      have h_add : p + q = (p.addRaw q).trim := by rfl
      have h_trim_coeff : ∀ (p : CPolynomial.Raw R) (i : ℕ), p.coeff i = p.trim.coeff i := by
          exact fun p i => Eq.symm (Trim.coeff_eq_coeff p i)
      convert h_trim_coeff ( p.addRaw q ) i using 1
      · rw[h_add, ←h_trim_coeff]
      · rw [← h_trim_coeff, add_coeff? ]

lemma add_equiv_raw [LawfulBEq R] (p q : CPolynomial.Raw R) :
    Trim.equiv (p.add q) (p.addRaw q) := by
  unfold Trim.equiv add
  exact Trim.coeff_eq_coeff (p.addRaw q)

omit [BEq R] in
lemma smul_equiv : ∀ (i : ℕ) (r : R),
    (smul r p).coeff i = r * (p.coeff i) := by
  intro i r
  unfold smul mk coeff
  rcases (Nat.lt_or_ge i p.size) with hi | hi <;> simp [hi]

lemma nsmulRaw_equiv [LawfulBEq R] : ∀ (n i : ℕ),
    (nsmulRaw n p).trim.coeff i = n * p.trim.coeff i := by
  intro n i
  unfold nsmulRaw
  repeat rw [Trim.coeff_eq_coeff]
  unfold mk
  rcases (Nat.lt_or_ge i p.size) with hi | hi <;> simp [hi]

lemma mul_pow_assoc : ∀ (p : CPolynomial.Raw R) (n : ℕ),
    ∀ (q : CPolynomial.Raw R) (m l : ℕ),
  l + m = n →
  p.mul^[n] q = p.mul^[m] (p.mul^[l] q) := by
  intro p n
  induction n with
  | zero =>
    intro q m l h_sizes
    rw [Nat.add_eq_zero_iff] at h_sizes
    obtain ⟨hl, hm⟩ := h_sizes
    rw [hl, hm]
    simp
  | succ n₀ ih =>
    intro q m l h_sizes
    cases l with
    | zero =>
      simp at h_sizes
      rw [h_sizes]
      simp
    | succ l₀ =>
      have h_sizes_simp : l₀ + m = n₀ := by linarith
      clear h_sizes
      simpa using ih (p.mul q) m l₀ h_sizes_simp

lemma mul_pow_succ (p q : CPolynomial.Raw R) (n : ℕ):
    p.mul^[n + 1] q = p.mul (p.mul^[n] q) := by
  rw [mul_pow_assoc p (n+1) q 1 n] <;> simp

lemma trim_add_trim [LawfulBEq R] (p q : CPolynomial.Raw R) : p.trim + q = p + q := by
  apply Trim.eq_of_equiv
  intro i
  rw [add_coeff?, add_coeff?, Trim.coeff_eq_coeff]

end AddDefs

section AddTheorems

omit [Semiring Q] in
@[simp] theorem zero_def : (0 : CPolynomial.Raw Q) = #[] := rfl

theorem add_comm : p + q = q + p := by
  apply congrArg trim
  ext
  · simp only [add_size]; omega
  · simp only [add_coeff]
    apply _root_.add_comm

theorem zero_canonical : (0 : CPolynomial.Raw R).trim = 0 := Trim.canonical_empty

theorem monomial_canonical [LawfulBEq R] [DecidableEq R] (n : ℕ) (c : R) :
    (monomial n c).trim = monomial n c := by
  by_cases h : c = 0
  · simp [monomial, if_pos h, Trim.canonical_empty]
  · simp [monomial, if_neg h, mk]
    rw [Trim.push_trim _ _ h]

theorem X_canonical [Nontrivial R] [LawfulBEq R] : X.trim = (X : CPolynomial.Raw R) := by
  unfold X
  change trim (#[0].push 1) = #[0].push 1
  apply Trim.push_trim
  simp

omit [BEq R] in
lemma coeff_monomial [DecidableEq R] {n i : ℕ} {c : R} :
    ((monomial n) c).coeff i = if n = i then c else 0 := by
  by_cases hc : c = 0
  · simp [monomial, hc]
  · unfold monomial
    rw [if_neg hc]; clear hc
    have h_arr : (mk (Array.replicate n 0 ++ #[c])) =
                   mk (Array.replicate n 0) ++ mk #[c] := by rfl
    rw [h_arr]; clear h_arr
    by_cases hn : n = i
    · rw [if_pos hn, hn]; clear hn
      have : (mk (Array.replicate i 0) ++ mk #[c]).coeff i = (mk #[c]).coeff 0 := by
        rw [concat_coeff₂]
        simp only [Array.size_replicate, tsub_self, Array.getD_eq_getD_getElem?,
                   List.size_toArray, List.length_cons, List.length_nil, zero_add,
                   zero_lt_one, getElem?_pos, List.getElem_toArray,
                   List.getElem_cons_zero, Option.getD_some]
        have : Array.size (mk (Array.replicate i 0)) = i := by grind
        rw [← this]
        simp
      rw [this]
      simp
    · rw [if_neg hn]
      by_cases h_ineq : i < n
      · have : (mk (Array.replicate n 0 ++ #[c])).coeff i =
               (mk (Array.replicate n 0)).coeff i := by
          rw [concat_coeff₁]
          grind
        rw [this]; clear this
        simp [Array.getD_eq_getD_getElem?]
        grind
      · have hi : i > n := by grind
        clear h_ineq hn
        grind

omit [BEq R] in
lemma coeff_C (r : R) (i : ℕ) : (C r).coeff i = if i = 0 then r else 0 := by
  unfold C coeff; split_ifs with h <;> simp [h]

omit [BEq R] in
lemma coeff_X (i : ℕ) : (X : CPolynomial.Raw R).coeff i = if i = 1 then 1 else 0 := by
  unfold coeff
  rcases i with ( _ | _ | i ) <;> rfl

omit [BEq R] in
@[simp]
lemma coeff_zero (i : ℕ) : (0 : CPolynomial.Raw R).coeff i = 0 := by
  simp [coeff, zero_def]

omit [BEq R] in
lemma coeff_one (i : ℕ) :
    coeff (1 : CPolynomial.Raw R) i = if i = 0 then 1 else 0 := by
  by_cases h : i = 0
  · rw [if_pos h, h]
    change coeff #[1] 0 = 1
    simp
  · rw [if_neg h]
    change coeff #[1] i = 0
    grind

theorem zero_add (hp : p.canonical) : 0 + p = p := by
  rw (occs := .pos [2]) [← hp]
  apply congrArg trim
  ext <;> simp [add_size, add_coeff, *]

theorem add_zero (hp : p.canonical) : p + 0 = p := by
  rw [add_comm, zero_add p hp]

theorem zero_add_trim [LawfulBEq R] (p : CPolynomial.Raw R) : 0 + p = p.trim := by
  apply congrArg trim
  ext <;> simp [add_size, add_coeff, *]

theorem add_zero_trim [LawfulBEq R] (p : CPolynomial.Raw R) : p + 0 = p.trim := by
  apply congrArg trim
  ext <;> simp [add_size, add_coeff, *]

theorem add_assoc [LawfulBEq R] : p + q + r = p + (q + r) := by
  change (addRaw p q).trim + r = p + (addRaw q r).trim
  rw [trim_add_trim, add_comm p, trim_add_trim, add_comm _ p]
  apply congrArg trim
  ext i
  · simp only [add_size]; omega
  · simp only [add_coeff, add_coeff?]
    apply _root_.add_assoc

end AddTheorems

section MulInfrastructure

section MulOneTrimHelpers

lemma foldl_preserves_canonical {α : Type*}
    (f : CPolynomial.Raw R → α → CPolynomial.Raw R)
    (z : CPolynomial.Raw R) (as : Array α)
    (hz : z.trim = z)
    (hf : ∀ acc x, (f acc x).trim = f acc x) :
    (as.foldl f z).trim = as.foldl f z := by
      induction' as using Array.recOn with a as ih
      induction a using List.reverseRecOn <;> aesop

lemma coeff_foldl_add {α : Type*} [LawfulBEq R]
    (l : List α)
    (f : α → CPolynomial.Raw R)
    (z : CPolynomial.Raw R) (k : ℕ) :
    (l.foldl (fun acc x => acc + f x) z).coeff k
      = z.coeff k + (l.map (fun x => (f x).coeff k)).sum := by
      induction' l using List.reverseRecOn with l ih generalizing z
      · simp
      · simp +zetaDelta at *
        convert congr_arg₂ ( · + · ) ( ‹∀ z : CPolynomial.Raw R, (
          List.foldl ( fun ( acc : CPolynomial.Raw R ) ( x : α ) => acc + f x ) z l )[ k ]?.getD 0
            = z[k]?.getD 0 + ( List.map ( fun x => ( f x)[ k ]?.getD 0 ) l ).sum› z ) rfl using 1
        any_goals exact ( f ih )[ k ]?.getD 0
        · convert add_coeff_trimmed _ _ k
          rotate_left 3
          (expose_names; exact inst_1)
          (expose_names; exact inst_2)
          exact List.foldl ( fun acc x => acc + f x ) z l
          exact f ih
          · exact Eq.symm Array.getD_eq_getD_getElem?
          · exact Eq.symm Array.getD_eq_getD_getElem?
          · exact Eq.symm Array.getD_eq_getD_getElem?
        · module

end MulOneTrimHelpers

section MulAssocSumHelpers

omit [BEq R] in
lemma sum_zipIdx_eq_sum_range {α : Type*} [AddCommMonoid α] (p : CPolynomial.Raw R)
    (f : R → ℕ → α) : (p.zipIdx.toList.map (fun ⟨a, i⟩ => f a i)).sum =
    (Finset.range p.size).sum (fun i => f (p.coeff i) i) := by
      refine' congr_arg _ ( List.ext_get _ _ ) <;> aesop

theorem double_sum_eq [LawfulBEq R] (p q r : CPolynomial.Raw R) (n : ℕ) :
    (Finset.range (n + 1)).sum (fun j =>
      (Finset.range (j + 1)).sum (fun i =>
        p.coeff i * q.coeff (j - i) * r.coeff (n - j)))
    =
    (Finset.range (n + 1)).sum (fun i =>
      (Finset.range (n - i + 1)).sum (fun k =>
        p.coeff i * q.coeff k * r.coeff (n - i - k))) := by
          have h_interchange : ∑ j ∈ Finset.range (n + 1),
              ∑ i ∈ Finset.range (j + 1), p.coeff i * q.coeff (j - i) * r.coeff (n - j)
                  = ∑ i ∈ Finset.range (n + 1),
                      ∑ j ∈ Finset.Ico i (n + 1),
                          p.coeff i * q.coeff (j - i) * r.coeff (n - j) := by
            rw [ Finset.range_eq_Ico, Finset.sum_Ico_Ico_comm ]
          convert h_interchange using 2
          rw [ Finset.sum_Ico_eq_sum_range ]
          simp +decide [ Nat.sub_add_comm ( Finset.mem_range_succ_iff.mp ‹_› ) ]
          exact Finset.sum_congr rfl fun _ _ => by rw [ Nat.sub_sub ]

omit [BEq R] in
lemma sum_range_extend  (p q : CPolynomial.Raw R) (k : ℕ) :
    (Finset.range p.size).sum (fun i => if k < i then 0 else p.coeff i * q.coeff (k - i)) =
    (Finset.range (k + 1)).sum (fun i => p.coeff i * q.coeff (k - i)) := by
      by_cases h : p.size ≤ k + 1
      · rw [ ← Finset.sum_range_add_sum_Ico _ h ]
        rw [ Finset.sum_congr rfl fun i hi =>
            if_neg ( by linarith [ Finset.mem_range.mp hi ] ), Finset.sum_Ico_eq_sum_range ]
        simp +decide [ coeff ]
      · rw [ Finset.sum_ite ]
        rw [ show Finset.filter ( fun x => ¬k < x ) ( Finset.range ( Array.size p ) )
            = Finset.range ( k + 1 ) from ?_ ]
        · simp +zetaDelta at *
        · ext; simp; omega

lemma sum_range_reverse [LawfulBEq R] (p q : CPolynomial.Raw R) (k : ℕ) :
    (Finset.range (k + 1)).sum (fun i => p.coeff i * q.coeff (k - i)) =
    (Finset.range (k + 1)).sum (fun j => p.coeff (k - j) * q.coeff j) := by
  rw [← Finset.sum_range_reflect (fun j => p.coeff (k - j) * q.coeff j) (k + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have hj' : j ≤ k := Nat.lt_succ_iff.mp hj
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hj']

end MulAssocSumHelpers

end MulInfrastructure

section SMulTheorems

theorem nsmul_zero [LawfulBEq R] (p : CPolynomial.Raw R) : nsmul 0 p = 0 := by
  suffices (nsmulRaw 0 p).lastNonzero = none by simp [nsmul, trim, *]
  apply Trim.lastNonzero_none
  intros; unfold nsmulRaw
  simp only [Nat.cast_zero, zero_mul, Array.getElem_map]

theorem nsmulRawSucc (n : ℕ) (p : CPolynomial.Raw Q) :
    nsmulRaw (n + 1) p = addRaw (nsmulRaw n p) p := by
  unfold nsmulRaw
  ext
  · simp [add_size]
  next i _ hi =>
    simp [add_size] at hi
    simp [add_coeff, hi]
    rw [_root_.add_mul (R:=Q) n 1 p[i], one_mul]

theorem nsmul_succ [LawfulBEq R] (n : ℕ) {p : CPolynomial.Raw R} :
    nsmul (n + 1) p = nsmul n p + p := by
  unfold nsmul
  rw [trim_add_trim]
  apply congrArg trim
  apply nsmulRawSucc

lemma smul_coeff [LawfulBEq R] (a : R) (p : CPolynomial.Raw R) (k : ℕ) :
    (smul a p).coeff k = a * p.coeff k := by
  exact smul_equiv p k a

lemma smul_addRaw_distrib [LawfulBEq R] :
    ∀ (a' : R) (q r : CPolynomial.Raw R), smul a' (q.addRaw r)
        = (smul a' q).addRaw (smul a' r) := by
          intros a' q r
          simp [smul, addRaw]
          refine' congr_arg _ ( Array.ext _ _ );
            simp [Array.size_zipWith]
          · intro i hi₁ hi₂
            rw [Array.getElem_zipWith, Array.getElem_zipWith ]
            simp +decide [mul_add ]
            by_cases hi₃ : i < q.size <;> by_cases hi₄ : i < r.size <;> simp_all +decide

lemma smul_distrib_trim [LawfulBEq R] :
    ∀ (a' : R) (q r : CPolynomial.Raw R), (smul a' (q + r)).trim
        = smul a' q + smul a' r := by
          intros a' q r
          have h_coeff : ∀ i, (smul a' (q + r)).coeff i
              = (smul a' q).coeff i
                  + (smul a' r).coeff i := by
            have h_smul : ∀ (a' : R) (q : CPolynomial.Raw R) (i : ℕ),
                (smul a' q).coeff i = a' * q.coeff i := by
              exact fun a' q i => smul_equiv q i a'
            have h_add : ∀ (q r : CPolynomial.Raw R) (i : ℕ), (q + r).coeff i
                = q.coeff i + r.coeff i := by
              exact fun q r i => add_coeff_trimmed q r i
            simp +decide [h_smul, h_add, mul_add ]
          have h_trim_eq : ∀ p q : CPolynomial.Raw R,
              (∀ i, p.coeff i = q.coeff i) → p.trim = q.trim := by
            exact fun p q a => Trim.eq_of_equiv a
          convert h_trim_eq _ _ _ using 1
          unfold addRaw; simp +decide [h_coeff ]
          grind

lemma coeff_smul_add_distrib [LawfulBEq R] (a : R) (q r : CPolynomial.Raw R) (i : ℕ) :
    (smul a (q + r)).coeff i = (smul a q).coeff i + (smul a r).coeff i := by
      have h_expand : (smul a (q + r)).coeff i = a * ((q + r).coeff i) ∧
                         ((smul a q).coeff i) + ((smul a r).coeff i) =
                            a * (q.coeff i) + a * (r.coeff i) := by
                           have h_expand : ∀ (p : CPolynomial.Raw R), (smul a p).coeff i
                              = a * p.coeff i := by
                             exact fun p => smul_equiv p i a
                           exact ⟨ h_expand _, by rw [ h_expand, h_expand ] ⟩
      convert h_expand.1 using 1
      rw [ h_expand.2 ]
      rw [ add_coeff_trimmed ]
      simp +decide [ mul_add ]

lemma coeff_add_smul [LawfulBEq R]  (a b : R) (q : CPolynomial.Raw R) (k : ℕ) :
    (smul (a + b) q).coeff k = (smul a q).coeff k + (smul b q).coeff k := by
      have h_distrib : ∀ (a b : R) (q : CPolynomial.Raw R) (k : ℕ),
          (a + b) * q.coeff k = a * q.coeff k + b * q.coeff k := by
        exact fun a b q k => add_mul a b _
      convert h_distrib a b q k using 1
      · exact smul_equiv q k (a + b)
      · congr! 1
        · exact smul_equiv q k a
        · exact smul_equiv q k b

end SMulTheorems

section MulPowXLemmas

omit [BEq R] in
lemma coeff_sum : ∀ (p : CPolynomial.Raw R) (k : ℕ),
    (p.zipIdx.map (fun ⟨a, i⟩ => ((smul a 1).mulPowX i).coeff k)).sum = p.coeff k := by
  intro p k; induction' p with p ih generalizing k; simp +decide [ * ]
  induction' p using List.reverseRecOn with p ih generalizing k <;>
    simp +decide [ *, List.zipIdx_append ]
  by_cases hk : k < p.length <;> simp_all +decide [ List.getElem?_append_right ]
  · simp +decide [ hk, List.getElem?_append]
    rw [ mulPowX ]
    simp +decide [ Array.getElem?_append, hk ]
  · simp +decide [ mulPowX ]
    unfold smul; simp +decide [ Array.getElem?_append ]
    rw [ if_neg hk.not_gt ]; cases k - p.length <;> simp +decide
    · exact mul_one _
    · exact rfl

lemma coeff_mul [LawfulBEq R] (p q : CPolynomial.Raw R) (k : ℕ) :
    (p * q).coeff k = (p.zipIdx.toList.map (fun ⟨a, i⟩ =>
        ((smul a q).mulPowX i).coeff k)).sum := by
      convert coeff_foldl_add _ _ _ _ using 1
      rotate_left 2
      exact inferInstance
      exact inferInstance
      exact R × ℕ
      (expose_names; exact inst_2)
      exact ( Array.zipIdx p ).toList
      exact fun x => smul x.1 q |> fun y
          => mulPowX x.2 y
      exact mk #[]
      exact k
      · congr
        simp only [Array.toList_zipIdx]
        have h_mul_def : ∀ (p q : CPolynomial.Raw R), p * q
            = (p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + (smul a q).mulPowX i) (mk #[])) := by
          exact fun p q => rfl
        convert h_mul_def p q using 1
        conv => rw [ ← Array.toList_zipIdx ]
        rw [Array.foldl_toList]
      · cases k <;> simp +decide [ * ]

lemma coeff_mulPowX [LawfulBEq R] (i : ℕ) (p : CPolynomial.Raw R) (k : ℕ) :
    (p.mulPowX i).coeff k = if k < i then 0 else p.coeff (k - i) := by
      split_ifs <;> simp_all +decide [ coeff, mulPowX ]
      · rw [ Array.getElem?_append ]; aesop
      · grind

lemma coeff_mulPowX' [LawfulBEq R] (p : CPolynomial.Raw R) (n i : ℕ) :
    (p.mulPowX n).coeff i = if i < n then 0 else p.coeff (i - n) := by
      unfold mulPowX
      split_ifs <;> simp_all +decide [ coeff ]
      · rw [ Array.getElem?_append ]
        aesop
      · simp only [Array.getElem?_append, Array.getElem?_replicate,Array.size_replicate]
        split_ifs
        · omega
        · rfl

lemma mulPowX_coeff' [LawfulBEq R] (p : CPolynomial.Raw R) (n k : ℕ) :
    (p.mulPowX n).coeff k = if k < n then 0 else p.coeff (k - n) := by
  exact coeff_mulPowX' p n k

lemma coeff_mulPowX_smul_add [LawfulBEq R] (i : ℕ) (a b : R) (q : CPolynomial.Raw R) (k : ℕ) :
    ((smul (a + b) q).mulPowX i).coeff k =
        ((smul a q).mulPowX i).coeff k + ((smul b q).mulPowX i).coeff k := by
  rw [coeff_mulPowX, coeff_mulPowX, coeff_mulPowX]
  split_ifs
  · simp
  · rw [coeff_add_smul]

omit [BEq R] in
lemma mulPowX_zero (p : CPolynomial.Raw R) :
    p.mulPowX 0 = p := by
    simp [mulPowX]

end MulPowXLemmas

section MulInfrastructure

section MulCoeffHelpers

lemma equiv_mul_one [LawfulBEq R] (p : CPolynomial.Raw R) : Trim.equiv (p * 1) p := by
  have h_mul_one : ∀ (p : CPolynomial.Raw R), (p * 1).coeff = p.coeff := by
    intro p; funext i
    rw [ show p * 1 = p * 1 from rfl ]
    have mul_one_unwrap : ∀ (p : CPolynomial.Raw R), (p * 1).coeff = fun k =>
      (p.zipIdx.map (fun ⟨a, i⟩ => ((smul a 1).mulPowX i).coeff k)).sum := by
      intro p; funext k; exact (by
      convert coeff_foldl_add
          ( p.zipIdx.toList ) ( fun ⟨ a, i ⟩ => ( smul a 1 ).mulPowX i ) ( mk #[] ) k using 1
      · have h_mul_def : ∀ (p : CPolynomial.Raw R), p * 1 =
            (p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + (smul a 1).mulPowX i) (mk #[])) := by
          exact fun p => rfl
        rw [h_mul_def, Array.foldl_toList]
      · simp +decide
        conv => rw [ ← Array.toList_zipIdx ]
        conv => rw [ ← Array.toList_map ]
        exact Eq.symm Array.sum_eq_sum_toList)
    exact (by exact mul_one_unwrap p ▸ coeff_sum p i ▸ rfl)
  exact congrFun (h_mul_one p)

theorem mul_is_trimmed [LawfulBEq R] (p q : CPolynomial.Raw R) : (p * q).trim = p * q := by
  convert foldl_preserves_canonical _ _ _ _ _
  · exact Trim.canonical_empty
  · intros acc x
    simp [add, addRaw]
    exact Trim.trim_twice
      (mk (Array.zipWith (fun x1 x2 => x1 + x2)
        (acc ++ Array.replicate (Array.size (mulPowX x.2 (smul x.1 q)) - Array.size acc) 0)
          (mulPowX x.2 (smul x.1 q) ++
            Array.replicate (Array.size acc - Array.size (mulPowX x.2 (smul x.1 q))) 0)))

lemma coeff_mul_eq_sum_range [LawfulBEq R] (p q : CPolynomial.Raw R) (k : ℕ) (n : ℕ)
    (h : p.size ≤ n) : (p * q).coeff k =
        List.sum ((List.range n).map (fun i => ((smul (p.coeff i) q).mulPowX i).coeff k)) := by
      have h_coeff : (p * q).coeff k =
          ((p.zipIdx.toList).map
              (fun (x : R × ℕ) => ((smul x.1 q).mulPowX x.2).coeff k)).sum := by
        convert coeff_mul p q k using 1
      have h_split : List.sum (List.map
          (fun i => (mulPowX i (smul (p.coeff i) q)).coeff k) (List.range n)) =
        List.sum (List.map
            (fun i => (mulPowX i (smul (p.coeff i) q)).coeff k) (List.range p.size)) +
                List.sum (List.map (fun i => (mulPowX i (smul (p.coeff i) q)).coeff k)
                    (List.drop p.size (List.range n))) := by
          rw [ ← List.sum_append, ← List.take_append_drop ( Array.size p )
               ( List.range n ), List.map_append ]
          simp +decide [ h ]
      have h_drop_zero : List.sum (List.map
          (fun i => (mulPowX i (smul (p.coeff i) q)).coeff k)
              (List.drop p.size (List.range n))) = 0 := by
        have h_zero_sum : ∀ i ∈ List.drop p.size (List.range n),
            (mulPowX i (smul (p.coeff i) q)).coeff k = 0 := by
          intro i hi
          have h_zero_coeff : p.coeff i = 0 := by
            have := List.mem_iff_get.mp hi; aesop
          simp [h_zero_coeff]
          simp +decide [ mulPowX, smul ]
          grind
        exact List.sum_eq_zero fun x hx =>
            by obtain ⟨ i, hi, rfl ⟩ := List.mem_map.mp hx; exact h_zero_sum i hi
      simp_all +decide
      congr! 1
      refine' List.ext_get _ _ <;> aesop

lemma mul_eq_foldl (p q : CPolynomial.Raw R) :
    p * q = p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + (smul a q).mulPowX i) (mk #[]) := by
  rfl

lemma C_mul_eq_smul_trim [LawfulBEq R] (r : R)
    (q : CPolynomial.Raw R) :
    C r * q = (smul r q).trim := by
  rw [ mul_eq_foldl ]
  simp +decide [ C ]
  convert zero_add_trim ( smul r q ) using 1
  congr
  exact mulPowX_zero (smul r q)

omit [BEq R] in
lemma smul_one_eq_self (p : CPolynomial.Raw R) :
    smul 1 p = p := by
  unfold smul
  cases p; aesop

omit [BEq R] in
lemma smul_zero_eq_replicate_zero (p : CPolynomial.Raw R) :
    smul 0 p = mk (Array.replicate p.size 0) := by
  unfold smul; aesop

lemma trim_replicate_zero [LawfulBEq R] (n : ℕ) :
    (mk (Array.replicate n (0 : R))).trim = 0 := by
  convert Trim.trim_twice ( mk ( Array.replicate n 0 ) ) using 1;
  have h_trim_empty : ∀ {p : CPolynomial.Raw R},
      p = mk (Array.replicate p.size 0) → p.trim = 0 := by
    intro p hp
    have h_last : p.lastNonzero = none := by
      apply Trim.lastNonzero_none
      grind
    unfold trim; simp +decide [ h_last ]
  rw [ h_trim_empty ]
  · exact iff_of_true rfl ( Trim.trim_twice _ )
  · grind

lemma smul_zero_trim [LawfulBEq R]
    (p : CPolynomial.Raw R) : (smul 0 p).trim = 0 := by
  rw [ smul_zero_eq_replicate_zero ];
  exact trim_replicate_zero (Array.size p)

lemma X_mul_eq_mulX_trim [LawfulBEq R]
    (p : CPolynomial.Raw R) :
    X * p = (mulX p).trim := by
  convert zero_add_trim p.mulX using 1
  rw [ mul_eq_foldl ]
  simp [X, Array.zipIdx]
  congr! 1
  · convert smul_zero_trim p using 1
    convert zero_add_trim _ using 1
    · exact congr_arg _ ( by exact Eq.symm (mulPowX_zero (smul 0 p)) )
    · infer_instance
  · rw [ smul_one_eq_self ]
    rfl

lemma mulX_monomial_one [DecidableEq R] [LawfulBEq R] [Nontrivial R] (n : ℕ) :
    mulX (monomial n (1 : R)) =
    monomial (n + 1) 1 := by
  unfold monomial;
  simp +decide [ mulX, Array.replicate_succ ];
  unfold mulPowX;
  simp +decide [ mk, Array.push ];
  exact Nat.recOn n (by simp +decide) fun n ih =>
    by simp +decide [ List.replicate ] at ih ⊢; tauto

lemma X_pow_eq_monomial_one [DecidableEq R] [LawfulBEq R] [Nontrivial R] (n : ℕ) :
    (X : CPolynomial.Raw R) ^ n = monomial n 1 := by
  have h_monomial : ∀ n : ℕ,
      (monomial n (1 : R)).trim =
      monomial n (1 : R) := by
    exact fun n => monomial_canonical n 1
  induction' n with n ih;
  · unfold X monomial
    aesop
  · rw [ pow_succ, ih ];
    rw [ X_mul_eq_mulX_trim ];
    rw [ mulX_monomial_one, h_monomial ]

lemma smul_monomial_one_trim [DecidableEq R] [LawfulBEq R]
    [Nontrivial R] (n : ℕ) (r : R) :
    (smul r (monomial n 1)).trim =
    monomial n r := by
  unfold smul monomial
  simp +decide
  split_ifs with h;
  · convert trim_replicate_zero ( n + 1 ) using 1;
    congr! 1;
    · simp +decide [ h, Array.replicate_succ ];
    · infer_instance;
  · exact Trim.push_trim (Array.replicate n 0) r h

lemma smul_mulPowX_coeff [LawfulBEq R] (a : R) (q : CPolynomial.Raw R) (i k : ℕ) :
    ((smul a q).mulPowX i).coeff k = if k < i then 0 else a * q.coeff (k - i) := by
    convert mulPowX_coeff' (smul a q) i k using 1
    rw [ smul_coeff ]

lemma mul_coeff_list [LawfulBEq R] (p q : CPolynomial.Raw R) (k : ℕ) :
    (p * q).coeff k = (p.zipIdx.toList.map
      (fun ⟨a, i⟩ => if k < i then 0 else a * q.coeff (k - i))).sum := by
  rw [coeff_mul, Array.toList_zipIdx]
  have h_term : ∀ x ∈ p.toList.zipIdx,
      ((smul x.1 q).mulPowX x.2).coeff k = if k < x.2 then 0 else x.1 * q.coeff (k - x.2) := by
    intro x hx
    exact smul_mulPowX_coeff x.1 q x.2 k
  rw [List.map_congr_left h_term]

lemma mul_coeff_range_size [LawfulBEq R] (p q : CPolynomial.Raw R) (k : ℕ) :
    (p * q).coeff k = (Finset.range p.size).sum
      (fun i => if k < i then 0 else p.coeff i * q.coeff (k - i)) := by
        have h_coeff_mul_ci : (p * q).coeff k = (p.zipIdx.toList.map (fun ⟨a, i⟩
            => if k < i then 0 else a * q.coeff (k - i))).sum := by
          exact mul_coeff_list p q k
        convert sum_zipIdx_eq_sum_range p ( fun a i =>
            if k < i then 0 else a * q.coeff ( k - i ) ) using 1

lemma mul_coeff [LawfulBEq R] (p q : CPolynomial.Raw R) (k : ℕ) :
    (p * q).coeff k = (Finset.range (k + 1)).sum (fun i => p.coeff i * q.coeff (k - i)) := by
  rw [mul_coeff_range_size, sum_range_extend]

lemma mul_assoc_coeff_rhs [LawfulBEq R] (p q r : CPolynomial.Raw R) (n : ℕ) :
    (p * (q * r)).coeff n =
      (Finset.range (n + 1)).sum (fun i =>
        (Finset.range (n - i + 1)).sum (fun j =>
          p.coeff i * q.coeff j * r.coeff (n - i - j))) := by
  rw [mul_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_coeff]
  simp only [Finset.mem_range] at hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (mul_assoc _ _ _).symm

lemma mul_mul_coeff [LawfulBEq R] (p q r : CPolynomial.Raw R) (n : ℕ) :
    ((p * q) * r).coeff n =
      (Finset.range (n + 1)).sum (fun j =>
        (Finset.range (j + 1)).sum (fun i =>
          p.coeff i * q.coeff (j - i) * r.coeff (n - j))) := by
            convert mul_coeff _ _ _
            · rw [ mul_coeff, Finset.sum_mul _ _ _ ]
            · (expose_names; exact inst_2)

lemma mul_assoc_coeff [LawfulBEq R] (p q r : CPolynomial.Raw R) (n : ℕ) :
    ((p * q) * r).coeff n = (p * (q * r)).coeff n := by
  rw [mul_mul_coeff, mul_assoc_coeff_rhs, double_sum_eq]

lemma mul_assoc_equiv [LawfulBEq R] (p q r : CPolynomial.Raw R) :
    Trim.equiv ((p * q) * r) (p * (q * r)) := by
  intro i
  exact mul_assoc_coeff p q r i

end MulCoeffHelpers

end MulInfrastructure

section MulTheorems

protected theorem mul_zero [LawfulBEq R] (p : CPolynomial.Raw R) : p * 0 = 0 := by
  have : ∀ (k : ℕ), ( p * 0 ).coeff k = 0 := by
    intro k
    rw [ mul_coeff ]
    simp
  apply Trim.canonical_ext
  · exact mul_is_trimmed p 0
  · exact Trim.canonical_empty
  · exact this

protected theorem zero_mul [LawfulBEq R] (p : CPolynomial.Raw R) : 0 * p = 0 := by
  have : ∀ (k : ℕ), ( 0 * p ).coeff k = 0 := by
    intro k
    rw [ mul_coeff ]
    simp
  apply Trim.canonical_ext
  · exact mul_is_trimmed 0 p
  · exact Trim.canonical_empty
  · exact this

theorem mul_one_trim [LawfulBEq R] (p : CPolynomial.Raw R) : p * 1 = p.trim := by
  have h_equiv : Trim.equiv (p * 1) p := by
    exact equiv_mul_one p
  have h_trim : (p * 1).trim = p * 1 := by
    exact mul_is_trimmed p 1
  have h_trim_p : p.trim.trim = p.trim := by
    exact Trim.trim_twice p
  exact (by
  apply Trim.canonical_ext
  · exact h_trim
  · exact h_trim_p
  · exact fun i => by rw [ h_equiv i, Trim.coeff_eq_coeff .. ])

theorem one_mul_trim [LawfulBEq R] (p : CPolynomial.Raw R) : 1 * p = p.trim := by
  have h_mul_def : ∀ (a b : CPolynomial.Raw R),
      a.mul b = (a.zipIdx.foldl (fun acc ⟨a', i⟩ => acc.add ((smul a' b).mulPowX i)) (mk #[])) :=
        by exact fun a b => rfl
  have : 1 * p = (mk #[1] : CPolynomial.Raw R).mul p := by rfl
  rw [this, h_mul_def]
  show (mk #[1]).zipIdx.foldl (fun acc ⟨a', i⟩ => acc.add ((smul a' p).mulPowX i)) (mk #[])
      = p.trim
  conv_lhs => rw [show (mk #[1] : CPolynomial.Raw R).zipIdx = #[(1, 0)] by rfl]
  rw [show Array.foldl (fun acc ⟨a', i⟩ => acc.add ((smul a' p).mulPowX i)) (mk #[]) #[(1, 0)] =
           (mk #[] : CPolynomial.Raw R).add ((smul 1 p).mulPowX 0) by rfl]
  rw [show (smul (1 : R) p).mulPowX 0 = p by simp [smul, mulPowX, one_mul]]
  have : (mk #[]).add p = 0 + p := by rfl
  rw[this, zero_add_trim]

protected theorem mul_add [LawfulBEq R] (p q r : CPolynomial.Raw R) :
    p * (q + r) = p * q + p * r := by
      have h_eq : p * (q + r) = p * q + p * r ↔ p * (q + r) = (p * q + p * r).trim := by
        have h_canonical : (p * q).trim = p * q ∧ (p * r).trim = p * r := by
          exact ⟨ mul_is_trimmed p q, mul_is_trimmed p r ⟩
        have h_add_trim : ∀ (p q : CPolynomial.Raw R), (p + q).trim = p.trim + q.trim := by
          intros p q
          have h_add_trim : ∀ (p q : CPolynomial.Raw R), (p + q).trim = p.trim + q.trim := by
            intros p q
            have h_add_trim : ∀ (p q : CPolynomial.Raw R), (p + q).coeff
                = (p.trim + q.trim).coeff := by
              intros p q
              ext k
              simp only [Array.getD_eq_getD_getElem?]
              convert add_coeff_trimmed p q k using 1
              ·exact Eq.symm Array.getD_eq_getD_getElem?
              · convert add_coeff_trimmed p.trim q.trim k using 1
                · exact Eq.symm Array.getD_eq_getD_getElem?
                · rw [ Trim.coeff_eq_coeff, Trim.coeff_eq_coeff ]
            apply Trim.canonical_ext
            · exact Trim.trim_twice (p + q)
            · apply Trim.trim_twice
            · exact fun i => by rw [ Trim.coeff_eq_coeff, h_add_trim ]
          exact h_add_trim p q
        rw [ h_add_trim, h_canonical.1, h_canonical.2 ]
      have h_equiv : (p * (q + r)).coeff = (p * q + p * r).coeff := by
        ext k
        rw [ coeff_mul, add_coeff_trimmed ]
        rw [ coeff_mul, coeff_mul ]
        rw [ ← List.sum_map_add ]
        congr! 2
        ext ⟨ a, i ⟩; by_cases hi : k < i <;> simp +decide
        · simp +decide [mulPowX]
          rw [ Array.getElem?_append, Array.getElem?_append, Array.getElem?_append ]; aesop
        · convert coeff_smul_add_distrib a q r ( k - i ) using 1
          · convert coeff_mulPowX i ( smul a ( q + r ) ) k using 1
            · exact Eq.symm Array.getD_eq_getD_getElem?
            · aesop
          · simp +decide [ mulPowX]
            grind
      have h_trim : (p * (q + r)).trim = (p * q + p * r).trim := by
        exact Trim.eq_of_equiv (congrFun h_equiv)
      convert h_eq.mpr _
      convert h_trim using 1
      exact Eq.symm (mul_is_trimmed p (q + r))

protected theorem add_mul [LawfulBEq R] (p q r : CPolynomial.Raw R) :
    (p + q) * r = p * r + q * r := by
  have h_coeff : ∀ k, ((p + q) * r).coeff k = (p * r + q * r).coeff k := by
    intro k
    have h_sum : ((p + q) * r).coeff k =
        List.sum ((List.range (p.size + q.size)).map
            (fun i => ((smul ((p + q).coeff i) r).mulPowX i).coeff k)) := by
      convert coeff_mul_eq_sum_range ( p + q ) r k ( p.size + q.size ) _ using 1
      have h_size_sum : (p + q).size ≤ max p.size q.size := by
        convert Trim.size_le_size ( p.addRaw q ) using 1
        exact Eq.symm add_size
      exact le_trans h_size_sum ( max_le ( Nat.le_add_right _ _ ) ( Nat.le_add_left _ _ ) )
    have h_split : List.sum ((List.range (p.size + q.size)).map
        (fun i => ((smul ((p + q).coeff i) r).mulPowX i).coeff k)) =
      List.sum ((List.range (p.size + q.size)).map
          (fun i => ((smul (p.coeff i) r).mulPowX i).coeff k)) +
          List.sum ((List.range (p.size + q.size)).map
              (fun i => ((smul (q.coeff i) r).mulPowX i).coeff k)) := by
        have h_split : ∀ i ∈ List.range (p.size + q.size),
            ((smul ((p + q).coeff i) r).mulPowX i).coeff k =
              ((smul (p.coeff i) r).mulPowX i).coeff k +
                  ((smul (q.coeff i) r).mulPowX i).coeff k := by
            intro i hi
            have h_split : ((p + q).coeff i) = (p.coeff i) + (q.coeff i) := by
              exact add_coeff_trimmed p q i
            convert coeff_mulPowX_smul_add i ( p.coeff i ) ( q.coeff i ) r k using 1
            rw [ h_split ]
        rw [ ← List.sum_map_add, List.map_congr_left h_split ]
    have h_coeff_r : (p * r).coeff k + (q * r).coeff k =
        List.sum ((List.range (p.size + q.size)).map
            (fun i => ((smul (p.coeff i) r).mulPowX i).coeff k)) +
                List.sum ((List.range (p.size + q.size)).map
                    (fun i => ((smul (q.coeff i) r).mulPowX i).coeff k)) := by
      have h_coeff_r : (p * r).coeff k =
          List.sum ((List.range (p.size + q.size)).map
              (fun i => ((smul (p.coeff i) r).mulPowX i).coeff k))
                  ∧ (q * r).coeff k = List.sum
                      ((List.range (p.size + q.size)).map
                          (fun i => ((smul (q.coeff i) r).mulPowX i).coeff k)) := by
        apply And.intro
        · convert coeff_mul_eq_sum_range p r k ( p.size + q.size )
              ( by linarith ) using 1
        · convert coeff_mul_eq_sum_range q r k ( p.size + q.size )
              ( by linarith ) using 1
      rw [h_coeff_r.1, h_coeff_r.2 ]
    rw [ h_sum, h_split, ← h_coeff_r, add_coeff_trimmed ]
  convert Trim.canonical_ext _ _ ( h_coeff )
  · exact mul_is_trimmed (p + q) r
  · apply Trim.trim_twice

protected theorem mul_assoc [LawfulBEq R] (p q r : CPolynomial.Raw R) :
    p * q * r = p * (q * r) := by
  apply Trim.canonical_ext
  · exact mul_is_trimmed (p * q) r
  · exact mul_is_trimmed p (q * r)
  · exact mul_assoc_equiv p q r

end MulTheorems

end Semiring

section CommutativeSemiring

variable [CommSemiring R] [BEq R]

lemma mul_coeff_comm [LawfulBEq R] (p q : CPolynomial.Raw R) (k : ℕ) :
    (Finset.range (k + 1)).sum (fun i => p.coeff i * q.coeff (k - i)) =
    (Finset.range (k + 1)).sum (fun i => q.coeff i * p.coeff (k - i)) := by
  rw [sum_range_reverse]
  apply Finset.sum_congr rfl
  intro j _
  ring_nf

lemma mul_comm_coeff [LawfulBEq R] (p q : CPolynomial.Raw R) (k : ℕ) :
    (p * q).coeff k = (q * p).coeff k := by
  rw [mul_coeff, mul_coeff]
  exact mul_coeff_comm p q k

lemma mul_comm_equiv [LawfulBEq R] (p q : CPolynomial.Raw R) :
    Trim.equiv (p * q) (q * p) := by
  intro i
  exact mul_comm_coeff p q i

protected theorem mul_comm [LawfulBEq R] (p q : CPolynomial.Raw R) : p * q = q * p := by
  apply Trim.canonical_ext
  · exact mul_is_trimmed p q
  · exact mul_is_trimmed q p
  · exact mul_comm_equiv p q

end CommutativeSemiring

lemma neg_coeff {R : Type*} [NegZeroClass R] (p : CPolynomial.Raw R) (i : ℕ) :
    p.neg.coeff i = - p.coeff i := by
  unfold neg coeff
  rcases (Nat.lt_or_ge i p.size) with hi | hi <;> simp [hi]

section Ring

variable [Ring R] [BEq R]

theorem neg_trim [LawfulBEq R] (p : CPolynomial.Raw R) : p.trim = p → (-p).trim = -p := by
  apply Trim.non_zero_map
  simp

theorem neg_add_cancel [LawfulBEq R] (p : CPolynomial.Raw R) : -p + p = 0 := by
  rw [← zero_canonical]
  apply Trim.eq_of_equiv; unfold Trim.equiv; intro i
  rw [add_coeff?]
  rcases (Nat.lt_or_ge i p.size) with hi | hi <;> simp [hi, Neg.neg, neg]

lemma sub_coeff [LawfulBEq R] (p q : CPolynomial.Raw R) (i : ℕ) :
    (p - q).coeff i = p.coeff i - q.coeff i := by
  have h_add : coeff (p + -q) i =
      coeff p i + coeff (-q) i := by
    convert add_coeff_trimmed p ( -q ) i using 1
  have h_neg : coeff (-q) i = -coeff q i := by
    convert neg_coeff _ _
  convert h_add.trans ( congr_arg₂ ( · + · ) rfl h_neg ) using 1
  exact sub_eq_add_neg (p.coeff i) (q.coeff i)

end Ring

end Operations

section AddCommSemigroup

variable [Semiring R] [BEq R]

instance [LawfulBEq R] : AddCommSemigroup (CPolynomial.Raw R) where
  add_assoc := by intro _ _ _; rw [add_assoc]
  add_comm := add_comm

end AddCommSemigroup

section RepeatedSquaring

variable [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]

/-- `pow` preserves trimming (Raw-level version). -/
lemma pow_is_trimmed (p : CPolynomial.Raw R) (n : ℕ) :
    (p ^ n).trim = p ^ n := by
  induction n with
  | zero => exact Trim.push_trim #[] 1 one_ne_zero
  | succ n ih => rw [pow_succ]; exact mul_is_trimmed p (p ^ n)

/-- Additive law for exponentiation: `p ^ (a + b) = p ^ a * p ^ b`. -/
theorem pow_add (p : CPolynomial.Raw R) (a b : ℕ) :
    p ^ (a + b) = p ^ a * p ^ b := by
  induction a with
  | zero =>
    simp only [Nat.zero_add, pow_zero]
    show p ^ b = (C 1) * p ^ b
    rw [show (C 1 : CPolynomial.Raw R) = 1 from rfl, one_mul_trim, pow_is_trimmed]
  | succ n ih =>
    rw [Nat.succ_add, pow_succ, ih, pow_succ, Raw.mul_assoc]

omit [LawfulBEq R] [Nontrivial R] in
private theorem mul_eq_hmul (a b : CPolynomial.Raw R) : a.mul b = a * b := rfl

/-- `powBySq` agrees with `pow` (repeated squaring = repeated multiplication). -/
theorem powBySq_eq_pow (p : CPolynomial.Raw R) : ∀ n : ℕ, powBySq p n = p ^ n
  | 0 => by unfold powBySq; exact (pow_zero p).symm
  | n + 1 => by
    unfold powBySq
    have ih : powBySq p ((n + 1) / 2) = p ^ ((n + 1) / 2) :=
      powBySq_eq_pow p ((n + 1) / 2)
    simp only [ih, mul_eq_hmul, ← pow_add]
    by_cases heven : (n + 1) % 2 = 0
    · simp only [heven, ↓reduceIte]
      congr 1; omega
    · simp only [heven, ↓reduceIte, ← pow_succ]
      congr 1; omega
termination_by n => n
decreasing_by omega

end RepeatedSquaring

end CPolynomial.Raw

end CompPoly
