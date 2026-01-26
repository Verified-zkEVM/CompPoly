import CompPoly.Univariate.Basic
import Batteries.Data.Array

open CompPoly

theorem CompPoly.Array.foldl_range_zero {α : Type*} (f : α → ℕ → α) (init : α) :
    Array.foldl f init (Array.range 0) 0 0 = init :=   rfl

theorem CompPoly.Array.range_foldl_succ {α : Type*} (f : α → ℕ → α) (init : α) (n : ℕ) :
    (Array.range (n + 1)).foldl f init = f ((Array.range n).foldl f init) n := by
  -- try using foldl_push with correct arguments
  simpa [Array.range_succ] using
    (Array.foldl_push (f := f) (init := init) (xs := Array.range n) (a := n))

theorem CompPoly.Array.range_foldl_min_succ {α : Type*} (f : α → ℕ → α) (init : α) (i k : ℕ) :
    (Array.range (min (k + 1) (i + 1))).foldl f init =
      if i < k then
        (Array.range (min k (i + 1))).foldl f init
      else
        f ((Array.range (min k (i + 1))).foldl f init) k := by
  by_cases h : i < k
  · have hik : i + 1 ≤ k := Nat.succ_le_of_lt h
    have hik' : i + 1 ≤ k + 1 := Nat.le_succ_of_le hik
    -- simp should rewrite mins
    simp [h, Nat.min_eq_right, hik, hik']
  · have hk : k ≤ i := Nat.le_of_not_gt h
    have hk1 : k + 1 ≤ i + 1 := Nat.succ_le_succ hk
    have hk' : k ≤ i + 1 := le_trans hk (Nat.le_succ i)
    -- rewrite mins then use range_foldl_succ
    simp [h, Nat.min_eq_left, hk1, hk']
    simpa using (CompPoly.Array.range_foldl_succ (f := f) (init := init) (n := k))

theorem CompPoly.Array.range_foldl_zero {α : Type*} (f : α → ℕ → α) (init : α) :
    (Array.range 0).foldl f init = init := by
  simp [Array.range]

theorem CompPoly.Array.zipIdx_size {α : Type*} (a : Array α) : a.zipIdx.size = a.size := by
  simp [Array.zipIdx]


theorem CompPoly.CPolynomial.coeff_add {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p q : CompPoly.CPolynomial R) (i : ℕ) :
    (p + q).coeff i = p.coeff i + q.coeff i := by
  change (CompPoly.CPolynomial.add p q).coeff i = p.coeff i + q.coeff i
  unfold CompPoly.CPolynomial.add
  -- remove the `trim` on the left
  rw [CompPoly.CPolynomial.Trim.coeff_eq_coeff (p := CompPoly.CPolynomial.addRaw p q) i]
  -- now use the raw coefficient lemma
  simpa using (CompPoly.CPolynomial.add_coeff? p q i)


theorem CompPoly.CPolynomial.mulPowX_coeff {R : Type*} [Ring R] [BEq R] (p : CompPoly.CPolynomial R) (k i : ℕ) :
    (CompPoly.CPolynomial.mulPowX k p).coeff i = if i < k then 0 else p.coeff (i - k) := by
  classical
  by_cases hi : i < k
  · have hik : i < (Array.replicate k (0 : R)).size := by
      simpa using hi
    have h1 :=
      CompPoly.CPolynomial.concat_coeff₁ (p := Array.replicate k (0 : R)) (q := p) i hik
    -- simplify the concatenation lemma and use it to reduce to a replicate lookup
    simp [CompPoly.CPolynomial.mulPowX, CompPoly.CPolynomial.mk, CompPoly.CPolynomial.coeff, hi] at h1 ⊢
    -- now the goal is the coefficient of a replicated zero array
    simpa using h1.trans (by simp)
  · have hi' : i ≥ k := Nat.le_of_not_lt hi
    have hik : i ≥ (Array.replicate k (0 : R)).size := by
      simpa using hi'
    have h1 :=
      CompPoly.CPolynomial.concat_coeff₂ (p := Array.replicate k (0 : R)) (q := p) i hik
    -- simplify and finish
    simpa [CompPoly.CPolynomial.mulPowX, CompPoly.CPolynomial.mk, CompPoly.CPolynomial.coeff, hi, hi'] using h1

theorem CompPoly.CPolynomial.mul_coeff_partial_base {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p q : CompPoly.CPolynomial R) (i : ℕ) :
    (CompPoly.CPolynomial.C (R := R) 0).coeff i =
      (Array.range (min 0 (i + 1))).foldl (fun acc j => acc + p.coeff j * q.coeff (i - j)) 0 := by
  have hmin : min 0 (i + 1) = 0 := by
    simp
  -- simplify the `min` on the RHS
  rw [hmin]
  -- fold over an empty range
  rw [CompPoly.Array.range_foldl_zero (f := fun acc j => acc + p.coeff j * q.coeff (i - j)) (init := (0 : R))]
  -- coefficient of the zero constant polynomial
  simp [CompPoly.CPolynomial.C, CompPoly.CPolynomial.coeff]


theorem CompPoly.CPolynomial.mul_coeff_partial_step {R : Type*} [Ring R] (p q : CompPoly.CPolynomial R) (i k : ℕ) (s : R) :
    let g : R → ℕ → R := fun t j => t + p.coeff j * q.coeff (i - j)
    (Array.range (min k (i + 1))).foldl g s + (if i < k then 0 else p.coeff k * q.coeff (i - k)) =
      (Array.range (min (k + 1) (i + 1))).foldl g s := by
  classical
  -- unfold the `let g := ...`
  dsimp
  have hfold :=
    CompPoly.Array.range_foldl_min_succ
      (f := fun t j => t + p.coeff j * q.coeff (i - j)) (init := s) (i := i) (k := k)
  -- expand the RHS fold using the axiom
  rw [hfold]
  by_cases h : i < k
  · -- the new term vanishes
    simp [h, add_assoc, add_left_comm, add_comm]
  · -- the new term is added via `g`
    simp [h, add_assoc, add_left_comm, add_comm]

theorem CompPoly.CPolynomial.range_foldl_min_eq_range_foldl {R : Type*} [Ring R] (p q : CompPoly.CPolynomial R) (i : ℕ) :
    (Array.range (min p.size (i + 1))).foldl (fun acc j => acc + p.coeff j * q.coeff (i - j)) 0 =
      (Array.range (i + 1)).foldl (fun acc j => acc + p.coeff j * q.coeff (i - j)) 0 := by
  classical
  let f : R → ℕ → R := fun acc j => acc + p.coeff j * q.coeff (i - j)
  change (Array.range (min p.size (i + 1))).foldl f 0 = (Array.range (i + 1)).foldl f 0
  by_cases h : i + 1 ≤ p.size
  · simpa [min_eq_right h]
  · have hp : p.size ≤ i + 1 := Nat.le_of_lt (Nat.lt_of_not_ge h)
    let d : ℕ := (i + 1) - p.size
    have hd : p.size + d = i + 1 := by
      dsimp [d]
      exact Nat.add_sub_of_le hp
    have hfold : (Array.range (p.size + d)).foldl f 0 = (Array.range p.size).foldl f 0 := by
      induction d with
      | zero =>
        simp
      | succ d ih =>
        have hsucc :
            (Array.range (p.size + Nat.succ d)).foldl f 0 =
              f ((Array.range (p.size + d)).foldl f 0) (p.size + d) := by
          simpa [Nat.add_assoc] using
            (CompPoly.Array.range_foldl_succ (f := f) (init := (0 : R)) (n := p.size + d))
        rw [hsucc, ih]
        have hpcoeff : p.coeff (p.size + d) = (0 : R) := by
          have hge : p.size ≤ p.size + d := Nat.le_add_right p.size d
          simp [CompPoly.CPolynomial.coeff, Array.getD, hge]
        simp [f, hpcoeff]
    have h' : (Array.range p.size).foldl f 0 = (Array.range (i + 1)).foldl f 0 := by
      calc
        (Array.range p.size).foldl f 0 = (Array.range (p.size + d)).foldl f 0 := by
          simpa using hfold.symm
        _ = (Array.range (i + 1)).foldl f 0 := by
          simpa [hd]
    simpa [min_eq_left hp] using h'

theorem CompPoly.CPolynomial.smul_mulPowX_coeff {R : Type*} [Ring R] [BEq R] (a : R) (q : CompPoly.CPolynomial R) (j i : ℕ) :
    ((CompPoly.CPolynomial.smul a q).mulPowX j).coeff i = if i < j then 0 else a * q.coeff (i - j) := by
  classical
  -- Rewrite the coefficient of `mulPowX` using the given formula.
  rw [CompPoly.CPolynomial.mulPowX_coeff (p := CompPoly.CPolynomial.smul a q) (k := j) (i := i)]
  -- Now split on whether `i < j`.
  by_cases hij : i < j
  · simp [hij]
  · -- In the `i ≥ j` case, use the coefficient formula for scalar multiplication.
    simpa [hij] using (CompPoly.CPolynomial.smul_equiv (p := q) (i := i - j) (r := a))


theorem CompPoly.CPolynomial.coeff_add_smul_mulPowX {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (acc q : CompPoly.CPolynomial R) (a : R) (k i : ℕ) :
    (acc + ((CompPoly.CPolynomial.smul a q).mulPowX k)).coeff i =
      acc.coeff i + (if i < k then 0 else a * q.coeff (i - k)) := by
  classical
  rw [CompPoly.CPolynomial.coeff_add (p := acc)
        (q := (CompPoly.CPolynomial.smul a q).mulPowX k) (i := i)]
  rw [CompPoly.CPolynomial.smul_mulPowX_coeff (a := a) (q := q) (j := k) (i := i)]

theorem CompPoly.CPolynomial.mul_coeff_partial_fold_step {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (p q : CompPoly.CPolynomial R) (i k : ℕ) (acc : CompPoly.CPolynomial R) :
    (acc.coeff i =
        (Array.range (min k (i + 1))).foldl (fun t j => t + p.coeff j * q.coeff (i - j)) 0) →
      (acc.add ((CompPoly.CPolynomial.smul (p.coeff k) q).mulPowX k)).coeff i =
        (Array.range (min (k + 1) (i + 1))).foldl (fun t j => t + p.coeff j * q.coeff (i - j)) 0 := by
  intro hk
  have hcoeff :
      (acc.add ((CompPoly.CPolynomial.smul (p.coeff k) q).mulPowX k)).coeff i =
        acc.coeff i + (if i < k then 0 else p.coeff k * q.coeff (i - k)) := by
    simpa using
      (CompPoly.CPolynomial.coeff_add_smul_mulPowX (acc := acc) (q := q)
        (a := p.coeff k) (k := k) (i := i))
  rw [hcoeff, hk]
  simpa using
    (CompPoly.CPolynomial.mul_coeff_partial_step (p := p) (q := q) (i := i) (k := k) (s := (0 : R)))

theorem CompPoly.CPolynomial.mul_coeff_partial_fold_step_getElem {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (p q : CompPoly.CPolynomial R) (i k : ℕ) (hklt : k < p.size) (acc : CompPoly.CPolynomial R) :
    (acc.coeff i =
        (Array.range (min k (i + 1))).foldl (fun t j => t + p.coeff j * q.coeff (i - j)) 0) →
      (acc.add ((CompPoly.CPolynomial.smul (p[k]) q).mulPowX k)).coeff i =
        (Array.range (min (k + 1) (i + 1))).foldl (fun t j => t + p.coeff j * q.coeff (i - j)) 0 := by
  intro hk
  have hp : p.coeff k = p[k] := by
    simpa using (CompPoly.CPolynomial.Trim.coeff_eq_getElem (p := p) (i := k) hklt)
  simpa [hp] using
    (CompPoly.CPolynomial.mul_coeff_partial_fold_step (p := p) (q := q) (i := i) (k := k) (acc := acc) hk)


theorem CompPoly.CPolynomial.mul_coeff_partial {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p q : CompPoly.CPolynomial R) (i : ℕ) :
    (p * q).coeff i =
      (Array.range (min p.size (i + 1))).foldl (fun acc j => acc + p.coeff j * q.coeff (i - j)) 0 := by
  classical
  change (CompPoly.CPolynomial.mul p q).coeff i = _
  unfold CompPoly.CPolynomial.mul
  let g : R → ℕ → R := fun t j => t + p.coeff j * q.coeff (i - j)
  let motive : ℕ → CompPoly.CPolynomial R → Prop :=
    fun k acc => acc.coeff i = (Array.range (min k (i + 1))).foldl g 0
  have hm :
      motive p.zipIdx.size
        (p.zipIdx.foldl
          (fun acc (x : R × ℕ) =>
            acc.add ((CompPoly.CPolynomial.smul x.1 q).mulPowX x.2))
          (CompPoly.CPolynomial.C (R := R) 0)) := by
    refine Array.foldl_induction (as := p.zipIdx)
      (motive := motive)
      (init := (CompPoly.CPolynomial.C (R := R) 0))
      (f := fun acc (x : R × ℕ) =>
        acc.add ((CompPoly.CPolynomial.smul x.1 q).mulPowX x.2))
      ?_ ?_
    · -- base
      simpa [motive, g] using
        (CompPoly.CPolynomial.mul_coeff_partial_base (p := p) (q := q) (i := i))
    · -- step
      intro k acc hk
      set n : ℕ := (k : ℕ)
      have hk' : acc.coeff i =
          (Array.range (min n (i + 1))).foldl
            (fun t j => t + p.coeff j * q.coeff (i - j)) 0 := by
        simpa [motive, g, n] using hk
      have hn : n < p.size := by
        have : (k : ℕ) < p.size := by
          simpa [CompPoly.Array.zipIdx_size (a := p)] using (show (k : ℕ) < p.zipIdx.size from k.is_lt)
        simpa [n] using this
      have hstep :=
        CompPoly.CPolynomial.mul_coeff_partial_fold_step_getElem
          (p := p) (q := q) (i := i) (k := n) (hklt := hn) (acc := acc) hk'
      simpa [motive, g, n, Array.getElem_zipIdx] using hstep
  have hz : p.zipIdx.size = p.size := by
    simpa using (CompPoly.Array.zipIdx_size (a := p))
  simpa [motive, g, hz] using hm

theorem CompPoly.CPolynomial.mul_coeff {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p q : CompPoly.CPolynomial R) (i : ℕ) :
    (p * q).coeff i =
      (Array.range (i + 1)).foldl (fun acc j => acc + p.coeff j * q.coeff (i - j)) 0 := by
  rw [CompPoly.CPolynomial.mul_coeff_partial, CompPoly.CPolynomial.range_foldl_min_eq_range_foldl]
