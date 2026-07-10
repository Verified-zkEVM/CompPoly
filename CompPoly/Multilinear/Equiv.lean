/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Aristotle (Harmonic), Elias Judin
-/
import CompPoly.Multilinear.TransformEquiv

/-!
  # Equivalence between `CMlPolynomial` and multilinear polynomials in `MvPolynomial`

  This file establishes the mathematical foundations for `CMlPolynomial` by proving:
  1. Basis properties for the coefficient representation
  2. Change-of-basis matrices between different representations
  3. Equivalences with mathlib's `MvPolynomial.restrictDegree`: `equivMvPolynomialDeg1`
  4. Arithmetic operation compatibilities
-/
open MvPolynomial

variable {R : Type*} {n : ℕ}

noncomputable section

namespace CompPoly

namespace CMlPolynomial

variable [CommSemiring R]

/-! ### Equivalence with Mathlib MvPolynomial
- Note: maybe we have to add more restrictions on `CMlPolynomial R n` and `CMlPolynomialEval R n`
  so we can differentiate them?
-/
/--
Converts a natural number to a monomial with 0/1 exponents.
Uses little‑endian bit encoding: bit 0 is the least significant bit.
The exponent at variable j is `Nat.getBit j i ∈ {0,1}`.
-/
noncomputable def monomialOfNat (i : ℕ) : (Fin n) →₀ ℕ :=
  Finsupp.onFinset (s:=Finset.univ (α:=Fin n)) (fun j => Nat.getBit j.val i) (by
    simp only [ne_eq, Finset.mem_univ, implies_true]) -- the support set is exactly Finset.univ

theorem eq_monomialOfNat_iff_eq_bitRepr (m : Fin n →₀ ℕ)
    (h_binary : ∀ j : Fin n, m j ≤ 1) (i: Fin (2^n)) :
  monomialOfNat i = m ↔ i = Nat.binaryFinMapToNat m h_binary := by
  constructor
  · intro h_mono_eq
    rw [Finsupp.ext_iff] at h_mono_eq
    apply Fin.eq_of_val_eq
    apply Nat.eq_iff_eq_all_getBits.mpr
    intro k
    -- ⊢ (if k < n then k.getBit ↑i else 0) = k.getBit ↑(Nat.binaryFinMapToNat (⇑m) h_binary)
    rw [Nat.getBit_of_lt_two_pow (a:=i) (k:=k)]
    rw [Nat.getBit_of_lt_two_pow (a:=Nat.binaryFinMapToNat m h_binary) (k:=k)]
    if h_k: k < n then
      simp only [h_k, ↓reduceIte]
      have h_getBit_binaryFinMap := Nat.getBit_of_binaryFinMapToNat (n:=n)
        (m:=m) (h_binary:=h_binary) (k:=k)
      rw [h_getBit_binaryFinMap]
      have h_monomialOfNat_at_k := h_mono_eq ⟨k, by omega⟩
      simp only [h_k, ↓reduceDIte]
      rw [h_monomialOfNat_at_k.symm] -- ⊢ k.getBit ↑i = (monomialOfNat ↑i) ⟨k, h_k⟩
      rfl -- due to definition of `monomialOfNat`
    else
      simp only [h_k, ↓reduceIte]
  · intro h_i_eq_i_of_m
    -- ⊢ monomialOfNat ↑i = m
    rw [Finsupp.ext_iff]
    intro a
    have h_k_getBit_eq_mono: ∀ k: Fin n, (monomialOfNat (n:=n) i) k = Nat.getBit k i := by
      intro k
      rfl
    -- ⊢ (monomialOfNat ↑i) a = m a
    have h_lhs := h_k_getBit_eq_mono (k:=a); rw [h_lhs] -- convert lhs to bit access
    -- ⊢ (↑a).getBit ↑i = m a
    rw [h_i_eq_i_of_m] -- convert lhs to access bit of `binaryFinMapToNat`
    simp only [Nat.getBit_of_binaryFinMapToNat (⇑m) h_binary a, Fin.is_lt, ↓reduceDIte, Fin.eta]

/--
Converts an `CMlPolynomial` to a mathlib multivariate polynomial.
Sums over all indices `i : Fin (2^n)` with monomial exponents from `monomialOfNat i`
and coefficients `p[i]`.
-/
def toMvPolynomial (p : CMlPolynomial R n) : MvPolynomial (Fin n) R :=
  ∑ i : Fin (2 ^ n), MvPolynomial.monomial (monomialOfNat i) (a:=p[i])

/-- Evaluating the associated multivariate polynomial agrees with coefficient evaluation. -/
theorem eval_toMvPolynomial (p : CMlPolynomial R n) (x : Vector R n) :
    MvPolynomial.eval (fun i ↦ x[i]) (toMvPolynomial p) = p.eval x := by
  unfold toMvPolynomial eval
  simp +decide [MvPolynomial.eval_monomial, Vector.dotProduct_eq_root_dotProduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr! 2
  unfold monomialOfNat monomialBasis
  simp +decide [Finset.prod_ite]
  rw [Finset.prod_filter]
  congr
  ext j
  simp +decide [Nat.getBit]
  cases Nat.mod_two_eq_zero_or_one (i.val >>> j.val) <;> simp +decide [*, Nat.testBit]

-- #check (toMvPolynomial (CMlPolynomial.mk 2 #v[(1: ℤ), 2, 3, 4]))

theorem toMvPolynomial_is_multilinear (p : CMlPolynomial R n) :
    (toMvPolynomial p) ∈ MvPolynomial.restrictDegree (Fin n) R 1 := by
  rw [toMvPolynomial]
    -- ⊢ (∑ i, C p[i] * ∏ j, if { toFin := i }.getLsb j = true then X j else 1)
    -- ∈ MvPolynomial.restrictDegree (Fin n) R 1
  simp only [MvPolynomial.mem_restrictDegree]
  intro s hs k -- s is a point X where the sum evaluates to non-zero
  rw [MvPolynomial.mem_support_iff] at hs
  rw [MvPolynomial.coeff_sum] at hs
  by_contra h_s_k_gt_1
  push Not at h_s_k_gt_1 -- h_s_k_gt_1 : 1 < s k
  have h_invalid: ∀ x: Fin (2^n),
    (coeff s (MvPolynomial.monomial (R:=R) (monomialOfNat x) (a:=p[x]))) = 0 := by
    intro x
    rw [MvPolynomial.coeff_monomial]
    -- ⊢ (if monomialOfNat ↑x = s then p[x] else 0) = 0
    have h_monomialOfNat_x_ne_s: monomialOfNat x ≠ s := by
      by_contra h_s_eq_mx
      subst h_s_eq_mx
      simp_rw [monomialOfNat] at h_s_k_gt_1
      simp only [Finsupp.onFinset_apply] at h_s_k_gt_1
      have h_getBit_lt_2: Nat.getBit k x.val < 2 := by exact Nat.getBit_lt_2
      have h_ne_1_lt_getBit: ¬(1 < Nat.getBit k x.val) := by omega
      exact h_ne_1_lt_getBit h_s_k_gt_1
    simp only [h_monomialOfNat_x_ne_s, ↓reduceIte]
  have h_sum_zero: ∑ x: Fin (2^n), (coeff s (MvPolynomial.monomial
    (R:=R) (monomialOfNat x) (a:=p[x]))) = 0 := by
    simp_rw [h_invalid]
    exact Fintype.sum_eq_zero (fun a ↦ 0) (congrFun rfl)
  exact hs h_sum_zero

theorem coeff_of_toMvPolynomial_eq_coeff_of_CMlPolynomial (p : CMlPolynomial R n) (m : Fin n →₀ ℕ) :
    coeff m (toMvPolynomial p) =
    if h_binary : (∀ j : Fin n, m j ≤ 1) then
        let i_of_m : ℕ := Nat.binaryFinMapToNat (m := m) (h_binary := h_binary)
        p[i_of_m]
      else
        0 := by
  if h_binary: (∀ j: Fin n, m j ≤ 1) then
    unfold toMvPolynomial
    simp only [h_binary, implies_true, ↓reduceDIte]
    let i_of_m := Nat.binaryFinMapToNat m h_binary
    have h_mono_eq : monomialOfNat i_of_m = m := by
      ext j; simp only [monomialOfNat, Finsupp.onFinset_apply]
      have h_getBit := Nat.getBit_of_binaryFinMapToNat (n:=n) (m:=m)
        (h_binary:=h_binary) (k:=j)
      rw [h_getBit]
      simp only [j.isLt, ↓reduceDIte, Fin.eta]
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    -- ⊢ (∑ x, if monomialOfNat ↑x = m then p[x] else 0) = p[↑(Nat.binaryFinMapToNat ⇑m ⋯)]
    set f := fun x: Fin (2^n) => if monomialOfNat x.val = m then p[x] else (0: R)
    -- ⊢ Finset.univ.sum f = p[↑(Nat.binaryFinMapToNat ⇑m ⋯)]
    rw [Finset.sum_eq_single (a:=⟨i_of_m, by omega⟩)]
    · -- Goal 1: Prove the main term is correct.
      simp only [h_mono_eq, ↓reduceIte, Fin.eta, Fin.getElem_fin];
      rfl
    · -- Goal 2: Prove all other terms are zero.
      intro j h_j_mem_univ h_ji_ne
      -- If `j ≠ i_of_m`, then `monomialOfNat j ≠ monomialOfNat i_of_m` (which is `m`).
      -- ⊢ (monomial (monomialOfNat ↑j)) p[j] = 0
      have h_mono_ne : monomialOfNat j.val ≠ m := by
        intro h_eq_contra
        have h_j_is_i_of_m := eq_monomialOfNat_iff_eq_bitRepr (m:=m)
          (h_binary:=h_binary) (i:=j).mp h_eq_contra
        exact h_ji_ne h_j_is_i_of_m
      simp only [h_mono_ne, ↓reduceIte]
    -- Goal 3: Prove `i` is in the summation set.
    · simp [Finset.mem_univ]
  else -- this case is similar to the proof of `right_inv` in `equivMvPolynomialDeg1`
    simp only [h_binary, ↓reduceDIte]
    -- ⊢ coeff m p.toMvPolynomial = 0
    have hv := toMvPolynomial_is_multilinear p
    let vCMlPolynomial: MvPolynomial.restrictDegree (Fin n) R 1 := ⟨p.toMvPolynomial, hv⟩
    have h_v_coeff_zero : vCMlPolynomial.val.coeff m = 0 := by
      refine notMem_support_iff.mp ?_
      by_contra h_mem_support
      have hvCMlPolynomial := vCMlPolynomial.2
      rw [MvPolynomial.mem_restrictDegree] at hvCMlPolynomial
      have h_deg_le_one: ∀ j: Fin n, (m j) ≤ 1 := by
        exact fun j ↦ hvCMlPolynomial m h_mem_support j
      simp only [not_forall, not_le] at h_binary -- h_binary : ∃ x, 1 < m x
      obtain ⟨j, hj⟩ := h_binary
      have h_not_1_lt_m_j: ¬(1 < m j) := by exact Nat.not_lt.mpr (hv h_mem_support j)
      exact h_not_1_lt_m_j hj
    exact h_v_coeff_zero

/--
Converts an `CMlPolynomial` to a mathlib restricted-degree multivariate polynomial.
Wraps `toMvPolynomial` with a proof that the result is multilinear (i.e. individual degrees ≤ 1).
-/
def toMvPolynomialDeg1 (p : CMlPolynomial R n) : MvPolynomial.restrictDegree (Fin n) R 1 :=
  ⟨toMvPolynomial p, by exact toMvPolynomial_is_multilinear p⟩

/--
Converts a mathlib restricted-degree multivariate polynomial to an `CMlPolynomial`.
Extracts coefficients using `monomialOfNat` to map indices to monomials.
-/
def ofMvPolynomialDeg1 (p : MvPolynomial.restrictDegree (Fin n) R 1) : CMlPolynomial R n :=
  Vector.ofFn (fun i : Fin (2 ^ n) => p.val.coeff (monomialOfNat i))

-- #eval finFunctionFinEquiv.invFun (⟨3, by omega⟩: Fin (2^2)) 4
-- #eval Nat.getBit (k:=4) (n:=3)

/--
Equivalence between `CMlPolynomial` and mathlib's restricted-degree multivariate polynomials.
Establishes that both representations are isomorphic via coefficient extraction/insertion.
-/
def equivMvPolynomialDeg1 : CMlPolynomial R n ≃ MvPolynomial.restrictDegree (Fin n) R 1 where
  toFun := toMvPolynomialDeg1
  invFun := ofMvPolynomialDeg1
  left_inv v := by
    unfold ofMvPolynomialDeg1 toMvPolynomialDeg1
    apply Vector.ext; intro j x
    simp only [Vector.getElem_ofFn]
    simp only [toMvPolynomial, Fin.getElem_fin]
    -- ⊢ coeff (monomialOfNat j) (∑ x, (monomial (monomialOfNat ↑x)) v[↑x]) = v[j]
    rw [MvPolynomial.coeff_sum]
    -- ⊢ ∑ x, coeff (monomialOfNat j) ((monomial (monomialOfNat ↑x)) v[↑x]) = v[j]
    simp only [MvPolynomial.coeff_monomial]
    -- ⊢ (∑ x, if monomialOfNat ↑x = monomialOfNat j then v[↑x] else 0) = v[j]
    set f := fun x: Fin (2^n) => if monomialOfNat x.val = monomialOfNat j then v[x.val] else (0: R)
    -- ⊢ Finset.univ.sum f = v[j]
    have h_v_j: v[j] = f ⟨j, by omega⟩ := by
      simp only [f]
      simp only [↓reduceIte]
    rw [h_v_j]
    -- ⊢ Finset.univ.sum f = f ⟨j, x⟩
    rw [Finset.sum_eq_single (a:=⟨j, by omega⟩)]
      -- Goal 1: Prove the main term is correct.
    · intro b hb hb_ne
      have h_monominal_diff: monomialOfNat (n:=n) (i:=b.val) ≠ monomialOfNat (i:=j) := by
        simp only [monomialOfNat, ne_eq]
        -- ⊢ ¬Finsupp.onFinset Finset.univ (fun j ↦ (↑j).getBit ↑b) ⋯
        -- = Finsupp.onFinset Finset.univ (fun j_1 ↦ (↑j_1).getBit j) ⋯
        refine Finsupp.ne_iff.mpr ?_
        have h_exists_bit_diff := Nat.exist_bit_diff_if_diff (a:=b) (b:=⟨j, by omega⟩)
          (h_a_ne_b:=hb_ne)
        obtain ⟨k, h_getBit_k_diff⟩ := h_exists_bit_diff
        use k
        simp only [Finsupp.onFinset_apply, ne_eq]
        exact h_getBit_k_diff
      simp only [h_monominal_diff, ↓reduceIte]
    · intro h_jx_ne_in_univ
      have h_jx_in_univ: (⟨j, x⟩: Fin (2^n)) ∈ Finset.univ := by
        exact Finset.mem_univ (⟨j, x⟩: Fin (2^n))
      contradiction
  right_inv v := by
    unfold toMvPolynomialDeg1 ofMvPolynomialDeg1 toMvPolynomial
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    -- ⊢ ⟨∑ x, (monomial (monomialOfNat ↑x)) (coeff (monomialOfNat ↑x) ↑v), ⋯⟩ = v
    ext m
    simp only
    rw [MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_monomial]
    -- ⊢ (∑ x, if monomialOfNat ↑x = m then coeff (monomialOfNat ↑x) ↑v else 0) = coeff m ↑v
    by_cases h_m_is_ML_mono: (∀ j : Fin n, m j ≤ 1) -- this cond could leads to m ∈ v.support
    · let i_of_m := Nat.binaryFinMapToNat m h_m_is_ML_mono
      -- We can prove that `monomialOfNat i.val` is indeed `m`.
      have h_mono_eq : monomialOfNat i_of_m = m := by
        ext j; simp only [monomialOfNat, Finsupp.onFinset_apply]
        have h_getBit := Nat.getBit_of_binaryFinMapToNat (n:=n) (m:=m)
          (h_binary:=h_m_is_ML_mono) (k:=j)
        rw [h_getBit]
        simp only [j.isLt, ↓reduceDIte, Fin.eta]
      rw [Finset.sum_eq_single (a:=i_of_m)]
      · simp only [h_mono_eq, ↓reduceIte] -- Goal 1: Prove the main term is correct.
      · intro j h_j_mem_univ h_ji_ne -- Goal 2: Prove all other terms are zero.
        -- If `j ≠ i`, then `monomialOfNat j ≠ monomialOfNat i` (which is `m`).
        have h_mono_ne : monomialOfNat j.val ≠ m := by
          intro h_eq_contra
          have h_j_is_i_of_m := eq_monomialOfNat_iff_eq_bitRepr (m:=m)
            (h_binary:=h_m_is_ML_mono) (i:=j).mp h_eq_contra
          exact h_ji_ne h_j_is_i_of_m
        simp only [h_mono_ne, ↓reduceIte]
      -- Goal 3: Prove `i` is in the summation set.
      · simp [Finset.mem_univ]
    · -- `m` is not a multilinear monomial => rhs = `coeff m v = 0`, since `v` is multilinear.
      push Not at h_m_is_ML_mono
      obtain ⟨j, hj⟩ := h_m_is_ML_mono
      have h_v_coeff_zero : v.val.coeff m = 0 := by
        refine notMem_support_iff.mp ?_
        by_contra h_mem_support
        have hv := v.2
        simp only [MvPolynomial.mem_restrictDegree] at hv
        have h_deg_le_one: ∀ j: Fin n, (m j) ≤ 1 := by
          exact fun j ↦ hv m h_mem_support j
        have hj_le_1 := h_deg_le_one j
        linarith
      -- We now show the LHS is also zero.
      rw [h_v_coeff_zero]
      apply Finset.sum_eq_zero
      intro i hi
      -- `monomialOfNat i` is always multilinear. `m` is not.
      -- Therefore, `m` can never equal `monomialOfNat i`, so the `if` is always false.
      have h_mono_ne : monomialOfNat i.val ≠ m := by
        intro h_eq_contra
        have h_m_i_multi : ∀ j: Fin n, (monomialOfNat i.val) j ≤ 1 := by
          intro j; simp [monomialOfNat, Finsupp.onFinset_apply]
          have h := Nat.getBit_lt_2 (k:=j) (n:=i)
          omega
        rw [h_eq_contra] at h_m_i_multi
        have h_m_i_multi_j_le_1 := h_m_i_multi j
        linarith
      simp only [h_mono_ne, ↓reduceIte]

/-- Linear equivalence between `CMlPolynomial` and `MvPolynomial.restrictDegree` -/
noncomputable def linearEquivMvPolynomialDeg1 :
  CMlPolynomial R n ≃ₗ[R] MvPolynomial.restrictDegree (Fin n) R 1 :=
  { toEquiv := equivMvPolynomialDeg1
    map_add' := by
      intro p q
      -- ⊢ (p + q).toMvPolynomialDeg1 = p.toMvPolynomialDeg1 + q.toMvPolynomialDeg1
      ext i
      -- ⊢ coeff i ↑(p + q).toMvPolynomialDeg1 =
      -- coeff i ↑(p.toMvPolynomialDeg1 + q.toMvPolynomialDeg1)
      unfold equivMvPolynomialDeg1 toMvPolynomialDeg1
      simp only [AddMemClass.mk_add_mk, coeff_add]
      erw [coeff_of_toMvPolynomial_eq_coeff_of_CMlPolynomial (p := p + q)]
      simp only [coeff_of_toMvPolynomial_eq_coeff_of_CMlPolynomial (p := p)]
      simp only [coeff_of_toMvPolynomial_eq_coeff_of_CMlPolynomial (p := q)]
      if h_binary: (∀ j: Fin n, i j ≤ 1) then
        simp only [h_binary, implies_true, ↓reduceDIte]
        erw [Vector.getElem_zipWith]
      else
        simp only [h_binary, ↓reduceDIte, add_zero]
    map_smul' := by
      intro r p
      ext i
      unfold equivMvPolynomialDeg1 toMvPolynomialDeg1
      simp only [RingHom.id_apply, SetLike.mk_smul_mk, coeff_smul, smul_eq_mul]
      erw [coeff_of_toMvPolynomial_eq_coeff_of_CMlPolynomial (p := r • p)]
      simp only [coeff_of_toMvPolynomial_eq_coeff_of_CMlPolynomial (p := p)]
      if h_binary: (∀ j: Fin n, i j ≤ 1) then
        simp only [h_binary, implies_true, ↓reduceDIte]
        erw [Vector.getElem_map]; rfl
      else
        simp only [h_binary, ↓reduceDIte, mul_zero]
    }

end CMlPolynomial

namespace CMlPolynomialEval

variable [CommRing R]

/-- Converts a hypercube-evaluation representation to a Mathlib multivariate polynomial by first
recovering the monomial-basis representation. -/
def toMvPolynomial (p : CMlPolynomialEval R n) : MvPolynomial (Fin n) R :=
  CMlPolynomial.toMvPolynomial (CMlPolynomial.lagrangeToMono n p)

/-- The inverse of the finite-function encoder reads the corresponding
little-endian bit. -/
private theorem finFunctionFinEquiv_symm_apply_two (i : Fin (2 ^ n)) (j : Fin n) :
    ((finFunctionFinEquiv.symm i) j).val = Nat.getBit j.val i.val := by
  simp [finFunctionFinEquiv, Equiv.ofRightInverseOfCardLE, Nat.getBit,
    Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

/-- The local factor used to expand a Boolean-lattice zeta transform against
the multilinear Lagrange basis. -/
private def basisChangeFactor (x : Vector R n) (j : Fin (2 ^ n))
    (k : Fin n) (b : Fin 2) : R :=
  if j.val.testBit k.val then
    (b.val : R) * x[k]
  else
    (b.val : R) * x[k] + (1 - (b.val : R)) * (1 - x[k])

private theorem sum_basisChangeFactor (x : Vector R n) (j : Fin (2 ^ n))
    (k : Fin n) :
    (∑ b : Fin 2, basisChangeFactor x j k b) =
      if j.val.testBit k.val then x[k] else 1 := by
  rw [Fin.sum_univ_two]
  by_cases hj : j.val.testBit k.val <;> simp [basisChangeFactor, hj]

private theorem submask_lagrange_eq_factor_prod
    (x : Vector R n) (i j : Fin (2 ^ n)) :
    (if i.val &&& j.val = j.val then (lagrangeBasis x).get i else 0) =
      ∏ k : Fin n, basisChangeFactor x j k ((finFunctionFinEquiv.symm i) k) := by
  by_cases hsub : i.val &&& j.val = j.val
  · rw [if_pos hsub]
    unfold lagrangeBasis
    simp only [Vector.get_ofFn, BitVec.getLsb_eq_getElem, Fin.getElem_fin,
      BitVec.getElem_ofFin]
    apply Finset.prod_congr rfl
    intro k _
    have hdecode := finFunctionFinEquiv_symm_apply_two i k
    by_cases hj : j.val.testBit k.val = true
    · have hi : i.val.testBit k.val = true := by
        have hbits := congrArg (fun m : ℕ ↦ m.testBit k.val) hsub
        simpa [Nat.testBit_and, hj] using hbits
      simp [Nat.getBit_eq_testBit, hi] at hdecode
      simp [basisChangeFactor, hj, hi, hdecode]
    · cases hi : i.val.testBit k.val <;>
        simp [Nat.getBit_eq_testBit, hi] at hdecode <;>
        simp [basisChangeFactor, hj, hdecode]
  · rw [if_neg hsub]
    obtain ⟨k, hj, hi⟩ :
        ∃ k : Fin n, j.val.testBit k.val = true ∧ i.val.testBit k.val = false := by
      by_contra h
      apply hsub
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and]
      by_cases hk : k < n
      · let k' : Fin n := ⟨k, hk⟩
        by_cases hj' : j.val.testBit k = true
        · have hi' : i.val.testBit k ≠ false := by
            intro hi'
            exact h ⟨k', hj', hi'⟩
          cases hibit : i.val.testBit k <;> simp_all
        · cases hjbit : j.val.testBit k <;> simp_all
      · have hnk : n ≤ k := Nat.le_of_not_gt hk
        have hi' : i.val.testBit k = false :=
          Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right two_pos hnk))
        have hj' : j.val.testBit k = false :=
          Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right two_pos hnk))
        simp [hi', hj']
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    have hdecode := finFunctionFinEquiv_symm_apply_two i k
    simp [Nat.getBit_eq_testBit, hi] at hdecode
    simp [basisChangeFactor, hj, hdecode]

private theorem submask_lagrange_sum (x : Vector R n) (j : Fin (2 ^ n)) :
    (∑ i : Fin (2 ^ n),
        if i.val &&& j.val = j.val then (lagrangeBasis x).get i else 0) =
      (CMlPolynomial.monomialBasis x).get j := by
  calc
    _ = ∑ i : Fin (2 ^ n),
        ∏ k : Fin n, basisChangeFactor x j k ((finFunctionFinEquiv.symm i) k) := by
      exact Finset.sum_congr rfl fun i _ ↦ submask_lagrange_eq_factor_prod x i j
    _ = ∑ y : Fin n → Fin 2, ∏ k : Fin n, basisChangeFactor x j k (y k) := by
      symm
      exact Fintype.sum_equiv finFunctionFinEquiv _ _ fun y ↦ by simp
    _ = ∏ k : Fin n, ∑ b : Fin 2, basisChangeFactor x j k b := by
      rw [Fintype.prod_sum]
    _ = ∏ k : Fin n, if j.val.testBit k.val then x[k] else 1 := by
      exact Finset.prod_congr rfl fun k _ ↦ sum_basisChangeFactor x j k
    _ = (CMlPolynomial.monomialBasis x).get j := by
      unfold CMlPolynomial.monomialBasis
      simp only [Vector.get_ofFn, BitVec.getLsb_eq_getElem, Fin.getElem_fin,
        BitVec.getElem_ofFin]

/-- Changing monomial coefficients to Boolean-hypercube evaluations preserves
evaluation at every point. -/
theorem eval_monoToLagrange (p : CMlPolynomial R n) (x : Vector R n) :
    (CMlPolynomial.monoToLagrange n p : CMlPolynomialEval R n).eval x = p.eval x := by
  rw [CMlPolynomial.monoToLagrange_eq_monoToLagrangeSpec]
  rw [eval, CMlPolynomial.eval, Vector.dotProduct_eq_root_dotProduct,
    Vector.dotProduct_eq_root_dotProduct]
  unfold _root_.dotProduct CMlPolynomial.monoToLagrangeSpec
  simp only [Vector.get_ofFn]
  calc
    (∑ i : Fin (2 ^ n),
        (∑ j : Fin (2 ^ n), if i.val &&& j.val = j.val then p.get j else 0) *
          (lagrangeBasis x).get i) =
        ∑ i : Fin (2 ^ n), ∑ j : Fin (2 ^ n),
          p.get j *
            (if i.val &&& j.val = j.val then (lagrangeBasis x).get i else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hsub : i.val &&& j.val = j.val <;> simp [hsub]
    _ = ∑ j : Fin (2 ^ n), ∑ i : Fin (2 ^ n),
          p.get j *
            (if i.val &&& j.val = j.val then (lagrangeBasis x).get i else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin (2 ^ n), p.get j *
          (∑ i : Fin (2 ^ n),
            if i.val &&& j.val = j.val then (lagrangeBasis x).get i else 0) := by
      exact Finset.sum_congr rfl fun j _ ↦ (Finset.mul_sum _ _ _).symm
    _ = ∑ j : Fin (2 ^ n), p.get j * (CMlPolynomial.monomialBasis x).get j := by
      exact Finset.sum_congr rfl fun j _ ↦ by rw [submask_lagrange_sum]

/-- Recovering monomial coefficients from a hypercube table preserves its
multilinear-extension evaluation. -/
theorem eval_lagrangeToMono (p : CMlPolynomialEval R n) (x : Vector R n) :
    CMlPolynomial.eval (CMlPolynomial.lagrangeToMono n p) x =
      CMlPolynomialEval.eval p x := by
  have h := eval_monoToLagrange (CMlPolynomial.lagrangeToMono n p) x
  have hinv :=
    (CMlPolynomial.equivMonomialLagrangeRepr (R := R) (n := n)).apply_symm_apply p
  have hinv' :
      CMlPolynomial.monoToLagrange n (CMlPolynomial.lagrangeToMono n p) = p := by
    simpa [CMlPolynomial.equivMonomialLagrangeRepr] using hinv
  rw [hinv'] at h
  exact h.symm

/-- Evaluating the multivariate polynomial recovered from a hypercube table
agrees with multilinear-extension evaluation. -/
theorem eval_toMvPolynomial (p : CMlPolynomialEval R n) (x : Vector R n) :
    MvPolynomial.eval (fun i ↦ x[i]) (toMvPolynomial p) = p.eval x := by
  rw [toMvPolynomial, CMlPolynomial.eval_toMvPolynomial]
  exact eval_lagrangeToMono p x

/-- Converts a hypercube-evaluation representation to a Mathlib restricted-degree multivariate
polynomial. -/
def toMvPolynomialDeg1 (p : CMlPolynomialEval R n) :
    MvPolynomial.restrictDegree (Fin n) R 1 :=
  CMlPolynomial.toMvPolynomialDeg1 (CMlPolynomial.lagrangeToMono n p)

/-- The multilinear equality polynomial centered at `w`. -/
def eqPolynomial (w : Vector R n) : MvPolynomial (Fin n) R :=
  toMvPolynomial (lagrangeBasis w)

/-- The restricted-degree multilinear equality polynomial centered at `w`. -/
def eqPolynomialDeg1 (w : Vector R n) :
    MvPolynomial.restrictDegree (Fin n) R 1 :=
  toMvPolynomialDeg1 (lagrangeBasis w)

end CMlPolynomialEval

end CompPoly
