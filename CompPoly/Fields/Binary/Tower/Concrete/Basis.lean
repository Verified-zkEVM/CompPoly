/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Fields.Binary.Tower.Concrete.Algebra

namespace ConcreteBinaryTower

open Polynomial

noncomputable section ConcreteMultilinearBasis
/- Multilinear basis and defining polynomials -/

open Module

@[simp]
theorem Basis_cast_index_eq (i j k n : ℕ) (h_le : k ≤ n) (h_eq : i = j) :
    letI instAlgebra : Algebra (ConcreteBTField k) (ConcreteBTField n) :=
      ConcreteBTFieldAlgebra (l:=k) (r:=n) (h_le:=h_le)
    letI : Module (ConcreteBTField k) (ConcreteBTField n) := instAlgebra.toModule
    (Basis (Fin (i)) (ConcreteBTField k) (ConcreteBTField n)) =
    (Basis (Fin (j)) (ConcreteBTField k) (ConcreteBTField n)) := by
  subst h_eq
  rfl

theorem Basis_cast_dest_eq {ι : Type*} (k n m : ℕ) (h_k_le_n : k ≤ n)
    (h_k_le_m : k ≤ m) (h_eq : m = n) :
  letI instLeftAlgebra := ConcreteBTFieldAlgebra (l:=k) (r:=m) (h_le:=h_k_le_m)
  letI instRightAlgebra := ConcreteBTFieldAlgebra (l:=k) (r:=n) (h_le:=h_k_le_n)
  @Basis ι (ConcreteBTField k) (ConcreteBTField m) _ _ instLeftAlgebra.toModule =
  @Basis ι (ConcreteBTField k) (ConcreteBTField n) _ _ instRightAlgebra.toModule := by
  subst h_eq
  rfl

theorem PowerBasis_cast_dest_eq (k n m : ℕ) (h_k_le_n : k ≤ n)
    (h_k_le_m : k ≤ m) (h_eq : m = n) :
  letI instLeftAlgebra := ConcreteBTFieldAlgebra (l:=k) (r:=m) (h_le:=h_k_le_m)
  letI instRightAlgebra := ConcreteBTFieldAlgebra (l:=k) (r:=n) (h_le:=h_k_le_n)
  @PowerBasis (ConcreteBTField k) (ConcreteBTField m) _ _ instLeftAlgebra =
  @PowerBasis (ConcreteBTField k) (ConcreteBTField n) _ _ instRightAlgebra := by
  subst h_eq
  rfl
/-!
The following two theorems are used to cast the basis of `ConcreteBTField α`
to `ConcreteBTField β` via changing in index type : `Fin (i)` to `Fin (j)` when `α ≤ β`.
-/
@[simp]
theorem Basis_cast_index_apply {α β i j : ℕ} {k : Fin j}
    (h_le : α ≤ β) (h_eq : i = j)
    {b : @Basis (Fin (i)) (ConcreteBTField α) (ConcreteBTField β) _ _
      (@ConcreteBTFieldAlgebra (l := α) (r := β) (h_le := h_le)).toModule} :
  let castBasis : @Basis (Fin j) (ConcreteBTField α) (ConcreteBTField β) _ _
    (@ConcreteBTFieldAlgebra (l:=α) (r:=β) (h_le:=h_le)).toModule :=
    cast (by exact Basis_cast_index_eq i j α β h_le h_eq) b
  (castBasis k) = b (Fin.cast (h_eq.symm) k) := by
  subst h_eq
  rfl

@[simp]
theorem Basis_cast_dest_apply {ι : Type*} (α β γ : ℕ)
    (h_le1 : α ≤ β) (h_le2 : α ≤ γ)
    (h_eq : β = γ) {k : ι} (b : @Basis ι (ConcreteBTField α) (ConcreteBTField β) _ _
    (@ConcreteBTFieldAlgebra (l := α) (r := β) (h_le := h_le1)).toModule) :
    let castBasis : @Basis ι (ConcreteBTField α) (ConcreteBTField γ) _ _
      (@ConcreteBTFieldAlgebra (l := α) (r := γ) (h_le := h_le2)).toModule :=
      cast (by
        exact Basis_cast_dest_eq α γ β h_le2 h_le1 h_eq
      ) b
    (castBasis k) = cast (by
      exact cast_ConcreteBTField_eq β γ h_eq) (b k) := by
  subst h_eq
  rfl

def basisSucc (k : ℕ) : Basis (Fin 2) (ConcreteBTField k) (ConcreteBTField (k + 1)) := by
  letI instAlgebra:= ConcreteBTFieldAlgebra (l:=k) (r:=k + 1) (h_le:=by omega)
  let generator := Z (k + 1)
  apply @Basis.mk (ι:=Fin 2) (R:=ConcreteBTField k) (M:=ConcreteBTField (k + 1))
    _ _ instAlgebra.toModule (v:=fun i => generator ^ (i : ℕ))
  · -- This proof now works smoothly.
    set basisFunc := fun (i : Fin 2) => (generator) ^ (i : ℕ)
    refine linearIndependent_fin2'.mpr ?_
    constructor
    · simp only [basisFunc]
      simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, ne_eq, one_ne_zero,
        not_false_eq_true]
    · intro a
      -- ⊢ a • basisFunc 1 ≠ basisFunc 0
      unfold basisFunc
      simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, Nat.mod_succ, pow_one,
        ne_eq]
      rw [Algebra.smul_def']
      change (¬(concreteTowerAlgebraMap (l:=k) (r:=k+1) (h_le:=by omega) a) * 1 = generator)
      rw [mul_one]
      rw [concreteTowerAlgebraMap_succ_1]
      -- ⊢ ¬(canonicalAlgMap k) a = generator
      exact generator_is_not_lifted_to_succ k a
  · intro x hx
    -- proof that the span of powers of generator is ConcreteBTField (k+1)
    rw [Submodule.mem_span]
    intro p h_p_contains_basis
    have h_one_in_p : (1 : ConcreteBTField (k + 1)) ∈ p := by
      convert h_p_contains_basis (Set.mem_range_self (0 : Fin 2));

    have h_gen_in_p : generator ∈ p := by
      convert h_p_contains_basis (Set.mem_range_self (1 : Fin 2)); simp

    -- Now, use the lemma from your project that decomposes any element `x`
    -- into a linear combination of the basis vectors.
    -- I'm using `exists_decomp_lemma` as a placeholder for its name.
    obtain ⟨a, b, hx_decomp⟩ : ∃ (a b : ConcreteBTField k),
        x = (concreteTowerAlgebraMap (l:=k) (r:=k+1) (h_le:=by omega) a) +
          (concreteTowerAlgebraMap (l:=k) (r:=k+1) (h_le:=by omega) b) * generator := by
      -- ⊢ ∃ a b, x = (concreteTowerAlgebraMap k (k + 1)
      -- ⋯) a + (concreteTowerAlgebraMap k (k + 1) ⋯) b * generator
      let h_split_x_raw := split (k:=k+1) (h:=by omega) x
      let hi_btf := h_split_x_raw.fst
      let lo_btf := h_split_x_raw.snd
      have h_split_x : split (k:=k+1) (h:=by omega) x = (hi_btf, lo_btf) := by rfl
      have h_join_x : 《 hi_btf, lo_btf 》 = x := by
        rw [join_of_split (by omega) x hi_btf lo_btf h_split_x]
      have h_sum_if_join := join_eq_join_via_add_smul (h_pos:=by omega)
        (hi_btf:=hi_btf) (lo_btf:=lo_btf)
      have h_add_smul := by
        rw [h_sum_if_join] at h_join_x
        exact h_join_x
      use lo_btf, hi_btf
      rw [←h_add_smul]
      unfold join_via_add_smul
      simp only [Nat.add_one_sub_one]
      rw [algebraMap, Algebra.algebraMap, ConcreteBTFieldAlgebra_def]
      simp only
      simp only [generator]
      rw [add_comm]
      congr -- .Q.E.D
    rw [hx_decomp] -- Now we rewrite `x` using this decomposition.
    -- Since `p` is a submodule, it's closed under scalar multiplication and addition.
    -- We show each part of the sum is in `p`.
    -- The first part of the sum is `a' • 1`.
    have h_part1_in_p : (concreteTowerAlgebraMap (l:=k) (r:=k+1) (h_le:=by omega) a) ∈ p := by
      rw [← mul_one (concreteTowerAlgebraMap (l:=k) (r:=k+1) (h_le:=by omega) a)]
      -- , ← AlgebraTower.smul_def']
      exact p.smul_mem a h_one_in_p

    -- The second part of the sum is `b' • generator`.
    have h_part2_in_p : (concreteTowerAlgebraMap (l:=k) (r:=k+1) (h_le:=by omega) b)
      * generator ∈ p := by
      -- rw [← AlgebraTower.m]
      exact p.smul_mem b h_gen_in_p
    -- Since both parts are in `p`, their sum is also in `p`.
    exact p.add_mem h_part1_in_p h_part2_in_p

/-!
The power basis for `ConcreteBTField (k + 1)` over `ConcreteBTField k` is {1, Z (k + 1)}
-/
def powerBasisSucc (k : ℕ) :
    PowerBasis (ConcreteBTField k) (ConcreteBTField (k + 1)) := by
  exact {
    gen := Z (k + 1),
    dim := 2,
    basis := basisSucc k,
    basis_eq_pow := by
      intro i
      rw [basisSucc]
      simp only [Basis.coe_mk]
  }

lemma powerBasisSucc_gen (k : ℕ) :
    (powerBasisSucc k).gen = (Z (k + 1)) := by rfl

@[simp]
theorem minPoly_of_powerBasisSucc_generator (k : ℕ) :
    (minpoly (ConcreteBTField k) (powerBasisSucc k).gen) = X^2 + (Z k) • X + 1 := by
  unfold powerBasisSucc
  simp only
  rw [←C_mul']
  letI: Fintype (ConcreteBTField k) := (getBTFResult k).instFintype
  refine Eq.symm (minpoly.unique' (ConcreteBTField k) (Z (k + 1)) ?_ ?_ ?_)
  · exact (definingPoly_is_monic (s:=Z (k)))
  · exact aeval_definingPoly_at_Z_succ k
  · intro q h_degQ_lt_deg_minPoly
    -- h_degQ_lt_deg_minPoly : q.degree < (X ^ 2 + Z k • X + 1).degree
    -- ⊢ q = 0 ∨ (aeval (Z (k + 1))) q ≠ 0
    have h_degree_definingPoly : (definingPoly (s:=Z (k))).degree = 2 := by
      exact degree_definingPoly (s:=Z (k))
    rw [←definingPoly, h_degree_definingPoly] at h_degQ_lt_deg_minPoly
    if h_q_is_zero : q = 0 then
      rw [h_q_is_zero]
      simp only [map_zero, ne_eq, not_true_eq_false, or_false]
    else
      -- reason stuff related to IsUnit here
      have h_q_is_not_zero : q ≠ 0 := by omega
      simp only [h_q_is_zero, ne_eq, false_or]
      -- ⊢ ¬(aeval (Z (k + 1))) q = 0
      have h_deg_q_ne_bot : q.degree ≠ ⊥ := by
        exact degree_ne_bot.mpr h_q_is_zero
      have q_natDegree_lt_2 : q.natDegree < 2 := by
        exact (natDegree_lt_iff_degree_lt h_q_is_zero).mpr h_degQ_lt_deg_minPoly
      -- do case analysis on q.degree
      interval_cases hqNatDeg : q.natDegree
      · simp only [ne_eq]
        have h_q_is_c : ∃ r : ConcreteBTField k, q = C r := by
          use q.coeff 0
          exact Polynomial.eq_C_of_natDegree_eq_zero hqNatDeg
        let hx := h_q_is_c.choose_spec
        set x := h_q_is_c.choose
        simp only [hx, aeval_C, map_eq_zero, ne_eq]
        -- ⊢ ¬x = 0
        by_contra h_x_eq_0
        simp only [h_x_eq_0, map_zero] at hx -- hx : q = 0, h_q_is_not_zero : q ≠ 0
        contradiction
      · have h_q_natDeg_ne_0 : q.natDegree ≠ 0 := by exact ne_zero_of_eq_one hqNatDeg
        have h_q_deg_ne_0 : q.degree ≠ 0 := by
          by_contra h_q_deg_is_0
          have h_q_natDeg_is_0 : q.natDegree = 0 := by exact
            (degree_eq_iff_natDegree_eq h_q_is_zero).mp h_q_deg_is_0
          contradiction
        have h_natDeg_q_is_1 : q.natDegree = 1 := by exact hqNatDeg
        have h_deg_q_is_1 : q.degree = 1 := by
          apply (degree_eq_iff_natDegree_eq h_q_is_zero).mpr
          exact hqNatDeg
        have h_q_is_not_unit : ¬IsUnit q := by
          by_contra h_q_is_unit
          rw [←is_unit_iff_deg_0] at h_q_is_unit
          contradiction
        let c := q.coeff 1
        let r := q.coeff 0
        have hc : c = q.leadingCoeff := by
          rw [Polynomial.leadingCoeff]
          exact congrArg q.toFinsupp.2 (id (Eq.symm hqNatDeg))
        have hc_ne_zero : c ≠ 0 := by
          rw [hc]
          by_contra h_c_eq_zero
          simp only [leadingCoeff_eq_zero] at h_c_eq_zero -- h_c_eq_zero : q = 0
          contradiction
        have hq_form : q = c • X + C r := by
          rw [Polynomial.eq_X_add_C_of_degree_eq_one (p:=q) (h:=by exact h_deg_q_is_1)]
          congr
          rw [hc]
          exact C_mul' q.leadingCoeff X
        -- ⊢ ¬(aeval (Z (k + 1))) q = 0
        simp only [hq_form, map_add, map_smul, aeval_X, aeval_C, ne_eq]
        -- ⊢ ¬Z k • Z (k + 1) + (algebraMap (ConcreteBTField k) (ConcreteBTField (k + 1))) x = 0
        have h_split_smul := split_smul_Z_eq_zero_x (k:=k+1) (h_pos:=by omega) (x:=c)
        rw [smul_Z_eq_zero_x (k:=k+1) (h_pos:=by omega) (x:=c)]
        have h_alg_map_x := algebraMap_succ_eq_zero_x (k:=k+1) (h_pos:=by omega) (x:=r)
        simp only [Nat.add_one_sub_one] at h_alg_map_x
        rw [h_alg_map_x, join_add_join]
        simp only [Nat.add_one_sub_one, _root_.add_zero, _root_.zero_add,
          ne_eq]
        -- ⊢ ¬join ⋯ c x = 0
        by_contra h_join_eq_zero
        rw [←zero_is_0] at h_join_eq_zero
        rw! [←join_zero_zero (k:=k+1) (h_k:=by omega)] at h_join_eq_zero
        rw [join_eq_join_iff] at h_join_eq_zero
        have h_c_eq_zero := h_join_eq_zero.1
        contradiction

lemma powerBasisSucc_dim (k : ℕ) :
    powerBasisSucc (k:=k).dim = 2 := by
  simp only [ConcreteBTField, powerBasisSucc]

def hli_level_diff_0 (l : ℕ) :
    letI instAlgebra:= ConcreteBTFieldAlgebra (l:=l) (r:=l) (h_le:=by omega)
  @Basis (Fin 1) (ConcreteBTField l) (ConcreteBTField l) _ _ instAlgebra.toModule:= by
  letI instAlgebra:= ConcreteBTFieldAlgebra (l:=l) (r:=l) (h_le:=by omega)
  letI instModule:= instAlgebra.toModule
  apply @Basis.mk (ι:=Fin 1) (R:=ConcreteBTField l) (M:=ConcreteBTField l)
    _ _ instAlgebra.toModule (v:=fun _ => 1)
  · -- This proof now works smoothly.
    rw [Fintype.linearIndependent_iff (R:=ConcreteBTField l)
      (v:=fun (_ : Fin 1) => (1 : ConcreteBTField l))]
    intro g hg j
    -- ⊢ g i = 0
    unfold instModule at *
    unfold instAlgebra at *
    rw [ConcreteBTFieldAlgebra_id (by omega)] at *
    have hj : j = 0 := by omega
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      smul_eq_mul, Finset.sum_singleton] at hg -- hg : g 0 = 0 ∨ 1 = 0
    have h_one_ne_zero : (1 : ConcreteBTField l) ≠ (0 : ConcreteBTField l) := by
      exact one_ne_zero
    simp only [ConcreteBTField, Fin.isValue] at hg
    rw [Subsingleton.elim j 0] -- j must be 0
    rw [hg.symm]
    exact Eq.symm (MulOneClass.mul_one (g 0))
  · rw [Set.range_const]
    have h : instAlgebra = Algebra.id (ConcreteBTField l) := by
      unfold instAlgebra
      rw [ConcreteBTFieldAlgebra_id (by omega)]
    rw! [h] -- convert to Algebra.id for clear goal
    rw [Ideal.submodule_span_eq]
    rw [Ideal.span_singleton_one]

def isScalarTower_succ_right (l r : ℕ) (h_le : l ≤ r) :=
    instAlgebraTowerConcreteBTF.toIsScalarTower (i:=l) (j:=r) (k:=r+1)
    (h1:=by omega) (h2:=by omega)
/--
The multilinear basis for `ConcreteBTField τ` over `ConcreteBTField k`
is the set of multilinear monomials in the tower generators `Z(k + 1), ..., Z(τ)`.
This is done via scalar tower multiplication of power basis across adjacent levels.
-/
def multilinearBasis (l r : ℕ) (h_le : l ≤ r) :
    letI instAlgebra := ConcreteBTFieldAlgebra (h_le:=h_le)
    Basis (Fin (2 ^ (r - l))) (ConcreteBTField l) (ConcreteBTField r) := by
  letI instAlgebra := ConcreteBTFieldAlgebra (h_le:=h_le)
  if h_r_sub_l : r - l = 0 then -- Avoid using `match` to avoid `Eq.rec` when reasoning recursively
    have h_l_eq_r : l = r := by omega
    subst h_l_eq_r
    have h_res := hli_level_diff_0 (l:=l)
    rw [←Nat.pow_zero 2, ←Nat.sub_self l] at h_res
    exact h_res
  else
    have h_l_lt_r : l < r := by omega
    set n' := r - l - 1 with h_n'
    set r1 := l + n' with h_r1
    have h_r_sub_l : r - l = n' + 1 := by omega
    have h_r1_sub_l : r1 - l = n' := by omega
    have h_r : r = r1 + 1 := by omega
    letI instAlgebraPrev : Algebra (ConcreteBTField l) (ConcreteBTField (r1)) :=
      ConcreteBTFieldAlgebra (l:=l) (r:=r1) (h_le:=by omega)
    set prevMultilinearBasis := multilinearBasis (l:=l) (r:=r1) (h_le:=by omega)
    rw! [h_r1_sub_l] at prevMultilinearBasis
    letI instAlgebra : Algebra (ConcreteBTField l) (ConcreteBTField (r1 + 1)) :=
      ConcreteBTFieldAlgebra (l:=l) (r:=r1 + 1) (h_le:=by omega)
    rw! [h_r_sub_l]
    apply Basis.reindex (e:=revFinProdFinEquiv (m:=2 ^ (n')) (n:=2)
      (h_m:=by exact Nat.two_pow_pos n'))
    -- ⊢ Basis (Fin 2 × Fin (2 ^ n')) (ConcreteBTField l) (ConcreteBTField (r))
    have h_eq : l + (n' + 1) = (r1) + 1 := by rw [←Nat.add_assoc]
    letI instAlgebraSucc : Algebra (ConcreteBTField (r1)) (ConcreteBTField (r1 + 1)) := by
      exact algebra_adjacent_tower (r1)
    letI instModuleSucc : Module (ConcreteBTField l) (ConcreteBTField (r1 + 1)) := by
      exact instAlgebra.toModule
    letI : IsScalarTower (ConcreteBTField l) (ConcreteBTField (r1))
      (ConcreteBTField (r1 + 1)) := by
      exact isScalarTower_succ_right (l:=l) (r:=r1) (h_le:=by omega)
    have res := Basis.smulTower (ι:=Fin (2 ^ n')) (ι':=Fin (2)) (R:=ConcreteBTField l)
      (S:=ConcreteBTField (r1)) (A:=ConcreteBTField (r1 + 1))
      (b:=by
        convert prevMultilinearBasis;
      ) (c:=by
        convert (powerBasisSucc (r1)).basis
      )
    convert res
    -- Basis are equal under the same @ConcreteBTFieldAlgebra
    -- ⊢ Basis (Fin (2 ^ n') × Fin 2) (ConcreteBTField l) (ConcreteBTField r)
    -- = Basis (Fin (2 ^ n') × Fin 2) (ConcreteBTField l) (ConcreteBTField (r1 + 1))
    unfold instModuleSucc -- Module used in rhs
    rw! [h_r]
    rfl

@[simp]
theorem PowerBasis.dim_of_eq_rec
    (r1 r : ℕ)
    (h_r : r = r1 + 1)
    (b : PowerBasis (ConcreteBTField r1) (ConcreteBTField (r1 + 1))) :
    letI instAlgebra : Algebra (ConcreteBTField r1) (ConcreteBTField r) :=
      ConcreteBTFieldAlgebra (l:=r1) (r:=r) (h_le:=by omega)
    ((Eq.rec (motive:=fun (x : ℕ) (_ : r1 + 1 = x) => by
      letI instAlgebraCur : Algebra (ConcreteBTField r1) (ConcreteBTField x) :=
        ConcreteBTFieldAlgebra (l:=r1) (r:=x) (h_le:=by omega)
      exact PowerBasis (ConcreteBTField r1) (ConcreteBTField x)) (refl:=b) (t:=h_r.symm)) :
        PowerBasis (ConcreteBTField r1) (ConcreteBTField r)).dim
    = b.dim := by
  subst h_r
  rfl

@[simp]
theorem PowerBasis.cast_basis_succ_of_eq_rec_apply
    (r1 r : ℕ) (h_r : r = r1 + 1)
    (k : Fin 2) :
    letI instAlgebra : Algebra (ConcreteBTField r1) (ConcreteBTField r) :=
      ConcreteBTFieldAlgebra (l:=r1) (r:=r) (h_le:=by omega)
    letI instAlgebraSucc : Algebra (ConcreteBTField (r1 + 1)) (ConcreteBTField (r)) :=
      ConcreteBTFieldAlgebra (l:=r1 + 1) (r:=r) (h_le:=by omega)
    let b : PowerBasis (ConcreteBTField r1) (ConcreteBTField (r1 + 1)) :=
      powerBasisSucc (k:=r1)
    let bCast : PowerBasis (ConcreteBTField r1) (ConcreteBTField r) := Eq.rec (motive:=
      fun (x : ℕ) (_ : r1 + 1 = x) => by
        letI instAlgebraCur : Algebra (ConcreteBTField r1) (ConcreteBTField x) :=
          ConcreteBTFieldAlgebra (l:=r1) (r:=x) (h_le:=by omega)
        exact PowerBasis (ConcreteBTField r1) (ConcreteBTField x)) (refl:=b) (t:=h_r.symm)
    have h_pb_dim : b.dim = 2 := by
      exact powerBasisSucc_dim r1

    have h_pb'_dim : bCast.dim = 2 := by
      dsimp [bCast]
      rw [PowerBasis.dim_of_eq_rec (r1:=r1) (r:=r) (h_r:=h_r) (b:=b)]
      exact h_pb_dim

    have h_pb_type_eq : Basis (Fin bCast.dim) (ConcreteBTField r1) (ConcreteBTField r) =
      Basis (Fin 2) (ConcreteBTField r1) (ConcreteBTField r) := by
      congr

   -- The `cast` needs a proof that `bCast.dim = 2`. We construct it here.
    let left : Basis (Fin 2) (ConcreteBTField r1) (ConcreteBTField r) :=
      cast (by exact h_pb_type_eq) bCast.basis
    let right := (algebraMap (ConcreteBTField (r1 + 1)) (ConcreteBTField r))
      (b.basis (Fin.cast h_pb_dim.symm k))
    left k = right := by
  -- The proof of the theorem itself remains simple.
  subst h_r
  simp only [ConcreteBTFieldAlgebra_id,
    Algebra.algebraMap_self, PowerBasis.coe_basis, Fin.val_cast, RingHom.id_apply]
  rw [Basis_cast_index_apply (h_eq:=by
    exact powerBasisSucc_dim r1) (h_le:=by omega)]
  simp only [PowerBasis.coe_basis, Fin.val_cast]

@[simp]
theorem coe_basis_apply {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    (pb : PowerBasis R S) (i : Fin pb.dim) : ⇑pb.basis i = pb.gen ^ (i : ℕ) :=
  pb.basis_eq_pow i

/-- When two indices are equal, the tower algebra maps send the respective 𝕏 to the same element. -/
lemma algebraMap_𝕏_eq_of_index_eq (r k m : ℕ) (h_k_le : k + 1 ≤ r) (h_m_le : m + 1 ≤ r)
    (h_eq : k = m) :
    letI := ConcreteBTFieldAlgebra (l := k + 1) (r := r) (h_le := h_k_le)
    letI := ConcreteBTFieldAlgebra (l := m + 1) (r := r) (h_le := h_m_le)
    (Algebra.algebraMap (𝕏 k) : ConcreteBTField r) =
      (Algebra.algebraMap (𝕏 m) : ConcreteBTField r) := by
  subst h_eq
  rfl

/-!
The basis element at index `j` is the product of the tower generators at
the ON bits in binary representation of `j`.
-/
theorem multilinearBasis_apply (r : ℕ) : ∀ l : ℕ, (h_le : l ≤ r) → ∀ (j : Fin (2 ^ (r - l))),
    multilinearBasis (l:=l) (r:=r) (h_le:=h_le) j =
    (Finset.univ : Finset (Fin (r - l))).prod (fun i =>
      (ConcreteBTFieldAlgebra (l:=l + i + 1) (r:=r) (h_le:=by omega)).algebraMap (
        (𝕏 (l + i)) ^ (Nat.getBit i j))) := by
  induction r with
  | zero => -- Fin (2 ^ 0) = Fin 1, so j = 0
    intro l h_l_le_0 j
    simp only [zero_tsub, pow_zero] at j
    have h_l_eq_r : l = 0 := by omega
    subst h_l_eq_r
    simp only [Nat.sub_zero, Nat.pow_zero, Finset.univ_eq_empty, 𝕏, Z, _root_.zero_add,
      Fin.val_eq_zero, map_pow, Finset.prod_empty]
    have hj_eq_0 : j = 0 := by exact Fin.eq_of_val_eq (by omega)
    rw! [hj_eq_0]
    rw [multilinearBasis]
    simp only [tsub_self, ↓reduceDIte, Nat.sub_zero, Nat.pow_zero, Fin.isValue]
    rw [hli_level_diff_0]
    simp only [eq_mp_eq_cast, cast_eq, Fin.isValue, Basis.coe_mk]
  | succ r1 ih_r1 =>
    set r := r1 + 1 with hr
    intro l h_l_le_r j
    haveI instAlgebraR : Algebra (ConcreteBTField r) (ConcreteBTField r) :=
      ConcreteBTFieldAlgebra (l:=r) (r:=r) (h_le:=by omega)
    if h_r_sub_l : r - l = 0 then
      rw [multilinearBasis]
      have h_l_eq_r : l = r := by omega
      subst h_l_eq_r
      simp only [tsub_self, ↓reduceDIte, Nat.pow_zero,
        hli_level_diff_0, eq_mp_eq_cast, cast_eq]
      have h1 : 1 = 2 ^ (r - r) := by rw [Nat.sub_self, Nat.pow_zero];
      have h_r_sub_r : r - r = 0 := by omega
      rw [←Fin.prod_congr' (b:=r - r) (a:=0) (h:=by omega), Fin.prod_univ_zero]
      rw [Basis_cast_index_apply (h_eq:=by omega) (h_le:=by omega)]
      simp only [Basis.coe_mk]
    else
      rw [multilinearBasis]
      -- key to remove Eq.rec : dif_neg h_r_sub_l
      simp only [Nat.pow_zero, eq_mp_eq_cast, cast_eq,
        eq_mpr_eq_cast, dif_neg h_r_sub_l]
      have h2 : 2 ^ (r - l - 1) * 2 = 2 ^ (r - l) := by
        rw [←Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
      rw [Basis_cast_index_apply (h_eq:=by omega) (h_le:=by omega)]
      simp only [Basis.coe_reindex, Function.comp_apply,
        revFinProdFinEquiv_symm_apply]
      rw [Basis_cast_dest_apply (h_eq:=by omega)
        (h_le1:=by omega) (h_le2:=by omega)]

      set prevDiff := r - l - 1 with h_prevDiff
      have h_r_sub_l : r - l = prevDiff + 1 := by omega
      have h_r1_sub_l : r1 - l = prevDiff := by omega
      have h_r1_eq_l_plus_prevDiff : r1 = l + prevDiff := by omega
      have h_r : r = r1 + 1 := by omega
      have h1 : l + (r - l - 1) = r1 := by omega
      letI instAlgebraPrev : Algebra (ConcreteBTField l) (ConcreteBTField (r1)) :=
        ConcreteBTFieldAlgebra (l:=l) (r:=r1) (h_le:=by omega)
      set prevMultilinearBasis :=
        multilinearBasis (l:=l) (r:=r1) (h_le:=by omega) with h_prevMultilinearBasis
      rw! [h_r1_sub_l] at prevMultilinearBasis
      letI instAlgebra : Algebra (ConcreteBTField l) (ConcreteBTField (r1 + 1)) :=
        ConcreteBTFieldAlgebra (l:=l) (r:=r1 + 1) (h_le:=by omega)
      rw! (castMode:=.all) [h1]

      letI instAlgebraSucc : Algebra (ConcreteBTField (r1)) (ConcreteBTField (r1 + 1)) := by
        exact algebra_adjacent_tower (r1)
      letI instModuleSucc : Module (ConcreteBTField l) (ConcreteBTField (r1 + 1)) := by
        exact instAlgebra.toModule

      letI : IsScalarTower (ConcreteBTField l) (ConcreteBTField (r1))
        (ConcreteBTField (r1 + 1)) := by
        exact isScalarTower_succ_right (l:=l) (r:=r1) (h_le:=by omega)
      rw [Basis.smulTower_apply]
      rw [Algebra.smul_def]
      rw! [cast_mul (m:=r1 + 1) (n:=r) (h_eq:=by omega)]
      -- simp_rw [h_.r]
      rw [cast_eq, cast_eq]

      letI instAlgebra2 : Algebra (ConcreteBTField r1) (ConcreteBTField r) :=
        ConcreteBTFieldAlgebra (l:=r1) (r:=r) (h_le:=by omega)
      set b := (powerBasisSucc r1) with hb
      rw! (castMode:=.all) [←hb]
      have h : (2 ^ (r1 - l)) = (2 ^ (r - l - 1)) := by
        rw [h_r]
        rw [Nat.sub_right_comm, Nat.add_sub_cancel r1 1]
      rw [Basis_cast_index_apply (h_eq:=h) (h_le:=by omega)]
      simp only [leftDivNat, Fin.val_cast]

      set indexLeft : Fin 2 := ⟨j.val / 2 ^ (r - l - 1), by
        change j.val / 2 ^ (r - l - 1) < 2 ^ 1
        apply div_two_pow_lt_two_pow (x:=j.val) (i:=1) (j:=r - l - 1) (h_x_lt_2_pow_i:=by
          rw [Nat.add_comm, Nat.sub_add_cancel (by omega)];
          exact j.isLt
        )
      ⟩
      have h_cast_basis_succ_of_eq_rec_apply :=
        PowerBasis.cast_basis_succ_of_eq_rec_apply (r1:=r1) (r:=r) (h_r:=h_r) (k:=indexLeft)
      unfold algebra_adjacent_tower
      rw! (castMode:=.all) [←h_r]
      conv_lhs =>
        arg 2
        erw [h_cast_basis_succ_of_eq_rec_apply]

      unfold indexLeft
      conv_lhs =>
        simp only [Fin.cast_mk, PowerBasis.coe_basis];
        rw [powerBasisSucc_gen, ←𝕏]
        rw [ih_r1 (l:=l) (h_le:=by omega)]
        rw [Fin.cast_val_eq_val (h_eq:=by omega)]

      conv_rhs =>
        rw [←Fin.prod_congr' (b:=r - l) (a:=prevDiff + 1) (h:=by omega)]
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.val_cast, Fin.val_castSucc, Fin.val_last]

      simp_rw [algebraMap.coe_pow]
      simp_rw [algebraMap.coe_prod]
      unfold Algebra.cast
      rw! (castMode:=.all) [←algebraMap]
      conv_lhs =>
        rw [←Fin.prod_congr' (b:=r1 - l) (a:=prevDiff) (h:=by omega)]
        simp only [Fin.val_cast]
      simp_rw [algebraMap, instAlgebraSucc, algebra_adjacent_tower]
      rw [RingHom.map_pow]
      simp_rw [←ConcreteBTFieldAlgebra_apply_assoc]
      ------------------ Equality of bit-based powers of generators -----------------
      have hfinProd_msb := bit_revFinProdFinEquiv_symm_2_pow_succ (n:=prevDiff)
        (i:=⟨prevDiff, by omega⟩) (j:=⟨j, by omega⟩)
      simp only [lt_self_iff_false, ↓reduceIte, revFinProdFinEquiv_symm_apply] at hfinProd_msb
      conv_rhs => simp only [hfinProd_msb, leftDivNat]
      --- Inner-prod term: prove equality of the two factors
      refine congr_arg₂ (· * ·) ?_ ?_
      · congr 1
        funext i
        have hfinProd_lsb := bit_revFinProdFinEquiv_symm_2_pow_succ
          (n:=prevDiff) (i:=⟨i, by omega⟩)
          (j:=⟨j, by omega⟩)
        simp only [Fin.is_lt, ↓reduceIte, revFinProdFinEquiv_symm_apply] at hfinProd_lsb
        rw [hfinProd_lsb]
        rfl
      · have h_exp_eq : (↑j : ℕ) / 2 ^ (r - l - 1) = (↑j : ℕ) / 2 ^ prevDiff :=
          congr_arg (fun d => (↑j : ℕ) / 2 ^ d) h_prevDiff.symm
        refine congr_arg₂ (· ^ ·)
            (algebraMap_𝕏_eq_of_index_eq r r1 (l + prevDiff) (by omega) (by omega)
              h_r1_eq_l_plus_prevDiff)
            h_exp_eq

end ConcreteMultilinearBasis

end ConcreteBinaryTower
