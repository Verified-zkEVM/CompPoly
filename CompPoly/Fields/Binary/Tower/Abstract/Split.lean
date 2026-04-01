/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import CompPoly.Fields.Binary.Tower.Abstract.Algebra

/-!
# Abstract Binary Tower Split

Splitting and recombination lemmas for abstract binary tower extensions.
-/

namespace BinaryTower

noncomputable section MultilinearBasis

open Polynomial
open AdjoinRoot
open Module

@[simp]
theorem BTField.Basis_cast_index_eq (i j k n : ℕ) (h_le : k ≤ n) (h_eq : i = j) :
    letI instAlgebra : Algebra (BTField k) (BTField n) :=
      binaryAlgebraTower (l:=k) (r:=n) (h_le:=h_le)
    letI : Module (BTField k) (BTField n) := instAlgebra.toModule
    (Basis (Fin (i)) (BTField k) (BTField n)) = (Basis (Fin (j)) (BTField k) (BTField n)) := by
  subst h_eq
  rfl

theorem BTField.Basis_cast_dest_eq {ι : Type*} (k n m : ℕ) (h_k_le_n : k ≤ n)
    (h_k_le_m : k ≤ m) (h_eq : m = n) :
  letI instLeftAlgebra := binaryAlgebraTower (l:=k) (r:=m) (h_le:=h_k_le_m)
  letI instRightAlgebra := binaryAlgebraTower (l:=k) (r:=n) (h_le:=h_k_le_n)
  @Basis ι (BTField k) (BTField m) _ _ instLeftAlgebra.toModule =
  @Basis ι (BTField k) (BTField n) _ _ instRightAlgebra.toModule := by
  subst h_eq
  rfl

theorem BTField.PowerBasis_cast_dest_eq (k n m : ℕ) (h_k_le_n : k ≤ n)
    (h_k_le_m : k ≤ m) (h_eq : m = n) :
  letI instLeftAlgebra := binaryAlgebraTower (l:=k) (r:=m) (h_le:=h_k_le_m)
  letI instRightAlgebra := binaryAlgebraTower (l:=k) (r:=n) (h_le:=h_k_le_n)
  @PowerBasis (BTField k) (BTField m) _ _ instLeftAlgebra =
  @PowerBasis (BTField k) (BTField n) _ _ instRightAlgebra := by
  subst h_eq
  rfl
/-!
The following two theorems are used to cast the basis of `BTField α` to `BTField β`
via changing in index type : `Fin (i)` to `Fin (j)` when `α ≤ β`.
-/
@[simp]
theorem BTField.Basis_cast_index_apply {α β i j : ℕ} {k : Fin j} (h_le : α ≤ β) (h_eq : i = j)
    {b : @Basis (Fin (i)) (BTField α) (BTField β) _ _
    (@binaryAlgebraTower (l := α) (r := β) (h_le := h_le)).toModule} :
  let castBasis : @Basis (Fin j) (BTField α) (BTField β) _ _
    (@binaryAlgebraTower (l:=α) (r:=β) (h_le:=h_le)).toModule :=
    cast (by exact BTField.Basis_cast_index_eq i j α β h_le h_eq) b
  (castBasis k) = b (Fin.cast (h_eq.symm) k) := by
  subst h_eq
  rfl

@[simp]
theorem BTField.Basis_cast_dest_apply {ι : Type*} (α β γ : ℕ) (h_le1 : α ≤ β) (h_le2 : α ≤ γ)
    (h_eq : β = γ) {k : ι} (b : @Basis ι (BTField α) (BTField β) _ _
    (@binaryAlgebraTower (l := α) (r := β) (h_le := h_le1)).toModule) :
    let castBasis : @Basis ι (BTField α) (BTField γ) _ _
      (@binaryAlgebraTower (l := α) (r := γ) (h_le := h_le2)).toModule :=
      cast (by
        exact Basis_cast_dest_eq α γ β h_le2 h_le1 h_eq
      ) b
    (castBasis k) = cast (by exact BTField.cast_BTField_eq β γ h_eq) (b k) := by
  subst h_eq
  rfl

/-!
The power basis for `BTField (k+1)` over `BTField k` is {1, Z (k+1)}
-/
def powerBasisSucc (k : ℕ) :
    PowerBasis (BTField k) (BTField (k+1)) := by
  let pb : PowerBasis (BTField k) (AdjoinRoot (poly k)) :=
    AdjoinRoot.powerBasis (hf:=by exact poly_ne_zero k)
  -- NOTE : pb.gen is definitionally equal to AdjoinRoot.root (poly k)
  -- See `algebra_adjacent_tower_eq_AdjoinRoot_algebra` for the algebra instance equality.
  have h_eq : AdjoinRoot (poly k) = BTField (k+1) := BTField_succ_eq_adjoinRoot k
  -- ⊢ PowerBasis (BTField k) (BTField (k + 1))
  apply pb.map (e:=BTField_succ_alg_equiv_adjoinRoot k)

lemma powerBasisSucc_gen (k : ℕ) :
    (powerBasisSucc k).gen = (Z (k+1)) := by
  -- Z (k+1) is generator of BTField (k+1) over (BTField k)
  -- Correctness : Both sides are definitionally equal to AdjoinRoot.root (poly k)
  rfl

lemma powerBasisSucc_dim (k : ℕ) :
    powerBasisSucc (k:=k).dim = 2 := by
  simp only [BTField, CommRing, BTFieldIsField, powerBasisSucc, poly, PowerBasis.map_dim,
    powerBasis_dim]
  exact natDegree_definingPoly (Z k)

def join_via_add_smul {k : ℕ} (h_pos : k > 0) (hi_btf lo_btf : BTField (k - 1)) :
    BTField k := by
  letI instAlgebra := binaryAlgebraTower (l:=k-1) (r:=k) (h_le:=by omega)
  exact hi_btf • Z k + (algebraMap (BTField (k - 1)) (BTField k) lo_btf)

scoped[BinaryTower] notation "⋘" hi ", " lo "⋙" => join_via_add_smul (h_pos:=by omega) hi lo

lemma join_via_add_smul_zero {k : ℕ} (h_pos : k > 0) :
    ⋘ 0, 0 ⋙ = 0 := by
  unfold join_via_add_smul
  simp only [map_zero, add_zero]
  letI instAlgebra := binaryAlgebraTower (l:=k-1) (r:=k) (h_le:=by omega)
  rw [Algebra.smul_def', map_zero, zero_mul]

lemma join_via_add_smul_one_zero_eq_Z {k : ℕ} (h_pos : k > 0) :
    ⋘ 1, 0 ⋙ = Z k := by
  unfold join_via_add_smul
  letI instAlgebra := binaryAlgebraTower (l:=k-1) (r:=k) (h_le:=by omega)
  rw [Algebra.smul_def', map_one, map_zero, one_mul, add_zero]

lemma join_via_add_smul_one {k : ℕ} (h_pos : k > 0) :
    ⋘ 0, 1 ⋙ = 1 := by
  unfold join_via_add_smul
  letI instAlgebra := binaryAlgebraTower (l:=k-1) (r:=k) (h_le:=by omega)
  rw [Algebra.smul_def', map_zero, map_one, zero_mul, zero_add]

theorem sum_join_via_add_smul (k : ℕ) (h_pos : k > 0) (a₁ a₀ b₁ b₀ : BTField (k - 1)) :
    ⋘ a₁, a₀ ⋙ + ⋘ b₁, b₀ ⋙ = ⋘ a₁ + b₁, a₀ + b₀ ⋙ := by
  letI instAlgebra := binaryAlgebraTower (l:=k-1) (r:=k) (h_le:=by omega)
  unfold join_via_add_smul
  simp only [map_add]
  rw [add_smul a₁ b₁ (Z k)]
  abel_nf

/--
(a₁ • Z k + a₀) * (b₁ • Z k + b₀)
= a₁ * b₁ • (Z k)^2 + (a₁ * b₀ + a₀ * b₁) • Z k + a₀ * b₀
= a₁ * b₁ • (Z (k-1) * Z k + 1) + (a₁ * b₀ + a₀ * b₁) • Z k + a₀ * b₀
= [a₁ * b₁ * Z (k - 1) + a₁ * b₀ + a₀ * b₁] * (Z k) + (a₀ * b₀ + a₁ * b₁)
-/
theorem mul_join_via_add_smul (k : ℕ) (h_pos : k > 0) (a₁ a₀ b₁ b₀ : BTField (k - 1)) :
    ⋘ a₁, a₀ ⋙ * ⋘ b₁, b₀ ⋙ = ⋘ a₁ * b₁ * Z (k - 1) + a₁ * b₀ + a₀ * b₁, a₀ * b₀ + a₁ * b₁ ⋙ := by
  letI instAlgebra := binaryAlgebraTower (l:=k-1) (r:=k) (h_le:=by omega)
  conv_lhs =>
    unfold join_via_add_smul
    rw [mul_add, add_mul, add_mul, ←map_mul]
    rw [mul_comm (a₁ • Z k) ((algebraMap (BTField (k - 1)) (BTField k)) b₀)]

  have h_a₁_b₀_Z_k : (algebraMap (BTField (k - 1)) (BTField k)) b₀ * a₁ • Z k
    = (a₁ * b₀) • Z k := by
    rw [Algebra.smul_def', ←algebraMap, ←mul_assoc, ←map_mul, ←Algebra.smul_def, mul_comm]
  have h_a₀_b₁_Z_k :  (algebraMap (BTField (k - 1)) (BTField k)) a₀ * b₁ • Z k
    = (a₀ * b₁) • Z k := by
    rw [Algebra.smul_def', ←algebraMap, ←mul_assoc, ←map_mul, ←Algebra.smul_def, mul_comm]
  have h_Z_k_pow_2 : (Z k) ^ 2 = Z (k - 1) • Z k + 1 := by
    rw [sumZeroIffEq (x:=(Z k)^2) (y:=Z (k - 1) • Z k + 1).mp]
    rw [←add_assoc]
    rw [Algebra.smul_def', mul_comm]
    have h := eval_poly_at_root (k - 1)
    rw! (castMode:=.all) [Nat.sub_one_add_one (by omega)] at h
    simp only [eq_mp_eq_cast] at h
    convert h
    rw [Algebra.algebraMap]
    conv_lhs =>
      simp only [instAlgebra];
      change (towerAlgebraMap (l:=k-1) (r:=k) (h_le:=by omega)) (Z (k - 1))
    have h_towerMap_succ := towerAlgebraMap_succ_1 (k:=k-1)
    rw! (castMode:=.all) [Nat.sub_one_add_one (by omega)] at h_towerMap_succ
    rw [h_towerMap_succ]
    rw [eqRec_eq_cast, canonicalEmbedding]
    have h := BTField.RingHom_cast_dest_AdjoinRoot_apply
      (f:=AdjoinRoot.of (poly (k-1))) (x:=Z (k-1))
    rw! (castMode:=.all) [Nat.sub_one_add_one (by omega)] at h
    exact h
  have h_a₁_Z_k_b₁_Z_k : a₁ • Z k * b₁ • Z k
    = (a₁ * b₁ * Z (k - 1)) • Z k + (algebraMap (BTField (k - 1)) (BTField k)) (a₁ * b₁) := by
    conv_lhs =>
      rw [Algebra.smul_def, Algebra.smul_def]
      rw [mul_comm ((algebraMap (BTField (k - 1)) (BTField k)) b₁) (Z k)]
      rw [←mul_assoc, mul_assoc ((algebraMap (BTField (k - 1)) (BTField k)) a₁) (Z k) (Z k)]
      rw [←pow_two, h_Z_k_pow_2, Algebra.smul_def, mul_add, add_mul, mul_one]
      rw [←map_mul]
      rw [mul_comm, ←mul_assoc, ←map_mul, ←mul_assoc, ←map_mul, ←Algebra.smul_def, mul_comm b₁ a₁]
  conv_lhs =>
    rw [h_a₁_b₀_Z_k, h_a₀_b₁_Z_k, h_a₁_Z_k_b₁_Z_k]
    rw [add_comm, add_comm ((a₁ * b₀) • Z k), add_assoc, add_comm]
    rw [←add_assoc, ←add_assoc, ←add_smul (x:=Z k)]
    rw [add_assoc (c:=(a₀ * b₁) • Z k), add_comm (b:=(a₀ * b₁) • Z k), ←add_assoc, ←add_smul]
    rw [add_assoc, ←map_add]
    rw [add_comm (a₁ * b₀), add_comm (a₁ * b₁)]
  rfl

theorem unique_linear_decomposition_succ (k : ℕ) :
    ∀ (x : BTField (k+1)), ∃! (p : BTField k × BTField k),
    x = ⋘ p.1, p.2 ⋙ := by
  intro x
  -- First, we have `AdjoinRoot.powerBasis'` of dim 2 (`powerBasis'_dim`)
  -- Second, we represent `x` as a linear combination of the
  -- basis elements : `x = a0 + a1 * Z (k+1)`, this combination is unique
  -- Last, we prove the equality : `•` => `*`, `lo_btf` and `hi_btf` => `algebraMap`
  unfold join_via_add_smul
  simp only [Nat.add_one_sub_one]
  simp only [Algebra.smul_def]
  have unique_linear_combination : ∀ (c1 : AdjoinRoot (poly k)),
    ∃! (p : BTField k × BTField k), c1 = (of (poly k)) p.1 * root (poly k) + (of (poly k)) p.2 := by
    apply unique_linear_form_of_elements_in_adjoined_commring
    · apply BinaryTower.poly_natDegree_eq_2
    · apply BinaryTower.polyMonic
  let px := unique_linear_combination (c1:=x)
  simp_rw [algebraMap_adjacent_tower_succ_eq_Adjoin_of k]
  convert px

def split (k : ℕ) (h_k : k > 0) (x : BTField k) : BTField (k-1) × BTField (k-1) := by
  have h_eq : k - 1 + 1 = k := by omega
  have h_BTField_eq : BTField k = BTField (k-1+1) := by
    apply BTField.cast_BTField_eq
    exact h_eq.symm
  have h_unique := unique_linear_decomposition_succ (k:=(k-1)) (x:=(Eq.mp (h:=h_BTField_eq) x))
  exact h_unique.choose

/-! Proofs that `split` is the inverse of `join_via_add_smul`
-/
theorem eq_join_via_add_smul_eq_iff_split (k : ℕ) (h_pos : k > 0)
    (x : BTField k) (hi_btf lo_btf : BTField (k - 1)) :
    x = ⋘ hi_btf, lo_btf ⋙ ↔
  split (k:=k) (h_k:=h_pos) x = (hi_btf, lo_btf) := by
  have h_k_sub_1_add_1_eq_k : k - 1 + 1 = k := by omega
  have h_BTField_eq := BTField.cast_BTField_eq (k:=k) (m:=k-1+1) (h_eq:=by omega)
  set p := unique_linear_decomposition_succ (k:=(k-1)) (x:=(Eq.mp (h:=h_BTField_eq) x)) with hp
  -- -- ⊢ x = join_via_add_smul k h_pos hi lo
  have h_p_satisfy := p.choose_spec
  set xPair := p.choose
  constructor
  · intro h_x_eq_join
    -- Due to `unique_linear_decomposition_succ`, there must be exactly one pair
    -- `(hi, lo)` that satisfies the equation : `x = join_via_add_smul k h_pos hi lo`
    -- Now we prove `⟨hi_btf, lo_btf⟩` is `Exists.choose` of `unique_linear_decomposition_succ`
    -- which is actually same as the definition of the `split` function
    have h_must_eq := h_p_satisfy.2 (⟨hi_btf, lo_btf⟩)
    simp only [eq_mp_eq_cast] at h_must_eq
    have h_hibtf_lobtf_eq_xPair := h_must_eq (by
      rw! (castMode := .all) [h_k_sub_1_add_1_eq_k]
      simp only [cast_eq]
      convert h_x_eq_join
      · rw [eqRec_eq_cast]; rfl
      · rw [eqRec_eq_cast]; rfl
    )
    have h_split_eq_xPair : split k h_pos x = xPair := by rfl
    rw [h_split_eq_xPair, h_hibtf_lobtf_eq_xPair.symm]
  · intro h_split_eq
    unfold split at h_split_eq
    have h_hibtf_lobtf_eq_xPair : ⟨hi_btf, lo_btf⟩ = xPair := by rw [←h_split_eq]
    have h_xPair_satisfy_join_via_add_smul := h_p_satisfy.1
    rw [←h_hibtf_lobtf_eq_xPair] at h_xPair_satisfy_join_via_add_smul
    rw [eq_mp_eq_cast] at h_xPair_satisfy_join_via_add_smul
    rw! (castMode := .all) [h_k_sub_1_add_1_eq_k] at h_xPair_satisfy_join_via_add_smul
    simp only [cast_eq] at h_xPair_satisfy_join_via_add_smul
    convert h_xPair_satisfy_join_via_add_smul
    · rw [eqRec_eq_cast]; rfl
    · rw [eqRec_eq_cast]; rfl

lemma split_join_via_add_smul_eq_iff_split (k : ℕ) (h_pos : k > 0)
    (hi_btf lo_btf : BTField (k - 1)) :
    split (k:=k) (h_k:=h_pos) (⋘ hi_btf, lo_btf ⋙) = (hi_btf, lo_btf) := by
  exact (eq_join_via_add_smul_eq_iff_split k h_pos (⋘ hi_btf, lo_btf ⋙) hi_btf lo_btf).mp rfl

lemma join_eq_join_iff (k : ℕ) (h_pos : k > 0) (hi₁ hi₀ lo₁ lo₀ : BTField (k - 1)) :
    ⋘ hi₁, lo₁ ⋙ = ⋘ hi₀, lo₀ ⋙ ↔
  hi₁ = hi₀ ∧ lo₁ = lo₀ := by
  constructor
  · intro h_join_eq
    rw [eq_join_via_add_smul_eq_iff_split] at h_join_eq
    rw [split_join_via_add_smul_eq_iff_split] at h_join_eq
    simp only [Prod.mk.injEq] at h_join_eq
    exact h_join_eq
  · intro h_hi_eq_lo_eq
    simp only [h_hi_eq_lo_eq]

/--
An element `x` lifted from the base field `BTField (k-1)` has `(0, x)` as its
split representation in `BTField k`.
-/
lemma split_algebraMap_eq_zero_x {k : ℕ} (h_pos : k > 0) (x : BTField (k - 1)) :
    letI instAlgebra := binaryAlgebraTower (l:=k-1) (r:=k) (h_le:=by omega)
  split (k:=k) (h_k:=h_pos) (algebraMap (BTField (k - 1)) (BTField k) x) = (0, x) := by
  -- this one is long because of the `cast` stuff, but it should be quite straightforward
  -- via def of `canonicalEmbedding` and `eq_join_via_add_smul_eq_iff_split`
  letI instAlgebra := binaryAlgebraTower (l:=k-1) (r:=k) (h_le:=by omega)
  set mappedVal := algebraMap (BTField (k - 1)) (BTField k) x
  -- ⊢ split k h_pos mappedVal = (0, x)
  have h := eq_join_via_add_smul_eq_iff_split (k:=k) (h_pos:=by omega)
    (x:=mappedVal) (hi_btf:=0) (lo_btf:=x)
  apply h.mp
  -- ⊢ mappedVal = join_via_add_smul h_pos 0 x
  unfold mappedVal
  rw [algebraMap, Algebra.algebraMap]
  unfold instAlgebra binaryAlgebraTower
  rw [AlgebraTower.toAlgebra, AlgebraTower.algebraMap, instAlgebraTowerNatBTField]
  simp only
  have h_concrete_embedding_succ_1 := towerAlgebraMap_succ_1 (k:=k-1)
  rw! (castMode:=.all) [Nat.sub_one_add_one (by omega)] at h_concrete_embedding_succ_1
  rw! (castMode:=.all) [h_concrete_embedding_succ_1]
  rw [eqRec_eq_cast]
  rw [BTField.RingHom_cast_dest_apply (f:=canonicalEmbedding (k - 1))
    (x:=x) (h_eq:=by omega)]
  -- ⊢ cast ⋯ ((canonicalEmbedding (k - 1)) x) = join_via_add_smul h_pos 0 x
  have h_k_sub_1_add_1 : k - 1 + 1 = k := by omega
  rw! (castMode:=.all) [h_k_sub_1_add_1]
  rw [eqRec_eq_cast, cast_eq]
  unfold join_via_add_smul
  -- letI instAlgebra := binaryAlgebraTower (l:=k-1) (r:=k) (h_le:=by omega)
  rw [Algebra.smul_def', map_zero, zero_mul, zero_add]
  have h := algebraMap_adjacent_tower_def (l:=k-1)
  rw! (castMode:=.all) [Nat.sub_one_add_one (by omega)] at h
  simp only [algebra_adjacent_tower, eqRec_eq_cast] at h
  rw [algebraMap, Algebra.algebraMap] at ⊢ h
  rw! (castMode:=.all) [Nat.sub_one_add_one (by omega)] at h
  simp only [cast_eq] at h
  conv_rhs => rw [h]
  rw [eqRec_eq_cast]

lemma algebraMap_succ_eq_zero_x {k : ℕ} (h_pos : k > 0) (x : BTField (k - 1)) :
    letI instAlgebra := binaryAlgebraTower (l:=k-1) (r:=k) (h_le:=by omega)
  algebraMap (BTField (k - 1)) (BTField k) x = ⋘ 0, x ⋙ := by
  letI instAlgebra := binaryAlgebraTower (l:=k-1) (r:=k) (h_le:=by omega)
  have h := eq_join_via_add_smul_eq_iff_split (k:=k) (h_pos:=h_pos)
    (x:=(algebraMap (BTField (k - 1)) (BTField k)) x) (hi_btf:=0) (lo_btf:=x).mpr
  apply h
  exact split_algebraMap_eq_zero_x h_pos x

lemma algebraMap_eq_zero_x {i j : ℕ} (h_le : i < j) (x : BTField i) :
    letI instAlgebra := binaryAlgebraTower (l:=i) (r:=j) (h_le:=by omega)
    letI instAlgebraPred := binaryAlgebraTower (l:=i) (r:=j-1) (h_le:=by omega)
    algebraMap (BTField i) (BTField j) x
      = ⋘ 0, algebraMap (BTField i) (BTField (j-1)) x ⋙ := by
  set d := j - i with d_eq
  induction hd : d with
  | zero =>
    have h_i_eq_j : i = j := by omega
    have h_i_ne_j : i ≠ j := by omega
    contradiction
  | succ d' => -- this one does not even use inductive hypothesis
    have h_j_eq : j = i + d' + 1 := by omega
    change (towerAlgebraMap (l:=i) (r:=j) (h_le:=by omega)) x =
      join_via_add_smul (h_pos:=by omega) 0 ((towerAlgebraMap (l:=i) (r:=j-1) (h_le:=by omega)) x)
    rw! [h_j_eq]
    rw [towerAlgebraMap_succ (l:=i) (r:=i+d') (h_le:=by omega)]
    simp only [RingHom.coe_comp, Function.comp_apply, Nat.add_one_sub_one]
    set r := towerAlgebraMap (l:=i) (r:=i+d') (h_le:=by omega) x with h_r
    have h := algebraMap_succ_eq_zero_x (k:=i+d'+1) (h_pos:=by omega) r
    simp only [Nat.add_one_sub_one] at h
    rw [←h]
    rfl

@[simp]
theorem minPoly_of_powerBasisSucc_generator (k : ℕ) :
    (minpoly (BTField k) (powerBasisSucc k).gen) = X^2 + (Z k) • X + 1 := by
  have h_minPoly := AdjoinRoot.minpoly_powerBasis_gen_of_monic (f:=poly k)
    (hf:=by exact polyMonic k)
  conv_rhs at h_minPoly => rw [poly_form, ←add_assoc, ←Polynomial.smul_eq_C_mul]
  rw [←h_minPoly]
  -- ⊢ minpoly (BTField k) (powerBasisSucc k).gen = minpoly (BTField k) (powerBasis ⋯).gen
  unfold powerBasisSucc
  simp only [PowerBasis.map_gen, powerBasis_gen, minpoly.algEquiv_eq]

end MultilinearBasis

end BinaryTower
