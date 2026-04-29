/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Fields.Binary.Tower.Concrete.Basis

/-!
# Binary Tower Equivalence

Equivalences between the abstract and concrete binary tower constructions.
-/

set_option backward.isDefEq.respectTransparency false
namespace ConcreteBinaryTower

open Polynomial

section TowerEquivalence
/- Tower equivalence between abstract and concrete constructions -/

open BinaryTower

noncomputable def towerEquiv_zero : RingEquiv (R:=GF(2)) (S:=ConcreteBTField 0) :=  {
  toFun := fun x => if x = 0 then 0 else 1,
  invFun := fun x => if x = 0 then 0 else 1,
  left_inv := fun x => by
    rcases GF_2_value_eq_zero_or_one x with x_zero | x_one
    · simp only [x_zero, ↓reduceIte]
    · simp only [x_one, one_ne_zero, ↓reduceIte]
  right_inv := fun x => by
    rcases concrete_eq_zero_or_eq_one (a:=x) (by omega) with x_zero | x_one
    · simp only [x_zero, ite_eq_left_iff, one_ne_zero, imp_false, Decidable.not_not];
      simp only [zero_is_0, ↓reduceIte]
    · simp only [x_one, one_is_1, one_ne_zero, ↓reduceIte]
  map_add' := fun x y => by
    rcases GF_2_value_eq_zero_or_one x with x_zero | x_one
    · simp only [x_zero, _root_.zero_add, ↓reduceIte]
    · simp only [x_one, one_ne_zero, ↓reduceIte]
      rcases GF_2_value_eq_zero_or_one y with y_zero | y_one
      · simp only [y_zero, _root_.add_zero, one_ne_zero, ↓reduceIte]
      · simp only [y_one, one_ne_zero, ↓reduceIte];
        simp only [GF_2_one_add_one_eq_zero, ↓reduceIte]
        exact rfl
  map_mul' := fun x y => by
    rcases GF_2_value_eq_zero_or_one x with x_zero | x_one
    · simp only [x_zero, zero_mul, ↓reduceIte, mul_ite, mul_zero, mul_one, ite_self]
    · simp only [mul_eq_zero, mul_ite, mul_zero, mul_one]
      rcases GF_2_value_eq_zero_or_one y with y_zero | y_one
      · simp only [y_zero, or_true, ↓reduceIte]
      · simp only [y_one, one_ne_zero, or_false, ↓reduceIte]
}
noncomputable def towerRingEquiv0 : BTField 0 ≃+* ConcreteBTField 0 := by
  apply RingEquiv.trans (R:=BTField 0) (S:=GF(2)) (S':=ConcreteBTField 0)
  · exact RingEquiv.refl (BTField 0)
  · exact towerEquiv_zero

noncomputable def towerRingEquivFromConcrete0 : ConcreteBTField 0 ≃+* BTField 0 := by
  exact towerRingEquiv0.symm

noncomputable def towerRingHomForwardMap (k : ℕ) : ConcreteBTField k → BTField k := by
  if h_k_eq_0 : k = 0 then
    subst h_k_eq_0
    exact towerRingEquivFromConcrete0.toFun
  else
    intro x
    let h_split_x_raw := split (k:=k) (h:=by omega) x
    let hi_btf := h_split_x_raw.fst
    let lo_btf := h_split_x_raw.snd
    have hi_mapped := towerRingHomForwardMap (k:=k-1) hi_btf
    have lo_mapped := towerRingHomForwardMap (k:=k-1) lo_btf
    exact BinaryTower.join_via_add_smul (k:=k) (h_pos:=by omega)
      (hi_btf:=hi_mapped) (lo_btf:=lo_mapped)

noncomputable def towerRingHomBackwardMap (k : ℕ) : BTField k → ConcreteBTField k := by
  if h_k_eq_0 : k = 0 then
    subst h_k_eq_0
    exact towerRingEquiv0.toFun
  else
    intro x
    let res := BinaryTower.split (k:=k) (h_k:=by omega) x
    let hi := res.fst
    let lo := res.snd
    let hi_mapped := towerRingHomBackwardMap (k:=k-1) hi
    let lo_mapped := towerRingHomBackwardMap (k:=k-1) lo
    exact join_via_add_smul (k:=k) (h_pos:=by omega) (hi_btf:=hi_mapped) (lo_btf:=lo_mapped)

lemma towerRingHomForwardMap0_eq :
    towerRingEquivFromConcrete0.toFun = towerRingHomForwardMap 0 := by
  unfold towerRingHomForwardMap
  simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, ↓reduceDIte]

lemma towerRingHomForwardMap_zero {k : ℕ} :
    (towerRingHomForwardMap k) 0 = 0 := by
  induction k with
  | zero =>
    unfold towerRingHomForwardMap
    simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, ↓reduceDIte,
      towerRingEquivFromConcrete0]
    rfl
  | succ k ih =>
    unfold towerRingHomForwardMap
    simp only [BTField.eq_1, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_one_sub_one]
    rw! [←zero_is_0, split_zero]
    simp only [Nat.add_one_sub_one, zero_is_0]
    rw! [ih]
    exact BinaryTower.join_via_add_smul_zero (k:=k+1) (h_pos:=by omega)

lemma towerRingHomForwardMap_one {k : ℕ} :
    (towerRingHomForwardMap k) 1 = 1 := by
  induction k with
  | zero =>
    unfold towerRingHomForwardMap
    simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, ↓reduceDIte,
      towerRingEquivFromConcrete0]
    rfl
  | succ k ih =>
    unfold towerRingHomForwardMap
    simp only [BTField.eq_1, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_one_sub_one]
    rw! [←one_is_1, split_one]
    simp only [Nat.add_one_sub_one, one_is_1, zero_is_0]
    rw! [ih, towerRingHomForwardMap_zero]
    exact BinaryTower.join_via_add_smul_one (k:=k+1) (h_pos:=by omega)

lemma towerRingHomForwardMap_Z (k : ℕ) :
    towerRingHomForwardMap k (Z k) = BinaryTower.Z k := by
  induction k with
  | zero =>
    unfold towerRingHomForwardMap
    simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, ↓reduceDIte,
      towerRingEquivFromConcrete0]
    rfl
  | succ k ih =>
    unfold towerRingHomForwardMap
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_one_sub_one]
    rw! [split_Z]
    simp only [Nat.add_one_sub_one, one_is_1, zero_is_0]
    rw! [towerRingHomForwardMap_zero, towerRingHomForwardMap_one]
    exact BinaryTower.join_via_add_smul_one_zero_eq_Z (k:=k+1) (h_pos:=by omega)

lemma towerRingHomBackwardMap_forwardMap_eq (k : ℕ) (x : ConcreteBTField k) :
    towerRingHomBackwardMap (k:=k) (towerRingHomForwardMap (k:=k) x) = x := by
  induction k with
  | zero =>
    unfold towerRingHomBackwardMap towerRingHomForwardMap
    simp only [↓reduceDIte, RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe]
    rcases concrete_eq_zero_or_eq_one (a:=x) (by omega) with x_zero | x_one
    · rw [x_zero, zero_is_0]
      unfold towerRingEquivFromConcrete0 -- unfold the inner RingEquiv only
      simp only [RingEquiv.apply_symm_apply] -- due to definition of `towerRingEquiv0`
    · rw [x_one, one_is_1]
      unfold towerRingEquivFromConcrete0 -- unfold the inner RingEquiv only
      simp only [RingEquiv.apply_symm_apply] -- due to definition of `towerRingEquiv0`
  | succ k ih =>
    rw [towerRingHomForwardMap] -- split inner
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, Nat.add_one_sub_one]
    rw [towerRingHomBackwardMap] -- split outer
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, Nat.add_one_sub_one]
    rw [←join_eq_join_via_add_smul]
    apply Eq.symm
    apply join_of_split
    simp only [Nat.add_one_sub_one]
    rw [BinaryTower.split_join_via_add_smul_eq_iff_split (k:=k + 1)]
    simp only
    -- apply induction hypothesis
    rw [ih, ih]
    simp only [Prod.mk.eta]

lemma towerRingHomForwardMap_backwardMap_eq (k : ℕ) (x : BTField k) :
    towerRingHomForwardMap (k:=k) (towerRingHomBackwardMap (k:=k) x) = x := by
  induction k with
  | zero =>
    unfold towerRingHomForwardMap towerRingHomBackwardMap
    simp only [↓reduceDIte, RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe]
    rcases GF_2_value_eq_zero_or_one x with x_zero | x_one
    · rw [x_zero];
      unfold towerRingEquivFromConcrete0 -- ⊢ towerRingEquiv0.symm (towerRingEquiv0 0) = 0
      exact RingEquiv.symm_apply_apply towerRingEquiv0 0
    · rw [x_one];
      unfold towerRingEquivFromConcrete0 -- ⊢ towerRingEquiv0.symm (towerRingEquiv0 1) = 1
      exact RingEquiv.symm_apply_apply towerRingEquiv0 1
  | succ k ih =>
    rw [towerRingHomBackwardMap] -- split inner
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_one_sub_one]
    rw [towerRingHomForwardMap] -- split outer
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_one_sub_one]
    apply Eq.symm
    rw! [split_join_via_add_smul_eq_iff_split (k:=k + 1)]
    simp only
    -- apply induction hypothesis
    rw [ih, ih]
    rw [BinaryTower.eq_join_via_add_smul_eq_iff_split]

lemma towerRingHomForwardMap_add_eq (k : ℕ) (x y : ConcreteBTField k) :
    towerRingHomForwardMap (k:=k) (x + y)
    = towerRingHomForwardMap (k:=k) x + towerRingHomForwardMap (k:=k) y := by
  induction k with
  | zero =>
    unfold towerRingHomForwardMap
    simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
      ↓reduceDIte, towerRingEquivFromConcrete0]
    have h_map_0 : towerRingEquiv0.symm 0 = 0 := by rfl
    have h_map_1 : towerRingEquiv0.symm 1 = 1 := by rfl
    rcases concrete_eq_zero_or_eq_one (a:=x) (by omega) with x_zero | x_one
    · simp only [x_zero, zero_is_0, _root_.zero_add]
      rw [h_map_0]
      simp only [_root_.zero_add]
    · simp only [x_one, one_is_1]
      rcases concrete_eq_zero_or_eq_one (a:=y) (by omega) with y_zero | y_one
      · simp only [y_zero, zero_is_0]
        simp only [_root_.add_zero]
        rw [h_map_0]; norm_num
      · simp only [y_one, one_is_1]
        simp only [add_self_cancel, h_map_1]
        rw [GF_2_one_add_one_eq_zero]
        rfl
  | succ k ih =>
    unfold towerRingHomForwardMap
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_one_sub_one]
    rw [BinaryTower.sum_join_via_add_smul (k:=k+1)]
    simp only [Nat.add_one_sub_one]
    set x₁ := (split (k:=k+1) (x:=x) (by omega)).fst
    set x₀ := (split (k:=k+1) (x:=x) (by omega)).snd
    set y₁ := (split (k:=k+1) (x:=y) (by omega)).fst
    set y₀ := (split (k:=k+1) (x:=y) (by omega)).snd
    have h_split_sum_x_add_y := split_sum_eq_sum_split (k:=k+1)
      (h_pos:=by omega) x y (hi₀:=x₁) (lo₀:=x₀) (hi₁:=y₁) (lo₁:=y₀) (by rfl) (by rfl)
    rw [h_split_sum_x_add_y]
    simp only [Nat.add_one_sub_one]
    congr
    -- apply induction hypothesis
    · rw [ih (x:=x₁) (y:=y₁)]
    · rw [ih (x:=x₀) (y:=y₀)]

theorem split_mul_eq_mul_split {k : ℕ} (h_pos : k > 0) (x₀ x₁ : ConcreteBTField k)
    (hi₀ lo₀ hi₁ lo₁ : ConcreteBTField (k - 1))
  (h_split_x₀ : split h_pos x₀ = (hi₀, lo₀))
  (h_split_x₁ : split h_pos x₁ = (hi₁, lo₁)) :
  split h_pos (x₀ * x₁) =
    (lo₀ * hi₁ + lo₁ * hi₀ + hi₀ * hi₁ * Z (k - 1), lo₀ * lo₁ + hi₀ * hi₁) := by
  rw [split_of_join]
  have h_mul_eq := (getBTFResult k).mul_eq
  -- ⊢ x₀ * x₁ = join h_pos (hi₀ * hi₁ + hi₀ * lo₁ + lo₀ * hi₁) (lo₀ * lo₁)
  have h_mul_repr := h_mul_eq (a:=x₀) (b:=x₁) (h_k:=h_pos) (a₁:=hi₀) (a₀:=lo₀) (b₁:=hi₁) (b₀:=lo₁)
    (by exact Eq.symm h_split_x₀) (by exact Eq.symm h_split_x₁)
  -- Now convert all * to concrete_mul and all + to concrete_add
  simp only [HMul.hMul]
  rw [h_mul_repr]

lemma towerRingHomForwardMap_mul_eq (k : ℕ) (x y : ConcreteBTField k) :
    towerRingHomForwardMap (k:=k) (x * y)
    = towerRingHomForwardMap (k:=k) x * towerRingHomForwardMap (k:=k) y := by
  induction k with
  | zero =>
    unfold towerRingHomForwardMap
    simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
      ↓reduceDIte, towerRingEquivFromConcrete0]
    have h_map_0 : towerRingEquiv0.symm 0 = 0 := by rfl
    have h_map_1 : towerRingEquiv0.symm 1 = 1 := by rfl
    rcases concrete_eq_zero_or_eq_one (a:=x) (by omega) with x_zero | x_one
    · simp only [x_zero, zero_is_0, zero_mul, h_map_0]
    · simp only [x_one, one_is_1]
      rcases concrete_eq_zero_or_eq_one (a:=y) (by omega) with y_zero | y_one
      · simp only [y_zero, zero_is_0, mul_zero, h_map_1, one_mul]
      · simp only [y_one, one_is_1, mul_one, h_map_1]
  | succ k ih =>
    unfold towerRingHomForwardMap
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_one_sub_one]
    rw [BinaryTower.mul_join_via_add_smul (k:=k+1) (h_pos:=by omega)]
    simp only [Nat.add_one_sub_one]
    set x₁ : ConcreteBTField k := (split (k:=k+1) (x:=x) (by omega)).fst
    set x₀ : ConcreteBTField k := (split (k:=k+1) (x:=x) (by omega)).snd
    set y₁ : ConcreteBTField k := (split (k:=k+1) (x:=y) (by omega)).fst
    set y₀ : ConcreteBTField k := (split (k:=k+1) (x:=y) (by omega)).snd
    have h_split_mul_x_add_y := split_mul_eq_mul_split (k:=k+1)
      (h_pos:=by omega) x y (hi₀:=x₁) (lo₀:=x₀) (hi₁:=y₁) (lo₁:=y₀) (by rfl) (by rfl)
    rw [h_split_mul_x_add_y]
    simp only [Nat.add_one_sub_one]
    congr
    · rw [←ih, ←ih, ←ih];
      rw [towerRingHomForwardMap_add_eq, towerRingHomForwardMap_add_eq]
      simp only [Nat.add_one_sub_one]
      have h : towerRingHomForwardMap k (x₁ * y₁ * Z k)
        = towerRingHomForwardMap k (x₁ * y₁) * BinaryTower.Z k := by
        rw [ih, towerRingHomForwardMap_Z k]
      rw [h, mul_comm y₀ x₁]
      abel_nf
    · rw [towerRingHomForwardMap_add_eq, ih, ih];

lemma towerRingHomForwardMap_split_eq (k : ℕ) (h_pos : k > 0) (x : ConcreteBTField k) :
    let p := split (k:=k) (h:=h_pos) x
  towerRingHomForwardMap (k:=k) (x) =
    BinaryTower.join_via_add_smul (k:=k) (h_pos:=h_pos)
      (hi_btf := towerRingHomForwardMap (k:=k-1) (p.1))
      (lo_btf := towerRingHomForwardMap (k:=k-1) (p.2)) := by
  -- This lemma is actually due to the definition of `towerRingHomForwardMap` for `k > 0`
  simp only [BTField.eq_1]
  conv_lhs => unfold towerRingHomForwardMap -- not unfold in the rhs
  have h_k_ne_0 : k ≠ 0 := by omega
  set hi := (split (k:=k) (h:=h_pos) x).1 with hhi
  set lo := (split (k:=k) (h:=h_pos) x).2 with hlo
  simp only [h_k_ne_0, ↓reduceDIte]
  rw! [←hhi]
  grind

lemma towerRingHomForwardMap_join {k : ℕ} (h_pos : k > 0) (hi lo : ConcreteBTField (k - 1)) :
    towerRingHomForwardMap (k:=k) (《 hi, lo 》) =
    BinaryTower.join_via_add_smul (k:=k) (h_pos:=by omega)
      (hi_btf := towerRingHomForwardMap (k:=k-1) hi)
      (lo_btf := towerRingHomForwardMap (k:=k-1) lo) := by
  set x := 《 hi, lo 》
  have h_split : (hi, lo) = (split (k:=k) (h:=h_pos) x) := by
    apply split_of_join (k:=k)
    rfl
  have h_hi : hi = (split (k:=k) (h:=h_pos) x).1 := by rw [←h_split]
  have h_lo : lo = (split (k:=k) (h:=h_pos) x).2 := by rw [←h_split]
  rw [towerRingHomForwardMap_split_eq (k:=k) (h_pos:=h_pos) x]
  congr
  · rw [h_hi]
  · rw [h_lo]

structure TowerEquivResult (k : ℕ) where
  ringEquiv : ConcreteBTField k ≃+* BTField k
  ringEquivForwardMapEq : ringEquiv = towerRingHomForwardMap k

noncomputable def towerEquiv (n : ℕ) : TowerEquivResult n := by
  induction n with
  | zero =>
    have h_ringHom_0 := towerRingHomForwardMap0_eq
    exact {
      ringEquiv := towerRingEquivFromConcrete0
      ringEquivForwardMapEq := by
        exact h_ringHom_0
    }
  | succ n ih =>
    let pb_abstract : PowerBasis (BTField n) (BTField (n + 1)) :=
      BinaryTower.powerBasisSucc n

    let pb_concrete : PowerBasis (ConcreteBTField n) (ConcreteBTField (n + 1)) :=
      powerBasisSucc n

    let curRingHom : ConcreteBTField (n+1) ≃+* BTField (n + 1) := by
      exact {
        toFun := fun x => by exact towerRingHomForwardMap (k:=n+1) x
        invFun := fun x => by exact towerRingHomBackwardMap (k:=n+1) x
        left_inv := fun x => by
          exact towerRingHomBackwardMap_forwardMap_eq (n + 1) x
        right_inv := fun x => by
          exact towerRingHomForwardMap_backwardMap_eq (n + 1) x
        map_add' := fun x y => by
          exact towerRingHomForwardMap_add_eq (n + 1) x y
        map_mul' := fun x y => by
          exact towerRingHomForwardMap_mul_eq (n + 1) x y
      }
    exact {
      ringEquiv := by exact curRingHom
      ringEquivForwardMapEq := by
        change curRingHom.toFun = towerRingHomForwardMap (n+1)
        rfl
    }

theorem BTField_algebraMap_succ_eq_join (k : ℕ) (x : BTField k) :
    algebraMap (BTField k) (BTField (k+1)) x =
      BinaryTower.join_via_add_smul (k:=k+1) (h_pos:=by omega) 0 x := by
  simpa using (BinaryTower.algebraMap_succ_eq_zero_x (k := k+1) (h_pos := by omega) (x := x))

theorem ConcreteBTField_algebraMap_succ_eq_join (k : ℕ) (r : ConcreteBTField k) :
    algebraMap (ConcreteBTField k) (ConcreteBTField (k+1)) r =
      join (k:=k+1) (h_pos:=by omega) 0 r := by
  simpa [Nat.add_one_sub_one] using
    (algebraMap_succ_eq_zero_x (k:=k+1) (h_pos:=by omega) (x:=r))

theorem towerEquiv_ringEquiv_apply (k : ℕ) (r : ConcreteBTField k) :
    (towerEquiv k).ringEquiv r = towerRingHomForwardMap k r := by
  -- Use the forward-map characterization of the ring equivalence
  simpa using congrArg (fun f => f r) (towerEquiv k).ringEquivForwardMapEq

theorem towerEquiv_commutes_left_succ (k : ℕ) : ∀ r : ConcreteBTField k,
    (AlgebraTower.algebraMap k (k+1) (by omega)) ((towerEquiv k).ringEquiv r) =
  (towerEquiv (k+1)).ringEquiv ((AlgebraTower.algebraMap k (k+1) (by omega)) r) := by
  intro r
  -- Rewrite the tower equivalence maps to the explicit forward map
  rw [towerEquiv_ringEquiv_apply (k:=k) (r:=r)]
  rw [towerEquiv_ringEquiv_apply (k:=k + 1)
    (r:=(AlgebraTower.algebraMap k (k + 1) (by omega) r))]
  -- Turn the adjacent tower maps into the usual `algebraMap` so we can use the join rewrite lemmas
  change algebraMap (BTField k) (BTField (k + 1)) (towerRingHomForwardMap k r) =
      towerRingHomForwardMap (k + 1)
        (algebraMap (ConcreteBTField k) (ConcreteBTField (k + 1)) r)
  -- Rewrite both adjacent algebra maps as joins
  rw [BTField_algebraMap_succ_eq_join (k:=k) (x:=towerRingHomForwardMap k r)]
  rw [ConcreteBTField_algebraMap_succ_eq_join (k:=k) (r:=r)]
  -- Evaluate `towerRingHomForwardMap` on a concrete join
  rw [towerRingHomForwardMap_join (k:=k + 1) (h_pos:=by omega) (hi:=0) (lo:=r)]
  -- Normalize the predecessor index `k + 1 - 1`
  simp only [Nat.add_one_sub_one] at *
  -- Simplify the `hi` part
  rw [towerRingHomForwardMap_zero (k:=k)]

theorem towerEquiv_commutes_left_diff (i d : ℕ) : ∀ r : ConcreteBTField i,
    (AlgebraTower.algebraMap i (i+d) (by omega)) ((towerEquiv i).ringEquiv r) =
  (towerEquiv (i+d)).ringEquiv ((AlgebraTower.algebraMap i (i+d) (by omega)) r) := by
  intro r
  induction d with
  | zero =>
      simp only [Nat.add_zero]
      change (towerAlgebraMap (l:=i) (r:=i) (h_le:=by omega)) ((towerEquiv i).ringEquiv r) =
        (towerEquiv i).ringEquiv ((concreteTowerAlgebraMap (l:=i) (r:=i) (h_le:=by omega)) r)
      simp [towerAlgebraMap_id, concreteTowerAlgebraMap_id]
  | succ d ih =>
      calc
        (AlgebraTower.algebraMap i (i + Nat.succ d) (by omega)) ((towerEquiv i).ringEquiv r)
            = ((AlgebraTower.algebraMap (i + d) (i + d + 1) (by omega)).comp
                (AlgebraTower.algebraMap i (i + d) (by omega))) ((towerEquiv i).ringEquiv r) := by
              simpa [Nat.add_assoc] using congrArg (fun f => f ((towerEquiv i).ringEquiv r))
                (towerAlgebraMap_succ (l:=i) (r:=i + d) (h_le:=by omega))
        _ = (AlgebraTower.algebraMap (i + d) (i + d + 1) (by omega))
              ((AlgebraTower.algebraMap i (i + d) (by omega)) ((towerEquiv i).ringEquiv r)) := by
              simp only [RingHom.coe_comp, Function.comp_apply]
        _ = (AlgebraTower.algebraMap (i + d) (i + d + 1) (by omega))
              ((towerEquiv (i + d)).ringEquiv
                ((AlgebraTower.algebraMap i (i + d) (by omega)) r)) := by
              rw [ih]
        _ = (towerEquiv (i + d + 1)).ringEquiv
              ((AlgebraTower.algebraMap (i + d) (i + d + 1) (by omega))
                ((AlgebraTower.algebraMap i (i + d) (by omega)) r)) := by
              simpa using (towerEquiv_commutes_left_succ (k:=i + d)
                ((AlgebraTower.algebraMap i (i + d) (by omega)) r))
        _ = (towerEquiv (i + d + 1)).ringEquiv
              ((AlgebraTower.algebraMap i (i + d + 1) (by omega)) r) := by
              have hconc : (AlgebraTower.algebraMap (AT:=ConcreteBTField) i (i + d + 1) (by omega))
                    = (AlgebraTower.algebraMap (AT:=ConcreteBTField) (i + d) (i + d + 1)
                        (by omega)).comp
                        (AlgebraTower.algebraMap (AT:=ConcreteBTField) i (i + d) (by omega)) := by
                simpa [Nat.add_assoc] using
                  (concreteTowerAlgebraMap_succ (l:=i) (r:=i + d) (h_le:=by omega))
              have hconc_apply := congrArg (fun f => f r) hconc
              have h_inner :
                  (AlgebraTower.algebraMap (AT:=ConcreteBTField) (i + d) (i + d + 1) (by omega))
                      ((AlgebraTower.algebraMap (AT:=ConcreteBTField) i (i + d) (by omega)) r) =
                    (AlgebraTower.algebraMap (AT:=ConcreteBTField) i (i + d + 1) (by omega)) r := by
                simpa [RingHom.comp_apply] using hconc_apply.symm
              simp [h_inner]
        _ = (towerEquiv (i + Nat.succ d)).ringEquiv
              ((AlgebraTower.algebraMap i (i + Nat.succ d) (by omega)) r) := by
              rfl

theorem towerEquiv_commutes_left (i j : ℕ) (h : i ≤ j) : ∀ r : ConcreteBTField i,
    (AlgebraTower.algebraMap i j h) ((towerEquiv i).ringEquiv r) =
  (towerEquiv j).ringEquiv ((AlgebraTower.algebraMap i j h) r) := by
  let d := j - i
  have h_j_eq : j = i + d := by omega
  rw! [h_j_eq]
  exact towerEquiv_commutes_left_diff (i:=i) (d:=d)

noncomputable instance instAlgebraTowerEquiv : AlgebraTowerEquiv
  (ConcreteBTField) (BTField) where
  toRingEquiv := fun i => (towerEquiv i).ringEquiv
  commutesLeft' := fun i j h r => by
    exact towerEquiv_commutes_left (i:=i) (j:=j) (h:=h) (r:=r)

-- #check instAlgebraTowerEquiv.toAlgEquivOverLeft 7 100 (by omega)
-- #check instAlgebraTowerEquiv.toAlgEquivOverRight 7 100 (by omega)

end TowerEquivalence

end ConcreteBinaryTower
