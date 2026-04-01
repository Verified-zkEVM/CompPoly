/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import CompPoly.Fields.Binary.Tower.Abstract.Core
import Batteries.Data.Fin.Fold

/-!
# Abstract Binary Tower Algebra

Algebra maps and tower embeddings for the abstract binary tower fields.
-/

namespace BinaryTower

noncomputable section

open Polynomial
open AdjoinRoot
open Module

section BinaryAlgebraTower
/--
The canonical ring homomorphism embedding `BTField k` into `BTField (k+1)`.
This is the `AdjoinRoot.of` map.
-/
def canonicalEmbedding (k : ℕ) : BTField k →+* BTField (k+1) :=
  AdjoinRoot.of (poly k)

@[simp]
lemma BTField_add_eq (k n m) : BTField (k + n + m) = BTField (k + (n + m)) := by
  rw [add_assoc]

@[simp]
theorem BTField.RingHom_eq_of_dest_eq (k m n : ℕ) (h_eq : m = n) :
    (BTField k →+* BTField m) = (BTField k →+* BTField n) := by
  subst h_eq
  rfl

@[simp]
theorem BTField.RingHom_eq_of_dest_AdjoinRoot_eq (k m : ℕ) :
    (BTField k →+* BTField (m+1)) = (BTField k →+* (AdjoinRoot (poly m))) := by
  rw! (castMode:=.all) [BTField_succ_eq_adjoinRoot m]
  rfl

@[simp]
theorem BTField.RingHom_cast_dest_apply (k m n : ℕ) (h_eq : m = n)
    (f : BTField k →+* BTField m) (x : BTField k) :
    (cast (BTField.RingHom_eq_of_dest_eq (k:=k) (m:=m) (n:=n) h_eq) f) x
    = cast (by apply cast_BTField_eq (h_eq:=h_eq)) (f x) := by
  subst h_eq
  rfl

@[simp]
theorem BTField.RingHom_cast_dest_AdjoinRoot_apply (k m : ℕ)
    (f : BTField k →+* AdjoinRoot (poly m)) (x : BTField k) :
  (cast (BTField.RingHom_eq_of_dest_AdjoinRoot_eq (k:=k) (m:=m)).symm f) x
  = cast (BTField_succ_eq_adjoinRoot m) (f x) := by
  rfl

/-- Compose `d` adjacent canonical embeddings starting from level `l`:
    `BTField l →+* BTField (l+1) →+* ⋯ →+* BTField (l+d)`. -/
def towerAlgebraMapCore (l d : ℕ) :
    BTField l →+* BTField (l + d) :=
  Fin.dfoldl d
    (fun (i : Fin (d + 1)) => BTField l →+* BTField (l + i.val))
    (fun i acc => (canonicalEmbedding (l + i.val)).comp acc)
    (RingHom.id (BTField l))

@[simp]
lemma towerAlgebraMapCore_zero (l : ℕ) :
    towerAlgebraMapCore l 0 = RingHom.id (BTField l) :=
  Fin.dfoldl_zero _ _

lemma towerAlgebraMapCore_succ (l d : ℕ) :
    towerAlgebraMapCore l (d + 1) =
      (canonicalEmbedding (l + d)).comp (towerAlgebraMapCore l d) := by
  simp only [towerAlgebraMapCore]
  rw [Fin.dfoldl_succ_last]
  simp only [Fin.val_last, Function.comp_def, Fin.val_castSucc]

/-- Ring homomorphism embedding `BTField l` into `BTField r`,
    constructed by iterating `canonicalEmbedding` via `Fin.dfoldl`. -/
def towerAlgebraMap (l r : ℕ) (h_le : l ≤ r) : BTField l →+* BTField r :=
  if h_eq : l = r then
    h_eq ▸ RingHom.id (BTField l)
  else
    (towerAlgebraMap (l + 1) r (by omega)).comp (canonicalEmbedding l)
termination_by r - l

lemma towerAlgebraMap_id (k : ℕ) : towerAlgebraMap (h_le:=by omega) = RingHom.id (BTField k) := by
  unfold towerAlgebraMap
  exact (Ne.dite_eq_left_iff fun h a ↦ h rfl).mpr rfl

lemma towerAlgebraMap_succ_1 (k : ℕ) :
    towerAlgebraMap (l:=k) (r:=k+1) (h_le:=by omega) = canonicalEmbedding k := by
  conv_lhs => rw [towerAlgebraMap]
  have : k ≠ k + 1 := by omega
  simp only [this, ↓reduceDIte]
  rw [towerAlgebraMap_id, RingHom.id_comp]

/-! Left decomposition of the Tower Map (helper for right associativity) -/
private lemma towerAlgebraMap_succ_left (l r : ℕ) (h_le : l ≤ r) :
    towerAlgebraMap (l:=l) (r:=r + 1) (h_le:=by omega) =
  (towerAlgebraMap (l:=l + 1) (r:=r + 1) (by omega)).comp
  (canonicalEmbedding l) := by
  conv_lhs => rw [towerAlgebraMap]
  have : l ≠ r + 1 := by omega
  simp only [this, ↓reduceDIte]

/-! Right associativity of the Tower Map -/
lemma towerAlgebraMap_succ (l r : ℕ) (h_le : l ≤ r) :
    towerAlgebraMap (l:=l) (r:=r+1) (h_le:=by omega) =
  (towerAlgebraMap (l:=r) (r:=r+1) (h_le:=by omega)).comp
  (towerAlgebraMap (l:=l) (r:=r) (h_le:=by omega)) := by
  -- Induction on the gap r - l, with both l and r free
  suffices aux : ∀ g l r (hle : l ≤ r), g = r - l →
      towerAlgebraMap l (r + 1) (Nat.le_succ_of_le hle) =
      (towerAlgebraMap r (r + 1) (Nat.le_succ r)).comp
        (towerAlgebraMap l r hle) from
    aux (r - l) l r h_le rfl
  intro g
  induction g with
  | zero =>
    intro l r hle hg
    have : l = r := by omega
    subst this
    rw [towerAlgebraMap_id, RingHom.comp_id]
  | succ g ih =>
    intro l r hle hg
    have h_lt : l < r := by omega
    have h_le' : l + 1 ≤ r := by omega
    -- l < r, so we can decompose from the left
    rw [towerAlgebraMap_succ_left l r hle]
    -- Apply IH with l' = l+1 (gap = r - (l+1) = g)
    rw [ih (l + 1) r h_le' (by omega)]
    rw [RingHom.comp_assoc]
    congr 1
    -- Need: (towerAlgebraMap (l+1) r).comp (canonicalEmbedding l) = towerAlgebraMap l r
    conv_rhs => rw [towerAlgebraMap]
    have : l ≠ r := by omega
    simp only [this, ↓reduceDIte]

/-! Left associativity of the Tower Map -/
theorem towerAlgebraMap_succ_last (r : ℕ) : ∀ l : ℕ, (h_le : l ≤ r) →
    towerAlgebraMap (l:=l) (r:=r+1) (h_le:=by
    exact Nat.le_trans (n:=l) (m:=r) (k:=r+1) (h_le) (by omega)) =
  (towerAlgebraMap (l:=l+1) (r:=r+1) (by omega)).comp (towerAlgebraMap
    (l:=l) (r:=l+1) (by omega)) := by
  induction r using Nat.strong_induction_on with
  | h r ih_r => -- prove for width = r + 1
    intro l h_le
    if h_l_eq_r : l = r then
      subst h_l_eq_r
      rw [towerAlgebraMap_id, RingHom.id_comp]
    else
      -- A = |l| --- (1) --- |l+1| --- (2) --- |r| --- (3) --- |r+1|
      -- ⊢ towerMap l (r + 1) = (towerMap (l + 1) r).comp (towerMap l l+1) => ⊢ A = (23) ∘ (1)
      -- Proof : A = 3 ∘ (12) (succ decomposition) = 3 ∘ (2 ∘ 1) (ind of width = r)
      rw [towerAlgebraMap_succ (l:=l) (r:=r) (by omega)]
      have h_l_r := ih_r (m:=r-1) (l:=l) (h_le:=by omega) (by omega)
      have h_r_sub_1_add_1 : r - 1 + 1 = r := by omega
      rw! [h_r_sub_1_add_1] at h_l_r
      rw [h_l_r, ←RingHom.comp_assoc, ←towerAlgebraMap_succ]

/--
Cast of composition of BTField ring homomorphism is composition of casted BTField ring homomorphism.
Note that this assumes the SAME underlying instances (e.g. NonAssocSemiring)
for both the input and output ring homs.
-/
@[simp]
theorem BTField.RingHom_comp_cast {α β γ δ : ℕ} (f : BTField α →+* BTField β)
    (g : BTField β →+* BTField γ) (h : γ = δ) :
    ((cast (BTField.RingHom_eq_of_dest_eq (k:=β) (m:=γ) (n:=δ) h) g).comp f)
    = cast (BTField.RingHom_eq_of_dest_eq (k:=α) (m:=γ) (n:=δ) h) (g.comp f) := by
  have h1 := BTField.RingHom_eq_of_dest_eq (k:=β) (m:=γ) (n:=δ) h
  have h2 := BTField.RingHom_eq_of_dest_eq (k:=α) (m:=γ) (n:=δ) h
  have h_heq : HEq ((cast (h1) g).comp f) (cast (h2) (g.comp f)) := by
    subst h -- this simplifies h1 h2 in cast which makes them trivial equality
      -- => hence it becomes easier to simplify
    simp only [BTField, BTFieldIsField, cast_eq, heq_eq_eq]
  apply eq_of_heq h_heq

theorem towerAlgebraMap_assoc : ∀ r mid l : ℕ, (h_l_le_mid : l ≤ mid) → (h_mid_le_r : mid ≤ r) →
    towerAlgebraMap (l:=l) (r:=r) (h_le:=by exact Nat.le_trans h_l_le_mid h_mid_le_r) =
    (towerAlgebraMap (l:=mid) (r:=r) (h_le:=h_mid_le_r)).comp
    (towerAlgebraMap (l:=l) (r:=mid) (h_le:=h_l_le_mid)) := by
  -- We induct on `r`, keeping `l` and `mid` as variables in the induction hypothesis.
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih_r => -- right width = r, left width = l
    intro mid l h_l_le_mid h_mid_le_r
    -- A = |l| --- (1) --- |mid| --- (2) --- |r-1| --- (3) --- |r|
    -- Proof : A = 3 ∘ (12) (succ decomposition) = 3 ∘ (2 ∘ 1) (induction hypothesis)
    -- = (3 ∘ 2) ∘ 1 = (23) ∘ 1 (succ decomp) (Q.E.D)
    if h_mid_eq_r : mid = r then
      subst h_mid_eq_r
      simp only [towerAlgebraMap_id, RingHom.id_comp]
    else
      have h_mid_lt_r : mid < r := by omega
      set r_sub_1 := r - 1 with hr_sub_1
      have h_r_sub_1_add_1 : r_sub_1 + 1 = r := by omega
      -- A = 3 ∘ (12)
      rw! [h_r_sub_1_add_1.symm]
      rw [towerAlgebraMap_succ (l:=l) (r:=r_sub_1) (by omega)]
      -- A = 3 ∘ (2 ∘ 1)
      have right_split := ih_r (m:=r_sub_1) (l:=l) (mid:=mid) (by omega) (by omega) (by omega)
      rw [right_split, ←RingHom.comp_assoc]
      -- A = (23) ∘ 1
      rw [←towerAlgebraMap_succ]
/--
**Formalization of Cross-Level Algebra** : For any `k ≤ τ`, `BTField τ` is an
algebra over `BTField k`.
-/
instance : AlgebraTower (BTField) where
  algebraMap := towerAlgebraMap
  commutes' := by
    intro i j h r x
    exact CommMonoid.mul_comm ((towerAlgebraMap i j h) r) x
  coherence' := by exact fun i j k h1 h2 ↦ towerAlgebraMap_assoc k j i h1 h2

def binaryAlgebraTower {l r : ℕ} (h_le : l ≤ r) : Algebra (BTField l) (BTField r) := by
  exact AlgebraTower.toAlgebra h_le

lemma binaryTowerAlgebra_def (l r : ℕ) (h_le : l ≤ r) :
    @binaryAlgebraTower (l:=l) (r:=r) (h_le:=h_le)
    = (towerAlgebraMap l r h_le).toAlgebra := by rfl

lemma algebraMap_binaryTowerAlgebra_def (l r : ℕ) (h_le : l ≤ r) :
    (@binaryAlgebraTower (l:=l) (r:=r) (h_le:=h_le)).algebraMap = towerAlgebraMap l r h_le := by rfl

lemma BTField.coe_one_succ (l : ℕ) :
    (@binaryAlgebraTower (l:=l) (r:=l+1) (h_le:=by omega)).algebraMap (1 : BTField l) =
    (1 : BTField (l+1)) := by
  exact RingHom.map_one (binaryAlgebraTower (l:=l) (r:=l+1) (h_le:=by omega)).algebraMap

@[simp]
theorem binaryTowerAlgebra_id {l r : ℕ} (h_eq : l = r) :
    @binaryAlgebraTower l r (h_le:=by omega) =
    (h_eq ▸ (Algebra.id (BTField l)) : Algebra (BTField l) (BTField r)) := by
  subst h_eq
  simp only [binaryTowerAlgebra_def, towerAlgebraMap_id]
  rfl

theorem binaryTowerAlgebra_apply_assoc (l mid r : ℕ) (h_l_le_mid : l ≤ mid) (h_mid_le_r : mid ≤ r) :
    ∀ x : BTField l,
    (@binaryAlgebraTower (l:=l) (r:=r) (h_le:=by
      exact Nat.le_trans h_l_le_mid h_mid_le_r)).algebraMap x =
    (@binaryAlgebraTower (l:=mid) (r:=r) (h_le:=h_mid_le_r)).algebraMap
      (    (@binaryAlgebraTower (l:=l) (r:=mid) (h_le:=h_l_le_mid)).algebraMap x) := by
  intro x
  simp_rw [algebraMap_binaryTowerAlgebra_def]
  rw [←RingHom.comp_apply]
  rw [towerAlgebraMap_assoc (l:=l) (mid:=mid) (r:=r)
    (h_l_le_mid:=h_l_le_mid) (h_mid_le_r:=h_mid_le_r)]

/-- This also provides the corresponding Module instance. -/
def binaryTowerModule {l r : ℕ} (h_le : l ≤ r) : Module (BTField l) (BTField r) :=
  (binaryAlgebraTower (h_le:=h_le)).toModule

instance (priority := 1000) algebra_adjacent_tower (l : ℕ) :
  Algebra (BTField l) (BTField (l+1)) := by
  exact binaryAlgebraTower (h_le:=by omega)

lemma algebraMap_adjacent_tower_def (l : ℕ) :
    (algebraMap (BTField l) (BTField (l + 1))) = canonicalEmbedding l := by
  unfold algebra_adjacent_tower
  rw [binaryTowerAlgebra_def]
  exact towerAlgebraMap_succ_1 l

lemma algebraMap_adjacent_tower_succ_eq_Adjoin_of (k : ℕ) :
    (algebraMap (BTField k) (BTField (k + 1))) = of (poly k) := by
  rw [algebraMap_adjacent_tower_def]
  rfl

lemma algebra_adjacent_tower_def (l : ℕ) :
    (algebra_adjacent_tower l) = (canonicalEmbedding l).toAlgebra := by
  unfold algebra_adjacent_tower
  rw [binaryTowerAlgebra_def]
  rw [towerAlgebraMap_succ_1]

lemma algebra_adjacent_tower_eq_AdjoinRoot_algebra (k : ℕ) :
    (algebra_adjacent_tower k) = (AdjoinRoot.instAlgebra (poly k)) := by
  rw [algebra_adjacent_tower_def]
  unfold canonicalEmbedding
  rw [←AdjoinRoot.algebraMap_eq]
  rw [algebraMap, Algebra.algebraMap]
  exact
    Algebra.algebra_ext (AdjoinRoot.instAlgebra (poly k)).2.toAlgebra
      (AdjoinRoot.instAlgebra (poly k)) (congrFun rfl)

def BTField_succ_alg_equiv_adjoinRoot (k : ℕ) :
    AdjoinRoot (poly k) ≃ₐ[BTField k] BTField (k + 1) := by
  have h_eq : AdjoinRoot (poly k) = BTField (k + 1) := BTField_succ_eq_adjoinRoot k
  exact { -- We can construct RingEquiv in a similar way
    toFun     := Equiv.cast h_eq,
    invFun    := Equiv.cast h_eq.symm,
    left_inv  := by { intro x; cases h_eq; rfl },
    right_inv := by { intro x; cases h_eq; rfl },
    map_mul'  := by { intros x y; cases h_eq; rfl },
    map_add'  := by { intros x y; cases h_eq; rfl },
    commutes' := by {
      intros r
      rw [algebraMap_adjacent_tower_def]
      rfl -- canonicalEmbedding is compatible with AdjoinRoot
    }
  }

end BinaryAlgebraTower

end

end BinaryTower
