/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Fields.Binary.Tower.Concrete.Field
import Batteries.Data.Fin.Fold

/-!
# Concrete Binary Tower Algebra

Algebra maps and embeddings for the concrete bitvector binary tower.
-/

namespace ConcreteBinaryTower

open Polynomial

section ConcreteBTFieldAlgebraConstruction

def canonicalAlgMap (k : ℕ) := concreteCanonicalEmbedding (k:=k)
  (prevBTFieldProps:= ((getBTFResult k).toConcreteBTFieldProps))
  (curBTFieldProps:= ((getBTFResult (k + 1)).toConcreteBTFieldProps))

/-- `Z(k+1)` is the adjoined root of `poly k` to `ConcreteBTField (k+1)`, so it is not
lifted to `ConcreteBTField (k+1)` by `canonicalAlgMap` -/
@[simp]
theorem generator_is_not_lifted_to_succ (k : ℕ) :
    ∀ x : ConcreteBTField k, canonicalAlgMap (k:=k) x ≠ Z (k + 1) := by
  by_contra hx
  simp only [ne_eq, not_forall, Decidable.not_not] at hx
  -- unfold canonicalAlgMap at hx
  have h_x_join : ∃ x : ConcreteBTField k,
    join (k:=k + 1) (h_pos:=by omega) (zero (k:=k)) x = Z (k + 1) := by
    exact hx
  have h_Z_split := split_Z (k:=k + 1) (h_pos:=by omega)
  have hx := h_x_join.choose_spec
  set x := h_x_join.choose
  have h_Z_split_into_0_x := split_of_join (k:=k + 1) (h_pos:=by omega) (x:=Z (k+1))
    (hi_btf:=zero (k:=k)) (lo_btf:=x) (h_join:=by exact id (Eq.symm hx))
  rw [←h_Z_split_into_0_x] at h_Z_split
  -- h_Z_split : (zero, x) = (one, zero)
  rw [Prod.mk.injEq] at h_Z_split
  have h_zero_eq_one : zero (k:=k) = one (k:=k) := by exact h_Z_split.1
  have h_zero_ne_one : zero (k:=k) ≠ one (k:=k) := by exact one_ne_zero.symm
  contradiction

@[simp]
lemma ConcreteBTField_add_eq (k n m) :
    ConcreteBTField (k + n + m) = ConcreteBTField (k + (n + m)) := by
  rw [Nat.add_assoc]

@[simp]
theorem ConcreteBTField.RingHom_eq_of_dest_eq (k m n : ℕ) (h_eq : m = n) :
    (ConcreteBTField k →+* ConcreteBTField m)
    = (ConcreteBTField k →+* ConcreteBTField n) := by
  subst h_eq
  rfl

@[simp]
theorem ConcreteBTField.RingHom_eq_of_source_eq (k n m : ℕ) (h_eq : k = n) :
    (ConcreteBTField k →+* ConcreteBTField m)
    = (ConcreteBTField n →+* ConcreteBTField m) := by
  subst h_eq
  rfl

@[simp]
theorem ConcreteBTField.RingHom_cast_dest_apply (k m n : ℕ) (h_eq : m = n)
    (f : ConcreteBTField k →+* ConcreteBTField m) (x : ConcreteBTField k) :
    (cast (ConcreteBTField.RingHom_eq_of_dest_eq (k:=k) (m:=m) (n:=n) h_eq) f) x
    = cast (by apply cast_ConcreteBTField_eq (h_eq:=h_eq)) (f x) := by
  subst h_eq
  rfl

@[simp]
theorem ConcreteBTField.RingHom_cast_source_apply (k n m : ℕ) (h_eq : k = n)
    (f : ConcreteBTField k →+* ConcreteBTField m) (x : ConcreteBTField n) :
    (cast (ConcreteBTField.RingHom_eq_of_source_eq (k:=k) (n:=n) (m:=m) h_eq) f) x
    = f (cast (by apply cast_ConcreteBTField_eq (h_eq:=h_eq.symm)) x) := by
  subst h_eq
  rfl

/-- Compose `d` adjacent canonical embeddings starting from level `l`:
    `ConcreteBTField l →+* ConcreteBTField (l+1) →+* ⋯ →+* ConcreteBTField (l+d)`. -/
def concreteTowerAlgebraMapCore (l d : ℕ) :
    ConcreteBTField l →+* ConcreteBTField (l + d) :=
  Fin.dfoldl d
    (fun (i : Fin (d + 1)) => ConcreteBTField l →+* ConcreteBTField (l + i.val))
    (fun i acc => (canonicalAlgMap (l + i.val)).comp acc)
    (RingHom.id (ConcreteBTField l))

@[simp]
lemma concreteTowerAlgebraMapCore_zero (l : ℕ) :
    concreteTowerAlgebraMapCore l 0 = RingHom.id (ConcreteBTField l) :=
  Fin.dfoldl_zero _ _

lemma concreteTowerAlgebraMapCore_succ (l d : ℕ) :
    concreteTowerAlgebraMapCore l (d + 1) =
      (canonicalAlgMap (l + d)).comp (concreteTowerAlgebraMapCore l d) := by
  simp only [concreteTowerAlgebraMapCore]
  rw [Fin.dfoldl_succ_last]
  simp only [Fin.val_last, Function.comp_def, Fin.val_castSucc]

/-- Ring homomorphism embedding `ConcreteBTField l` into `ConcreteBTField r`,
    constructed by iterating `canonicalAlgMap` from the left.
    The core computation uses `Fin.dfoldl` via `concreteTowerAlgebraMapCore`. -/
def concreteTowerAlgebraMap (l r : ℕ) (h_le : l ≤ r) :
    ConcreteBTField l →+* ConcreteBTField r :=
  if h_eq : l = r then
    h_eq ▸ RingHom.id (ConcreteBTField l)
  else
    (concreteTowerAlgebraMap (l + 1) r (by omega)).comp (canonicalAlgMap l)
termination_by r - l

lemma concreteTowerAlgebraMap_id (k : ℕ) :
    concreteTowerAlgebraMap (h_le:=by omega) = RingHom.id (ConcreteBTField k) := by
  unfold concreteTowerAlgebraMap
  exact (Ne.dite_eq_left_iff fun h a ↦ h rfl).mpr rfl

lemma concreteTowerAlgebraMap_succ_1 (k : ℕ) :
    concreteTowerAlgebraMap (l:=k) (r:=k + 1) (h_le:=by omega) = canonicalAlgMap k := by
  conv_lhs => rw [concreteTowerAlgebraMap]
  have : k ≠ k + 1 := by omega
  simp only [this, ↓reduceDIte]
  rw [concreteTowerAlgebraMap_id, RingHom.id_comp]

/-! Left decomposition of the Tower Map (helper for right associativity) -/
private lemma concreteTowerAlgebraMap_succ_left (l r : ℕ) (h_le : l ≤ r) :
    concreteTowerAlgebraMap (l:=l) (r:=r + 1) (h_le:=by omega) =
  (concreteTowerAlgebraMap (l:=l + 1) (r:=r + 1) (by omega)).comp
  (canonicalAlgMap l) := by
  conv_lhs => rw [concreteTowerAlgebraMap]
  have : l ≠ r + 1 := by omega
  simp only [this, ↓reduceDIte]

/-! Right associativity of the Tower Map -/
lemma concreteTowerAlgebraMap_succ (l r : ℕ) (h_le : l ≤ r) :
    concreteTowerAlgebraMap (l:=l) (r:=r + 1) (h_le:=by omega) =
  (concreteTowerAlgebraMap (l:=r) (r:=r + 1) (h_le:=by omega)).comp
  (concreteTowerAlgebraMap (l:=l) (r:=r) (h_le:=by omega)) := by
  -- Induction on the gap r - l, with both l and r free
  suffices aux : ∀ g l r (hle : l ≤ r), g = r - l →
      concreteTowerAlgebraMap l (r + 1) (Nat.le_succ_of_le hle) =
      (concreteTowerAlgebraMap r (r + 1) (Nat.le_succ r)).comp
        (concreteTowerAlgebraMap l r hle) from
    aux (r - l) l r h_le rfl
  intro g
  induction g with
  | zero =>
    intro l r hle hg
    have : l = r := by omega
    subst this
    rw [concreteTowerAlgebraMap_id, RingHom.comp_id]
  | succ g ih =>
    intro l r hle hg
    have h_lt : l < r := by omega
    have h_le' : l + 1 ≤ r := by omega
    -- l < r, so we can decompose from the left
    rw [concreteTowerAlgebraMap_succ_left l r hle]
    -- Apply IH with l' = l+1 (gap = r - (l+1) = g)
    rw [ih (l + 1) r h_le' (by omega)]
    rw [RingHom.comp_assoc]
    congr 1
    -- Need: (concreteTowerAlgebraMap (l+1) r).comp (canonicalAlgMap l) = concreteTowerAlgebraMap l r
    -- This is succ_left backwards: unfold concreteTowerAlgebraMap l r once
    conv_rhs => rw [concreteTowerAlgebraMap]
    have : l ≠ r := by omega
    simp only [this, ↓reduceDIte]

/-! Left associativity of the Tower Map -/
theorem concreteTowerAlgebraMap_succ_last (r : ℕ) : ∀ l : ℕ, (h_le : l ≤ r) →
    concreteTowerAlgebraMap (l:=l) (r:=r + 1) (h_le:=by
    exact Nat.le_trans (n:=l) (m:=r) (k:=r + 1) (h_le) (by omega)) =
  (concreteTowerAlgebraMap (l:=l + 1) (r:=r + 1) (by omega)).comp (concreteTowerAlgebraMap
    (l:=l) (r:=l + 1) (by omega)) := by
  induction r using Nat.strong_induction_on with
  | h r ih_r => -- prove for width = r + 1
    intro l h_le
    if h_l_eq_r : l = r then
      subst h_l_eq_r
      rw [concreteTowerAlgebraMap_id, RingHom.id_comp]
    else
      -- A = |l| --- (1) --- |l + 1| --- (2) --- |r| --- (3) --- |r + 1|
      -- ⊢ towerMap l (r + 1) = (towerMap (l + 1) r).comp (towerMap l l + 1) => ⊢ A = (23) ∘ (1)
      -- Proof : A = 3 ∘ (12) (succ decomposition) = 3 ∘ (2 ∘ 1) (ind of width = r)
      rw [concreteTowerAlgebraMap_succ (l:=l) (r:=r) (by omega)]
      have h_l_r := ih_r (m:=r - 1) (l:=l) (h_le:=by omega) (by omega)
      have h_r_sub_1_add_1 : r - 1 + 1 = r := by omega
      rw! [h_r_sub_1_add_1] at h_l_r
      rw [h_l_r, ←RingHom.comp_assoc, ←concreteTowerAlgebraMap_succ]

/--
Cast of composition of ConcreteBTField ring homomorphism is composition of
casted ConcreteBTField ring homomorphism.
Note that this assumes the SAME underlying instances (e.g. NonAssocSemiring)
for both the input and output ring homs.
-/
@[simp]
theorem ConcreteBTField.RingHom_comp_cast {α β γ δ : ℕ}
    (f : ConcreteBTField α →+* ConcreteBTField β)
    (g : ConcreteBTField β →+* ConcreteBTField γ) (h : γ = δ) :
    ((cast (ConcreteBTField.RingHom_eq_of_dest_eq (k:=β) (m:=γ) (n:=δ) h) g).comp f)
    = cast (ConcreteBTField.RingHom_eq_of_dest_eq (k:=α) (m:=γ) (n:=δ) h) (g.comp f) := by
  have h1 := ConcreteBTField.RingHom_eq_of_dest_eq (k:=β) (m:=γ) (n:=δ) h
  have h2 := ConcreteBTField.RingHom_eq_of_dest_eq (k:=α) (m:=γ) (n:=δ) h
  have h_heq : HEq ((cast (h1) g).comp f) (cast (h2) (g.comp f)) := by
    subst h -- this simplifies h1 h2 in cast which makes them trivial equality
      -- => hence it becomes easier to simplify
    rfl
  apply eq_of_heq h_heq

theorem concreteTowerAlgebraMap_assoc :
    ∀ r mid l : ℕ, (h_l_le_mid : l ≤ mid) → (h_mid_le_r : mid ≤ r) →
    concreteTowerAlgebraMap (l:=l) (r:=r) (h_le:=by exact Nat.le_trans h_l_le_mid h_mid_le_r) =
    (concreteTowerAlgebraMap (l:=mid) (r:=r) (h_le:=h_mid_le_r)).comp
    (concreteTowerAlgebraMap (l:=l) (r:=mid) (h_le:=h_l_le_mid)) := by
  -- We induct on `r`, keeping `l` and `mid` as variables in the induction hypothesis.
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih_r => -- right width = r, left width = l
    intro mid l h_l_le_mid h_mid_le_r
    -- A = |l| --- (1) --- |mid| --- (2) --- |r - 1| --- (3) --- |r|
    -- Proof : A = 3 ∘ (12) (succ decomposition) = 3 ∘ (2 ∘ 1) (induction hypothesis)
    -- = (3 ∘ 2) ∘ 1 = (23) ∘ 1 (succ decomp) (Q.E.D)
    if h_mid_eq_r : mid = r then
      subst h_mid_eq_r
      simp only [concreteTowerAlgebraMap_id, RingHom.id_comp]
    else
      have h_mid_lt_r : mid < r := by omega
      set r_sub_1 := r - 1 with hr_sub_1
      have h_r_sub_1_add_1 : r_sub_1 + 1 = r := by omega
      -- A = 3 ∘ (12)
      rw! [h_r_sub_1_add_1.symm]
      rw [concreteTowerAlgebraMap_succ (l:=l) (r:=r_sub_1) (by omega)]
      -- A = 3 ∘ (2 ∘ 1)
      have right_split := ih_r (m:=r_sub_1) (l:=l) (mid:=mid) (by omega) (by omega) (by omega)
      rw [right_split, ←RingHom.comp_assoc]
      -- A = (23) ∘ 1
      rw [←concreteTowerAlgebraMap_succ]
/--
**Formalization of Cross - Level Algebra** : For any `k ≤ τ`, `ConcreteBTField τ` is an
algebra over `ConcreteBTField k`.
-/
instance instAlgebraTowerConcreteBTF : AlgebraTower (ConcreteBTField) where
  algebraMap := concreteTowerAlgebraMap
  commutes' := by
    intro i j h r x
    exact CommMonoid.mul_comm ((concreteTowerAlgebraMap i j h) r) x
  coherence' := by
    intro i j k h1 h2
    exact concreteTowerAlgebraMap_assoc k j i h1 h2

def ConcreteBTFieldAlgebra {l r : ℕ} (h_le : l ≤ r) :
    Algebra (ConcreteBTField l) (ConcreteBTField r) := instAlgebraTowerConcreteBTF.toAlgebra h_le

-- Since `join_via_add_smul` is equal `join`, it is also inverse of `split`
def join_via_add_smul (k : ℕ) (h_pos : k > 0) (hi_btf lo_btf : ConcreteBTField (k - 1)) :
    ConcreteBTField k := by
  letI instAlgebra := ConcreteBTFieldAlgebra (l:=k-1) (r:=k) (h_le:=by omega)
  exact hi_btf • Z k + (algebraMap (ConcreteBTField (k - 1)) (ConcreteBTField k) lo_btf)

/--
An element `x` lifted from the base field `ConcreteBTField (k-1)` has `(0, x)` as its
split representation in `ConcreteBTField k`.
-/
lemma split_algebraMap_eq_zero_x {k : ℕ} (h_pos : k > 0) (x : ConcreteBTField (k - 1)) :
    letI instAlgebra := ConcreteBTFieldAlgebra (l:=k-1) (r:=k) (h_le:=by omega)
  split h_pos (algebraMap (ConcreteBTField (k - 1)) (ConcreteBTField k) x) = (0, x) := by
  -- this one is long because of the `cast` stuff, but it should be quite straightforward
  -- via def of `canonicalAlgMap` and `split_of_join`
  apply Eq.symm
  letI instAlgebra := ConcreteBTFieldAlgebra (l:=k-1) (r:=k) (h_le:=by omega)
  set mappedVal := algebraMap (ConcreteBTField (k - 1)) (ConcreteBTField k) x
  have h := split_of_join (k:=k) (h_pos:=by omega) (x:=mappedVal)
    (hi_btf:=zero (k:=k-1)) (lo_btf:=x)
  apply h
  -- ⊢ mappedVal = join h_pos zero x
  unfold mappedVal
  rw [algebraMap, Algebra.algebraMap]
  unfold instAlgebra ConcreteBTFieldAlgebra
  rw [AlgebraTower.toAlgebra, AlgebraTower.algebraMap, instAlgebraTowerConcreteBTF]
  simp only
  have h_concrete_embedding_succ_1 := concreteTowerAlgebraMap_succ_1 (k:=k-1)
  rw! (castMode:=.all) [Nat.sub_one_add_one (by omega)] at h_concrete_embedding_succ_1
  rw! (castMode:=.all) [h_concrete_embedding_succ_1]
  rw [eqRec_eq_cast]
  rw [ConcreteBTField.RingHom_cast_dest_apply (f:=canonicalAlgMap (k - 1))
    (x:=x) (h_eq:=by omega)]
  have h_k_sub_1_add_1 : k - 1 + 1 = k := by omega
  rw! (castMode:=.all) [h_k_sub_1_add_1]
  simp only [cast_eq]
  rw [eqRec_eq_cast]
  rw [ConcreteBTField.RingHom_cast_dest_apply (k:=k - 1) (m:=k - 1 + 1) (n:=k)
    (h_eq:=by omega) (f:=canonicalAlgMap (k - 1)) (x:=x)]
  simp only [canonicalAlgMap, concreteCanonicalEmbedding, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk]
  rw [cast_join (k:=k - 1 + 1) (h_pos:=by omega) (n:=k) (heq:=by omega)]
  simp only [Nat.add_one_sub_one, cast_eq, cast_cast]

lemma algebraMap_succ_eq_zero_x {k : ℕ} (h_pos : k > 0) (x : ConcreteBTField (k - 1)) :
    letI instAlgebra := ConcreteBTFieldAlgebra (l:=k-1) (r:=k) (h_le:=by omega)
  algebraMap (ConcreteBTField (k - 1)) (ConcreteBTField k) x = 《 0, x 》 := by
  apply join_of_split
  exact split_algebraMap_eq_zero_x h_pos x

lemma algebraMap_eq_zero_x {i j : ℕ} (h_le : i < j) (x : ConcreteBTField i) :
    letI instAlgebra := ConcreteBTFieldAlgebra (l:=i) (r:=j) (h_le:=by omega)
    letI instAlgebraPred := ConcreteBTFieldAlgebra (l:=i) (r:=j-1) (h_le:=by omega)
    algebraMap (ConcreteBTField i) (ConcreteBTField j) x
      = 《 0, algebraMap (ConcreteBTField i) (ConcreteBTField (j-1)) x 》 := by
  set d := j - i with d_eq
  induction hd : d with
  | zero =>
    have h_i_eq_j : i = j := by omega
    have h_i_ne_j : i ≠ j := by omega
    contradiction
  | succ d' => -- this one does not even use inductive hypothesis
    have h_j_eq : j = i + d' + 1 := by omega
    change (concreteTowerAlgebraMap (l:=i) (r:=j) (h_le:=by omega)) x =
      《 0, ((concreteTowerAlgebraMap (l:=i) (r:=j-1) (h_le:=by omega)) x) 》
    rw! [h_j_eq]
    rw [concreteTowerAlgebraMap_succ (l:=i) (r:=i+d') (h_le:=by omega)]
    simp only [RingHom.coe_comp, Function.comp_apply, Nat.add_one_sub_one]
    set r := concreteTowerAlgebraMap (l:=i) (r:=i+d') (h_le:=by omega) x with h_r
    have h := algebraMap_succ_eq_zero_x (k:=i+d'+1) (h_pos:=by omega) r
    simp only [Nat.add_one_sub_one] at h
    rw [←h]
    rfl

lemma split_smul_Z_eq_zero_x {k : ℕ} (h_pos : k > 0) (x : ConcreteBTField (k - 1)) :
    letI instAlgebra := ConcreteBTFieldAlgebra (l:=k-1) (r:=k) (h_le:=by omega)
  split h_pos (x • Z k) = (x, 0) := by
  letI instAlgebra := ConcreteBTFieldAlgebra (l:=k-1) (r:=k) (h_le:=by omega)
  change split h_pos ((algebraMap (ConcreteBTField (k - 1)) (ConcreteBTField k) x) * Z k) = (x, 0)
  have h_split_xLifted := split_algebraMap_eq_zero_x h_pos x
  have h_split_Z := split_Z h_pos
  set xLifted := algebraMap (ConcreteBTField (k - 1)) (ConcreteBTField k) x with h_xLifted
  -- ⊢ split h_pos (xLifted * Z k) = (0, x)
  -- {a₁ a₀ b₁ b₀ : ConcreteBTField (k - 1)},
  have hCBTF := (getBTFResult k)
  have hCBTFPrev := (getBTFResult (k-1))
  have h_x_mul_Z := hCBTF.mul_eq (k:=k) (a:=xLifted) (b:=Z k)
    (a₁:=0) (a₀:=x) (b₁:=1) (b₀:=0) (h_k := by omega)
    (by exact id (Eq.symm h_split_xLifted)) (by exact id (Eq.symm h_split_Z))
  rw! [←zero_is_0, ←one_is_1] at h_x_mul_Z
  rw! [hCBTFPrev.mul_zero, hCBTFPrev.add_zero, hCBTFPrev.mul_one, hCBTFPrev.zero_mul,
    hCBTFPrev.add_zero, hCBTFPrev.mul_zero, hCBTFPrev.zero_mul, hCBTFPrev.add_zero] at h_x_mul_Z
  -- h_x_mul_Z : concrete_mul xLifted (Z k) = join h_pos x zero => Very simplified already
  -- ⊢ split h_pos (xLifted * Z k) = (0, x)
  change split h_pos (concrete_mul xLifted (Z k)) = (x, 0)
  rw [h_x_mul_Z]
  rw [split_join_eq_split, zero_is_0]

lemma smul_Z_eq_zero_x {k : ℕ} (h_pos : k > 0) (x : ConcreteBTField (k - 1)) :
    letI instAlgebra := ConcreteBTFieldAlgebra (l:=k-1) (r:=k) (h_le:=by omega)
  x • Z k = 《 x, 0 》 := by
  apply join_of_split
  exact split_smul_Z_eq_zero_x h_pos x

@[simp]
theorem join_eq_join_via_add_smul {k : ℕ} (h_pos : k > 0)
    (hi_btf lo_btf : ConcreteBTField (k - 1)) :
    《 hi_btf, lo_btf 》 = join_via_add_smul k h_pos hi_btf lo_btf := by
  unfold join_via_add_smul
  set instAlgebra := ConcreteBTFieldAlgebra (l:=k-1) (r:=k) (h_le:=by omega)
  set hi_lifted := instAlgebra.2 hi_btf with h_hi_lifted
  -- First, show `hi_btf • Z k` corresponds to `join h_pos hi_btf 0`.
  have h_hi_term : hi_btf • Z k = 《 hi_btf, 0 》 := by
    apply join_of_split
    exact split_smul_Z_eq_zero_x h_pos hi_btf
  -- Second, show `algebraMap ... lo_btf` corresponds to `join h_pos 0 lo_btf`.
  have h_lo_term : algebraMap (ConcreteBTField (k-1))
    (ConcreteBTField k) lo_btf = 《 0, lo_btf 》 := by
    have h := join_of_split (x := algebraMap (ConcreteBTField (k-1)) (ConcreteBTField k) lo_btf)
      (h_pos:=by omega) (hi_btf:=zero (k:=k-1)) (lo_btf:=lo_btf)
    apply h
    rw [split_algebraMap_eq_zero_x h_pos lo_btf]
    rfl
  rw [h_hi_term, h_lo_term]
   -- ⊢ join h_pos hi_btf lo_btf = join h_pos hi_btf 0 + join h_pos 0 lo_btf
  rw [join_add_join h_pos hi_btf 0 0 lo_btf]
  simp only [_root_.add_zero, _root_.zero_add]

lemma split_join_via_add_smul_eq_iff_split {k : ℕ} (h_pos : k > 0)
    (hi_btf lo_btf : ConcreteBTField (k - 1)) :
    split (k:=k) (h:=by omega) (x:=join_via_add_smul (k:=k) (h_pos:=h_pos) hi_btf lo_btf) =
      (hi_btf, lo_btf) := by
  rw [split_of_join (k:=k) (h_pos:=h_pos)
    (x:=join_via_add_smul (k:=k) (h_pos:=h_pos) hi_btf lo_btf)]
  exact Eq.symm (join_eq_join_via_add_smul h_pos hi_btf lo_btf)

lemma ConcreteBTFieldAlgebra_def (l r : ℕ) (h_le : l ≤ r) :
    @ConcreteBTFieldAlgebra (l:=l) (r:=r) (h_le:=h_le)
    = (concreteTowerAlgebraMap l r h_le).toAlgebra := by rfl

lemma algebraMap_ConcreteBTFieldAlgebra_def (l r : ℕ) (h_le : l ≤ r) :
    (@ConcreteBTFieldAlgebra (l:=l) (r:=r) (h_le:=h_le)).algebraMap
    = concreteTowerAlgebraMap l r h_le := by rfl

lemma coe_one_succ (l : ℕ) :
    (@ConcreteBTFieldAlgebra (l:=l) (r:=l + 1) (h_le:=by omega)).algebraMap
    (1 : ConcreteBTField l) = (1 : ConcreteBTField (l + 1)) := by
  exact RingHom.map_one (ConcreteBTFieldAlgebra (l:=l) (r:=l + 1) (h_le:=by omega)).algebraMap

theorem unique_linear_decomposition_succ (k : ℕ) :
    letI : Algebra (ConcreteBTField k) (ConcreteBTField (k+1)) :=
    ConcreteBTFieldAlgebra (l:=k) (r:=k+1) (h_le:=by omega)
  ∀ (x : ConcreteBTField (k+1)), ∃! (p : ConcreteBTField k × ConcreteBTField k),
    x = join_via_add_smul (k+1) (by omega) p.1 p.2 := by
  intro x
  let h_split_x_raw := split (k:=k+1) (h:=by omega) x
  let hi_btf := h_split_x_raw.fst
  let lo_btf := h_split_x_raw.snd
  have h_split_x : split (k:=k+1) (h:=by omega) x = (hi_btf, lo_btf) := by rfl
  have h_join_x : 《 hi_btf, lo_btf 》 = x := by
    rw [join_of_split (by omega) x hi_btf lo_btf h_split_x]
  -- ⊢ ∃! p, x = p.1 • Z (k + 1) + (algebraMap (ConcreteBTField k) (ConcreteBTField (k + 1))) p.2
  use (hi_btf, lo_btf)
  simp only [Prod.forall, Prod.mk.injEq]
  constructor
  · have h_x_eq_if_join := join_eq_join_via_add_smul (k:=k+1)
      (h_pos:=by omega) hi_btf lo_btf
    rw [h_join_x.symm]
    exact h_x_eq_if_join
  · intro a b hx
    have hjoin_eq := join_eq_join_via_add_smul (k:=k+1) (h_pos:=by omega) (hi_btf:=a) (lo_btf:=b)
    rw [←hjoin_eq] at hx
    have h_split_a := split_of_join (k:=k+1) (h_pos:=by omega) (x:=x) (hi_btf:=a) (lo_btf:=b)
      (by exact hx)
    exact Prod.mk_inj.mp h_split_a

@[simp]
theorem ConcreteBTFieldAlgebra_id {l r : ℕ} (h_eq : l = r) :
    @ConcreteBTFieldAlgebra l r (h_le:=by omega) =
    (h_eq ▸ (Algebra.id (ConcreteBTField l)) :
      Algebra (ConcreteBTField l) (ConcreteBTField r)) := by
  subst h_eq
  simp only [ConcreteBTFieldAlgebra_def, concreteTowerAlgebraMap_id]
  rfl

theorem ConcreteBTFieldAlgebra_apply_assoc (l mid r : ℕ)
    (h_l_le_mid : l ≤ mid) (h_mid_le_r : mid ≤ r) :
    ∀ x : ConcreteBTField l,
    (@ConcreteBTFieldAlgebra (l:=l) (r:=r) (h_le:=by
      exact Nat.le_trans h_l_le_mid h_mid_le_r)).algebraMap x =
    (@ConcreteBTFieldAlgebra (l:=mid) (r:=r) (h_le:=h_mid_le_r)).algebraMap
      ((@ConcreteBTFieldAlgebra (l:=l) (r:=mid) (h_le:=h_l_le_mid)).algebraMap x) := by
  intro x
  simp_rw [algebraMap_ConcreteBTFieldAlgebra_def]
  rw [←RingHom.comp_apply]
  rw [concreteTowerAlgebraMap_assoc (l:=l) (mid:=mid) (r:=r)
    (h_l_le_mid:=h_l_le_mid) (h_mid_le_r:=h_mid_le_r)]

/-- This also provides the corresponding Module instance. -/
def binaryTowerModule {l r : ℕ} (h_le : l ≤ r) :
    Module (ConcreteBTField l) (ConcreteBTField r) :=
  (ConcreteBTFieldAlgebra (h_le:=h_le)).toModule

instance (priority := 1000) algebra_adjacent_tower (l : ℕ) :
  Algebra (ConcreteBTField l) (ConcreteBTField (l + 1)) := by
  exact ConcreteBTFieldAlgebra (h_le:=by omega)

lemma algebraMap_adjacent_tower_def (l : ℕ) :
    (algebraMap (ConcreteBTField l) (ConcreteBTField (l + 1))) =
    canonicalAlgMap l := by
  unfold algebra_adjacent_tower
  rw [ConcreteBTFieldAlgebra_def]
  exact concreteTowerAlgebraMap_succ_1 l

lemma aeval_definingPoly_at_Z_succ (k : ℕ) :
    (aeval (Z (k + 1))) (definingPoly (s:=Z (k))) = 0 := by
  rw [aeval_def]
  set f := algebraMap (ConcreteBTField k) (ConcreteBTField (k + 1))
  have h_f_is_canonical_embedding :
    f = concreteTowerAlgebraMap (l:=k) (r:=k+1) (h_le:=by omega) := by rfl
  rw [definingPoly, eval₂_add, eval₂_add] -- break down into sum of terms
  rw [eval₂_X_pow]
  rw [C_mul']
  -- ⊢ Z (k + 1) ^ 2 + eval₂ f (Z (k + 1)) (Z k • X) + eval₂ f (Z (k + 1)) 1 = 0
  simp only [eval₂_one, eval₂_smul, eval₂_X]
  -- Z_square_mul_form uses instAlgebraLiftConcreteBTField internally
  rw [Z_square_mul_form (k:=k) (prev:=(getBTFResult (k:=k)))]
  rw [add_assoc]
  rw [algebraMap, Algebra.algebraMap, instAlgebraLiftConcreteBTField]
  simp only
  -- f uses ConcreteBTFieldAlgebra, it's same as instAlgebraLiftConcreteBTField at step = 1
  rw [h_f_is_canonical_embedding, concreteTowerAlgebraMap_succ_1]
  simp only [canonicalAlgMap]; rw [mul_comm]
  rw [add_self_cancel]

end ConcreteBTFieldAlgebraConstruction

end ConcreteBinaryTower
