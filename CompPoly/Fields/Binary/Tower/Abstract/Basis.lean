/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import CompPoly.Fields.Binary.Tower.Abstract.Split

/-!
# Abstract Binary Tower Basis

Basis constructions and index-casting lemmas for abstract binary tower extensions.
-/

namespace BinaryTower

noncomputable section MultilinearBasis

open Polynomial
open AdjoinRoot
open Module

def hli_level_diff_0 (l : ℕ) :
    letI instAlgebra:= binaryAlgebraTower (l:=l) (r:=l) (h_le:=by omega)
  @Basis (Fin 1) (BTField l) (BTField l) _ _ instAlgebra.toModule:= by
  letI instAlgebra:= binaryAlgebraTower (l:=l) (r:=l) (h_le:=by omega)
  letI instModule:= instAlgebra.toModule
  apply @Basis.mk (ι:=Fin 1) (R:=BTField l) (M:=BTField l) _ _ instAlgebra.toModule (v:=fun _ => 1)
  · -- This proof now works smoothly.
    rw [Fintype.linearIndependent_iff (R:=BTField l) (v:=fun (_ : Fin 1) => (1 : BTField l))]
    intro g hg j
    -- ⊢ g i = 0
    unfold instModule at *
    unfold instAlgebra at *
    rw [binaryTowerAlgebra_id (by omega)] at *
    have hj : j = 0 := by omega
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      smul_eq_mul, Finset.sum_singleton] at hg -- hg : g 0 = 0 ∨ 1 = 0
    have h_one_ne_zero : (1 : BTField l) ≠ (0 : BTField l) := by
      exact BTFieldNeZero1 (k:=l).out
    simp only [BTField, BTFieldIsField, Fin.isValue] at hg
    rw [Subsingleton.elim j 0] -- j must be 0
    rw [hg.symm]
    exact Eq.symm (MulOneClass.mul_one (g 0))
  · rw [Set.range_const]
    have h : instAlgebra = Algebra.id (BTField l) := by
      unfold instAlgebra
      rw [binaryTowerAlgebra_id (by omega)]
    rw! [h] -- convert to Algebra.id for clear goal
    rw [Ideal.submodule_span_eq]
    rw [Ideal.span_singleton_one]

def BTField.isScalarTower_succ_right (l r : ℕ) (h_le : l ≤ r) :=
  instAlgebraTowerNatBTField.toIsScalarTower (i:=l) (j:=r) (k:=r+1)
  (h1:=by omega) (h2:=by omega)

/--
The multilinear basis for `BTField τ` over `BTField k` is the set of multilinear monomials
in the tower generators `Z(k+1), ..., Z(τ)`.
This is done via scalar tower multiplication of power basis across adjacent levels.
-/
def multilinearBasis (l r : ℕ) (h_le : l ≤ r) :
    letI instAlgebra : Algebra (BTField l) (BTField r) := binaryAlgebraTower (h_le:=h_le)
    Basis (Fin (2 ^ (r - l))) (BTField l) (BTField r) := by
  letI instAlgebra : Algebra (BTField l) (BTField r) := binaryAlgebraTower (h_le:=h_le)
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
    letI instAlgebraPrev : Algebra (BTField l) (BTField (r1)) :=
      binaryAlgebraTower (l:=l) (r:=r1) (h_le:=by omega)
    set prevMultilinearBasis : Basis (Fin (2 ^ (r1 - l))) (BTField l) (BTField r1) :=
      multilinearBasis (l:=l) (r:=r1) (h_le:=by omega)
    rw! [h_r1_sub_l] at prevMultilinearBasis
    letI instAlgebra : Algebra (BTField l) (BTField (r1 + 1)) :=
      binaryAlgebraTower (l:=l) (r:=r1 + 1) (h_le:=by omega)
    rw! [h_r_sub_l]
    apply Basis.reindex
      (e:=revFinProdFinEquiv (m:=2^(n')) (n:=2) (h_m:=by exact Nat.two_pow_pos n'))
    -- ⊢ Basis (Fin 2 × Fin (2 ^ n')) (BTField l) (BTField (r))
    have h_eq : l + (n' + 1) = (r1) + 1 := by rw [←add_assoc]
    letI instAlgebraSucc : Algebra (BTField (r1)) (BTField (r1 + 1)) := by
      exact algebra_adjacent_tower (r1)
    letI instModuleSucc : Module (BTField l) (BTField (r1 + 1)) := by
      exact instAlgebra.toModule
    letI : IsScalarTower (BTField l) (BTField (r1)) (BTField (r1 + 1)) := by
      exact BTField.isScalarTower_succ_right (l:=l) (r:=r1) (h_le:=by omega)
    have res := Basis.smulTower (ι:=Fin (2 ^ n')) (ι':=Fin (2)) (R:=BTField l)
      (S:=BTField (r1)) (A:=BTField (r1 + 1))
      (b:=by
        convert prevMultilinearBasis;
      ) (c:=by
        convert (powerBasisSucc (r1)).basis
        rw [powerBasisSucc_dim (k:=r1)]
      )
    convert res
    -- Basis are equal under the same @binaryAlgebraTower
    -- ⊢ Basis (Fin (2 ^ n') × Fin 2) (BTField l) (BTField r)
    -- = Basis (Fin (2 ^ n') × Fin 2) (BTField l) (BTField (r1 + 1))
    unfold instModuleSucc -- Module used in rhs
    rw! [h_r]
    rfl

@[simp]
theorem BTField.PowerBasis.dim_of_eq_rec
    (r1 r : ℕ)
    (h_r : r = r1 + 1)
    (b : PowerBasis (BTField r1) (BTField (r1 + 1))) :
    letI instAlgebra : Algebra (BTField r1) (BTField r) :=
      binaryAlgebraTower (l:=r1) (r:=r) (h_le:=by omega)
    ((Eq.rec (motive:=fun (x : ℕ) (_ : r1 + 1 = x) => by
      letI instAlgebraCur : Algebra (BTField r1) (BTField x) :=
        binaryAlgebraTower (l:=r1) (r:=x) (h_le:=by omega)
      exact PowerBasis (BTField r1) (BTField x)) (refl:=b) (t:=h_r.symm)) :
        PowerBasis (BTField r1) (BTField r)).dim
    = b.dim := by
  subst h_r
  rfl

@[simp]
theorem PowerBasis.cast_basis_succ_of_eq_rec_apply
    (r1 r : ℕ) (h_r : r = r1 + 1)
    (k : Fin 2) :
    letI instAlgebra : Algebra (BTField r1) (BTField r) :=
      binaryAlgebraTower (l:=r1) (r:=r) (h_le:=by omega)
    letI instAlgebraSucc : Algebra (BTField (r1 + 1)) (BTField (r)) :=
      binaryAlgebraTower (l:=r1 + 1) (r:=r) (h_le:=by omega)
    let b : PowerBasis (BTField r1) (BTField (r1 + 1)) := powerBasisSucc (k:=r1)
    let bCast : PowerBasis (BTField r1) (BTField r) := Eq.rec (motive:=
      fun (x : ℕ) (_ : r1 + 1 = x) => by
        letI instAlgebraCur : Algebra (BTField r1) (BTField x) :=
          binaryAlgebraTower (l:=r1) (r:=x) (h_le:=by omega)
        exact PowerBasis (BTField r1) (BTField x)) (refl:=b) (t:=h_r.symm)
    have h_pb_dim : b.dim = 2 := by
      exact powerBasisSucc_dim r1

    have h_pb'_dim : bCast.dim = 2 := by
      dsimp [bCast]
      rw [BTField.PowerBasis.dim_of_eq_rec (r1:=r1) (r:=r) (h_r:=h_r) (b:=b)]
      exact h_pb_dim

    have h_pb_type_eq : Basis (Fin bCast.dim) (BTField r1) (BTField r) =
      Basis (Fin 2) (BTField r1) (BTField r) := by
      congr

   -- The `cast` needs a proof that `bCast.dim = 2`. We construct it here.
    let left : Basis (Fin 2) (BTField r1) (BTField r) := cast (by exact h_pb_type_eq) bCast.basis
    let right := (algebraMap (BTField (r1 + 1)) (BTField r))
      (b.basis (Fin.cast h_pb_dim.symm k))
    left k = right := by
  -- The proof of the theorem itself remains simple.
  subst h_r
  simp only [binaryTowerAlgebra_id,
    Algebra.algebraMap_self, PowerBasis.coe_basis, Fin.val_cast, RingHom.id_apply]
  rw [BTField.Basis_cast_index_apply (h_eq:=by exact powerBasisSucc_dim r1) (h_le:=by omega)]
  simp only [PowerBasis.coe_basis, Fin.val_cast]

/-- When two indices are equal, the tower algebra maps send the respective 𝕏 to the same element. -/
lemma algebraMap_𝕏_eq_of_index_eq (r k m : ℕ) (h_k_le : k + 1 ≤ r) (h_m_le : m + 1 ≤ r)
    (h_eq : k = m) :
    letI := binaryAlgebraTower (l := k + 1) (r := r) (h_le := h_k_le)
    letI := binaryAlgebraTower (l := m + 1) (r := r) (h_le := h_m_le)
    (Algebra.algebraMap (𝕏 k) : BTField r) = (Algebra.algebraMap (𝕏 m) : BTField r) := by
  subst h_eq
  rfl

/-!
The basis element at index `j` is the product of the tower generators at
the ON bits in binary representation of `j`.
-/
set_option maxHeartbeats 350000
theorem multilinearBasis_apply (r : ℕ) : ∀ l : ℕ, (h_le : l ≤ r) → ∀ (j : Fin (2  ^ (r - l))),
    multilinearBasis (l:=l) (r:=r) (h_le:=h_le) j =
    (Finset.univ : Finset (Fin (r - l))).prod (fun i =>
      (binaryAlgebraTower (l:=l + i + 1) (r:=r) (h_le:=by omega)).algebraMap (
        (𝕏 (l + i)) ^ (Nat.getBit i j))) := by
  induction r with
  | zero => -- Fin (2^0) = Fin 1, so j = 0
    intro l h_l_le_0 j
    simp only [zero_tsub, pow_zero] at j
    have h_l_eq_r : l = 0 := by omega
    subst h_l_eq_r
    simp only [Nat.sub_zero, Nat.pow_zero, Finset.univ_eq_empty,
      𝕏, Z, Fin.val_eq_zero, Finset.prod_empty]
    have hj_eq_0 : j = 0 := by exact Fin.eq_of_val_eq (by omega)
    rw! [hj_eq_0]
    rw [multilinearBasis]
    simp only [tsub_self, ↓reduceDIte, Nat.sub_zero, Nat.pow_zero, Fin.isValue]
    rw [hli_level_diff_0]
    simp only [eq_mp_eq_cast, cast_eq, Fin.isValue, Basis.coe_mk]
  | succ r1 ih_r1 =>
    set r := r1 + 1 with hr
    intro l h_l_le_r j
    haveI instAlgebraR : Algebra (BTField r) (BTField r) :=
      binaryAlgebraTower (l:=r) (r:=r) (h_le:=by omega)
    haveI instModuleR : Module (BTField r) (BTField r) := instAlgebraR.toModule
    if h_r_sub_l : r - l = 0 then
      rw [multilinearBasis]
      have h_l_eq_r : l = r := by omega
      subst h_l_eq_r
      simp only [tsub_self, ↓reduceDIte, Nat.pow_zero,
        hli_level_diff_0, eq_mp_eq_cast, cast_eq]
      have h1 : 1 = 2 ^ (r - r) := by rw [Nat.sub_self, Nat.pow_zero];
      have h_r_sub_r : r - r = 0 := by omega
      rw [←Fin.prod_congr' (b:=r-r) (a:=0) (h:=by omega), Fin.prod_univ_zero]
      rw [BTField.Basis_cast_index_apply (h_eq:=by omega) (h_le:=by omega)]
      simp only [Basis.coe_mk]
    else
      rw [multilinearBasis]
      -- key to remove Eq.rec : dif_neg h_r_sub_l
      simp only [Nat.pow_zero, eq_mp_eq_cast, cast_eq,
        eq_mpr_eq_cast, dif_neg h_r_sub_l]
      have h2 : 2 ^ (r - l - 1) * 2 = 2 ^ (r - l) := by
        rw [←Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
      rw [BTField.Basis_cast_index_apply (h_eq:=by omega) (h_le:=by omega)]
      simp only [Basis.coe_reindex, Function.comp_apply,
        revFinProdFinEquiv_symm_apply]
      rw [BTField.Basis_cast_dest_apply (h_eq:=by omega) (h_le1:=by omega) (h_le2:=by omega)]

      set prevDiff := r - l - 1 with h_prevDiff
      have h_r_sub_l : r - l = prevDiff + 1 := by omega
      have h_r1_sub_l : r1 - l = prevDiff := by omega
      have h_r1_eq_l_plus_prevDiff : r1 = l + prevDiff := by omega
      have h_r : r = r1 + 1 := by omega
      have h1 : l + (r - l - 1) = r1 := by omega
      letI instAlgebraPrev : Algebra (BTField l) (BTField (r1)) :=
        binaryAlgebraTower (l:=l) (r:=r1) (h_le:=by omega)
      set prevMultilinearBasis : Basis (Fin (2 ^ (r1 - l))) (BTField l) (BTField r1) :=
        multilinearBasis (l:=l) (r:=r1) (h_le:=by omega) with h_prevMultilinearBasis
      rw! [h_r1_sub_l] at prevMultilinearBasis
      letI instAlgebra : Algebra (BTField l) (BTField (r1 + 1)) :=
        binaryAlgebraTower (l:=l) (r:=r1 + 1) (h_le:=by omega)
      rw! (castMode:=.all) [h1]

      letI instAlgebraSucc : Algebra (BTField (r1)) (BTField (r1 + 1)) := by
        exact algebra_adjacent_tower (r1)
      letI instModuleSucc : Module (BTField l) (BTField (r1 + 1)) := by
        exact instAlgebra.toModule

      letI : IsScalarTower (BTField l) (BTField (r1)) (BTField (r1 + 1)) := by
        exact BTField.isScalarTower_succ_right (l:=l) (r:=r1) (h_le:=by omega)
      rw [Basis.smulTower_apply]
      rw [Algebra.smul_def]
      rw [BTField.cast_mul (m:=r1 + 1) (n:=r) (h_eq:=by omega)]
      rw! (castMode:=.all) [h_r.symm]
      rw [cast_eq, cast_eq]

      letI instAlgebra2 : Algebra (BTField r1) (BTField r) :=
        binaryAlgebraTower (l:=r1) (r:=r) (h_le:=by omega)
      letI instModule2 : Module (BTField r1) (BTField r) := instAlgebra2.toModule
      set b := (powerBasisSucc r1) with hb
      rw! [←hb]
      have h : (2 ^ (r1 - l)) = (2 ^ (r - l - 1)) := by
        rw [h_r]
        rw [Nat.sub_right_comm, Nat.add_sub_cancel r1 1]
      rw [BTField.Basis_cast_index_apply (h_eq:=h) (h_le:=by omega)]
      simp only [leftDivNat, Fin.val_cast]

      set indexLeft : Fin 2 := ⟨j.val / 2 ^ (r - l - 1), by
        change j.val / 2 ^ (r - l - 1) < 2^1
        apply div_two_pow_lt_two_pow (x:=j.val) (i:=1) (j:=r-l-1) (h_x_lt_2_pow_i:=by
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
        rw [powerBasisSucc_gen, ←𝕏] -- convert to gen^i form
        rw [ih_r1 (l:=l) (h_le:=by omega)] -- inductive hypothesis of level r - 1
        rw [Fin.cast_val_eq_val (h_eq:=by omega)]

      conv_rhs =>
        rw [←Fin.prod_congr' (b:=r-l) (a:=prevDiff + 1) (h:=by omega)]
        rw [Fin.prod_univ_castSucc] -- split the prod of rhs
        simp only [Fin.val_cast, Fin.val_castSucc, Fin.val_last]

      simp_rw [algebraMap.coe_pow] -- rhs
      simp_rw [algebraMap.coe_prod] -- lhs
      unfold Algebra.cast
      rw! (castMode:=.all) [←algebraMap]
      conv_lhs =>
        rw [←Fin.prod_congr' (b:=r1-l) (a:=prevDiff) (h:=by omega)]
        simp only [Fin.val_cast]
      simp_rw [algebraMap, instAlgebraSucc, algebra_adjacent_tower]
      rw [RingHom.map_pow]
      simp_rw [←binaryTowerAlgebra_apply_assoc]
      ------------------ Equality of bit-based powers of generators -----------------
      --- The outtermost term
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

end MultilinearBasis

end BinaryTower
