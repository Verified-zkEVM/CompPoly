/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import CompPoly.Fields.Binary.Tower.Support.IrreducibilityAndTraceMapProperty
import CompPoly.Data.RingTheory.AlgebraTower
import Mathlib.Tactic.DepRewrite

namespace BinaryTower

noncomputable section

open Polynomial
open AdjoinRoot
open Module

section BTFieldDefs

structure BinaryTowerResult (F : Type _) (k : ℕ) where
  vec : (List.Vector F (k + 1))
  instField : (Field F)
  instFintype : Fintype F
  specialElement : F
  specialElementNeZero : NeZero specialElement
  firstElementOfVecIsSpecialElement [Inhabited F] : vec.1.headI = specialElement
  instIrreduciblePoly : (Irreducible (p := (definingPoly specialElement)))
  sumZeroIffEq : ∀ (x y : F), x + y = 0 ↔ x = y
  fieldFintypeCard : Fintype.card F = 2^(2^k)
  traceMapEvalAtRootsIs1 : TraceMapProperty F specialElement k

structure BinaryTowerInductiveStepResult (k : ℕ) (prevBTField : Type _)
  (prevBTResult : BinaryTowerResult prevBTField k) [instPrevBTFieldIsField : Field prevBTField]
  (prevPoly : Polynomial prevBTField) (F : Type _) where
  binaryTowerResult : BinaryTowerResult F (k+1)
  eq_adjoin : F = AdjoinRoot prevPoly
  u_is_root : Eq.mp (eq_adjoin) binaryTowerResult.specialElement = AdjoinRoot.root prevPoly
  eval_defining_poly_at_root : Eq.mp (eq_adjoin) binaryTowerResult.specialElement^2 +
    Eq.mp (eq_adjoin) binaryTowerResult.specialElement * (of prevPoly) prevBTResult.specialElement
    + 1 = 0

set_option maxHeartbeats 1000000 in
-- it takes more heartbeats to prove this theorem
def binary_tower_inductive_step
    (k : Nat)
  (prevBTField : Type _) [Field prevBTField]
  (prevBTResult : BinaryTowerResult prevBTField k) :
  Σ' (F : Type _), BinaryTowerInductiveStepResult (k:=k) (prevBTField:=prevBTField)
  (prevBTResult:=prevBTResult) (prevPoly:=definingPoly (F:=prevBTField)
    (instField:=prevBTResult.instField) (s:=prevBTResult.specialElement)) (F:=F)
  (instPrevBTFieldIsField:=prevBTResult.instField) := by
  letI := prevBTResult.instField
  letI := prevBTResult.instFintype
  let elts := prevBTResult.vec
  set t1 : prevBTField := prevBTResult.specialElement
  letI inst_t1_NeZero : NeZero t1 := prevBTResult.specialElementNeZero
  have t1_ne_zero_in_prevBTField : t1 ≠ 0 := inst_t1_NeZero.out
  set prevPoly := definingPoly t1
  let prevPolyDegIs2 : prevPoly.degree = 2 := degree_definingPoly t1
  let prevPolyNatDegIs2 := natDegree_definingPoly t1
  let prevPolyIsMonic : (Monic prevPoly) := definingPoly_is_monic t1
  let prevPolyNeZero := prevPolyIsMonic.ne_zero
  have degPrevPolyNe0 : prevPoly.degree ≠ 0 := by
    intro h_deg_eq_0
    rw [prevPolyDegIs2] at h_deg_eq_0
    contradiction
  let instPrevPolyIrreducible := prevBTResult.instIrreduciblePoly
  let prevBTFieldCard : Fintype.card prevBTField = 2^(2^k) := prevBTResult.fieldFintypeCard
  let instFactIrrPoly : Fact (Irreducible prevPoly) :=
    ⟨instPrevPolyIrreducible⟩ -- used for AdjoinRoot.instField
  let sumZeroIffEqPrevBTField : ∀ (x y : prevBTField), x + y = (0 : prevBTField)
    ↔ x = y := by exact prevBTResult.sumZeroIffEq
  let curBTField := AdjoinRoot prevPoly -- BTF(k) ≈ GF(2^(2^(k+1)))
  let instFieldAdjoinRootOfPoly : Field curBTField := by
    exact AdjoinRoot.instField (f := prevPoly)
  -- Lift to new BTField level
  let u : curBTField := AdjoinRoot.root prevPoly -- adjoined root and generator of curBTField
  let adjoinRootOfPoly : AdjoinRoot prevPoly = curBTField := by
    simp only [curBTField]
  have u_is_inv_of_u1 : u = u⁻¹⁻¹ := (inv_inv u).symm
  let newElts := elts.map (fun x => (AdjoinRoot.of prevPoly).toFun x)

  have unique_linear_form_of_elements_in_curBTField : ∀ (c1 : AdjoinRoot prevPoly),
    ∃! (p : prevBTField × prevBTField),
    c1 = (of prevPoly) p.1 * root prevPoly + (of prevPoly) p.2 :=
    unique_linear_form_of_elements_in_adjoined_commring
        (hf_deg := prevPolyNatDegIs2) (hf_monic := prevPolyIsMonic)

  have selfSumEqZero : ∀ (x : curBTField), x + x = 0 := self_sum_eq_zero
    (sumZeroIffEqPrevBTField) (prevPoly) (prevPolyNatDegIs2) (prevPolyIsMonic)

  have sumZeroIffEq : ∀ (x y : curBTField), x + y = 0 ↔ x = y :=
    sum_zero_iff_eq_of_self_sum_zero (selfSumEqZero)

  have u_is_root : u = AdjoinRoot.root prevPoly := rfl
  have h_eval : ∀ (x : curBTField), eval₂ (of prevPoly) x (X^2 + (C t1 * X + 1)) =
    x^2 + (of prevPoly) t1 * x + 1 := eval₂_quadratic_prevField_coeff (of_prev := of prevPoly) t1

  have eval_prevPoly_at_root : u^2 + (of prevPoly) t1 * u + 1 = 0 := by -- u^2 + t1 * u + 1 = 0
      have h_root : eval₂ (of prevPoly) u prevPoly = 0 := by
        rw [u_is_root]
        exact eval₂_root prevPoly
      have h_expand : eval₂ (of prevPoly) u (X^2 + (C t1 * X + 1)) = 0 := by
        rw [←add_assoc]
        change eval₂ (of prevPoly) u (definingPoly (F:=prevBTField) (s:=t1)) = 0
        exact h_root
      rw [h_eval u] at h_expand
      exact h_expand
  have h_u_square : u^2 = u*t1 + 1 := by
    have h1 := eval_prevPoly_at_root
    rw [←add_right_inj (u^2), ←add_assoc, ←add_assoc] at h1
    rw [selfSumEqZero (u^2), zero_add, add_zero, mul_comm] at h1
    exact h1.symm
  have one_ne_zero : (1 : curBTField) ≠ (0 : curBTField) := by exact NeZero.out
  have specialElementNeZero : u ≠ 0 := by
    by_contra h_eq
    rw [h_eq] at eval_prevPoly_at_root
    have two_pos : 2 ≠ 0 := by norm_num
    rw [zero_pow two_pos, mul_zero, zero_add, zero_add] at eval_prevPoly_at_root
    exact one_ne_zero eval_prevPoly_at_root
  letI inst_u_NeZero : NeZero u := { out := specialElementNeZero }
    -- Step 2 : transform the equations in curBTField and create new value equalitiy bounds
    -- (1) c1 + c2 = (a + c) * u + (b + d) = u
    -- <=> u * (1 - a - c) = b + d
  have u_plus_u1_eq_t1 : u + u⁻¹ = t1 := sum_of_root_and_inverse_is_t1 (u:=u)
    (t1:=(of prevPoly) t1) (specialElementNeZero)
    (eval_prevPoly_at_root) (sumZeroIffEq)

  let f : curBTField → prevBTField × prevBTField := fun c1 =>
    let h := unique_linear_form_of_elements_in_curBTField c1  -- Get the unique existential proof
    Classical.choose h

  have inj_f : Function.Injective f := by
    intros c1 c2 h_eq
    unfold f at h_eq
    -- h_eq is now (a1, b1) = (a2, b2), where a1, b1, a2, b2 are defined with Classical.choose
    let h1 := unique_linear_form_of_elements_in_curBTField c1
    let h2 := unique_linear_form_of_elements_in_curBTField c2
    let a1 := (Classical.choose h1).1
    let b1 := (Classical.choose h1).2
    let a2 := (Classical.choose h2).1
    let b2 := (Classical.choose h2).2
    -- Assert that h_eq matches the pair equality
    have pair_eq : (a1, b1) = (a2, b2) := h_eq
    have ha : a1 = a2 := (Prod.ext_iff.mp pair_eq).1
    have hb : b1 = b2 := (Prod.ext_iff.mp pair_eq).2
    have h1_eq : c1 = (of prevPoly) a1 * root prevPoly + (of prevPoly) b1 :=
      (Classical.choose_spec h1).1
    have h2_eq : c2 = (of prevPoly) a2 * root prevPoly + (of prevPoly) b2 :=
      (Classical.choose_spec h2).1
    rw [h1_eq, h2_eq, ha, hb]

  have surj_f : Function.Surjective f := by
    intro (p : prevBTField × prevBTField)
    let c1 := (of prevPoly) p.1 * root prevPoly + (of prevPoly) p.2
    use c1
    have h_ex : c1 = (of prevPoly) p.1 * root prevPoly + (of prevPoly) p.2 := rfl
    have h_uniq := unique_linear_form_of_elements_in_curBTField c1
    have p_spec : c1 = (of prevPoly) p.1 * root prevPoly + (of prevPoly) p.2 := h_ex
    -- Show that f c1 = p by using the uniqueness property
    have h_unique := (Classical.choose_spec h_uniq).2 p p_spec
    -- The function f chooses the unique representation, so f c1 must equal p
    exact h_unique.symm

  have bij_f : Function.Bijective f := by
    constructor
    · exact inj_f  -- Injectivity from instFintype
    · exact surj_f

  have equivRelation : curBTField ≃ prevBTField × prevBTField := by
    exact Equiv.ofBijective (f := f) (hf := bij_f)

  let instFintype : Fintype curBTField := by
    exact Fintype.ofEquiv (prevBTField × prevBTField) equivRelation.symm

  let fieldFintypeCard : Fintype.card curBTField = 2^(2^(k + 1)) := by
    let e : curBTField ≃ prevBTField × prevBTField := Equiv.ofBijective f bij_f
    -- ⊢ Fintype.card curBTField = 2 ^ 2 ^ (k + 1)
    have equivCard := Fintype.ofEquiv_card equivRelation.symm
    rw [Fintype.card_prod] at equivCard
    rw [prevBTFieldCard] at equivCard -- equivCard : Fintype.card curBTField = 2 ^ 2 ^ k * 2 ^ 2 ^ k
    have card_simp : 2 ^ 2 ^ k * 2 ^ 2 ^ k = 2 ^ (2 ^ k + 2 ^ k) := by rw [Nat.pow_add]
    have exp_simp : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
      rw [←Nat.mul_two, Nat.pow_succ]
    rw [card_simp, exp_simp] at equivCard
    exact equivCard

  let newPoly : curBTField[X] := definingPoly (F:=curBTField) (s:=u)

  have traceMapEvalAtRootsIs1 := traceMapProperty_of_quadratic_extension
    (F_prev:=prevBTField) (t1:=t1) (k:=k)
    (fintypeCardPrev:=prevBTResult.fieldFintypeCard)
    (F_cur:=curBTField) (u:=u) (h_rel:= {
      sum_inv_eq := u_plus_u1_eq_t1
      h_u_square := h_u_square
    }) (prev_trace_map := prevBTResult.traceMapEvalAtRootsIs1) (sumZeroIffEq := sumZeroIffEq)

  letI : CharP curBTField 2 := charP_eq_2_of_add_self_eq_zero (F:=curBTField)
    (sumZeroIffEq:=sumZeroIffEq)
  let instIrreduciblePoly : Irreducible newPoly :=
    irreducible_quadratic_defining_poly_of_traceMap_eq_1 (F:=curBTField) (s:=u) (k:=k+1)
      (trace_map_prop := traceMapEvalAtRootsIs1) (fintypeCard := fieldFintypeCard)
  let newVec := u ::ᵥ newElts
  let firstElementOfVecIsSpecialElement : newVec.1.headI = u := rfl
  let btResult : BinaryTowerResult curBTField (k + 1) := {
    vec := newVec,
    instField := instFieldAdjoinRootOfPoly,
    firstElementOfVecIsSpecialElement := firstElementOfVecIsSpecialElement,
    instIrreduciblePoly := instIrreduciblePoly,
    sumZeroIffEq := sumZeroIffEq,
    specialElement := u,
    specialElementNeZero := inst_u_NeZero,
    instFintype := instFintype,
    fieldFintypeCard := fieldFintypeCard,
    traceMapEvalAtRootsIs1 := traceMapEvalAtRootsIs1
  }

  rw [←mul_comm] at eval_prevPoly_at_root

  let btInductiveStepResult : BinaryTowerInductiveStepResult (k:=k) (prevBTField:=prevBTField)
    (prevBTResult:=prevBTResult) (prevPoly:=definingPoly t1)
    (F:=curBTField) (instPrevBTFieldIsField:=prevBTResult.instField) := {
    binaryTowerResult := btResult,
    eq_adjoin := adjoinRootOfPoly
    u_is_root := u_is_root,
    eval_defining_poly_at_root := eval_prevPoly_at_root
  }

  exact ⟨curBTField, btInductiveStepResult⟩

def BinaryTowerAux (k : ℕ) : (Σ' (F : Type 0), BinaryTowerResult F k) :=
  match k with
  | 0 => -- Base Case : k = 0
    let curBTField := GF(2)
    let newList : List.Vector (GF(2)) 1 := List.Vector.cons (1 : GF(2)) List.Vector.nil
    let specialElement : GF(2) := newList.1.headI
    let firstElementOfVecIsSpecialElement : newList.1.headI = specialElement := rfl
    let specialElementIs1 : specialElement = 1 := by
      unfold specialElement
      rfl
    let specialElementNeZero : NeZero specialElement := {
      out := by
        rw [specialElementIs1]
        norm_num
    }
    let newPoly : curBTField[X] := definingPoly (F:=curBTField) (s:=specialElement)
    have nat_deg_poly_is_2 : newPoly.natDegree = 2 := natDegree_definingPoly specialElement
    have coeffOfX_0 : newPoly.coeff 0 = 1 := definingPoly_coeffOf0 specialElement
    have coeffOfX_1 : newPoly.coeff 1 = specialElement := definingPoly_coeffOf1 specialElement

    let instIrreduciblePoly : Irreducible newPoly := by
      by_contra h_not_irreducible
      -- ¬Irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂
      obtain ⟨c₁, c₂, h_mul, h_add⟩ :=
        (Monic.not_irreducible_iff_exists_add_mul_eq_coeff
          (definingPoly_is_monic specialElement) (nat_deg_poly_is_2)).mp h_not_irreducible
      rw [coeffOfX_0] at h_mul -- 1 = c₁ * c₂
      rw [coeffOfX_1] at h_add -- specialElement = c₁ + c₂
      -- since c₁, c₂ ∈ GF(2), c₁ * c₂ = 1 => c₁ = c₂ = 1
      have c1_c2_eq_one : c₁ = 1 ∧ c₂ = 1 := by
        -- In GF(2), elements are only 0 or 1
        have c1_cases : c₁ = 0 ∨ c₁ = 1 := by exact GF_2_value_eq_zero_or_one c₁
        have c2_cases : c₂ = 0 ∨ c₂ = 1 := by exact GF_2_value_eq_zero_or_one c₂

        -- Case analysis on c₁ and c₂
        rcases c1_cases with c1_zero | c1_one
        · -- If c₁ = 0
          rw [c1_zero] at h_mul
          -- Then 0 * c₂ = 1, contradiction
          simp at h_mul
        · -- If c₁ = 1
          rcases c2_cases with c2_zero | c2_one
          · -- If c₂ = 0
            rw [c2_zero] at h_mul
            -- Then 1 * 0 = 1, contradiction
            simp at h_mul
          · -- If c₂ = 1
            -- Then we have our result
            exact ⟨c1_one, c2_one⟩

      -- Now we can show specialElement = 0
      have specialElement_eq_zero : specialElement = 0 := by
        rw [h_add]  -- Use c₁ + c₂ = specialElement
        rw [c1_c2_eq_one.1, c1_c2_eq_one.2]  -- Replace c₁ and c₂ with 1
        -- In GF(2), 1 + 1 = 0
        apply GF_2_one_add_one_eq_zero

      -- But we know specialElement = 1
      have specialElement_eq_one : specialElement = 1 := by
        unfold specialElement
        simp [newList]

      rw [specialElement_eq_zero] at specialElement_eq_one
      -- (0 : GF(2)) = (1 : GF(2))

      have one_ne_zero_in_gf2 : (1 : GF(2)) ≠ (0 : GF(2)) := by
        exact NeZero.out
      contradiction

    let sumZeroIffEq : ∀ (x y : GF(2)), x + y = 0 ↔ x = y := by
      intro x y
      constructor
      · -- (→) If x + y = 0, then x = y
        intro h_sum_zero
        -- Case analysis on x
        rcases GF_2_value_eq_zero_or_one x with x_zero | x_one
        · -- Case x = 0
          rcases GF_2_value_eq_zero_or_one y with y_zero | y_one
          · -- Case y = 0
            rw [x_zero, y_zero]
          · -- Case y = 1
            rw [x_zero, y_one] at h_sum_zero
            -- 0 + 1 = 0
            simp at h_sum_zero
        · -- Case x = 1
          rcases GF_2_value_eq_zero_or_one y with y_zero | y_one
          · -- Case y = 0
            rw [x_one, y_zero] at h_sum_zero
            -- 1 + 0 = 0
            simp at h_sum_zero
          · -- Case y = 1
            rw [x_one, y_one]
      · -- (←) If x = y, then x + y = 0
        intro h_eq
        rw [h_eq]
        -- In GF(2), x + x = 0 for any x
        rcases GF_2_value_eq_zero_or_one y with y_zero | y_one
        · rw [y_zero]
          simp
        · rw [y_one]
          exact GF_2_one_add_one_eq_zero
    let instFintype : Fintype (GF(2)) := GF_2_fintype
    let fieldFintypeCard : Fintype.card (GF(2)) = 2^(2^0) := by exact GF_2_card
    have traceMapEvalAtRootsIs1 : (∑ i ∈ Finset.range (2^0), specialElement^(2^i)) = 1
      ∧ (∑ i ∈ Finset.range (2^0), (specialElement⁻¹)^(2^i)) = 1 := by
      constructor
      · -- Prove first part : (∑ i ∈ Finset.range (2^0), specialElement^(2^i)) = 1
        rw [Nat.pow_zero] -- 2^0 = 1
        rw [Finset.range_one] -- range 1 = {0}
        rw [specialElementIs1] -- specialElement = 1
        norm_num
      · -- Prove second part : (∑ i ∈ Finset.range (2^0), (specialElement⁻¹)^(2^i)) = 1
        rw [Nat.pow_zero] -- 2^0 = 1
        simp [Finset.range_one] -- range 1 = {0}
        exact specialElementIs1

    let result : BinaryTowerResult curBTField 0 :={
      vec := newList,
      instField := inferInstance,
      specialElement := specialElement,
      specialElementNeZero := specialElementNeZero,
      firstElementOfVecIsSpecialElement := firstElementOfVecIsSpecialElement,
      instIrreduciblePoly := instIrreduciblePoly,
      sumZeroIffEq := sumZeroIffEq,
      instFintype := instFintype,
      fieldFintypeCard := fieldFintypeCard,
      traceMapEvalAtRootsIs1 := ⟨traceMapEvalAtRootsIs1.1, traceMapEvalAtRootsIs1.2⟩
    }

    ⟨ curBTField, result ⟩
  | k + 1 => by
    let prev := BinaryTowerAux (k:=k)
    let prevBTResult := prev.2
    let instPrevBTield := prevBTResult.instField
    let inductive_result := binary_tower_inductive_step (k:=k)
      (prevBTField:=prev.fst) (prevBTResult:=prev.snd)
    let res : (F : Type) ×' BinaryTowerResult F (k + 1) :=
      ⟨ inductive_result.fst, inductive_result.snd.binaryTowerResult ⟩
    exact res

@[simp]
def BTField (k : ℕ) := (BinaryTowerAux k).1

lemma BTField_is_BTFieldAux (k : ℕ) :
    BTField k = (BinaryTowerAux k).1 := by
  unfold BTField
  rfl

instance BTFieldIsField (k : ℕ) : Field (BTField k) := (BinaryTowerAux k).2.instField

instance CommRing (k : ℕ) : CommRing (BTField k) := Field.toCommRing

instance Nontrivial (k : ℕ) : Nontrivial (BTField k) := Field.toNontrivial

instance Inhabited (k : ℕ) : Inhabited (BTField k) where
  default := (0 : BTField k)

instance {k : ℕ} : _root_.Inhabited (BinaryTowerAux k).fst := by
  change _root_.Inhabited (BTField k)
  exact Inhabited k

instance BTFieldNeZero1 (k : ℕ) : NeZero (1 : BTField k) := by
  unfold BTField
  exact @neZero_one_of_nontrivial_comm_monoid_zero (BTField k) _ (Nontrivial k)

instance BTField_Fintype (k : ℕ) : Fintype (BTField k) := (BinaryTowerAux k).2.instFintype

@[simp]
def BTFieldCard (k : ℕ) : Fintype.card (BTField k) = 2^(2^k) :=
  (BinaryTowerAux k).2.fieldFintypeCard

instance BTFieldIsDomain (k : ℕ) : IsDomain (BTField k) := inferInstance

instance BTFieldNoZeroDiv (k : ℕ) : NoZeroDivisors (BTField k) := by
  unfold BTField
  infer_instance

@[simp]
def sumZeroIffEq (k : ℕ) : ∀ (x y : BTField k),
    x + y = 0 ↔ x = y := (BinaryTowerAux k).2.sumZeroIffEq

instance BTFieldChar2 (k : ℕ) : CharP (BTField k) 2 :=
  charP_eq_2_of_add_self_eq_zero (sumZeroIffEq:=sumZeroIffEq k)

@[simp]
theorem BTField_0_is_GF_2 : (BTField 0) = (GF(2)) := by
  unfold BTField
  rw [BinaryTowerAux]

@[simp]
def list (k : ℕ) : List.Vector (BTField k) (k + 1) := (BinaryTowerAux k).2.vec

/-- Z k is the generator of BTField k -/
@[simp]
def Z (k : ℕ) : BTField k := (BinaryTowerAux k).snd.specialElement -- (list k).1.headI

instance {k : ℕ} : NeZero (Z k) := (BinaryTowerAux k).snd.specialElementNeZero

@[simp]
def poly (k : ℕ) : Polynomial (BTField k) := definingPoly (s:=(Z k))

lemma poly_natDegree_eq_2 (k : ℕ) : (poly (k:=k)).natDegree = 2 :=
  natDegree_eq_of_degree_eq_some (degree_definingPoly (Z k))

lemma BTField.cast_BTField_eq (k m : ℕ) (h_eq : k = m) :
    BTField k = BTField m := by
  subst h_eq
  rfl

lemma BTField.cast_mul (m n : ℕ) {x y : BTField m} (h_eq : m = n) :
    (cast (by exact BTField.cast_BTField_eq m n h_eq) (x * y)) =
  (cast (by exact BTField.cast_BTField_eq m n h_eq) x) *
  (cast (by exact BTField.cast_BTField_eq m n h_eq) y) := by
  subst h_eq
  rfl

/-- adjoined root of poly k, generator of successor field BTField (k+1) -/
@[simp]
def 𝕏 (k : ℕ) : BTField (k+1) := Z (k+1)

@[coe]
theorem BTField_succ_eq_adjoinRoot (k : ℕ) : AdjoinRoot (poly k) = BTField (k+1) := rfl

instance coe_field_adjoinRoot (k : ℕ) : Coe (AdjoinRoot (poly k)) (BTField (k+1)) where
  coe := Eq.mp (BTField_succ_eq_adjoinRoot k)

@[simp]
theorem Z_succ_eq_adjointRoot_root (k : ℕ) : Z (k+1) = AdjoinRoot.root (poly k) := rfl

lemma list_0 : list 0 = List.Vector.cons (1 : GF(2)) List.Vector.nil := by
  unfold list
  rfl

@[simp]
lemma list_eq (k : ℕ) :
    list (k+1) = (Z (k+1)) ::ᵥ (list k).map (AdjoinRoot.of (poly k)) := by
  unfold list
  rfl

@[simp]
theorem eval_poly_at_root (k : ℕ) : (Z (k+1))^2 + (Z (k+1)) * Z k + 1 = 0 := by
  let btResult := BinaryTowerAux k
  let _instPrevBTield := btResult.2.instField
  let step := binary_tower_inductive_step k btResult.fst btResult.snd
  let eq := step.snd.eval_defining_poly_at_root
  exact eq

@[simp]
theorem poly_form (k : ℕ) : poly k = X^2 + (C (Z k) * X + 1) := by rw [←add_assoc]; rfl

@[simp]
theorem eval_mapped_poly_at_root (k : ℕ) :
    eval₂ (AdjoinRoot.of (poly k)) (Z (k+1)) (poly k) = 0 := by
  have h_BTField_succ_eq_adjoinRoot : BTField (k+1) = AdjoinRoot (poly k) :=
    BTField_succ_eq_adjoinRoot k
  have h_poly_form : poly k = X^2 + (C (Z k) * X + 1) := poly_form k
  -- ⊢ eval₂ (of (poly k)) (Z (k + 1)) (poly k) = 0
  -- NOTE : we explicitly use the output of coercion as BTField (k+1)
  -- instead of AdjoinRoot (poly k) for consistency
  set of_prev : BTField k →+* BTField (k+1) := AdjoinRoot.of (poly k)
  calc
    eval₂ of_prev (Z (k+1)) (poly k) = eval₂ of_prev (Z (k+1)) (X^2 + (C (Z k) * X + 1)) := by
      rw [←h_poly_form]
    _ = eval₂ of_prev (Z (k+1)) (X^2) + eval₂ of_prev (Z (k+1)) (C (Z k) * X)
      + eval₂ of_prev (Z (k+1)) 1 := by
      rw [eval₂_add, add_assoc, eval₂_add]
    _ = (Z (k+1))^2 + (of_prev (Z k)) * (Z (k+1)) + 1 := by
      rw [eval₂_pow, eval₂_mul, eval₂_C, eval₂_X, eval₂_one]
    _ = (Z (k+1))^2 + (Z (k+1)) * (of_prev (Z k)) + 1 := by
      rw [mul_comm]
    _ = (Z (k+1))^2 + (Z (k+1)) * (Z k) + 1 := by rfl -- x * (algegraMap scalar) = x * scalar
    _ = 0 := by
      rw [←eval_poly_at_root k]

@[simp]
lemma list_length (k : ℕ) : (list k).length = k + 1 := by
  unfold list
  rfl

@[simp]
theorem list_nonempty (k : ℕ) : (list k).1 ≠ [] := by
  by_contra h_empty
  have h_len := list_length k -- h_len : (list k).length = k + 1
  have h_len_zero := List.length_eq_zero_iff.mpr h_empty -- h_len_zero : (↑(list k)).length = 0
  have h_len_eq : (list k).length = List.length ((list k).1) := by
    simp only [BTField, list, list_length, List.Vector.length_val]
  rw [h_len_eq, h_len_zero] at h_len
  have : k + 1 ≠ 0 := Nat.succ_ne_zero k
  contradiction

instance polyIrreducible (n : ℕ) : Irreducible (poly n) := (BinaryTowerAux n).2.instIrreduciblePoly

instance polyIrreducibleFact (n : ℕ) : Fact (Irreducible (poly n)) := ⟨polyIrreducible n⟩

instance polyMonic (n : ℕ) : Monic (poly n) := definingPoly_is_monic (Z n)

lemma poly_ne_zero (n : ℕ) : poly n ≠ 0 := (polyMonic n).ne_zero

end BTFieldDefs

end

end BinaryTower
