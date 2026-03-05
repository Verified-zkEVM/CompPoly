/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import CompPoly.Fields.Binary.Tower.Prelude
import CompPoly.Data.RingTheory.AlgebraTower
import Mathlib.Tactic.DepRewrite
import Batteries.Data.Fin.Fold

/-!
# Binary Tower Fields

Define the binary tower field GF(2^{2^k}) as an iterated quadratic extension of GF(2).

## Main Definitions

- `BTField k` : the binary tower field GF(2^{2^k}) as an iterated quadratic extension of GF(2),
  where `BTField 0 = GF(2)`

## References

* [Wiedemann, D., *An Iterated Quadratic Extension of GF(2)*][Wie88]
* [Fan, J.L. and Paar, C., *On efficient inversion in tower fields of characteristic two*][FP97]
* [Lin, S., Chung, W., and Han, Y.S., *Novel polynomial basis and its application to Reed-Solomon
    erasure codes*][LCH14]
* [Diamond, B.E. and Posen, J., *Succinct Arguments over Towers of Binary Fields*][DP23]
* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]

## TODOs

-/

namespace BinaryTower
noncomputable section

open Polynomial AdjoinRoot Module

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

@[simp]
instance BTFieldIsField (k : ℕ) : Field (BTField k) := (BinaryTowerAux k).2.instField

@[simp]
instance CommRing (k : ℕ) : CommRing (BTField k) := Field.toCommRing

@[simp]
instance Nontrivial (k : ℕ) : Nontrivial (BTField k) := inferInstance

@[simp]
instance Inhabited (k : ℕ) : Inhabited (BTField k) where
  default := (0 : BTField k)

instance {k : ℕ} : _root_.Inhabited (BinaryTowerAux k).fst := by
  change _root_.Inhabited (BTField k)
  exact Inhabited k

@[simp]
instance BTFieldNeZero1 (k : ℕ) : NeZero (1 : BTField k) := by
  unfold BTField
  exact @neZero_one_of_nontrivial_comm_monoid_zero (BTField k) _ (Nontrivial k)

@[simp]
instance BTField_Fintype (k : ℕ) : Fintype (BTField k) := (BinaryTowerAux k).2.instFintype

@[simp]
def BTFieldCard (k : ℕ) : Fintype.card (BTField k) = 2^(2^k) :=
  (BinaryTowerAux k).2.fieldFintypeCard

@[simp]
instance BTFieldIsDomain (k : ℕ) : IsDomain (BTField k) := inferInstance

@[simp]
instance BTFieldNoZeroDiv (k : ℕ) : NoZeroDivisors (BTField k) := by
  unfold BTField
  infer_instance

@[simp]
def sumZeroIffEq (k : ℕ) : ∀ (x y : BTField k),
    x + y = 0 ↔ x = y := (BinaryTowerAux k).2.sumZeroIffEq

@[simp]
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

/--
Auxiliary definition for `towerAlgebraMap` using `Fin.dfoldl`.
It folds adjacent embeddings from level `l` up to level `l + d`.
-/
private def towerAlgebraMapCore (l d : ℕ) : BTField l →+* BTField (l + d) := by
  let α : Fin (d + 1) → Type := fun i => BTField l →+* BTField (l + i)
  let init : α 0 := by
    simpa [α] using (RingHom.id (BTField l))
  let step : ∀ i : Fin d, α i.castSucc → α i.succ := by
    intro i f
    simpa [α, Fin.succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ((canonicalEmbedding (l + i)).comp f)
  let folded : α (Fin.last d) := Fin.dfoldl d α step init
  have h_last : l + (Fin.last d : Fin (d + 1)) = l + d := by simp
  exact cast (BTField.RingHom_eq_of_dest_eq (k:=l)
    (m:=l + (Fin.last d : Fin (d + 1))) (n:=l + d) h_last) folded

private lemma towerAlgebraMapCore_one (l : ℕ) :
    towerAlgebraMapCore l 1 = canonicalEmbedding l := by
  ext x
  rw [towerAlgebraMapCore]
  simp [Fin.dfoldl_succ, Fin.dfoldl_zero]

private lemma towerAlgebraMapCore_succ_last (l d : ℕ) :
    towerAlgebraMapCore l (d + 1) =
      (canonicalEmbedding (l + d)).comp (towerAlgebraMapCore l d) := by
  ext x
  rw [towerAlgebraMapCore, towerAlgebraMapCore]
  simp only [Fin.dfoldl_succ_last, Function.comp_apply]
  have hfold :
      Fin.dfoldl d
        ((fun i : Fin (d + 2) => BTField l →+* BTField (l + i)) ∘ Fin.castSucc)
        (fun i f => (canonicalEmbedding (l + i.castSucc)).comp f)
        (RingHom.id (BTField l))
      =
      Fin.dfoldl d
        (fun i : Fin (d + 1) => BTField l →+* BTField (l + i))
        (fun i f => (canonicalEmbedding (l + i)).comp f)
        (RingHom.id (BTField l)) := by
    have hα :
        ((fun i : Fin (d + 2) => BTField l →+* BTField (l + i)) ∘ Fin.castSucc)
        = (fun i : Fin (d + 1) => BTField l →+* BTField (l + i)) := by
      funext i
      simp
    cases hα
    rfl
  exact congrArg (fun f => ((canonicalEmbedding (l + d)).comp f) x) hfold

def towerAlgebraMap (l r : ℕ) (h_le : l ≤ r) : BTField l →+* BTField r := by
  if h_eq : l = r then
    subst h_eq
    exact RingHom.id (BTField l)
  else
    exact cast (BTField.RingHom_eq_of_dest_eq (k:=l) (m:=l + (r - l)) (n:=r)
      (Nat.add_sub_of_le h_le)) (towerAlgebraMapCore l (r - l))

lemma towerAlgebraMap_id (k : ℕ) : towerAlgebraMap (h_le:=by omega) = RingHom.id (BTField k) := by
  unfold towerAlgebraMap
  exact (Ne.dite_eq_left_iff fun h a ↦ h rfl).mpr rfl

lemma towerAlgebraMap_succ_1 (k : ℕ) :
    towerAlgebraMap (l:=k) (r:=k+1) (h_le:=by omega) = canonicalEmbedding k := by
  unfold towerAlgebraMap
  simp only [Nat.left_eq_add, one_ne_zero, ↓reduceDIte]
  have h_sub : k + 1 - k = 1 := by omega
  rw! (castMode := .all) [h_sub]
  rw [towerAlgebraMapCore_one]
  simp

/-! Right associativity of the Tower Map -/
lemma towerAlgebraMap_succ (l r : ℕ) (h_le : l ≤ r) :
    towerAlgebraMap (l:=l) (r:=r+1) (h_le:=by omega) =
  (towerAlgebraMap (l:=r) (r:=r+1) (h_le:=by omega)).comp
  (towerAlgebraMap (l:=l) (r:=r) (h_le:=by omega)) := by
  by_cases h_lr : l = r
  · subst h_lr
    rw [towerAlgebraMap_id, RingHom.comp_id]
  · ext x
    conv_lhs => rw [towerAlgebraMap]
    have h_l_ne_eq_r_add_1 : l ≠ r + 1 := by omega
    simp only [h_l_ne_eq_r_add_1, ↓reduceDIte, RingHom.coe_comp, Function.comp_apply]
    rw [towerAlgebraMap_succ_1]
    conv_rhs =>
      enter [2]
      rw [towerAlgebraMap]
    simp only [h_lr, ↓reduceDIte]
    set d := r - l with hd
    have h_diff : r + 1 - l = d + 1 := by omega
    rw! (castMode := .all) [h_diff]
    rw [towerAlgebraMapCore_succ_last]
    have h_idx : l + d = r := by omega
    rw! (castMode := .all) [h_idx]
    rw! (castMode := .all) [hd]
    conv_rhs =>
      enter [2]
      rw [BTField.RingHom_cast_dest_apply]
    rw [BTField.RingHom_cast_dest_apply]
    · rw! (castMode := .all) [h_idx]
      rfl
    · omega

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

noncomputable section MultilinearBasis

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
  -- ⊢ algebra_adjacent_tower k = AdjoinRoot.instAlgebra (poly k) => TODO : make a lemma for this
  -- NOTE : pb.gen is definitionally equal to AdjoinRoot.root (poly k)
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
end
