/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin
-/
import CompPoly.Data.Polynomial.Frobenius
import CompPoly.Fields.KoalaBear.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A degree-five extension of KoalaBear

This module defines a degree-five extension of the KoalaBear base field:

`F_{p^5} = F_p[X] / (X^5 + X^2 - 1)`.

The quotient model is `AdjoinRoot ext5Poly`. Its canonical basis is the power
basis of the adjoined root, reindexed by `Fin 5` in the order
`1, X, X^2, X^3, X^4`.

Irreducibility follows from Rabin's criterion in degree five. The finite
computations use the coordinate model `V = F_p^5`, whose multiplication agrees
with multiplication in the quotient.
-/

open Polynomial

namespace KoalaBear.Ext5

/-- The KoalaBear degree-5 extension polynomial `X^5 + X^2 - 1`. -/
noncomputable def ext5Poly : Polynomial KoalaBear.Field := X ^ 5 + X ^ 2 - 1

/-- The natural degree of `ext5Poly` is `5`. -/
theorem ext5Poly_natDegree : ext5Poly.natDegree = 5 := by
  unfold ext5Poly
  compute_degree!

/-- The extension polynomial is nonzero. -/
theorem ext5Poly_ne_zero : ext5Poly ≠ 0 := by
  intro h
  have hdeg := ext5Poly_natDegree
  rw [h] at hdeg
  simp at hdeg

private lemma exists_factor_le_two_of_reducible.{u} {R : Type u} [_root_.Field R]
    (P : Polynomial R) (h_deg : P.natDegree = 5) (h_red : ¬ Irreducible P) :
    ∃ q, Irreducible q ∧ q ∣ P ∧ q.natDegree ≤ 2 := by
  have h_ne_zero : P ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at h_deg
    contradiction
  have h_not_unit : ¬ IsUnit P := by
    intro h_unit
    have h0 : P.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit h_unit
    omega
  have h_exists_split : ∃ a b, P = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
    rw [irreducible_iff, not_and_or, not_forall] at h_red
    simp only [h_not_unit, not_false_eq_true] at h_red
    push Not at h_red
    simp only [IsEmpty.exists_iff, false_or] at h_red
    rcases h_red with ⟨a, b, h_eq, h_non_units⟩
    exact ⟨a, b, h_eq, h_non_units⟩
  rcases h_exists_split with ⟨a, b, h_eq, ha_nu, hb_nu⟩
  have h_a_ne_zero : a ≠ 0 := by
    intro h_a_eq_0
    rw [h_eq, h_a_eq_0] at h_deg
    simp at h_deg
  have h_b_ne_zero : b ≠ 0 := by
    intro h_b_eq_0
    rw [h_eq, h_b_eq_0] at h_deg
    simp at h_deg
  have h_deg_sum : a.natDegree + b.natDegree = 5 := by
    rw [← h_deg, h_eq, Polynomial.natDegree_mul (hp := h_a_ne_zero) (hq := h_b_ne_zero)]
  by_cases h_le : a.natDegree ≤ b.natDegree
  · have h_deg_a : a.natDegree ≤ 2 := by omega
    obtain ⟨q, hq_irr, hq_dvd_a⟩ :=
      WfDvdMonoid.exists_irreducible_factor ha_nu h_a_ne_zero
    refine ⟨q, hq_irr, dvd_trans hq_dvd_a (Dvd.intro b h_eq.symm), ?_⟩
    exact le_trans (Polynomial.natDegree_le_of_dvd hq_dvd_a h_a_ne_zero) h_deg_a
  · push Not at h_le
    have h_deg_b : b.natDegree ≤ 2 := by omega
    obtain ⟨q, hq_irr, hq_dvd_b⟩ :=
      WfDvdMonoid.exists_irreducible_factor hb_nu h_b_ne_zero
    refine ⟨q, hq_irr, dvd_trans hq_dvd_b (Dvd.intro_left a h_eq.symm), ?_⟩
    exact le_trans (Polynomial.natDegree_le_of_dvd hq_dvd_b h_b_ne_zero) h_deg_b

/-- Rabin irreducibility criterion, prime-degree-5 version.

The absence of linear factors is expressed as `IsCoprime (X^q - X) P`. -/
private lemma irreducible_of_rabin_5 (P : Polynomial KoalaBear.Field)
    (h_deg : P.natDegree = 5)
    (h_trace :
      P ∣ ((X : Polynomial KoalaBear.Field) ^ ((Fintype.card KoalaBear.Field) ^ 5) - X))
    (h_gcd :
      IsCoprime
        ((X : Polynomial KoalaBear.Field) ^ (Fintype.card KoalaBear.Field) - X) P) :
    Irreducible P := by
  have h_ringChar : ringChar KoalaBear.Field = KoalaBear.fieldSize := by
    change ringChar (ZMod KoalaBear.fieldSize) = KoalaBear.fieldSize
    exact ZMod.ringChar_zmod_n KoalaBear.fieldSize
  letI : Fact (Nat.Prime (ringChar KoalaBear.Field)) :=
    ⟨by rw [h_ringChar]; exact KoalaBear.is_prime⟩
  by_contra h_red
  rcases exists_factor_le_two_of_reducible P h_deg h_red with
    ⟨q, hq_irr, hq_dvd_P, hq_deg_le⟩
  have h_q_dvd_trace :
      q ∣ ((X : Polynomial KoalaBear.Field) ^ ((Fintype.card KoalaBear.Field) ^ 5) - X) :=
    dvd_trans hq_dvd_P h_trace
  have h_deg_dvd_5 : q.natDegree ∣ 5 := by
    exact (Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd (R := KoalaBear.Field)
      (n := 5) (q := q) (hq_irr := hq_irr)).mp h_q_dvd_trace
  have h_q_deg_eq_one : q.natDegree = 1 := by
    rcases h_deg_dvd_5 with ⟨k, hk⟩
    have h_q_deg_ne_zero : q.natDegree ≠ 0 := by
      intro h0
      rw [h0] at hk
      omega
    interval_cases q.natDegree <;> omega
  have h_deg_dvd_1 : q.natDegree ∣ 1 := by
    rw [h_q_deg_eq_one]
  have h_q_dvd_check :
      q ∣ ((X : Polynomial KoalaBear.Field) ^ (Fintype.card KoalaBear.Field) - X) := by
    have h := (Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd
      (R := KoalaBear.Field) (n := 1) (q := q) (hq_irr := hq_irr)).mpr h_deg_dvd_1
    simpa using h
  have h_q_unit : IsUnit q := h_gcd.isUnit_of_dvd' h_q_dvd_check hq_dvd_P
  exact (irreducible_iff.mp hq_irr).1 h_q_unit

/-!
## Coordinate model of `F_p[X]/(ext5Poly)`

`V = F_p^5` with multiplication induced by reduction modulo
`X^5 + X^2 - 1`.
-/

/-- The coordinate model of `F_p[X]/(ext5Poly)`: coefficient tuples
`(a₀, a₁, a₂, a₃, a₄)` representing `a₀ + a₁X + a₂X² + a₃X³ + a₄X⁴`. -/
private abbrev V :=
  KoalaBear.Field × KoalaBear.Field × KoalaBear.Field × KoalaBear.Field × KoalaBear.Field

/-- Squaring in the coordinate model (product reduced modulo `X^5 = 1 - X^2`). -/
private def vsq (v : V) : V :=
  let a0 := v.1
  let a1 := v.2.1
  let a2 := v.2.2.1
  let a3 := v.2.2.2.1
  let a4 := v.2.2.2.2
  ( a0 * a0 + (2 * a1 * a4 + 2 * a2 * a3) - a4 * a4
  , 2 * a0 * a1 + (2 * a2 * a4 + a3 * a3)
  , (2 * a0 * a2 + a1 * a1) - (2 * a1 * a4 + 2 * a2 * a3) +
      2 * a3 * a4 + a4 * a4
  , (2 * a0 * a3 + 2 * a1 * a2) - (2 * a2 * a4 + a3 * a3) + a4 * a4
  , (2 * a0 * a4 + 2 * a1 * a3 + a2 * a2) - 2 * a3 * a4 )

/-- Multiplication in the coordinate model (product reduced modulo `X^5 = 1 - X^2`). -/
private def vmul (u v : V) : V :=
  let a0 := u.1
  let a1 := u.2.1
  let a2 := u.2.2.1
  let a3 := u.2.2.2.1
  let a4 := u.2.2.2.2
  let b0 := v.1
  let b1 := v.2.1
  let b2 := v.2.2.1
  let b3 := v.2.2.2.1
  let b4 := v.2.2.2.2
  ( a0 * b0 + (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1) - a4 * b4
  , a0 * b1 + a1 * b0 + (a2 * b4 + a3 * b3 + a4 * b2)
  , (a0 * b2 + a1 * b1 + a2 * b0) -
      (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1) +
      (a3 * b4 + a4 * b3) + a4 * b4
  , (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) -
      (a2 * b4 + a3 * b3 + a4 * b2) + a4 * b4
  , (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0) -
      (a3 * b4 + a4 * b3) )

/-- Addition in the coordinate model. -/
private def vadd (u v : V) : V :=
  (u.1 + v.1, u.2.1 + v.2.1, u.2.2.1 + v.2.2.1,
    u.2.2.2.1 + v.2.2.2.1, u.2.2.2.2 + v.2.2.2.2)

/-- The scalar (constant) element `c` of the coordinate model. -/
private def scal (c : KoalaBear.Field) : V := (c, 0, 0, 0, 0)

/-- The unit `1` of the coordinate model. -/
private def vone : V := (1, 0, 0, 0, 0)

/-- The element `X` of the coordinate model. -/
private def ve1 : V := (0, 1, 0, 0, 0)

/-- Composition/substitution: `comp v w` evaluates the coefficient polynomial `v`
at the element `w`, i.e. `Σ vᵢ wⁱ`. -/
private def comp (v w : V) : V :=
  vadd (scal v.1)
    (vadd (vmul (scal v.2.1) w)
      (vadd (vmul (scal v.2.2.1) (vmul w w))
        (vadd (vmul (scal v.2.2.2.1) (vmul w (vmul w w)))
          (vmul (scal v.2.2.2.2) (vmul (vmul w w) (vmul w w))))))

/-- The interpretation `V → F_p[X]/(ext5Poly)`. -/
private noncomputable def toA (v : V) : AdjoinRoot ext5Poly :=
  AdjoinRoot.of ext5Poly v.1 +
    AdjoinRoot.of ext5Poly v.2.1 * AdjoinRoot.root ext5Poly +
    AdjoinRoot.of ext5Poly v.2.2.1 * AdjoinRoot.root ext5Poly ^ 2 +
    AdjoinRoot.of ext5Poly v.2.2.2.1 * AdjoinRoot.root ext5Poly ^ 3 +
    AdjoinRoot.of ext5Poly v.2.2.2.2 * AdjoinRoot.root ext5Poly ^ 4

/-- The polynomial associated with a coordinate tuple. -/
private noncomputable def vPoly (v : V) : Polynomial KoalaBear.Field :=
  C v.1 + C v.2.1 * X + C v.2.2.1 * X ^ 2 + C v.2.2.2.1 * X ^ 3 + C v.2.2.2.2 * X ^ 4

/-! ### Instances -/

instance instNontrivialAdjoin : Nontrivial (AdjoinRoot ext5Poly) :=
  AdjoinRoot.nontrivial ext5Poly (by
    rw [degree_eq_natDegree ext5Poly_ne_zero, ext5Poly_natDegree]; decide)

instance instCharPAdjoin : CharP (AdjoinRoot ext5Poly) KoalaBear.fieldSize := by
  have h : Function.Injective (algebraMap KoalaBear.Field (AdjoinRoot ext5Poly)) :=
    RingHom.injective _
  exact charP_of_injective_algebraMap h KoalaBear.fieldSize

/-! ### The defining relation and multiplication compatibility -/

/-- The root satisfies the defining relation. -/
private theorem root_rel :
    (AdjoinRoot.root ext5Poly) ^ 5 + (AdjoinRoot.root ext5Poly) ^ 2 - 1 = 0 := by
  have h0 : (AdjoinRoot.mk ext5Poly) ext5Poly = 0 := AdjoinRoot.mk_self
  have hP : ext5Poly = X ^ 5 + X ^ 2 - 1 := rfl
  rw [hP, map_sub, map_add, map_pow, map_pow, AdjoinRoot.mk_X, map_one] at h0
  exact h0

/-- Multiplication in the coordinate model agrees with the quotient ring. -/
private theorem toA_mul (u v : V) : toA (vmul u v) = toA u * toA v := by
  set r := AdjoinRoot.root ext5Poly with hrdef
  have hself : r ^ 5 + r ^ 2 - 1 = 0 := root_rel
  have hr5 : r ^ 5 = 1 - r ^ 2 := by linear_combination hself
  have hr6 : r ^ 6 = r - r ^ 3 := by rw [pow_succ, hr5]; ring
  have hr7 : r ^ 7 = r ^ 2 - r ^ 4 := by rw [pow_succ, hr6]; ring
  have hr8 : r ^ 8 = r ^ 3 + r ^ 2 - 1 := by rw [pow_succ, hr7]; linear_combination -hself
  simp only [toA, vmul, map_add, map_sub, map_mul]
  ring_nf
  rw [hr6, hr7, hr8, hr5]
  ring

/-- Addition in the coordinate model agrees with the quotient ring. -/
private theorem toA_add (u v : V) : toA (vadd u v) = toA u + toA v := by
  simp only [toA, vadd, map_add]
  ring

/-- The scalar element maps to the image of the scalar. -/
private theorem toA_scal (c : KoalaBear.Field) :
    toA (scal c) = AdjoinRoot.of ext5Poly c := by
  simp only [toA, scal, map_zero, zero_mul, add_zero]

/-- `ve1` maps to the root. -/
private theorem toA_ve1 : toA ve1 = AdjoinRoot.root ext5Poly := by
  simp only [toA, ve1, map_zero, map_one, zero_mul, zero_add, one_mul, add_zero]

/-- `vone` maps to `1`. -/
private theorem toA_vone : toA vone = 1 := by
  simp only [toA, vone, map_zero, map_one, zero_mul, add_zero]

/-- Squaring in the coordinate model agrees with the quotient ring. -/
private theorem toA_sq (v : V) : toA (vsq v) = (toA v) ^ 2 := by
  have heq : vsq v = vmul v v := by
    simp only [vsq, vmul, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring, by ring, by ring⟩
  rw [heq, toA_mul, sq]

/-- `comp` agrees with polynomial evaluation in the quotient ring. -/
private theorem toA_comp (v w : V) :
    toA (comp v w) =
      AdjoinRoot.of ext5Poly v.1
      + AdjoinRoot.of ext5Poly v.2.1 * toA w
      + AdjoinRoot.of ext5Poly v.2.2.1 * (toA w) ^ 2
      + AdjoinRoot.of ext5Poly v.2.2.2.1 * (toA w) ^ 3
      + AdjoinRoot.of ext5Poly v.2.2.2.2 * (toA w) ^ 4 := by
  simp only [comp, toA_add, toA_scal, toA_mul]
  ring

/-- `toA` factors through `AdjoinRoot.mk` of `vPoly`. -/
private theorem toA_eq_mk (v : V) : toA v = AdjoinRoot.mk ext5Poly (vPoly v) := by
  simp only [toA, vPoly, map_add, map_mul, map_pow, AdjoinRoot.mk_X]
  rfl

/-! ### The Frobenius power `root ^ p` -/

/-- The explicit value of `X^p mod P`, `p = fieldSize`. -/
private def cC : V := (1576402667, 1173144480, 1567662457, 1206866823, 2428146)

/-- `root ^ (2 ^ k)` is the `k`-fold square of `X` in the coordinate model. -/
private theorem pow2_correct (k : ℕ) :
    (AdjoinRoot.root ext5Poly) ^ (2 ^ k) = toA (vsq^[k] ve1) := by
  induction k with
  | zero => simp [toA_ve1]
  | succ n ih =>
    rw [pow_succ 2 n, pow_mul, ih, Function.iterate_succ', Function.comp_apply, toA_sq]

/-- The Frobenius image of the adjoined root is represented by `cC`. -/
private theorem root_pow_fieldSize :
    (AdjoinRoot.root ext5Poly) ^ KoalaBear.fieldSize = toA cC := by
  set r := AdjoinRoot.root ext5Poly with hrdef
  -- Use explicit intermediate tuples to keep each computation small.
  have step : ∀ (k : ℕ) (L L' : V), vsq^[k] ve1 = L → vsq L = L' → vsq^[k+1] ve1 = L' := by
    intro k L L' h hs; rw [Function.iterate_succ_apply', h, hs]
  have s1 : vsq^[1] ve1 = (0,0,1,0,0) := by decide
  have s2 := step 1 _ _ s1 (show vsq (0,0,1,0,0) = (0,0,0,0,1) by decide)
  have s3 := step 2 _ _ s2 (show vsq (0,0,0,0,1) = (2130706432,0,1,1,0) by decide)
  have s4 := step 3 _ _ s3 (show vsq (2130706432,0,1,1,0) = (3,1,2130706429,2130706430,1) by decide)
  have s5 := step 4 _ _ s4
    (show vsq (3,1,2130706429,2130706430,1) = (34,7,2130706379,2130706407,22) by decide)
  have s6 := step 5 _ _ s5
    (show vsq (34,7,2130706379,2130706407,22) =
      (3788,2130705209,2130699034,2130706093,5192) by decide)
  have s7 := step 6 _ _ s6
    (show vsq (3788,2130705209,2130699034,2130706093,5192)
        = (2110419817,2044717793,2107254785,119209392,98442673) by decide)
  have s8 := step 7 _ _ s7
    (show vsq (2110419817,2044717793,2107254785,119209392,98442673)
        = (1962757147,1517752019,2034103327,1821522190,1486994651) by decide)
  have s9 := step 8 _ _ s8
    (show vsq (1962757147,1517752019,2034103327,1821522190,1486994651)
        = (1769126182,159161379,1716678059,1359437718,1832431749) by decide)
  have s10 := step 9 _ _ s9
    (show vsq (1769126182,159161379,1716678059,1359437718,1832431749)
        = (992533826,1049099903,1999262994,91642174,863970281) by decide)
  have s11 := step 10 _ _ s10
    (show vsq (992533826,1049099903,1999262994,91642174,863970281)
        = (409320760,528924425,608828729,2124114134,475824548) by decide)
  have s12 := step 11 _ _ s11
    (show vsq (409320760,528924425,608828729,2124114134,475824548)
        = (2111237692,396498471,1124300053,961203683,1585691692) by decide)
  have s13 := step 12 _ _ s12
    (show vsq (2111237692,396498471,1124300053,961203683,1585691692)
        = (413260470,409516856,1431989188,1641019207,1704057837) by decide)
  have s14 := step 13 _ _ s13
    (show vsq (413260470,409516856,1431989188,1641019207,1704057837)
        = (1108180128,308487541,156248939,2116951396,1974449295) by decide)
  have s15 := step 14 _ _ s14
    (show vsq (1108180128,308487541,156248939,2116951396,1974449295)
        = (41990483,2006079421,1821017144,874368254,1995630240) by decide)
  have s16 := step 15 _ _ s15
    (show vsq (41990483,2006079421,1821017144,874368254,1995630240)
        = (1566642517,395592644,2090964960,1639164963,985945876) by decide)
  have s17 := step 16 _ _ s16
    (show vsq (1566642517,395592644,2090964960,1639164963,985945876)
        = (187322181,1526360033,1126590339,101840703,593878992) by decide)
  have s18 := step 17 _ _ s17
    (show vsq (187322181,1526360033,1126590339,101840703,593878992)
        = (1436296730,309967013,1477441957,817455747,1777251330) by decide)
  have s19 := step 18 _ _ s18
    (show vsq (1436296730,309967013,1477441957,817455747,1777251330)
        = (1185135385,1081768488,619543182,836527214,1154033604) by decide)
  have s20 := step 19 _ _ s19
    (show vsq (1185135385,1081768488,619543182,836527214,1154033604)
        = (490029673,1131493085,1304097286,337236161,1481816257) by decide)
  have s21 := step 20 _ _ s20
    (show vsq (490029673,1131493085,1304097286,337236161,1481816257)
        = (2021857567,854001862,1175881365,2053477554,391696094) by decide)
  have s22 := step 21 _ _ s21
    (show vsq (2021857567,854001862,1175881365,2053477554,391696094)
        = (687510172,769974275,355032796,1909331372,942441006) by decide)
  have s23 := step 22 _ _ s22
    (show vsq (687510172,769974275,355032796,1909331372,942441006)
        = (297794260,880422823,1923160268,1699843207,1741026385) by decide)
  have s24 := step 23 _ _ s23
    (show vsq (297794260,880422823,1923160268,1699843207,1741026385)
        = (1245429030,2123323988,1997199567,840428791,934310696) by decide)
  have s25 := step 24 _ _ s24
    (show vsq (1245429030,2123323988,1997199567,840428791,934310696)
        = (569013304,236098224,758792048,1272633629,2052091549) by decide)
  have s26 := step 25 _ _ s25
    (show vsq (569013304,236098224,758792048,1272633629,2052091549)
        = (170464830,492509808,868271568,272443740,1531518663) by decide)
  have s27 := step 26 _ _ s26
    (show vsq (170464830,492509808,868271568,272443740,1531518663)
        = (1874282980,1066852937,1433697031,1765783253,377756129) by decide)
  have s28 := step 27 _ _ s27
    (show vsq (1874282980,1066852937,1433697031,1765783253,377756129)
        = (1830263855,1832006692,688110156,388686197,6993364) by decide)
  have s29 := step 28 _ _ s28
    (show vsq (1830263855,1832006692,688110156,388686197,6993364)
        = (220557930,1557796740,232394723,1347875738,808949557) by decide)
  have s30 := step 29 _ _ s29
    (show vsq (220557930,1557796740,232394723,1347875738,808949557)
        = (275177653,1039982331,1461735331,1496659274,1976841709) by decide)
  -- Combine the nonzero binary digits of `fieldSize`.
  have hCval :
      vmul (vsq^[24] ve1) (vmul (vsq^[25] ve1) (vmul (vsq^[26] ve1)
        (vmul (vsq^[27] ve1) (vmul (vsq^[28] ve1) (vmul (vsq^[29] ve1)
          (vmul (vsq^[30] ve1) ve1)))))) = cC := by
    rw [s24, s25, s26, s27, s28, s29, s30]; decide
  rw [← hCval]
  simp only [toA_mul, toA_ve1, ← pow2_correct]
  have hpow : r ^ KoalaBear.fieldSize
      = r ^ (2 ^ 24 + (2 ^ 25 + (2 ^ 26 + (2 ^ 27 + (2 ^ 28 + (2 ^ 29 + (2 ^ 30 + 1))))))) :=
    congrArg (fun n ↦ r ^ n)
      (by decide : KoalaBear.fieldSize
          = 2 ^ 24 + (2 ^ 25 + (2 ^ 26 + (2 ^ 27 + (2 ^ 28 + (2 ^ 29 + (2 ^ 30 + 1)))))))
  rw [hpow]
  simp only [pow_add, pow_one, ← hrdef]

/-- The Frobenius (`p`-power) of any coordinate element is `comp` with `cC`. -/
private theorem frob_toA (v : V) :
    (toA v) ^ KoalaBear.fieldSize = toA (comp v cC) := by
  haveI : Fact (Nat.Prime KoalaBear.fieldSize) := ⟨KoalaBear.is_prime⟩
  set r := AdjoinRoot.root ext5Poly with hrdef
  have hofpow : ∀ c : KoalaBear.Field,
      (AdjoinRoot.of ext5Poly c) ^ KoalaBear.fieldSize = AdjoinRoot.of ext5Poly c := by
    intro c
    rw [← map_pow, ZMod.pow_card]
  have hrpow : r ^ KoalaBear.fieldSize = toA cC := root_pow_fieldSize
  have hexpand :
      (toA v) ^ KoalaBear.fieldSize
        = (AdjoinRoot.of ext5Poly v.1) ^ KoalaBear.fieldSize
          + (AdjoinRoot.of ext5Poly v.2.1) ^ KoalaBear.fieldSize
              * (r ^ KoalaBear.fieldSize)
          + (AdjoinRoot.of ext5Poly v.2.2.1) ^ KoalaBear.fieldSize
              * (r ^ KoalaBear.fieldSize) ^ 2
          + (AdjoinRoot.of ext5Poly v.2.2.2.1) ^ KoalaBear.fieldSize
              * (r ^ KoalaBear.fieldSize) ^ 3
          + (AdjoinRoot.of ext5Poly v.2.2.2.2) ^ KoalaBear.fieldSize
              * (r ^ KoalaBear.fieldSize) ^ 4 := by
    simp only [toA, ← hrdef]
    rw [add_pow_char, add_pow_char, add_pow_char, add_pow_char,
        mul_pow, mul_pow, mul_pow, mul_pow,
        pow_right_comm r 2 KoalaBear.fieldSize, pow_right_comm r 3 KoalaBear.fieldSize,
        pow_right_comm r 4 KoalaBear.fieldSize]
  rw [hexpand, toA_comp]
  simp only [hofpow, hrpow]

/-! ### The trace certificate -/

/-- The iterated Frobenius returns `X`. -/
private theorem trace_root :
    (AdjoinRoot.root ext5Poly) ^ (KoalaBear.fieldSize ^ 5) = AdjoinRoot.root ext5Poly := by
  set r := AdjoinRoot.root ext5Poly with hrdef
  set p := KoalaBear.fieldSize with hp
  have e1 : r ^ (p ^ 1) = toA cC := by
    rw [pow_one]; exact root_pow_fieldSize
  have e2 : r ^ (p ^ 2) = toA (comp cC cC) := by
    rw [show p ^ 2 = p ^ 1 * p by ring, pow_mul, e1, frob_toA]
  have e3 : r ^ (p ^ 3) = toA (comp (comp cC cC) cC) := by
    rw [show p ^ 3 = p ^ 2 * p by ring, pow_mul, e2, frob_toA]
  have e4 : r ^ (p ^ 4) = toA (comp (comp (comp cC cC) cC) cC) := by
    rw [show p ^ 4 = p ^ 3 * p by ring, pow_mul, e3, frob_toA]
  have e5 : r ^ (p ^ 5) = toA (comp (comp (comp (comp cC cC) cC) cC) cC) := by
    rw [show p ^ 5 = p ^ 4 * p by ring, pow_mul, e4, frob_toA]
  have h2 : comp cC cC
      = (361322221, 1970254932, 446925412, 2022674657, 1632465862) := by decide
  have h3 : comp (361322221, 1970254932, 446925412, 2022674657, 1632465862) cC
      = (866070051, 932157177, 618652440, 1443450085, 457078219) := by decide
  have h4 : comp (866070051, 932157177, 618652440, 1443450085, 457078219) cC
      = (1457617927, 185856276, 1628172557, 1719127734, 38734206) := by decide
  have h5 : comp (1457617927, 185856276, 1628172557, 1719127734, 38734206) cC
      = ve1 := by decide
  rw [e5, h2, h3, h4, h5, toA_ve1]

/-- Trace certificate: `ext5Poly ∣ X^(card^5) - X`. -/
private theorem ext5Poly_trace :
    ext5Poly ∣ ((X : Polynomial KoalaBear.Field) ^ ((Fintype.card KoalaBear.Field) ^ 5) - X) := by
  have hcard : Fintype.card KoalaBear.Field = KoalaBear.fieldSize := ZMod.card _
  rw [hcard]
  rw [← AdjoinRoot.mk_eq_zero]
  rw [map_sub, map_pow, AdjoinRoot.mk_X]
  rw [trace_root, sub_self]

/-! ### The no-linear-factor certificate -/

/-- The reduced polynomial `cC(X) - X` as a coordinate tuple. -/
private def gVec : V := (1576402667, 1173144479, 1567662457, 1206866823, 2428146)

/-- The inverse of `gVec` modulo `ext5Poly`, in the coordinate model. -/
private def hVec : V := (666019741, 1851614074, 1978360661, 214422949, 375508882)

/-- `gVec` is a unit in the coordinate model with inverse `hVec`. -/
private theorem gVec_mul_hVec : vmul gVec hVec = vone := by decide

/-- `vPoly gVec = vPoly cC - X`. -/
private theorem vPoly_gVec : vPoly gVec = vPoly cC - X := by
  simp only [vPoly, gVec, cC]
  rw [show (1173144479 : KoalaBear.Field) = 1173144480 - 1 by decide, map_sub, map_one]
  ring

/-- `ext5Poly ∣ X^p - vPoly cC`. -/
private theorem dvd_X_pow_sub_cPoly :
    ext5Poly ∣ ((X : Polynomial KoalaBear.Field) ^ KoalaBear.fieldSize - vPoly cC) := by
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, ← toA_eq_mk,
    ← root_pow_fieldSize, sub_self]

/-- `vPoly gVec` and `ext5Poly` are coprime. -/
private theorem isCoprime_gPoly : IsCoprime (vPoly gVec) ext5Poly := by
  -- `gVec` is a unit modulo `ext5Poly`.
  have hunit : AdjoinRoot.mk ext5Poly (vPoly gVec * vPoly hVec) = 1 := by
    rw [map_mul, ← toA_eq_mk, ← toA_eq_mk, ← toA_mul, gVec_mul_hVec, toA_vone]
  have hdvd : ext5Poly ∣ (vPoly gVec * vPoly hVec - 1) := by
    rw [← AdjoinRoot.mk_eq_zero, map_sub, hunit, map_one, sub_self]
  obtain ⟨s, hs⟩ := hdvd
  exact ⟨vPoly hVec, -s, by linear_combination hs⟩

/-- No-linear-factor certificate as coprimality. -/
private theorem ext5Poly_coprime :
    IsCoprime
      ((X : Polynomial KoalaBear.Field) ^ (Fintype.card KoalaBear.Field) - X) ext5Poly := by
  have hcard : Fintype.card KoalaBear.Field = KoalaBear.fieldSize := ZMod.card _
  rw [hcard]
  obtain ⟨Qp, hQp⟩ := dvd_X_pow_sub_cPoly
  -- Isolate the large power before normalization.
  have key : ∀ y : Polynomial KoalaBear.Field, y - X = (vPoly cC - X) + (y - vPoly cC) :=
    fun y ↦ by ring
  have hsplit :
      (X : Polynomial KoalaBear.Field) ^ KoalaBear.fieldSize - X
        = vPoly gVec + ext5Poly * Qp := by
    rw [vPoly_gVec, key ((X : Polynomial KoalaBear.Field) ^ KoalaBear.fieldSize), hQp]
  rw [hsplit]
  exact (isCoprime_gPoly).add_mul_left_left Qp

/-- The extension polynomial is irreducible over the KoalaBear base field. -/
theorem ext5Poly_irreducible : Irreducible ext5Poly := by
  apply irreducible_of_rabin_5
  · exact ext5Poly_natDegree
  · exact ext5Poly_trace
  · exact ext5Poly_coprime

instance : Fact (Irreducible ext5Poly) := ⟨ext5Poly_irreducible⟩

/-- The KoalaBear degree-5 extension field `F_p[X] / (X^5 + X^2 - 1)`. -/
abbrev Field : Type := AdjoinRoot ext5Poly

/-- The power basis of the adjoined root generating the extension field. -/
noncomputable def powerBasis : PowerBasis KoalaBear.Field Field :=
  AdjoinRoot.powerBasis ext5Poly_ne_zero

/-- The power basis has dimension `5`. -/
theorem powerBasis_dim : powerBasis.dim = 5 := by
  unfold powerBasis
  rw [AdjoinRoot.powerBasis_dim, ext5Poly_natDegree]

/-- The canonical `Fin 5`-indexed basis `1, X, X^2, X^3, X^4`. -/
noncomputable def basis : Module.Basis (Fin 5) KoalaBear.Field Field :=
  powerBasis.basis.reindex (finCongr powerBasis_dim)

/-- The `F_p`-linear equivalence from coordinate vectors to the extension field. -/
noncomputable def embed : (Fin 5 → KoalaBear.Field) ≃ₗ[KoalaBear.Field] Field :=
  basis.equivFun.symm

/-- The `i`-th canonical basis vector is the `i`-th power of the adjoined root. -/
theorem basis_apply (i : Fin 5) :
    basis i = powerBasis.gen ^ (i : ℕ) := by
  simp [basis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]

/-- Canonical coordinates in the basis `1, X, X², X³, X⁴`. -/
noncomputable def coords : Field ≃ₗ[KoalaBear.Field] (Fin 5 → KoalaBear.Field) :=
  basis.equivFun

/-- `embed` sends coordinates to their linear combination in the canonical basis. -/
theorem embed_apply (c : Fin 5 → KoalaBear.Field) :
    embed c = ∑ i, c i • basis i := by
  exact basis.equivFun_symm_apply c

private theorem embed_eq_toA (c : Fin 5 → KoalaBear.Field) :
    embed c = toA (c 0, c 1, c 2, c 3, c 4) := by
  rw [embed_apply]
  simp [basis_apply, Fin.sum_univ_succ, Algebra.smul_def, add_assoc, toA, powerBasis]

/-- Executable multiplication in canonical coordinates, reduced by `X⁵ = 1 - X²`. -/
def mulCoords (a b : Fin 5 → KoalaBear.Field) : Fin 5 → KoalaBear.Field :=
  ![
    a 0 * b 0 + (a 1 * b 4 + a 2 * b 3 + a 3 * b 2 + a 4 * b 1) - a 4 * b 4,
    a 0 * b 1 + a 1 * b 0 + (a 2 * b 4 + a 3 * b 3 + a 4 * b 2),
    (a 0 * b 2 + a 1 * b 1 + a 2 * b 0) -
      (a 1 * b 4 + a 2 * b 3 + a 3 * b 2 + a 4 * b 1) +
      (a 3 * b 4 + a 4 * b 3) + a 4 * b 4,
    (a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0) -
      (a 2 * b 4 + a 3 * b 3 + a 4 * b 2) + a 4 * b 4,
    (a 0 * b 4 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1 + a 4 * b 0) -
      (a 3 * b 4 + a 4 * b 3)
  ]

/-- Coordinate multiplication agrees with multiplication in the extension field. -/
theorem embed_mulCoords (a b : Fin 5 → KoalaBear.Field) :
    embed (mulCoords a b) = embed a * embed b := by
  rw [embed_eq_toA, embed_eq_toA, embed_eq_toA]
  simpa [mulCoords, vmul] using
    toA_mul (a 0, a 1, a 2, a 3, a 4) (b 0, b 1, b 2, b 3, b 4)

/-- The canonical coordinate embedding is bijective. -/
theorem embed_bijective : Function.Bijective embed := embed.bijective

end KoalaBear.Ext5
