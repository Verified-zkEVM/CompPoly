/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Extension.Bridge
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The field structure on a binomial extension

`toQuot` is not just injective but bijective: every class in `F[X] / (X^d - W)` has a unique
representative of degree `< d`. That gives `Ext.ringEquivQuot : Ext P ≃+* AdjoinRoot P.poly`,
hence `Fintype.card (Ext P) = q ^ d`, and — when the defining polynomial is irreducible — a
`Field` structure.

Inversion is by Fermat's little theorem, `x⁻¹ = x ^ (q^d - 2)`, matching how
`CompPoly/Fields/Montgomery/Native32Field.lean` inverts in the base field. Exponentiation is
binary, so this costs `O(d · log q)` extension multiplications.

The instance is assembled by hand rather than via `Function.Injective.field`, for the same
reason as `Ext.instCommRing`: that transport takes `toQuot` as data and would make the whole
structure `noncomputable`, which then shadows the computable `Mul` and `Pow`. The `qsmul` /
`nnqsmul` fields use the `castRec` defaults, following `mkDivisionRingInstance` in
`CompPoly/Fields/Binary/Tower/Concrete/Core.lean`.

## Main definitions and statements

* `Ext.equivFn`: `Ext P ≃ (Fin P.d → F)`, giving `Fintype (Ext P)` and its cardinality.
* `Ext.toQuot_surjective`, `Ext.ringEquivQuot`: `Ext P ≃+* AdjoinRoot P.poly`.
* `Ext.inv`: Fermat inversion.
* `Ext.instField`: the `Field` structure, given `[Fact (Irreducible P.poly)]`.

## Implementation notes

`Ext.inv` costs `O(d · log q)` extension multiplications. A norm-based inverse using the
Frobenius map — which on a binomial basis is a coordinate-wise scaling when `d ∣ q - 1` — would
be roughly an order of magnitude faster. See `ROADMAP.md`.
-/

@[expose] public section

namespace CompPoly.Extension.Ext

open Polynomial AdjoinRoot

variable {F : Type*} [Field F] [Fintype F] {P : BinomialParams F}

/-! ### Cardinality -/

/-- Coefficient vectors are exactly functions out of `Fin d`. -/
def equivFn (P : BinomialParams F) : Ext P ≃ (Fin P.d → F) where
  toFun := coeff
  invFun := ofFn
  left_inv := ofFn_coeff
  right_inv g := funext fun i => coeff_ofFn g i

instance instFintype : Fintype (Ext P) := Fintype.ofEquiv _ (equivFn P).symm

theorem card_ext : Fintype.card (Ext P) = P.q ^ P.d := by
  rw [Fintype.card_congr (equivFn P), Fintype.card_fun, P.card_eq, Fintype.card_fin]

instance instNontrivial : Nontrivial (Ext P) :=
  ⟨⟨0, 1, fun h => by
    have hc := congrArg (fun z => coeff z ⟨0, P.d_pos⟩) h
    simp only [coeff_zero, coeff_one] at hc
    exact zero_ne_one hc⟩⟩

/-- `4 ≤ q ^ d`, since `2 ≤ q` and `2 ≤ d`. Used to justify the Fermat exponent `q ^ d - 2`. -/
theorem four_le_card_pow : 4 ≤ P.q ^ P.d := by
  have hq : 2 ≤ P.q := by rw [← P.card_eq]; exact Fintype.one_lt_card
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ P.d := Nat.pow_le_pow_right (by omega) P.two_le
    _ ≤ P.q ^ P.d := Nat.pow_le_pow_left hq P.d

/-! ### Surjectivity and the ring equivalence -/

theorem toQuot_surjective : Function.Surjective (toQuot (P := P)) := by
  intro z
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  -- Reduce `p` modulo the (monic) defining polynomial to land in degree `< d`.
  have hdeg : (p %ₘ P.poly).natDegree < P.d := by
    rcases eq_or_ne (p %ₘ P.poly) 0 with h0 | h0
    · simpa [h0] using P.d_pos
    · refine (natDegree_lt_iff_degree_lt h0).mpr ?_
      rw [← degree_poly]
      exact degree_modByMonic_lt p P.monic_poly
  refine ⟨ofFn fun i => (p %ₘ P.poly).coeff (i : ℕ), ?_⟩
  rw [toQuot_eq_mk]
  simp only [coeff_ofFn]
  have hsum : ∑ i : Fin P.d, C ((p %ₘ P.poly).coeff (i : ℕ)) * X ^ (i : ℕ) = p %ₘ P.poly := by
    rw [Fin.sum_univ_eq_sum_range (fun i => C ((p %ₘ P.poly).coeff i) * X ^ i) P.d]
    exact (as_sum_range_C_mul_X_pow' _ hdeg).symm
  rw [hsum]
  refine AdjoinRoot.mk_eq_mk.mpr ⟨-(p /ₘ P.poly), ?_⟩
  linear_combination modByMonic_add_div p P.poly

theorem toQuot_bijective : Function.Bijective (toQuot (P := P)) :=
  ⟨toQuot_injective, toQuot_surjective⟩

/-- The extension is isomorphic to its specification `F[X] / (X^d - W)`. -/
noncomputable def ringEquivQuot (P : BinomialParams F) : Ext P ≃+* Quot[P] :=
  RingEquiv.ofBijective (toQuotRingHom P) toQuot_bijective

@[simp] theorem ringEquivQuot_apply (x : Ext P) : ringEquivQuot P x = toQuot x := rfl

/-- The quotient is finite, transported along the ring equivalence. -/
noncomputable instance instFintypeQuot : Fintype Quot[P] :=
  Fintype.ofEquiv _ (ringEquivQuot P).toEquiv

theorem card_quot : Fintype.card Quot[P] = P.q ^ P.d := by
  rw [← Fintype.card_congr (ringEquivQuot P).toEquiv, card_ext]

/-! ### Inversion

Inversion needs no irreducibility hypothesis to *define* — it is just exponentiation — only to
be correct, so it and the `Inv`/`Div` instances live outside the section below. `Div` in
particular must exist before the `Field` instance is assembled, because `NNRat.castRec` uses it.
-/

/--
Inversion by Fermat's little theorem: `x⁻¹ = x ^ (q^d - 2)`, since the multiplicative group of
the extension has order `q^d - 1`. Zero is sent to zero, as `Field` requires.
-/
def inv (x : Ext P) : Ext P := x ^ (P.q ^ P.d - 2)

instance instInv : Inv (Ext P) := ⟨inv⟩
instance instDiv : Div (Ext P) := ⟨fun x y => x * inv y⟩

theorem inv_def (x : Ext P) : x⁻¹ = x ^ (P.q ^ P.d - 2) := rfl
theorem div_def (x y : Ext P) : x / y = x * y⁻¹ := rfl

theorem inv_zero' : (0 : Ext P)⁻¹ = 0 := by
  have h4 := four_le_card_pow (P := P)
  rw [inv_def, zero_pow (by omega)]

/-! ### The field structure -/

section Irreducible

variable [Fact (Irreducible P.poly)]

theorem mul_inv_cancel' {x : Ext P} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  refine toQuot_injective ?_
  rw [toQuot_mul, inv_def, toQuot_pow, toQuot_one, ← pow_succ']
  have hz : toQuot x ≠ 0 := fun h => hx (toQuot_injective (by rw [h, toQuot_zero]))
  have h4 := four_le_card_pow (P := P)
  have hexp : P.q ^ P.d - 2 + 1 = Fintype.card Quot[P] - 1 := by
    rw [card_quot]; omega
  rw [hexp]
  exact FiniteField.pow_card_sub_one_eq_one _ hz

/--
The field structure. Every operation is computable: `inv` is Fermat exponentiation, `div` is
`x * y⁻¹`, and the rational-scalar fields use the generic `castRec` definitions.
-/
instance instField : Field (Ext P) where
  inv := inv
  div := fun x y => x * inv y
  div_eq_mul_inv _ _ := rfl
  mul_inv_cancel _ h := mul_inv_cancel' h
  inv_zero := inv_zero'
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)

end Irreducible

end CompPoly.Extension.Ext
