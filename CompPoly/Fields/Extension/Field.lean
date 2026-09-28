/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Extension.Bridge
public import CompPoly.Fields.Extension.Cardinality
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The field structure on an extension

`toQuot` is not just injective but bijective: every class in `F[X] / f` has a unique
representative of degree `< d`. That gives `Ext.ringEquivQuot : Ext P ≃+* AdjoinRoot P.poly`,
and the separately certified base cardinality gives `Nat.card (Ext P) = q ^ d`. A `Field`
structure requires `[Finite F]`, `[Fact (Nat.card F = P.q)]`, and irreducibility of the defining
polynomial.

Inversion is by Fermat's little theorem, `x⁻¹ = x ^ (q^d - 2)`, matching how
`CompPoly/Fields/Montgomery/Native32Field.lean` inverts in the base field. Exponentiation is
binary, so this costs `O(d · log q)` extension multiplications.

The instance is assembled by hand rather than via `Function.Injective.field`, for the same
reason as `Ext.instCommRing`: that transport takes `toQuot` as data and would make the whole
structure `noncomputable`, which then shadows the computable `Mul` and `Pow`. The `qsmul` /
`nnqsmul` fields use the `castRec` defaults, following `mkDivisionRingInstance` in
`CompPoly/Fields/Binary/Tower/Concrete/Core.lean`.

## Main definitions and statements

* `Ext.toQuot_surjective`, `Ext.ringEquivQuot`: `Ext P ≃+* AdjoinRoot P.poly`.
* `Ext.inv`: Fermat inversion.
* `Ext.instField`: the `Field` structure, given finite base field, certified `Nat.card F = P.q`,
  and irreducibility of `P.poly`.

## Implementation notes

The inverse candidate is defined in `Extension/Arithmetic.lean`; its correctness depends on
the certificates above. `Extension/Cardinality.lean` supplies the finite-coordinate facts
without importing the polynomial quotient bridge.
-/

@[expose] public section

namespace CompPoly.Extension.Ext

open Polynomial AdjoinRoot

variable {F : Type*} [Field F] {P : ExtensionParams F}

instance instNontrivial : Nontrivial (Ext P) :=
  ⟨⟨0, 1, fun h => by
    have hc := congrArg (fun z => coeff z ⟨0, P.d_pos⟩) h
    simp only [coeff_zero, coeff_one] at hc
    exact zero_ne_one hc⟩⟩

/-- `4 ≤ q ^ d`, since `2 ≤ q` and `2 ≤ d`. Used to justify the Fermat exponent `q ^ d - 2`. -/
theorem four_le_card_pow [Finite F] [Fact (Nat.card F = P.q)] : 4 ≤ P.q ^ P.d := by
  let := Fintype.ofFinite F
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

/-- The extension is isomorphic to its specification `F[X] / f`. -/
noncomputable def ringEquivQuot (P : ExtensionParams F) : Ext P ≃+* Quot[P] :=
  RingEquiv.ofBijective (toQuotRingHom P) toQuot_bijective

@[simp] theorem ringEquivQuot_apply (x : Ext P) : ringEquivQuot P x = toQuot x := rfl

/-- The quotient is finite, transported along the ring equivalence. -/
noncomputable instance instFintypeQuot [Fintype F] : Fintype Quot[P] :=
  Fintype.ofEquiv _ (ringEquivQuot P).toEquiv

theorem card_quot [Fintype F] [Fact (Nat.card F = P.q)] : Fintype.card Quot[P] = P.q ^ P.d := by
  rw [← Fintype.card_congr (ringEquivQuot P).toEquiv, card_ext]

/-! ### Inversion

The canonical inverse candidate and its `Inv`/`Div` instances come from the raw arithmetic
module. The following laws require certified cardinality; cancellation also requires
irreducibility.
-/

theorem inv_zero' [Finite F] [Fact (Nat.card F = P.q)] : (0 : Ext P)⁻¹ = 0 := by
  have h4 := four_le_card_pow (P := P)
  rw [inv_def, zero_pow (by omega)]

/-! ### The field structure -/

section Irreducible

variable [Finite F] [Fact (Nat.card F = P.q)] [Fact (Irreducible P.poly)]

theorem mul_inv_cancel' {x : Ext P} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  let := Fintype.ofFinite F
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
