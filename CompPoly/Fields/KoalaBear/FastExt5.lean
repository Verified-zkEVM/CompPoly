/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Extension.Bytes
public import CompPoly.Fields.Extension.Map
public import CompPoly.Fields.KoalaBear.Ext5
public import CompPoly.Fields.KoalaBear.Fast
public import CompPoly.Fields.Montgomery.Native32Bytes

/-!
# The degree-5 extension of KoalaBear over the fast carrier

`KoalaBear.Fast.Ext5` is `KoalaBear[X] / (X^5 + X^2 - 1)` with five Montgomery coefficients, the
same field as Plonky3's `QuinticTrinomialExtensionField<KoalaBear>`.

* Multiplication reduces the schoolbook product by `X^5 = 1 - X^2`. The reduction is folded into
  the right factors, so every output coefficient is a sum of five products: four go through
  `mulAdd4` with a single Montgomery reduction, the fifth is one more product.
* Inversion is Fermat's `a⁻¹ = a ^ (p^5 - 2)` by binary exponentiation.

The spec field `Ext5.Spec` is the framework's `Ext` over the fast base field itself
(`Ext5.params`). Its irreducibility certificate is `KoalaBear.quinticPoly_irreducible` for the spec
`KoalaBear.Ext5` over `KoalaBear.Field`, transferred along `ringEquiv` (`params_eq_map`).
`toSpec` maps into the spec field, and `toSpec_add`, `toSpec_mul`, `toSpec_inv`, … show that every
operation agrees with it; `specEquiv` packages it as a ring isomorphism. The byte encoding is the
five coefficient encodings in ascending order, as for the spec field and Plonky3
(`toBytes_toSpec`).
-/

@[expose] public section

namespace KoalaBear.Fast

open CompPoly CompPoly.Extension Montgomery.Native32 Polynomial

/-- `c0 + c1 X + c2 X^2 + c3 X^3 + c4 X^4` in `KoalaBear[X] / (X^5 + X^2 - 1)`, with fast
coefficients. -/
structure Ext5 where
  c0 : Field
  c1 : Field
  c2 : Field
  c3 : Field
  c4 : Field
deriving DecidableEq

namespace Ext5

instance : Zero Ext5 := ⟨⟨0, 0, 0, 0, 0⟩⟩
instance : One Ext5 := ⟨⟨1, 0, 0, 0, 0⟩⟩
instance : Inhabited Ext5 := ⟨0⟩
instance : Add Ext5 :=
  ⟨fun a b ↦ ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3, a.c4 + b.c4⟩⟩
instance : Neg Ext5 := ⟨fun a ↦ ⟨-a.c0, -a.c1, -a.c2, -a.c3, -a.c4⟩⟩
instance : Sub Ext5 :=
  ⟨fun a b ↦ ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2, a.c3 - b.c3, a.c4 - b.c4⟩⟩

/-- A base-field element. -/
@[inline] def ofBase (x : Field) : Ext5 := ⟨x, 0, 0, 0, 0⟩

/-- Multiplication by a base-field element. -/
@[inline] def smul (x : Field) (a : Ext5) : Ext5 :=
  ⟨x * a.c0, x * a.c1, x * a.c2, x * a.c3, x * a.c4⟩

/-- Product modulo `X^5 + X^2 - 1`. With `X^5 = 1 - X^2`, `X^6 = X - X^3`, `X^7 = X^2 - X^4` and
`X^8 = X^3 + X^2 - 1`, the reduction is folded into the differences `u`, `v`, `w`, `z` of the
right factor's coefficients. -/
@[inline] def mul (a b : Ext5) : Ext5 :=
  let u := b.c1 - b.c4
  let v := b.c0 - b.c3
  let w := b.c4 - b.c2
  let z := b.c3 - u
  ⟨mulAdd4 a.c0 b.c0 a.c1 b.c4 a.c2 b.c3 a.c3 b.c2 + a.c4 * u,
    mulAdd4 a.c0 b.c1 a.c1 b.c0 a.c2 b.c4 a.c3 b.c3 + a.c4 * b.c2,
    mulAdd4 a.c0 b.c2 a.c1 u a.c2 v a.c3 w + a.c4 * z,
    mulAdd4 a.c0 b.c3 a.c1 b.c2 a.c2 u a.c3 v + a.c4 * w,
    mulAdd4 a.c0 b.c4 a.c1 b.c3 a.c2 b.c2 a.c3 u + a.c4 * v⟩

instance : Mul Ext5 := ⟨mul⟩

/-- Exponentiation by repeated squaring. -/
@[specialize] def pow (a : Ext5) (n : ℕ) : Ext5 := npowBinRec n a

/-- The Fermat inversion exponent `p^5 - 2`. -/
def invExp : ℕ := fieldSize ^ 5 - 2

/-- Inverse by Fermat's little theorem, `a⁻¹ = a ^ (p^5 - 2)`. The zero element maps to zero. -/
@[inline] def inv (a : Ext5) : Ext5 := pow a invExp

instance : Inv Ext5 := ⟨inv⟩

theorem inv_def (a : Ext5) : a⁻¹ = inv a := rfl
instance : Div Ext5 := ⟨fun a b ↦ a * b⁻¹⟩

/-- The spec field's parameters: `X^5 + X^2 - 1` over the fast carrier, the lower coefficients
`(-1, 0, 1, 0, 0)`. -/
def params : ExtensionParams Field where
  d := 5
  two_le := by norm_num
  lower := #v[-1, 0, 1, 0, 0]
  q := fieldSize

/-- The spec field's parameters are those of `KoalaBear.Ext5`, mapped to the fast carrier. -/
theorem params_eq_map : params = ext5Params.map (ringEquiv.symm : KoalaBear.Field →+* Field) := by
  unfold params ExtensionParams.map ext5Params
  congr 1
  refine Vector.ext fun i hi ↦ ?_
  simp only [Vector.getElem_map]
  have hi : i < 5 := hi
  interval_cases i <;> simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, map_neg, map_one, map_zero]

instance : Fact (Nat.card Field = params.q) := ⟨natCard_fastField⟩

instance : Fact (Irreducible params.poly) :=
  ⟨params_eq_map ▸
    ExtensionParams.irreducible_map_poly _ _ (Fact.out (p := Irreducible ext5Params.poly))⟩

/-- The spec field `Field[X] / (X^5 + X^2 - 1)`. -/
abbrev Spec : Type := Ext params

@[simp] theorem card_spec : Fintype.card Spec = fieldSize ^ 5 := Ext.card_ext

/-- The spec field's parameters. -/
abbrev P : ExtensionParams Field := params

/-- The `k`-th coordinate. -/
def coord (a : Ext5) : ℕ → Field
  | 0 => a.c0
  | 1 => a.c1
  | 2 => a.c2
  | 3 => a.c3
  | _ => a.c4

/-- The same element of the spec field. -/
def toSpec (a : Ext5) : Spec := Ext.ofFn (P := P) fun i ↦ coord a i

/-- The fast element with the spec field element's coordinates. -/
def ofSpec (x : Spec) : Ext5 :=
  ⟨Ext.coeffNat x 0, Ext.coeffNat x 1, Ext.coeffNat x 2, Ext.coeffNat x 3, Ext.coeffNat x 4⟩

theorem d_eq : P.d = 5 := rfl

theorem coeffNat_toSpec (a : Ext5) {k : ℕ} (hk : k < 5) :
    Ext.coeffNat (toSpec a) k = coord a k := by
  rw [Ext.coeffNat_of_lt _ (by rw [d_eq]; exact hk)]
  simp only [toSpec, Ext.coeff_ofFn]

/-- Two spec elements agree when their first five coordinates do. -/
theorem spec_ext {x y : Spec} (h : ∀ k < 5, Ext.coeffNat x k = Ext.coeffNat y k) :
    x = y := by
  ext ⟨k, hk⟩
  have := h k hk
  rwa [Ext.coeffNat_of_lt _ hk, Ext.coeffNat_of_lt _ hk] at this

theorem ext' {a b : Ext5} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) (h2 : a.c2 = b.c2)
    (h3 : a.c3 = b.c3) (h4 : a.c4 = b.c4) : a = b := by
  cases a; cases b; simp_all

theorem toSpec_ofSpec (x : Spec) : toSpec (ofSpec x) = x := by
  apply spec_ext
  intro k hk
  rw [coeffNat_toSpec _ hk]
  interval_cases k <;> rfl

theorem ofSpec_toSpec (a : Ext5) : ofSpec (toSpec a) = a := by
  apply ext'
  · rw [ofSpec, coeffNat_toSpec a (by decide : 0 < 5)]; rfl
  · rw [ofSpec, coeffNat_toSpec a (by decide : 1 < 5)]; rfl
  · rw [ofSpec, coeffNat_toSpec a (by decide : 2 < 5)]; rfl
  · rw [ofSpec, coeffNat_toSpec a (by decide : 3 < 5)]; rfl
  · rw [ofSpec, coeffNat_toSpec a (by decide : 4 < 5)]; rfl

theorem toSpec_injective : Function.Injective toSpec :=
  Function.LeftInverse.injective ofSpec_toSpec

/-- The coordinates' image in the quotient. -/
local notation "ι" => algebraMap Field (AdjoinRoot P.poly)

/-- The coordinates of `toSpec a` in the adjoined-root quotient. -/
theorem toQuot_toSpec (a : Ext5) :
    Ext.toQuot (toSpec a) =
      ι a.c0 + ι a.c1 * Ext.rt P + ι a.c2 * Ext.rt P ^ 2 + ι a.c3 * Ext.rt P ^ 3 +
        ι a.c4 * Ext.rt P ^ 4 := by
  rw [Ext.toQuot_rangeForm, d_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, mul_one, zero_add]
  rw [coeffNat_toSpec a (by decide : 0 < 5), coeffNat_toSpec a (by decide : 1 < 5),
    coeffNat_toSpec a (by decide : 2 < 5), coeffNat_toSpec a (by decide : 3 < 5),
    coeffNat_toSpec a (by decide : 4 < 5)]
  rfl

/-- The defining relation of the root in the quotient. -/
theorem rt_pow_five : Ext.rt P ^ 5 = 1 - Ext.rt P ^ 2 := by
  have h : Ext.rt P ^ 5 + ∑ i : Fin 5, ι (P.lowerCoeff i) * Ext.rt P ^ (i : ℕ) = 0 :=
    Ext.rt_relation
  rw [Fin.sum_univ_five,
    show P.lowerCoeff (0 : Fin 5) = -1 from rfl, show P.lowerCoeff (1 : Fin 5) = 0 from rfl,
    show P.lowerCoeff (2 : Fin 5) = 1 from rfl, show P.lowerCoeff (3 : Fin 5) = 0 from rfl,
    show P.lowerCoeff (4 : Fin 5) = 0 from rfl] at h
  simp only [map_neg, map_one, map_zero, Fin.val_zero, Fin.val_two, pow_zero] at h
  linear_combination h

@[simp] theorem toSpec_zero : toSpec 0 = 0 := by
  apply spec_ext; intro k hk
  have hk' : k < P.d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_zero]
  interval_cases k <;> rfl

@[simp] theorem toSpec_one : toSpec 1 = 1 := by
  apply spec_ext; intro k hk
  have hk' : k < P.d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_one]
  interval_cases k <;> rfl

@[simp] theorem toSpec_add (a b : Ext5) : toSpec (a + b) = toSpec a + toSpec b := by
  apply spec_ext; intro k hk
  have hk' : k < P.d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_add,
    ← Ext.coeffNat_of_lt _ hk', ← Ext.coeffNat_of_lt _ hk',
    coeffNat_toSpec _ hk, coeffNat_toSpec _ hk]
  interval_cases k <;> rfl

@[simp] theorem toSpec_neg (a : Ext5) : toSpec (-a) = -toSpec a := by
  apply spec_ext; intro k hk
  have hk' : k < P.d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_neg,
    ← Ext.coeffNat_of_lt _ hk', coeffNat_toSpec _ hk]
  interval_cases k <;> rfl

@[simp] theorem toSpec_sub (a b : Ext5) : toSpec (a - b) = toSpec a - toSpec b := by
  apply spec_ext; intro k hk
  have hk' : k < P.d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_sub,
    ← Ext.coeffNat_of_lt _ hk', ← Ext.coeffNat_of_lt _ hk',
    coeffNat_toSpec _ hk, coeffNat_toSpec _ hk]
  interval_cases k <;> rfl

@[simp] theorem toSpec_mul (a b : Ext5) : toSpec (a * b) = toSpec a * toSpec b := by
  apply Ext.toQuot_injective
  rw [Ext.toQuot_mul, toQuot_toSpec, toQuot_toSpec, toQuot_toSpec]
  simp only [show a * b = mul a b from rfl, mul, mulAdd4_eq, map_add, map_sub, map_mul]
  set a0 := ι a.c0
  set a1 := ι a.c1
  set a2 := ι a.c2
  set a3 := ι a.c3
  set a4 := ι a.c4
  set b0 := ι b.c0
  set b1 := ι b.c1
  set b2 := ι b.c2
  set b3 := ι b.c3
  set b4 := ι b.c4
  set r := Ext.rt P
  linear_combination -((a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1) + (a2 * b4 + a3 * b3 + a4 * b2) * r +
    (a3 * b4 + a4 * b3) * r ^ 2 + a4 * b4 * (r ^ 3 - 1)) * rt_pow_five

/-! ### Inversion -/

/-- `toSpec` turns fast powers into spec powers. -/
@[simp] theorem toSpec_pow (a : Ext5) (n : ℕ) : toSpec (pow a n) = toSpec a ^ n := by
  let : Semigroup Ext5 :=
    { mul_assoc x y z := toSpec_injective (by simp only [toSpec_mul, _root_.mul_assoc]) }
  induction n with
  | zero => rw [pow, npowBinRec_zero, toSpec_one, _root_.pow_zero]
  | succ n ih => rw [pow, npowBinRec_succ, ← pow, toSpec_mul, ih, _root_.pow_succ]

theorem toSpec_inv (a : Ext5) : toSpec a⁻¹ = (toSpec a)⁻¹ := by
  have hq : 3 ≤ fieldSize ^ 5 :=
    le_trans (by unfold fieldSize; decide) (Nat.le_self_pow (by decide) _)
  rw [inv_def, inv, toSpec_pow]
  by_cases ha : toSpec a = 0
  · rw [ha, inv_zero, zero_pow (by unfold invExp; omega)]
  · refine eq_inv_of_mul_eq_one_left ?_
    have h := FiniteField.pow_card_sub_one_eq_one (toSpec a) ha
    rw [card_spec] at h
    rw [← _root_.pow_succ, show invExp + 1 = fieldSize ^ 5 - 1 by unfold invExp; omega, h]

@[simp] theorem toSpec_div (a b : Ext5) : toSpec (a / b) = toSpec a / toSpec b := by
  rw [div_eq_mul_inv, ← toSpec_inv, ← toSpec_mul]; rfl

@[simp] theorem toSpec_ofBase (x : Field) : toSpec (ofBase x) = Ext.ofBase x := by
  apply spec_ext; intro k hk
  have hk' : k < P.d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_ofBase]
  interval_cases k <;> rfl

@[simp] theorem toSpec_smul (x : Field) (a : Ext5) : toSpec (smul x a) = x • toSpec a := by
  apply spec_ext; intro k hk
  have hk' : k < P.d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_smul,
    ← Ext.coeffNat_of_lt _ hk', coeffNat_toSpec _ hk]
  interval_cases k <;> rfl

/-- The fast and spec quintic extensions are isomorphic rings. -/
def specEquiv : Ext5 ≃+* Spec where
  toFun := toSpec
  invFun := ofSpec
  left_inv := ofSpec_toSpec
  right_inv := toSpec_ofSpec
  map_mul' := toSpec_mul
  map_add' := toSpec_add

@[simp] theorem specEquiv_apply (a : Ext5) : specEquiv a = toSpec a := rfl

/-! ### Encoding -/

/-- The five coefficient encodings in ascending order. -/
instance : ByteCodec Ext5 where
  width := 5 * ByteCodec.width Field
  toBytes a := ByteCodec.toBytes (#v[a.c0, a.c1, a.c2, a.c3, a.c4] : Vector Field 5)
  ofBytes? b :=
    (ByteCodec.ofBytes? b : Option (Vector Field 5)).map fun v ↦ ⟨v[0], v[1], v[2], v[3], v[4]⟩
  ofBytes?_toBytes a := by simp only [ByteCodec.ofBytes?_toBytes, Option.map_some]; rfl

/-- The fast and spec quintic extensions encode the same element identically. -/
theorem toBytes_toSpec (a : Ext5) : ByteCodec.toBytes (toSpec a) = ByteCodec.toBytes a := by
  have hc : (toSpec a).coeffs.toList = [a.c0, a.c1, a.c2, a.c3, a.c4] := by
    apply List.ext_getElem (by rw [Vector.length_toList]; rfl)
    intro k hk _
    have hk5 : k < 5 := by rw [Vector.length_toList] at hk; exact hk
    have e : (toSpec a).coeffs.toList[k]'hk = Ext.coeffNat (toSpec a) k := by
      rw [Vector.getElem_toList, Ext.coeffNat_of_lt _ (by rw [d_eq]; exact hk5)]; rfl
    rw [e, coeffNat_toSpec _ hk5]
    interval_cases k <;> rfl
  apply Vector.toList_inj.mp
  rw [Ext.toBytes_eq, ByteCodec.toList_toBytes_vector, hc]
  rfl

end Ext5

end KoalaBear.Fast
