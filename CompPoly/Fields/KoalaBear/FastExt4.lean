/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.KoalaBear.Ext4
public import CompPoly.Fields.KoalaBear.Fast
public import CompPoly.Fields.Montgomery.Native32Bytes
public import CompPoly.Fields.Extension.Bytes
public import Mathlib.Tactic.ReduceModChar

/-!
# The degree-4 extension of KoalaBear over the fast carrier

`KoalaBear.Fast.Ext4` is `KoalaBear[X] / (X^4 - 3)` with four Montgomery coefficients, the same
field as the spec `KoalaBear.Ext4` and as Plonky3's `BinomialExtensionField<KoalaBear, 4>`.

* Multiplication reduces each output coefficient once: it is a sum of four products, with `3`
  folded into the left factors, and `mulAdd4` reduces such a sum with a single Montgomery step.
* Inversion uses the norm to the base field. Writing `a = α + X β` with `α, β ∈ F(X²)`,
  `a · σ(a) = g₀ + g₁ X²` for the automorphism `σ : X ↦ -X`, and `N = g₀² - 3 g₁²`, so
  `a⁻¹ = σ(a) (g₀ - g₁ X²) N⁻¹` costs one base-field inversion.

`toSpec` maps into the spec field, and `toSpec_add`, `toSpec_mul`, `toSpec_inv`, … show that every
operation agrees with it; `specEquiv` packages it as a ring isomorphism. The byte encoding is the
four coefficient encodings in ascending order, as for the spec field and Plonky3
(`toBytes_toSpec`).
-/

@[expose] public section

namespace KoalaBear.Fast

open CompPoly CompPoly.Extension Montgomery.Native32 Polynomial

/-- `c0 + c1 X + c2 X^2 + c3 X^3` in `KoalaBear[X] / (X^4 - 3)`, with fast coefficients. -/
structure Ext4 where
  c0 : Field
  c1 : Field
  c2 : Field
  c3 : Field
deriving DecidableEq

namespace Ext4

/-- `3 x`, the binomial constant applied to a coefficient. -/
@[inline] def triple (x : Field) : Field := x + x + x

instance : Zero Ext4 := ⟨⟨0, 0, 0, 0⟩⟩
instance : One Ext4 := ⟨⟨1, 0, 0, 0⟩⟩
instance : Inhabited Ext4 := ⟨0⟩
instance : Add Ext4 := ⟨fun a b ↦ ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩⟩
instance : Neg Ext4 := ⟨fun a ↦ ⟨-a.c0, -a.c1, -a.c2, -a.c3⟩⟩
instance : Sub Ext4 := ⟨fun a b ↦ ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2, a.c3 - b.c3⟩⟩

/-- A base-field element. -/
@[inline] def ofBase (x : Field) : Ext4 := ⟨x, 0, 0, 0⟩

/-- Multiplication by a base-field element. -/
@[inline] def smul (x : Field) (a : Ext4) : Ext4 := ⟨x * a.c0, x * a.c1, x * a.c2, x * a.c3⟩

/-- Product modulo `X^4 - 3`, one Montgomery reduction per output coefficient. -/
@[inline] def mul (a b : Ext4) : Ext4 :=
  let w1 := triple a.c1
  let w2 := triple a.c2
  let w3 := triple a.c3
  ⟨mulAdd4 a.c0 b.c0 w1 b.c3 w2 b.c2 w3 b.c1,
    mulAdd4 a.c0 b.c1 a.c1 b.c0 w2 b.c3 w3 b.c2,
    mulAdd4 a.c0 b.c2 a.c1 b.c1 a.c2 b.c0 w3 b.c3,
    mulAdd4 a.c0 b.c3 a.c1 b.c2 a.c2 b.c1 a.c3 b.c0⟩

instance : Mul Ext4 := ⟨mul⟩

/-- The constant coordinate of `a · σ(a)` for `σ : X ↦ -X`. -/
@[inline] def g0 (a : Ext4) : Field :=
  a.c0 * a.c0 + triple (a.c2 * a.c2) - triple (a.c1 * a.c3 + a.c1 * a.c3)

/-- The `X²` coordinate of `a · σ(a)`. -/
@[inline] def g1 (a : Ext4) : Field :=
  a.c0 * a.c2 + a.c0 * a.c2 - a.c1 * a.c1 - triple (a.c3 * a.c3)

/-- The norm `g₀² - 3 g₁²` of `a` to the base field. -/
@[inline] def norm (a : Ext4) : Field := g0 a * g0 a - triple (g1 a * g1 a)

/-- Inverse through the norm to the base field: `a · σ(a) = g₀ + g₁ X²` for `σ : X ↦ -X`, and
`a⁻¹ = σ(a) (g₀ - g₁ X²) / (g₀² - 3 g₁²)`. The zero element maps to zero. -/
@[inline] def inv (a : Ext4) : Ext4 :=
  let g0 := g0 a
  let g1 := g1 a
  let ni := (norm a)⁻¹
  ⟨(a.c0 * g0 - triple (a.c2 * g1)) * ni, (triple (a.c3 * g1) - a.c1 * g0) * ni,
    (a.c2 * g0 - a.c0 * g1) * ni, (a.c1 * g1 - a.c3 * g0) * ni⟩

instance : Inv Ext4 := ⟨inv⟩
instance : Div Ext4 := ⟨fun a b ↦ a * b⁻¹⟩

/-- The spec field's parameters. -/
abbrev P : ExtensionParams KoalaBear.Field := ext4Params.toExtensionParams

/-- The `k`-th coordinate in the spec base field. -/
def coord (a : Ext4) : ℕ → KoalaBear.Field
  | 0 => FastField.toField a.c0
  | 1 => FastField.toField a.c1
  | 2 => FastField.toField a.c2
  | _ => FastField.toField a.c3

/-- The same element of the spec field `KoalaBear.Ext4`. -/
def toSpec (a : Ext4) : KoalaBear.Ext4 := Ext.ofFn (P := P) fun i ↦ coord a i

/-- The fast element with the spec field element's coordinates. -/
def ofSpec (x : KoalaBear.Ext4) : Ext4 :=
  ⟨ofField (Ext.coeffNat x 0), ofField (Ext.coeffNat x 1), ofField (Ext.coeffNat x 2),
    ofField (Ext.coeffNat x 3)⟩

theorem d_eq : P.d = 4 := rfl

theorem coeffNat_toSpec (a : Ext4) {k : ℕ} (hk : k < 4) :
    Ext.coeffNat (toSpec a) k = coord a k := by
  rw [Ext.coeffNat_of_lt _ (by rw [d_eq]; exact hk)]
  simp only [toSpec, Ext.coeff_ofFn]

/-- Two spec elements agree when their first four coordinates do. -/
theorem spec_ext {x y : KoalaBear.Ext4} (h : ∀ k < 4, Ext.coeffNat x k = Ext.coeffNat y k) :
    x = y := by
  ext ⟨k, hk⟩
  have := h k hk
  rwa [Ext.coeffNat_of_lt _ hk, Ext.coeffNat_of_lt _ hk] at this

theorem ext' {a b : Ext4} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) (h2 : a.c2 = b.c2)
    (h3 : a.c3 = b.c3) : a = b := by
  cases a; cases b; simp_all

theorem toSpec_ofSpec (x : KoalaBear.Ext4) : toSpec (ofSpec x) = x := by
  apply spec_ext
  intro k hk
  rw [coeffNat_toSpec _ hk]
  interval_cases k <;> simp only [coord, ofSpec, ofField, toField_ofField]

theorem ofSpec_toSpec (a : Ext4) : ofSpec (toSpec a) = a := by
  apply ext'
  · rw [ofSpec, coeffNat_toSpec a (by decide : 0 < 4)]; exact ofField_toField _
  · rw [ofSpec, coeffNat_toSpec a (by decide : 1 < 4)]; exact ofField_toField _
  · rw [ofSpec, coeffNat_toSpec a (by decide : 2 < 4)]; exact ofField_toField _
  · rw [ofSpec, coeffNat_toSpec a (by decide : 3 < 4)]; exact ofField_toField _

theorem toSpec_injective : Function.Injective toSpec :=
  Function.LeftInverse.injective ofSpec_toSpec

/-- The coordinates of `toSpec a` in the adjoined-root quotient. -/
theorem toQuot_toSpec (a : Ext4) :
    Ext.toQuot (toSpec a) =
      algebraMap _ _ (FastField.toField a.c0) +
        algebraMap _ _ (FastField.toField a.c1) * Ext.rt P +
        algebraMap _ _ (FastField.toField a.c2) * Ext.rt P ^ 2 +
        algebraMap _ _ (FastField.toField a.c3) * Ext.rt P ^ 3 := by
  rw [Ext.toQuot_rangeForm, d_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, mul_one, zero_add]
  rw [coeffNat_toSpec a (by decide : 0 < 4), coeffNat_toSpec a (by decide : 1 < 4),
    coeffNat_toSpec a (by decide : 2 < 4), coeffNat_toSpec a (by decide : 3 < 4)]
  rfl

/-- The defining relation of the root in the quotient. -/
theorem rt_pow_four : Ext.rt P ^ 4 = 3 := by
  rw [show (4 : ℕ) = ext4Params.d from rfl, Ext.rt_pow_d_binomial ext4Params, ext4Params_W,
    map_ofNat]

@[simp] theorem toSpec_zero : toSpec 0 = 0 := by
  apply spec_ext; intro k hk
  have hk' : k < P.d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_zero]
  interval_cases k <;> exact toField_zero

@[simp] theorem toSpec_one : toSpec 1 = 1 := by
  apply spec_ext; intro k hk
  have hk' : k < P.d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_one]
  interval_cases k <;> simp only [coord, show (1 : Ext4).c0 = 1 from rfl,
    show (1 : Ext4).c1 = 0 from rfl, show (1 : Ext4).c2 = 0 from rfl,
    show (1 : Ext4).c3 = 0 from rfl, toField_one, toField_zero] <;> rfl

@[simp] theorem toSpec_add (a b : Ext4) : toSpec (a + b) = toSpec a + toSpec b := by
  apply spec_ext; intro k hk
  have hk' : k < P.d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_add,
    ← Ext.coeffNat_of_lt _ hk', ← Ext.coeffNat_of_lt _ hk',
    coeffNat_toSpec _ hk, coeffNat_toSpec _ hk]
  interval_cases k <;> exact toField_add _ _

@[simp] theorem toSpec_neg (a : Ext4) : toSpec (-a) = -toSpec a := by
  apply spec_ext; intro k hk
  have hk' : k < P.d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_neg,
    ← Ext.coeffNat_of_lt _ hk', coeffNat_toSpec _ hk]
  interval_cases k <;> exact toField_neg _

@[simp] theorem toSpec_sub (a b : Ext4) : toSpec (a - b) = toSpec a - toSpec b := by
  apply spec_ext; intro k hk
  have hk' : k < P.d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_sub,
    ← Ext.coeffNat_of_lt _ hk', ← Ext.coeffNat_of_lt _ hk',
    coeffNat_toSpec _ hk, coeffNat_toSpec _ hk]
  interval_cases k <;> exact toField_sub _ _

@[simp] theorem toSpec_mul (a b : Ext4) : toSpec (a * b) = toSpec a * toSpec b := by
  apply Ext.toQuot_injective
  rw [Ext.toQuot_mul, toQuot_toSpec, toQuot_toSpec, toQuot_toSpec]
  simp only [show a * b = mul a b from rfl, mul, triple, toField_mulAdd4, toField_add, map_add,
    map_mul]
  linear_combination -(algebraMap _ _ (FastField.toField a.c1) *
      algebraMap _ _ (FastField.toField b.c3) +
    algebraMap _ _ (FastField.toField a.c2) * algebraMap _ _ (FastField.toField b.c2) +
    algebraMap _ _ (FastField.toField a.c3) * algebraMap _ _ (FastField.toField b.c1) +
    (algebraMap _ _ (FastField.toField a.c2) * algebraMap _ _ (FastField.toField b.c3) +
      algebraMap _ _ (FastField.toField a.c3) * algebraMap _ _ (FastField.toField b.c2)) *
      Ext.rt P +
    algebraMap _ _ (FastField.toField a.c3) * algebraMap _ _ (FastField.toField b.c3) *
      Ext.rt P ^ 2) * rt_pow_four

/-! ### Inversion -/

/-- The base-field cardinality as a numeral, for `reduce_mod_char`. -/
private abbrev qNum : ℕ := 2130706433

/-- `3` is a quadratic non-residue: `3 ^ ((p - 1) / 2) = -1`. -/
theorem three_not_square (x : KoalaBear.Field) : x ^ 2 ≠ 3 := by
  intro hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : (3 : ZMod qNum) ≠ 0 := by decide
    exact this (by simpa using hx.symm)
  have hpow : (3 : KoalaBear.Field) ^ ((qNum - 1) / 2) = 1 := by
    rw [← hx, ← pow_mul, show 2 * ((qNum - 1) / 2) = fieldSize - 1 from rfl]
    exact ZMod.pow_card_sub_one_eq_one hx0
  have hneg : (3 : ZMod qNum) ^ ((qNum - 1) / 2) ≠ 1 := by
    reduce_mod_char
    decide
  exact hneg hpow

/-- The coordinates' image in the quotient. -/
local notation "ι" => algebraMap KoalaBear.Field (AdjoinRoot P.poly)

/-- The automorphism `X ↦ -X` of the quotient field. -/
noncomputable def sigma : AdjoinRoot P.poly →ₐ[KoalaBear.Field] AdjoinRoot P.poly :=
  AdjoinRoot.liftAlgHom P.poly (Algebra.ofId _ _) (-Ext.rt P) (by
    have hp : P.poly = X ^ 4 - C 3 := by
      rw [ext4Params.toExtensionParams_poly, BinomialParams.poly, ext4Params_d, ext4Params_W]
    conv_lhs => arg 3; rw [hp]
    rw [eval₂_sub, eval₂_X_pow, eval₂_C]
    simp only [map_ofNat]
    rw [neg_pow, show ((-1 : AdjoinRoot P.poly) ^ 4) = 1 by norm_num, one_mul, rt_pow_four,
      sub_self])

theorem sigma_rt : sigma (Ext.rt P) = -Ext.rt P := AdjoinRoot.liftAlgHom_root _ _ _ _

/-- `a · σ(a)` lies in `F(X²)`. -/
theorem toQuot_mul_sigma (a : Ext4) :
    Ext.toQuot (toSpec a) * sigma (Ext.toQuot (toSpec a)) =
      ι (FastField.toField a.c0 ^ 2 + 3 * FastField.toField a.c2 ^ 2 -
          6 * FastField.toField a.c1 * FastField.toField a.c3) +
        ι (2 * FastField.toField a.c0 * FastField.toField a.c2 - FastField.toField a.c1 ^ 2 -
          3 * FastField.toField a.c3 ^ 2) * Ext.rt P ^ 2 := by
  rw [toQuot_toSpec]
  simp only [map_add, map_mul, map_pow, map_sub, AlgHom.commutes, sigma_rt, map_ofNat]
  linear_combination (ι (FastField.toField a.c2) ^ 2 -
    2 * ι (FastField.toField a.c1) * ι (FastField.toField a.c3) -
    ι (FastField.toField a.c3) ^ 2 * Ext.rt P ^ 2) * rt_pow_four

/-- The norm of a nonzero element is nonzero. -/
theorem norm_ne_zero (a : Ext4) (ha : toSpec a ≠ 0) :
    (FastField.toField a.c0 ^ 2 + 3 * FastField.toField a.c2 ^ 2 -
        6 * FastField.toField a.c1 * FastField.toField a.c3) ^ 2 -
      3 * (2 * FastField.toField a.c0 * FastField.toField a.c2 - FastField.toField a.c1 ^ 2 -
        3 * FastField.toField a.c3 ^ 2) ^ 2 ≠ 0 := by
  set g0 := FastField.toField a.c0 ^ 2 + 3 * FastField.toField a.c2 ^ 2 -
    6 * FastField.toField a.c1 * FastField.toField a.c3
  set g1 := 2 * FastField.toField a.c0 * FastField.toField a.c2 - FastField.toField a.c1 ^ 2 -
    3 * FastField.toField a.c3 ^ 2
  have hA : Ext.toQuot (toSpec a) ≠ 0 := by
    rwa [Ne, ← Ext.toQuot_zero, Ext.toQuot_inj]
  have hσ : sigma (Ext.toQuot (toSpec a)) ≠ 0 := by
    rw [Ne, ← map_zero sigma]
    exact fun h ↦ hA ((sigma : AdjoinRoot P.poly →+* AdjoinRoot P.poly).injective h)
  have hγ : ι g0 + ι g1 * Ext.rt P ^ 2 ≠ 0 := by
    rw [← toQuot_mul_sigma]; exact mul_ne_zero hA hσ
  intro hN
  by_cases hg1 : g1 = 0
  · have hg0 : g0 = 0 := by
      rw [hg1] at hN; simpa using hN
    exact hγ (by rw [hg0, hg1, map_zero, zero_mul, add_zero])
  · apply three_not_square (g0 * g1⁻¹)
    field_simp
    linear_combination hN

theorem toField_g0 (a : Ext4) : FastField.toField (g0 a) =
    FastField.toField a.c0 ^ 2 + 3 * FastField.toField a.c2 ^ 2 -
      6 * FastField.toField a.c1 * FastField.toField a.c3 := by
  simp only [g0, triple, toField_add, toField_sub, toField_mul]; ring

theorem toField_g1 (a : Ext4) : FastField.toField (g1 a) =
    2 * FastField.toField a.c0 * FastField.toField a.c2 - FastField.toField a.c1 ^ 2 -
      3 * FastField.toField a.c3 ^ 2 := by
  simp only [g1, triple, toField_add, toField_sub, toField_mul]; ring

theorem toField_norm (a : Ext4) : FastField.toField (norm a) =
    FastField.toField (g0 a) ^ 2 - 3 * FastField.toField (g1 a) ^ 2 := by
  simp only [norm, triple, toField_add, toField_sub, toField_mul]; ring

/-- `a` times its inverse is `N · N⁻¹` for the norm `N`. -/
theorem toQuot_mul_inv (a : Ext4) :
    Ext.toQuot (toSpec a) * Ext.toQuot (toSpec a⁻¹) =
      ι (FastField.toField (norm a)) * ι (FastField.toField (norm a))⁻¹ := by
  rw [toQuot_toSpec, toQuot_toSpec]
  simp only [show a⁻¹ = inv a from rfl, inv, triple, toField_mul, toField_add, toField_sub,
    toField_inv, map_add, map_mul, map_sub]
  rw [toField_norm]
  set x0 := ι (FastField.toField a.c0)
  set x1 := ι (FastField.toField a.c1)
  set x2 := ι (FastField.toField a.c2)
  set x3 := ι (FastField.toField a.c3)
  set y0 := ι (FastField.toField (g0 a))
  set y1 := ι (FastField.toField (g1 a))
  have h0 : y0 = x0 ^ 2 + 3 * x2 ^ 2 - 6 * x1 * x3 := by
    simp only [y0, x0, x1, x2, x3, toField_g0, map_add, map_sub, map_mul, map_pow, map_ofNat]
  have h1 : y1 = 2 * x0 * x2 - x1 ^ 2 - 3 * x3 ^ 2 := by
    simp only [y1, x0, x1, x2, x3, toField_g1, map_sub, map_mul, map_pow, map_ofNat]
  set n := ι (FastField.toField (g0 a) ^ 2 - 3 * FastField.toField (g1 a) ^ 2)⁻¹
  have hn : ι (FastField.toField (g0 a) ^ 2 - 3 * FastField.toField (g1 a) ^ 2) =
      y0 ^ 2 - 3 * y1 ^ 2 := by
    simp only [y0, y1, map_sub, map_mul, map_pow, map_ofNat]
  rw [hn, h0, h1]
  set r := Ext.rt P
  linear_combination n * (-(2 * x0 * x2 - x1 ^ 2 - 3 * x3 ^ 2) ^ 2 +
    (x2 ^ 2 - 2 * x1 * x3 - x3 ^ 2 * r ^ 2) *
      ((x0 ^ 2 + 3 * x2 ^ 2 - 6 * x1 * x3) - (2 * x0 * x2 - x1 ^ 2 - 3 * x3 ^ 2) * r ^ 2) -
    (x0 + x1 * r + x2 * r ^ 2 + x3 * r ^ 3) *
      (-x2 * (2 * x0 * x2 - x1 ^ 2 - 3 * x3 ^ 2) + x3 * (2 * x0 * x2 - x1 ^ 2 - 3 * x3 ^ 2) * r)) *
    rt_pow_four

theorem toSpec_inv (a : Ext4) : toSpec a⁻¹ = (toSpec a)⁻¹ := by
  by_cases ha : toSpec a = 0
  · obtain rfl : a = 0 := toSpec_injective (by rw [ha, toSpec_zero])
    rw [toSpec_zero, inv_zero]
    apply spec_ext; intro k hk
    have hk' : k < P.d := by rw [d_eq]; exact hk
    rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_zero]
    interval_cases k <;> simp only [coord, show (0 : Ext4)⁻¹ = inv 0 from rfl, inv, triple,
      show (0 : Ext4).c0 = 0 from rfl, show (0 : Ext4).c1 = 0 from rfl,
      show (0 : Ext4).c2 = 0 from rfl, show (0 : Ext4).c3 = 0 from rfl, toField_zero, zero_mul,
      sub_zero, add_zero]
  · have hN : FastField.toField (norm a) ≠ 0 := by
      rw [toField_norm, toField_g0, toField_g1]; exact norm_ne_zero a ha
    apply eq_inv_of_mul_eq_one_right
    apply Ext.toQuot_injective
    rw [Ext.toQuot_mul, toQuot_mul_inv, Ext.toQuot_one, ← map_mul, mul_inv_cancel₀ hN, map_one]

@[simp] theorem toSpec_div (a b : Ext4) : toSpec (a / b) = toSpec a / toSpec b := by
  rw [div_eq_mul_inv, ← toSpec_inv, ← toSpec_mul]; rfl

@[simp] theorem toSpec_ofBase (x : Field) :
    toSpec (ofBase x) = Ext.ofBase (FastField.toField x) := by
  apply spec_ext; intro k hk
  have hk' : k < P.d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_ofBase]
  interval_cases k <;> simp only [coord, ofBase, toField_zero] <;> rfl

@[simp] theorem toSpec_smul (x : Field) (a : Ext4) :
    toSpec (smul x a) = FastField.toField x • toSpec a := by
  apply spec_ext; intro k hk
  have hk' : k < P.d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_smul,
    ← Ext.coeffNat_of_lt _ hk', coeffNat_toSpec _ hk]
  interval_cases k <;> exact toField_mul _ _

/-- The fast and spec quartic extensions are isomorphic rings. -/
def specEquiv : Ext4 ≃+* KoalaBear.Ext4 where
  toFun := toSpec
  invFun := ofSpec
  left_inv := ofSpec_toSpec
  right_inv := toSpec_ofSpec
  map_mul' := toSpec_mul
  map_add' := toSpec_add

@[simp] theorem specEquiv_apply (a : Ext4) : specEquiv a = toSpec a := rfl

/-! ### Encoding -/

/-- The four coefficient encodings in ascending order. -/
instance : ByteCodec Ext4 where
  width := 4 * ByteCodec.width Field
  toBytes a := ByteCodec.toBytes (#v[a.c0, a.c1, a.c2, a.c3] : Vector Field 4)
  ofBytes? b :=
    (ByteCodec.ofBytes? b : Option (Vector Field 4)).map fun v ↦ ⟨v[0], v[1], v[2], v[3]⟩
  ofBytes?_toBytes a := by simp only [ByteCodec.ofBytes?_toBytes, Option.map_some]; rfl

/-- The fast and spec quartic extensions encode the same element identically. -/
theorem toBytes_toSpec (a : Ext4) : ByteCodec.toBytes (toSpec a) = ByteCodec.toBytes a := by
  have hc : (toSpec a).coeffs.toList = [FastField.toField a.c0, FastField.toField a.c1,
      FastField.toField a.c2, FastField.toField a.c3] := by
    apply List.ext_getElem (by rw [Vector.length_toList]; rfl)
    intro k hk _
    have hk4 : k < 4 := by rw [Vector.length_toList] at hk; exact hk
    have e : (toSpec a).coeffs.toList[k]'hk = Ext.coeffNat (toSpec a) k := by
      rw [Vector.getElem_toList, Ext.coeffNat_of_lt _ (by rw [d_eq]; exact hk4)]; rfl
    rw [e, coeffNat_toSpec _ hk4]
    interval_cases k <;> rfl
  apply Vector.toList_inj.mp
  rw [Ext.toBytes_eq, ByteCodec.toList_toBytes_vector, hc]
  change _ = ByteCodec.encodeList [a.c0, a.c1, a.c2, a.c3]
  simp only [ByteCodec.encodeList_cons, ByteCodec.encodeList_nil,
    ← FastField.toBytes_eq_toBytes_toField]

end Ext4

end KoalaBear.Fast
