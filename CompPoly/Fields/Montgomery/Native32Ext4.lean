/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Extension
public import CompPoly.Fields.Extension.Bytes
public import CompPoly.Fields.Montgomery.Native32Bytes

/-!
# Fast quartic binomial extensions of 32-bit Montgomery fields

For a prime `p` with a `Mont32Field p` instance, a `Binomial4 p` instance chooses `W` with
`X^4 - W` irreducible over `FastField p`. `Ext4 p` is then `FastField p [X] / (X^4 - W)` with four
Montgomery coefficients, Plonky3's `BinomialExtensionField<F, 4>`.

* Multiplication reduces each output coefficient once: it is a sum of four products, with `W`
  folded into the left factors, and `mulAdd4` reduces such a sum with a single Montgomery step.
  `Binomial4.mulW` multiplies by `W`, so a field can supply a cheaper form than a product, such
  as `x + x + x` for `W = 3`.
* Inversion uses the norm to the base field. Writing `a = α + X β` with `α, β ∈ F(X²)`,
  `a · σ(a) = g₀ + g₁ X²` for the automorphism `σ : X ↦ -X`, and `N = g₀² - W g₁²`, so
  `a⁻¹ = σ(a) (g₀ - g₁ X²) N⁻¹` costs one base-field inversion. `N ≠ 0` for `a ≠ 0` because `W` is
  not a square, which follows from the irreducibility of `X^4 - W`.

The spec field is `Ext4.Spec p`, the framework's `Ext` over the fast base field itself for the
binomial `X^4 - W` (`Ext4.params p`). `toSpec` maps into it, `toSpec_add`, `toSpec_mul`,
`toSpec_inv`, … show that every operation agrees with it, and `specEquiv` packages it as a ring
isomorphism. The byte encoding is the four coefficient encodings in ascending order, as for the
spec field and Plonky3 (`toBytes_toSpec`).
-/

@[expose] public section

namespace Montgomery.Native32

open CompPoly CompPoly.Extension Polynomial

/-- An irreducible binomial `X^4 - W` over `FastField p`, with a fast multiplication by `W`. -/
class Binomial4 (p : ℕ) [Mont32Field p] where
  /-- The extension adjoins a fourth root of `W`. -/
  W : FastField p
  /-- Multiplication by `W`, by default the product. -/
  mulW : FastField p → FastField p := (W * ·)
  mulW_eq : ∀ x, mulW x = W * x := by intro; rfl
  /-- `X^4 - W` is irreducible, so the quotient is a field. -/
  irreducible : Irreducible (X ^ 4 - C W : (FastField p)[X])

/-- `c0 + c1 X + c2 X^2 + c3 X^3` in `FastField p [X] / (X^4 - W)`. -/
structure Ext4 (p : ℕ) [Mont32Field p] where
  c0 : FastField p
  c1 : FastField p
  c2 : FastField p
  c3 : FastField p
deriving DecidableEq

namespace Ext4

variable {p : ℕ} [Mont32Field p]

instance : Zero (Ext4 p) := ⟨⟨0, 0, 0, 0⟩⟩
instance : One (Ext4 p) := ⟨⟨1, 0, 0, 0⟩⟩
instance : Inhabited (Ext4 p) := ⟨0⟩
instance : Add (Ext4 p) := ⟨fun a b ↦ ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩⟩
instance : Neg (Ext4 p) := ⟨fun a ↦ ⟨-a.c0, -a.c1, -a.c2, -a.c3⟩⟩
instance : Sub (Ext4 p) := ⟨fun a b ↦ ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2, a.c3 - b.c3⟩⟩

/-- A base-field element. -/
@[inline] def ofBase (x : FastField p) : Ext4 p := ⟨x, 0, 0, 0⟩

/-- Multiplication by a base-field element. -/
@[inline] def smul (x : FastField p) (a : Ext4 p) : Ext4 p :=
  ⟨x * a.c0, x * a.c1, x * a.c2, x * a.c3⟩

theorem ext' {a b : Ext4 p} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) (h2 : a.c2 = b.c2)
    (h3 : a.c3 = b.c3) : a = b := by
  cases a; cases b; simp_all

variable [B : Binomial4 p]

open Binomial4 (W mulW mulW_eq)

/-- Product modulo `X^4 - W`, one Montgomery reduction per output coefficient. -/
@[inline] def mul (a b : Ext4 p) : Ext4 p :=
  let w1 := mulW a.c1
  let w2 := mulW a.c2
  let w3 := mulW a.c3
  ⟨mulAdd4 a.c0 b.c0 w1 b.c3 w2 b.c2 w3 b.c1,
    mulAdd4 a.c0 b.c1 a.c1 b.c0 w2 b.c3 w3 b.c2,
    mulAdd4 a.c0 b.c2 a.c1 b.c1 a.c2 b.c0 w3 b.c3,
    mulAdd4 a.c0 b.c3 a.c1 b.c2 a.c2 b.c1 a.c3 b.c0⟩

instance : Mul (Ext4 p) := ⟨mul⟩

/-- The constant coordinate of `a · σ(a)` for `σ : X ↦ -X`. -/
@[inline] def g0 (a : Ext4 p) : FastField p :=
  a.c0 * a.c0 + mulW (a.c2 * a.c2) - mulW (a.c1 * a.c3 + a.c1 * a.c3)

/-- The `X²` coordinate of `a · σ(a)`. -/
@[inline] def g1 (a : Ext4 p) : FastField p :=
  a.c0 * a.c2 + a.c0 * a.c2 - a.c1 * a.c1 - mulW (a.c3 * a.c3)

/-- The norm `g₀² - W g₁²` of `a` to the base field. -/
@[inline] def norm (a : Ext4 p) : FastField p := g0 a * g0 a - mulW (g1 a * g1 a)

/-- Inverse through the norm to the base field: `a · σ(a) = g₀ + g₁ X²` for `σ : X ↦ -X`, and
`a⁻¹ = σ(a) (g₀ - g₁ X²) / (g₀² - W g₁²)`. The zero element maps to zero. -/
@[inline] def inv (a : Ext4 p) : Ext4 p :=
  let g0 := g0 a
  let g1 := g1 a
  let ni := (norm a)⁻¹
  ⟨(a.c0 * g0 - mulW (a.c2 * g1)) * ni, (mulW (a.c3 * g1) - a.c1 * g0) * ni,
    (a.c2 * g0 - a.c0 * g1) * ni, (a.c1 * g1 - a.c3 * g0) * ni⟩

instance : Inv (Ext4 p) := ⟨inv⟩
instance : Div (Ext4 p) := ⟨fun a b ↦ a * b⁻¹⟩

/-! ### The spec field -/

variable (p) in
/-- The binomial `X^4 - W` as extension parameters over the fast base field. -/
def params : BinomialParams (FastField p) where
  d := 4
  W := W
  two_le := by norm_num
  q := p


variable (p) in
/-- The spec field's parameters, the binomial as a monic modulus. -/
abbrev P : ExtensionParams (FastField p) := (params p).toExtensionParams

variable (p) in
/-- The spec field `FastField p [X] / (X^4 - W)`. -/
abbrev Spec : Type := Ext (P p)

theorem d_eq : (P p).d = 4 := rfl

theorem params_poly : (params p).poly = X ^ 4 - C W := rfl

instance : Fact (Nat.card (FastField p) = (params p).q) := ⟨natCard_fastField⟩

instance : Fact (Irreducible (params p).poly) := ⟨B.irreducible⟩

/-- The irreducibility fact in the form the framework's `Field` instance consumes. -/
instance : Fact (Irreducible (params p).toExtensionParams.poly) :=
  ⟨(params p).toExtensionParams_poly ▸ B.irreducible⟩

@[simp] theorem card_spec : Fintype.card (Spec p) = p ^ 4 := Ext.card_ext

/-- The `k`-th coordinate. -/
def coord (a : Ext4 p) : ℕ → FastField p
  | 0 => a.c0
  | 1 => a.c1
  | 2 => a.c2
  | _ => a.c3

/-- The same element of the spec field. -/
def toSpec (a : Ext4 p) : Spec p := Ext.ofFn (P := P p) fun i ↦ coord a i

/-- The fast element with the spec field element's coordinates. -/
def ofSpec (x : Spec p) : Ext4 p :=
  ⟨Ext.coeffNat x 0, Ext.coeffNat x 1, Ext.coeffNat x 2, Ext.coeffNat x 3⟩

theorem coeffNat_toSpec (a : Ext4 p) {k : ℕ} (hk : k < 4) :
    Ext.coeffNat (toSpec a) k = coord a k := by
  rw [Ext.coeffNat_of_lt _ (by rw [d_eq]; exact hk)]
  simp only [toSpec, Ext.coeff_ofFn]

/-- Two spec elements agree when their first four coordinates do. -/
theorem spec_ext {x y : Spec p} (h : ∀ k < 4, Ext.coeffNat x k = Ext.coeffNat y k) :
    x = y := by
  ext ⟨k, hk⟩
  have := h k hk
  rwa [Ext.coeffNat_of_lt _ hk, Ext.coeffNat_of_lt _ hk] at this

theorem toSpec_ofSpec (x : Spec p) : toSpec (ofSpec x) = x := by
  apply spec_ext
  intro k hk
  rw [coeffNat_toSpec _ hk]
  interval_cases k <;> rfl

theorem ofSpec_toSpec (a : Ext4 p) : ofSpec (toSpec a) = a := by
  apply ext'
  · rw [ofSpec, coeffNat_toSpec a (by decide : 0 < 4)]; rfl
  · rw [ofSpec, coeffNat_toSpec a (by decide : 1 < 4)]; rfl
  · rw [ofSpec, coeffNat_toSpec a (by decide : 2 < 4)]; rfl
  · rw [ofSpec, coeffNat_toSpec a (by decide : 3 < 4)]; rfl

theorem toSpec_injective : Function.Injective (toSpec (p := p)) :=
  Function.LeftInverse.injective ofSpec_toSpec

/-- The coordinates' image in the quotient. -/
local notation "ι" => algebraMap (FastField p) (AdjoinRoot (ExtensionParams.poly (P p)))

/-- The coordinates of `toSpec a` in the adjoined-root quotient. -/
theorem toQuot_toSpec (a : Ext4 p) :
    Ext.toQuot (toSpec a) =
      ι a.c0 + ι a.c1 * Ext.rt (P p) + ι a.c2 * Ext.rt (P p) ^ 2 + ι a.c3 * Ext.rt (P p) ^ 3 := by
  rw [Ext.toQuot_rangeForm, d_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, mul_one, zero_add]
  rw [coeffNat_toSpec a (by decide : 0 < 4), coeffNat_toSpec a (by decide : 1 < 4),
    coeffNat_toSpec a (by decide : 2 < 4), coeffNat_toSpec a (by decide : 3 < 4)]
  rfl

/-- The defining relation of the root in the quotient. -/
theorem rt_pow_four : Ext.rt (P p) ^ 4 = ι W := Ext.rt_pow_d_binomial (params p)

@[simp] theorem toSpec_zero : toSpec (0 : Ext4 p) = 0 := by
  apply spec_ext; intro k hk
  have hk' : k < (P p).d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_zero]
  interval_cases k <;> rfl

@[simp] theorem toSpec_one : toSpec (1 : Ext4 p) = 1 := by
  apply spec_ext; intro k hk
  have hk' : k < (P p).d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_one]
  interval_cases k <;> rfl

@[simp] theorem toSpec_add (a b : Ext4 p) : toSpec (a + b) = toSpec a + toSpec b := by
  apply spec_ext; intro k hk
  have hk' : k < (P p).d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_add,
    ← Ext.coeffNat_of_lt _ hk', ← Ext.coeffNat_of_lt _ hk',
    coeffNat_toSpec _ hk, coeffNat_toSpec _ hk]
  interval_cases k <;> rfl

@[simp] theorem toSpec_neg (a : Ext4 p) : toSpec (-a) = -toSpec a := by
  apply spec_ext; intro k hk
  have hk' : k < (P p).d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_neg,
    ← Ext.coeffNat_of_lt _ hk', coeffNat_toSpec _ hk]
  interval_cases k <;> rfl

@[simp] theorem toSpec_sub (a b : Ext4 p) : toSpec (a - b) = toSpec a - toSpec b := by
  apply spec_ext; intro k hk
  have hk' : k < (P p).d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_sub,
    ← Ext.coeffNat_of_lt _ hk', ← Ext.coeffNat_of_lt _ hk',
    coeffNat_toSpec _ hk, coeffNat_toSpec _ hk]
  interval_cases k <;> rfl

@[simp] theorem toSpec_mul (a b : Ext4 p) : toSpec (a * b) = toSpec a * toSpec b := by
  apply Ext.toQuot_injective
  rw [Ext.toQuot_mul, toQuot_toSpec, toQuot_toSpec, toQuot_toSpec]
  simp only [show a * b = mul a b from rfl, mul, mulAdd4_eq, mulW_eq, map_add, map_mul]
  linear_combination -(ι a.c1 * ι b.c3 + ι a.c2 * ι b.c2 + ι a.c3 * ι b.c1 +
    (ι a.c2 * ι b.c3 + ι a.c3 * ι b.c2) * Ext.rt (P p) + ι a.c3 * ι b.c3 * Ext.rt (P p) ^ 2) *
      rt_pow_four (p := p)

/-! ### Inversion -/

/-- `W` is not a square: otherwise `X^4 - W = (X^2 - x) (X^2 + x)` would factor. -/
theorem W_not_square (x : FastField p) : x ^ 2 ≠ W := by
  intro hx
  have h : (X ^ 4 - C W : (FastField p)[X]) = (X ^ 2 - C x) * (X ^ 2 + C x) := by
    rw [← hx, C_pow]; ring
  rcases B.irreducible.isUnit_or_isUnit h with hu | hu
  · have := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_X_pow_sub_C] at this; omega
  · have := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_X_pow_add_C] at this; omega

/-- The automorphism `X ↦ -X` of the quotient field. -/
noncomputable def sigma : AdjoinRoot (P p).poly →ₐ[FastField p] AdjoinRoot (P p).poly :=
  AdjoinRoot.liftAlgHom (P p).poly (Algebra.ofId _ _) (-Ext.rt (P p)) (by
    conv_lhs => arg 3; rw [(params p).toExtensionParams_poly, params_poly]
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, neg_pow,
      show ((-1 : AdjoinRoot (P p).poly) ^ 4) = 1 by norm_num, one_mul, rt_pow_four]
    exact sub_self _)

theorem sigma_rt : sigma (Ext.rt (P p)) = -Ext.rt (P p) := AdjoinRoot.liftAlgHom_root _ _ _ _

theorem g0_eq (a : Ext4 p) : g0 a = a.c0 ^ 2 + W * a.c2 ^ 2 - 2 * W * a.c1 * a.c3 := by
  simp only [g0, mulW_eq]; ring

theorem g1_eq (a : Ext4 p) : g1 a = 2 * a.c0 * a.c2 - a.c1 ^ 2 - W * a.c3 ^ 2 := by
  simp only [g1, mulW_eq]; ring

theorem norm_eq (a : Ext4 p) : norm a = g0 a ^ 2 - W * g1 a ^ 2 := by
  simp only [norm, mulW_eq]; ring

/-- `a · σ(a)` lies in `F(X²)`. -/
theorem toQuot_mul_sigma (a : Ext4 p) :
    Ext.toQuot (toSpec a) * sigma (Ext.toQuot (toSpec a)) =
      ι (g0 a) + ι (g1 a) * Ext.rt (P p) ^ 2 := by
  rw [toQuot_toSpec, g0_eq, g1_eq]
  simp only [map_add, map_mul, map_pow, map_sub, AlgHom.commutes, sigma_rt, map_ofNat]
  linear_combination (ι a.c2 ^ 2 - 2 * ι a.c1 * ι a.c3 - ι a.c3 ^ 2 * Ext.rt (P p) ^ 2) *
    rt_pow_four (p := p)

/-- The norm of a nonzero element is nonzero. -/
theorem norm_ne_zero (a : Ext4 p) (ha : toSpec a ≠ 0) : norm a ≠ 0 := by
  have hA : Ext.toQuot (toSpec a) ≠ 0 := by
    rwa [Ne, ← Ext.toQuot_zero, Ext.toQuot_inj]
  have hσ : sigma (Ext.toQuot (toSpec a)) ≠ 0 := by
    rw [Ne, ← map_zero sigma]
    exact fun h ↦
      hA ((sigma (p := p) : AdjoinRoot (P p).poly →+* AdjoinRoot (P p).poly).injective h)
  have hγ : ι (g0 a) + ι (g1 a) * Ext.rt (P p) ^ 2 ≠ 0 := by
    rw [← toQuot_mul_sigma]; exact mul_ne_zero hA hσ
  rw [norm_eq]
  intro hN
  by_cases hg1 : g1 a = 0
  · have hg0 : g0 a = 0 := by
      rw [hg1] at hN; simpa using hN
    exact hγ (by rw [hg0, hg1, map_zero, zero_mul, add_zero])
  · apply W_not_square (g0 a * (g1 a)⁻¹)
    field_simp
    linear_combination hN

/-- `a` times its inverse is `N · N⁻¹` for the norm `N`. -/
theorem toQuot_mul_inv (a : Ext4 p) :
    Ext.toQuot (toSpec a) * Ext.toQuot (toSpec a⁻¹) = ι (norm a) * ι (norm a)⁻¹ := by
  rw [toQuot_toSpec, toQuot_toSpec]
  simp only [show a⁻¹ = inv a from rfl, inv, mulW_eq, map_mul, map_sub]
  rw [norm_eq]
  set x0 := ι a.c0
  set x1 := ι a.c1
  set x2 := ι a.c2
  set x3 := ι a.c3
  set w := ι W
  set y0 := ι (g0 a)
  set y1 := ι (g1 a)
  have h0 : y0 = x0 ^ 2 + w * x2 ^ 2 - 2 * w * x1 * x3 := by
    simp only [y0, x0, x1, x2, x3, w, g0_eq, map_add, map_sub, map_mul, map_pow, map_ofNat]
  have h1 : y1 = 2 * x0 * x2 - x1 ^ 2 - w * x3 ^ 2 := by
    simp only [y1, x0, x1, x2, x3, w, g1_eq, map_sub, map_mul, map_pow, map_ofNat]
  set n := ι (g0 a ^ 2 - W * g1 a ^ 2)⁻¹
  have hn : ι (g0 a ^ 2 - W * g1 a ^ 2) = y0 ^ 2 - w * y1 ^ 2 := by
    simp only [y0, y1, w, map_sub, map_mul, map_pow]
  rw [hn, h0, h1]
  set r := Ext.rt (P p)
  linear_combination n * (-(2 * x0 * x2 - x1 ^ 2 - w * x3 ^ 2) ^ 2 +
    (x2 ^ 2 - 2 * x1 * x3 - x3 ^ 2 * r ^ 2) *
      ((x0 ^ 2 + w * x2 ^ 2 - 2 * w * x1 * x3) - (2 * x0 * x2 - x1 ^ 2 - w * x3 ^ 2) * r ^ 2) -
    (x0 + x1 * r + x2 * r ^ 2 + x3 * r ^ 3) *
      (-x2 * (2 * x0 * x2 - x1 ^ 2 - w * x3 ^ 2) + x3 * (2 * x0 * x2 - x1 ^ 2 - w * x3 ^ 2) * r)) *
    rt_pow_four (p := p)

theorem inv_zero' : (0 : Ext4 p)⁻¹ = 0 := by
  have hN : norm (0 : Ext4 p) = 0 := by
    rw [norm_eq, g0_eq, g1_eq]
    simp only [show (0 : Ext4 p).c0 = 0 from rfl, show (0 : Ext4 p).c1 = 0 from rfl,
      show (0 : Ext4 p).c2 = 0 from rfl, show (0 : Ext4 p).c3 = 0 from rfl]
    ring
  simp only [show (0 : Ext4 p)⁻¹ = inv 0 from rfl, inv, hN, inv_zero, mul_zero]
  rfl

theorem toSpec_inv (a : Ext4 p) : toSpec a⁻¹ = (toSpec a)⁻¹ := by
  by_cases ha : toSpec a = 0
  · obtain rfl : a = 0 := toSpec_injective (by rw [ha, toSpec_zero])
    rw [toSpec_zero, _root_.inv_zero, inv_zero', toSpec_zero]
  · have hN := norm_ne_zero a ha
    apply eq_inv_of_mul_eq_one_right
    apply Ext.toQuot_injective
    rw [Ext.toQuot_mul, toQuot_mul_inv, Ext.toQuot_one, ← map_mul, mul_inv_cancel₀ hN, map_one]

@[simp] theorem toSpec_div (a b : Ext4 p) : toSpec (a / b) = toSpec a / toSpec b := by
  rw [div_eq_mul_inv, ← toSpec_inv, ← toSpec_mul]; rfl

@[simp] theorem toSpec_ofBase (x : FastField p) : toSpec (ofBase x) = Ext.ofBase x := by
  apply spec_ext; intro k hk
  have hk' : k < (P p).d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_ofBase]
  interval_cases k <;> rfl

@[simp] theorem toSpec_smul (x : FastField p) (a : Ext4 p) : toSpec (smul x a) = x • toSpec a := by
  apply spec_ext; intro k hk
  have hk' : k < (P p).d := by rw [d_eq]; exact hk
  rw [coeffNat_toSpec _ hk, Ext.coeffNat_of_lt _ hk', Ext.coeff_smul,
    ← Ext.coeffNat_of_lt _ hk', coeffNat_toSpec _ hk]
  interval_cases k <;> rfl

variable (p) in
/-- The fast and spec quartic extensions are isomorphic rings. -/
def specEquiv : Ext4 p ≃+* Spec p where
  toFun := toSpec
  invFun := ofSpec
  left_inv := ofSpec_toSpec
  right_inv := toSpec_ofSpec
  map_mul' := toSpec_mul
  map_add' := toSpec_add

@[simp] theorem specEquiv_apply (a : Ext4 p) : specEquiv p a = toSpec a := rfl

/-! ### Encoding -/

omit B in
/-- The four coefficient encodings in ascending order. -/
instance : ByteCodec (Ext4 p) where
  width := 4 * ByteCodec.width (FastField p)
  toBytes a := ByteCodec.toBytes (#v[a.c0, a.c1, a.c2, a.c3] : Vector (FastField p) 4)
  ofBytes? b :=
    (ByteCodec.ofBytes? b : Option (Vector (FastField p) 4)).map fun v ↦ ⟨v[0], v[1], v[2], v[3]⟩
  ofBytes?_toBytes a := by simp only [ByteCodec.ofBytes?_toBytes, Option.map_some]; rfl

/-- The fast and spec quartic extensions encode the same element identically. -/
theorem toBytes_toSpec (a : Ext4 p) : ByteCodec.toBytes (toSpec a) = ByteCodec.toBytes a := by
  have hc : (toSpec a).coeffs.toList = [a.c0, a.c1, a.c2, a.c3] := by
    apply List.ext_getElem (by rw [Vector.length_toList]; rfl)
    intro k hk _
    have hk4 : k < 4 := by rw [Vector.length_toList] at hk; exact hk
    have e : (toSpec a).coeffs.toList[k]'hk = Ext.coeffNat (toSpec a) k := by
      rw [Vector.getElem_toList, Ext.coeffNat_of_lt _ (by rw [d_eq]; exact hk4)]; rfl
    rw [e, coeffNat_toSpec _ hk4]
    interval_cases k <;> rfl
  apply Vector.toList_inj.mp
  rw [Ext.toBytes_eq, ByteCodec.toList_toBytes_vector, hc]
  rfl

end Ext4

end Montgomery.Native32
