/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Montgomery.Basic
public import CompPoly.Fields.Montgomery.Native64x8Defs

/-!
# Native Montgomery arithmetic over eight 32-bit limbs

Raw word operations for prime moduli below `2 ^ 255`, represented as eight 32-bit limbs
carried in the low halves of `UInt64` words (`Limbs8`).  This is the multi-limb sibling of
`Montgomery/Native32.lean`: every operation is a straight-line chain of `@[inline]` word
helpers, and each helper comes with an existential `toNat` specification that names its
outputs as fresh naturals.  The definitions themselves live in the zero-import module
`Montgomery/Native64x8Defs`; this module states and proves everything about them.

The limb helpers (`adcLo`/`adcCo`, `sbbLo`/`sbbBo`, `macLo`/`macHi`, `montM`) are combined by
the two telescoping lemmas `carry_chain_sum` and `borrow_chain_sum`, which turn an eight-step
carry or borrow chain into a single identity between recomposed values.  Every correctness
statement is generic in the modulus limbs; concrete fields supply their constants through
the `Mont64x8Field` class of `Montgomery/Native64x8Field`.

Conditional subtraction, addition, subtraction and negation are proved correct here.  The
CIOS multiplication round `mulRound` is defined in `Montgomery/Native64x8Defs`; its state
invariant is proved in the sibling module that builds the field carrier.

## Main results

* `condSub_toNat`, `add_toNat`, `sub_toNat`, `neg_toNat` — correctness of the raw operations
* `addLimbs_toNat`, `subLimbs_spec` — the underlying carry/borrow chains
-/

@[expose] public section

namespace Montgomery
namespace Native64x8

/-! ## Word-level specifications -/

private theorem land_mask32 (x : ℕ) : x &&& 4294967295 = x % 4294967296 := by
  have h : (4294967295 : ℕ) = 2 ^ 32 - 1 := by norm_num
  have h2 : (4294967296 : ℕ) = 2 ^ 32 := by norm_num
  rw [h, h2, Nat.and_two_pow_sub_one_eq_mod]

private theorem toNat_zero : (0 : UInt64).toNat = 0 := rfl

/-- Add-with-carry, existential form: the low limb and the carry-out are named as fresh
naturals together with their defining equations, so that a chain of them is a linear system
over plain variables. -/
theorem adc_spec (x y c : UInt64) (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32)
    (hc : c.toNat ≤ 1) :
    ∃ s co : ℕ, (adcLo x y c).toNat = s ∧ (adcCo x y c).toNat = co ∧
      s + 2 ^ 32 * co = x.toNat + y.toNat + c.toNat ∧ co ≤ 1 ∧ s < 2 ^ 32 := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  simp only [adcLo, adcCo, mask, UInt64.toNat_and, UInt64.toNat_add,
    UInt64.toNat_shiftRight, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, land_mask32]
  omega

/-- Add-with-carry when the first summand is one bit wider than a limb. -/
theorem adc_spec_wide (x y c : UInt64) (hx : x.toNat < 2 ^ 33) (hy : y.toNat < 2 ^ 32)
    (hc : c.toNat ≤ 1) :
    ∃ s co : ℕ, (adcLo x y c).toNat = s ∧ (adcCo x y c).toNat = co ∧
      s + 2 ^ 32 * co = x.toNat + y.toNat + c.toNat ∧ co ≤ 2 ∧ s < 2 ^ 32 := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  simp only [adcLo, adcCo, mask, UInt64.toNat_and, UInt64.toNat_add,
    UInt64.toNat_shiftRight, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, land_mask32]
  omega

/-- Subtract-with-borrow, existential form. -/
theorem sbb_spec (x y b : UInt64) (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32)
    (hb : b.toNat ≤ 1) :
    ∃ m bo : ℕ, (sbbLo x y b).toNat = m ∧ (sbbBo x y b).toNat = bo ∧
      m + y.toNat + b.toNat = x.toNat + 2 ^ 32 * bo ∧ bo ≤ 1 ∧ m < 2 ^ 32 := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  simp only [sbbLo, sbbBo, mask, UInt64.toNat_and, UInt64.toNat_sub,
    UInt64.toNat_shiftRight, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, land_mask32]
  omega

/-- Multiply-accumulate, existential form.  The accumulator, both factors and the carry-in
all fit in 32 bits, so `t + x * y + c` cannot overflow a 64-bit word. -/
theorem mac_spec (t x y c : UInt64) (ht : t.toNat < 2 ^ 32) (hx : x.toNat < 2 ^ 32)
    (hy : y.toNat < 2 ^ 32) (hc : c.toNat < 2 ^ 32) :
    ∃ lo hi : ℕ, (macLo t x y c).toNat = lo ∧ (macHi t x y c).toNat = hi ∧
      lo + 2 ^ 32 * hi = t.toNat + x.toNat * y.toNat + c.toNat ∧ hi < 2 ^ 32 ∧
      lo < 2 ^ 32 := by
  have hp : x.toNat * y.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  refine ⟨_, _, rfl, rfl, ?_⟩
  simp only [macLo, macHi, mask, UInt64.toNat_and, UInt64.toNat_add, UInt64.toNat_mul,
    UInt64.toNat_shiftRight, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, land_mask32]
  generalize x.toNat * y.toNat = p at hp ⊢
  omega

/-- The Montgomery multiplier agrees with its natural-number specification. -/
theorem montM_toNat (s negInv : UInt64) (hs : s.toNat < 2 ^ 32) (hn : negInv.toNat < 2 ^ 32) :
    (montM s negInv).toNat = s.toNat * negInv.toNat % 2 ^ 32 := by
  have hp : s.toNat * negInv.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [montM, mask, UInt64.toNat_and, UInt64.toNat_mul, UInt64.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod, land_mask32,
    Nat.mod_eq_of_lt (show s.toNat < 4294967296 by omega)]
  generalize s.toNat * negInv.toNat = p at hp ⊢
  omega

theorem adcLo_lt (x y c : UInt64) : (adcLo x y c).toNat < 2 ^ 32 := by
  simp only [adcLo, mask, UInt64.toNat_and, UInt64.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, land_mask32]
  omega

theorem sbbLo_lt (x y b : UInt64) : (sbbLo x y b).toNat < 2 ^ 32 := by
  simp only [sbbLo, mask, UInt64.toNat_and, UInt64.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, land_mask32]
  omega

theorem macLo_lt (t x y c : UInt64) : (macLo t x y c).toNat < 2 ^ 32 := by
  simp only [macLo, mask, UInt64.toNat_and, UInt64.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, land_mask32]
  omega

theorem montM_lt (s negInv : UInt64) : (montM s negInv).toNat < 2 ^ 32 := by
  simp only [montM, mask, UInt64.toNat_and, UInt64.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, land_mask32]
  omega

/-! ## Eight-limb values -/

namespace Limbs8

theorem zero_bounded : zero.Bounded := by
  simp only [Bounded, zero, toNat_zero]
  norm_num

theorem zero_toNat : zero.toNat = 0 := by
  simp only [toNat, zero, toNat_zero]

theorem one_bounded : one.Bounded := by decide

theorem one_toNat : one.toNat = 1 := by decide

theorem ofNat_bounded (n : ℕ) : (ofNat n).Bounded := by
  simp only [Bounded, ofNat, UInt64.toNat_ofNat', land_mask32]
  omega

theorem ofNat_toNat (n : ℕ) : (ofNat n).toNat = n % 2 ^ 256 := by
  simp only [toNat, ofNat, UInt64.toNat_ofNat', land_mask32]
  omega

end Limbs8

/-- A recomposed value with 32-bit limbs stays below `2 ^ 256`. -/
theorem sum8_lt {a0 a1 a2 a3 a4 a5 a6 a7 : ℕ} (h0 : a0 < 2 ^ 32) (h1 : a1 < 2 ^ 32)
    (h2 : a2 < 2 ^ 32) (h3 : a3 < 2 ^ 32) (h4 : a4 < 2 ^ 32) (h5 : a5 < 2 ^ 32)
    (h6 : a6 < 2 ^ 32) (h7 : a7 < 2 ^ 32) :
    a0 + 2 ^ 32 * a1 + 2 ^ 64 * a2 + 2 ^ 96 * a3 + 2 ^ 128 * a4 + 2 ^ 160 * a5 + 2 ^ 192 * a6 +
      2 ^ 224 * a7 < 2 ^ 256 := by
  omega

/-- Bounded limb vectors are determined by their value. -/
theorem Limbs8.ext_of_toNat {x y : Limbs8} (hx : x.Bounded) (hy : y.Bounded)
    (h : x.toNat = y.toNat) : x = y := by
  obtain ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩ := hx
  obtain ⟨hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7⟩ := hy
  simp only [Limbs8.toNat] at h
  have e0 : x.l0.toNat = y.l0.toNat := by omega
  have e1 : x.l1.toNat = y.l1.toNat := by omega
  have e2 : x.l2.toNat = y.l2.toNat := by omega
  have e3 : x.l3.toNat = y.l3.toNat := by omega
  have e4 : x.l4.toNat = y.l4.toNat := by omega
  have e5 : x.l5.toNat = y.l5.toNat := by omega
  have e6 : x.l6.toNat = y.l6.toNat := by omega
  have e7 : x.l7.toNat = y.l7.toNat := by omega
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := x
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ := y
  simp only [Limbs8.mk.injEq]
  exact ⟨UInt64.toNat_inj.mp e0, UInt64.toNat_inj.mp e1, UInt64.toNat_inj.mp e2,
    UInt64.toNat_inj.mp e3, UInt64.toNat_inj.mp e4, UInt64.toNat_inj.mp e5,
    UInt64.toNat_inj.mp e6, UInt64.toNat_inj.mp e7⟩

/-- A bounded eight-limb value is below `2 ^ 256`. -/
theorem Limbs8.toNat_lt {x : Limbs8} (hx : x.Bounded) : x.toNat < 2 ^ 256 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hx
  exact sum8_lt h0 h1 h2 h3 h4 h5 h6 h7

/-! ### Chain lemmas

Telescoping identities for an eight-step carry or borrow chain.  They are stated over plain
naturals and the `y` slots are arbitrary, so `carry_chain_sum` serves both the
add-with-carry chains and the multiply-accumulate chains of CIOS, where `yᵢ` is a limb
product. -/

/-- Weighted telescoping of an eight-step carry chain. -/
theorem carry_chain_sum {x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : ℕ}
    {s0 s1 s2 s3 s4 s5 s6 s7 cin c0 c1 c2 c3 c4 c5 c6 c7 : ℕ}
    (e0 : s0 + 2 ^ 32 * c0 = x0 + y0 + cin)
    (e1 : s1 + 2 ^ 32 * c1 = x1 + y1 + c0)
    (e2 : s2 + 2 ^ 32 * c2 = x2 + y2 + c1)
    (e3 : s3 + 2 ^ 32 * c3 = x3 + y3 + c2)
    (e4 : s4 + 2 ^ 32 * c4 = x4 + y4 + c3)
    (e5 : s5 + 2 ^ 32 * c5 = x5 + y5 + c4)
    (e6 : s6 + 2 ^ 32 * c6 = x6 + y6 + c5)
    (e7 : s7 + 2 ^ 32 * c7 = x7 + y7 + c6) :
    s0 + 2 ^ 32 * s1 + 2 ^ 64 * s2 + 2 ^ 96 * s3 + 2 ^ 128 * s4 + 2 ^ 160 * s5 + 2 ^ 192 * s6 +
      2 ^ 224 * s7 + 2 ^ 256 * c7 =
    (x0 + 2 ^ 32 * x1 + 2 ^ 64 * x2 + 2 ^ 96 * x3 + 2 ^ 128 * x4 + 2 ^ 160 * x5 +
      2 ^ 192 * x6 + 2 ^ 224 * x7) +
      (y0 + 2 ^ 32 * y1 + 2 ^ 64 * y2 + 2 ^ 96 * y3 + 2 ^ 128 * y4 + 2 ^ 160 * y5 +
      2 ^ 192 * y6 + 2 ^ 224 * y7) + cin := by
  omega

/-- Weighted telescoping of an eight-step borrow chain. -/
theorem borrow_chain_sum {x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : ℕ}
    {m0 m1 m2 m3 m4 m5 m6 m7 bin b0 b1 b2 b3 b4 b5 b6 b7 : ℕ}
    (e0 : m0 + y0 + bin = x0 + 2 ^ 32 * b0)
    (e1 : m1 + y1 + b0 = x1 + 2 ^ 32 * b1)
    (e2 : m2 + y2 + b1 = x2 + 2 ^ 32 * b2)
    (e3 : m3 + y3 + b2 = x3 + 2 ^ 32 * b3)
    (e4 : m4 + y4 + b3 = x4 + 2 ^ 32 * b4)
    (e5 : m5 + y5 + b4 = x5 + 2 ^ 32 * b5)
    (e6 : m6 + y6 + b5 = x6 + 2 ^ 32 * b6)
    (e7 : m7 + y7 + b6 = x7 + 2 ^ 32 * b7) :
    (m0 + 2 ^ 32 * m1 + 2 ^ 64 * m2 + 2 ^ 96 * m3 + 2 ^ 128 * m4 + 2 ^ 160 * m5 +
      2 ^ 192 * m6 + 2 ^ 224 * m7) +
      (y0 + 2 ^ 32 * y1 + 2 ^ 64 * y2 + 2 ^ 96 * y3 + 2 ^ 128 * y4 + 2 ^ 160 * y5 +
      2 ^ 192 * y6 + 2 ^ 224 * y7) + bin =
      x0 + 2 ^ 32 * x1 + 2 ^ 64 * x2 + 2 ^ 96 * x3 + 2 ^ 128 * x4 + 2 ^ 160 * x5 + 2 ^ 192 * x6 +
      2 ^ 224 * x7 + 2 ^ 256 * b7 := by
  omega

/-! ### Branch lemmas

The situations that a borrow chain can produce, each as a standalone linear problem over a
handful of naturals. -/

private theorem cond_of_borrow_zero {M Q T : ℕ} (h : M + Q = T) (hM : M < 2 ^ 256) :
    M = if T < Q then T else T - Q := by
  rw [if_neg (by omega)]
  omega

private theorem cond_of_borrow_one {M Q T : ℕ} (h : M + Q = T + 2 ^ 256) (hM : M < 2 ^ 256) :
    T = if T < Q then T else T - Q := by
  rw [if_pos (by omega)]

private theorem cond_eq_mod {T Q : ℕ} (h : T < 2 * Q) :
    (if T < Q then T else T - Q) = T % Q := by
  by_cases hc : T < Q
  · rw [if_pos hc, Nat.mod_eq_of_lt hc]
  · rw [if_neg hc]
    conv_rhs => rw [show T = T - Q + Q by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private theorem carry_top_zero {S A B Q c : ℕ} (h : S + 2 ^ 256 * c = A + B)
    (hS : S < 2 ^ 256) (hA : A < Q) (hB : B < Q) (hQ : 2 * Q < 2 ^ 256) :
    S = A + B ∧ S < 2 * Q := by
  omega

private theorem sub_of_borrow_zero {A B Q D : ℕ} (h : D + B = A + 2 ^ 256 * 0)
    (hB : B < Q) (hA : A < Q) : D = (A + (Q - B)) % Q := by
  conv_rhs => rw [show A + (Q - B) = D + Q by omega]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private theorem sub_of_borrow_one {A B Q D E c : ℕ} (hD : D + B = A + 2 ^ 256 * 1)
    (hE : E + 2 ^ 256 * c = D + Q) (hDlt : D < 2 ^ 256) (hElt : E < 2 ^ 256)
    (hB : B < Q) (hA : A < Q) (hQ : 2 * Q < 2 ^ 256) : E = (A + (Q - B)) % Q := by
  rw [show A + (Q - B) = E by omega, Nat.mod_eq_of_lt (by omega)]

/-! ## Limbwise addition and subtraction -/

theorem addLimbs_bounded (a b : Limbs8) : (addLimbs a b).Bounded := by
  simp only [addLimbs, Limbs8.Bounded]
  exact ⟨adcLo_lt _ _ _, adcLo_lt _ _ _, adcLo_lt _ _ _, adcLo_lt _ _ _,
    adcLo_lt _ _ _, adcLo_lt _ _ _, adcLo_lt _ _ _, adcLo_lt _ _ _⟩

/-- The limbwise sum and the discarded top carry recompose the sum of the inputs. -/
theorem addLimbs_toNat (a b : Limbs8) (ha : a.Bounded) (hb : b.Bounded) :
    ∃ c : ℕ, c ≤ 1 ∧ (addLimbs a b).toNat + 2 ^ 256 * c = a.toNat + b.toNat := by
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := ha
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hb
  obtain ⟨s0, c0, ds0, dc0, e0, gc0, hs0⟩ :=
    adc_spec a.l0 b.l0 (0 : UInt64) ha0 hb0 (by decide)
  obtain ⟨s1, c1, ds1, dc1, e1, gc1, hs1⟩ :=
    adc_spec a.l1 b.l1 _ ha1 hb1 (dc0 ▸ gc0)
  obtain ⟨s2, c2, ds2, dc2, e2, gc2, hs2⟩ :=
    adc_spec a.l2 b.l2 _ ha2 hb2 (dc1 ▸ gc1)
  obtain ⟨s3, c3, ds3, dc3, e3, gc3, hs3⟩ :=
    adc_spec a.l3 b.l3 _ ha3 hb3 (dc2 ▸ gc2)
  obtain ⟨s4, c4, ds4, dc4, e4, gc4, hs4⟩ :=
    adc_spec a.l4 b.l4 _ ha4 hb4 (dc3 ▸ gc3)
  obtain ⟨s5, c5, ds5, dc5, e5, gc5, hs5⟩ :=
    adc_spec a.l5 b.l5 _ ha5 hb5 (dc4 ▸ gc4)
  obtain ⟨s6, c6, ds6, dc6, e6, gc6, hs6⟩ :=
    adc_spec a.l6 b.l6 _ ha6 hb6 (dc5 ▸ gc5)
  obtain ⟨s7, c7, ds7, dc7, e7, gc7, hs7⟩ :=
    adc_spec a.l7 b.l7 _ ha7 hb7 (dc6 ▸ gc6)
  simp only [dc0, dc1, dc2, dc3, dc4, dc5, dc6, toNat_zero] at e0 e1 e2 e3 e4 e5 e6 e7
  refine ⟨c7, gc7, ?_⟩
  simp only [addLimbs, Limbs8.toNat, ds0, ds1, ds2, ds3, ds4, ds5, ds6, ds7]
  have h := carry_chain_sum e0 e1 e2 e3 e4 e5 e6 e7
  simp only [Nat.add_zero] at h
  exact h

theorem subLimbs_bounded (a b : Limbs8) : (subLimbs a b).Bounded := by
  simp only [subLimbs, Limbs8.Bounded]
  exact ⟨sbbLo_lt _ _ _, sbbLo_lt _ _ _, sbbLo_lt _ _ _, sbbLo_lt _ _ _,
    sbbLo_lt _ _ _, sbbLo_lt _ _ _, sbbLo_lt _ _ _, sbbLo_lt _ _ _⟩

/-- The limbwise difference and the final borrow recompose the difference of the inputs. -/
theorem subLimbs_spec (a b : Limbs8) (ha : a.Bounded) (hb : b.Bounded) :
    (subBorrow a b).toNat ≤ 1 ∧
      (subLimbs a b).toNat + b.toNat = a.toNat + 2 ^ 256 * (subBorrow a b).toNat := by
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := ha
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hb
  obtain ⟨d0, c0, dd0, dc0, e0, gc0, hd0⟩ :=
    sbb_spec a.l0 b.l0 (0 : UInt64) ha0 hb0 (by decide)
  obtain ⟨d1, c1, dd1, dc1, e1, gc1, hd1⟩ :=
    sbb_spec a.l1 b.l1 _ ha1 hb1 (dc0 ▸ gc0)
  obtain ⟨d2, c2, dd2, dc2, e2, gc2, hd2⟩ :=
    sbb_spec a.l2 b.l2 _ ha2 hb2 (dc1 ▸ gc1)
  obtain ⟨d3, c3, dd3, dc3, e3, gc3, hd3⟩ :=
    sbb_spec a.l3 b.l3 _ ha3 hb3 (dc2 ▸ gc2)
  obtain ⟨d4, c4, dd4, dc4, e4, gc4, hd4⟩ :=
    sbb_spec a.l4 b.l4 _ ha4 hb4 (dc3 ▸ gc3)
  obtain ⟨d5, c5, dd5, dc5, e5, gc5, hd5⟩ :=
    sbb_spec a.l5 b.l5 _ ha5 hb5 (dc4 ▸ gc4)
  obtain ⟨d6, c6, dd6, dc6, e6, gc6, hd6⟩ :=
    sbb_spec a.l6 b.l6 _ ha6 hb6 (dc5 ▸ gc5)
  obtain ⟨d7, c7, dd7, dc7, e7, gc7, hd7⟩ :=
    sbb_spec a.l7 b.l7 _ ha7 hb7 (dc6 ▸ gc6)
  simp only [dc0, dc1, dc2, dc3, dc4, dc5, dc6, toNat_zero] at e0 e1 e2 e3 e4 e5 e6 e7
  refine ⟨?_, ?_⟩
  · simp only [subBorrow, dc7]
    exact gc7
  · simp only [subLimbs, subBorrow, Limbs8.toNat, dd0, dd1, dd2, dd3, dd4, dd5, dd6, dd7,
      dc7]
    have h := borrow_chain_sum e0 e1 e2 e3 e4 e5 e6 e7
    simp only [Nat.add_zero] at h
    exact h

/-! ## Conditional subtraction -/

theorem condSub_bounded (q t : Limbs8) (ht : t.Bounded) : (condSub q t).Bounded := by
  simp only [condSub]
  split
  · exact subLimbs_bounded t q
  · exact ht

/-- `condSub` subtracts the modulus exactly when the input is at least the modulus. -/
theorem condSub_toNat (q t : Limbs8) (hq : q.Bounded) (ht : t.Bounded) :
    (condSub q t).toNat = if t.toNat < q.toNat then t.toNat else t.toNat - q.toNat := by
  obtain ⟨hbo, hchain⟩ := subLimbs_spec t q ht hq
  have hD := Limbs8.toNat_lt (subLimbs_bounded t q)
  simp only [condSub, beq_iff_eq, ← UInt64.toNat_inj, toNat_zero]
  split
  case isTrue h =>
    rw [h, Nat.mul_zero, Nat.add_zero] at hchain
    exact cond_of_borrow_zero hchain hD
  case isFalse h =>
    rw [show (subBorrow t q).toNat = 1 by omega, Nat.mul_one] at hchain
    exact cond_of_borrow_one hchain hD

/-- `condSub` returns a canonical representative for inputs below `2 * q`. -/
theorem condSub_lt (q t : Limbs8) (hq : q.Bounded) (ht : t.Bounded)
    (h : t.toNat < 2 * q.toNat) : (condSub q t).toNat < q.toNat := by
  rw [condSub_toNat q t hq ht]
  split <;> omega

/-! ## Field operations -/

theorem add_bounded (q a b : Limbs8) : (add q a b).Bounded :=
  condSub_bounded _ _ (addLimbs_bounded a b)

theorem sub_bounded (q a b : Limbs8) : (sub q a b).Bounded := by
  simp only [sub]
  split
  · exact subLimbs_bounded a b
  · exact addLimbs_bounded _ _

theorem neg_bounded (q a : Limbs8) : (neg q a).Bounded := sub_bounded _ _ _

/-- Modular addition is correct for canonical inputs of a modulus below `2 ^ 255`. -/
theorem add_toNat (q a b : Limbs8) (hq : q.Bounded) (ha : a.Bounded) (hb : b.Bounded)
    (hq2 : 2 * q.toNat < 2 ^ 256) (haq : a.toNat < q.toNat) (hbq : b.toNat < q.toNat) :
    (add q a b).toNat = (a.toNat + b.toNat) % q.toNat := by
  obtain ⟨c, hc, hchain⟩ := addLimbs_toNat a b ha hb
  obtain ⟨hsum, hlt⟩ :=
    carry_top_zero hchain (Limbs8.toNat_lt (addLimbs_bounded a b)) haq hbq hq2
  simp only [add]
  rw [condSub_toNat q _ hq (addLimbs_bounded a b), hsum]
  rw [hsum] at hlt
  exact cond_eq_mod hlt

theorem add_lt (q a b : Limbs8) (hq : q.Bounded) (ha : a.Bounded) (hb : b.Bounded)
    (hq2 : 2 * q.toNat < 2 ^ 256) (haq : a.toNat < q.toNat) (hbq : b.toNat < q.toNat) :
    (add q a b).toNat < q.toNat := by
  rw [add_toNat q a b hq ha hb hq2 haq hbq]
  exact Nat.mod_lt _ (by omega)

/-- Modular subtraction is correct for canonical inputs of a modulus below `2 ^ 255`. -/
theorem sub_toNat (q a b : Limbs8) (hq : q.Bounded) (ha : a.Bounded) (hb : b.Bounded)
    (hq2 : 2 * q.toNat < 2 ^ 256) (haq : a.toNat < q.toNat) (hbq : b.toNat < q.toNat) :
    (sub q a b).toNat = (a.toNat + (q.toNat - b.toNat)) % q.toNat := by
  obtain ⟨hbo, hchain⟩ := subLimbs_spec a b ha hb
  have hD := Limbs8.toNat_lt (subLimbs_bounded a b)
  simp only [sub, beq_iff_eq, ← UInt64.toNat_inj, toNat_zero]
  split
  case isTrue h =>
    rw [h] at hchain
    exact sub_of_borrow_zero hchain hbq haq
  case isFalse h =>
    rw [show (subBorrow a b).toNat = 1 by omega] at hchain
    obtain ⟨c, _, hchainE⟩ := addLimbs_toNat _ q (subLimbs_bounded a b) hq
    exact sub_of_borrow_one hchain hchainE hD
      (Limbs8.toNat_lt (addLimbs_bounded _ _)) hbq haq hq2

theorem sub_lt (q a b : Limbs8) (hq : q.Bounded) (ha : a.Bounded) (hb : b.Bounded)
    (hq2 : 2 * q.toNat < 2 ^ 256) (haq : a.toNat < q.toNat) (hbq : b.toNat < q.toNat) :
    (sub q a b).toNat < q.toNat := by
  rw [sub_toNat q a b hq ha hb hq2 haq hbq]
  exact Nat.mod_lt _ (by omega)

/-- Modular negation is correct for canonical inputs of a modulus below `2 ^ 255`. -/
theorem neg_toNat (q a : Limbs8) (hq : q.Bounded) (ha : a.Bounded)
    (hq2 : 2 * q.toNat < 2 ^ 256) (haq : a.toNat < q.toNat) :
    (neg q a).toNat = (q.toNat - a.toNat) % q.toNat := by
  simp only [neg]
  rw [sub_toNat q Limbs8.zero a hq Limbs8.zero_bounded ha hq2
    (by rw [Limbs8.zero_toNat]; omega) haq, Limbs8.zero_toNat, Nat.zero_add]

theorem neg_lt (q a : Limbs8) (hq : q.Bounded) (ha : a.Bounded)
    (hq2 : 2 * q.toNat < 2 ^ 256) (haq : a.toNat < q.toNat) : (neg q a).toNat < q.toNat :=
  sub_lt q Limbs8.zero a hq Limbs8.zero_bounded ha hq2
    (by rw [Limbs8.zero_toNat]; omega) haq

end Native64x8
end Montgomery
