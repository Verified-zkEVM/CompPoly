/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPoly.Fields.Montgomery.Basic
public import CompPoly.Fields.Montgomery.Native64x4Defs

/-!
# Native Montgomery arithmetic over four 64-bit limbs

Raw word operations for prime moduli below `2 ^ 256`, represented as four 64-bit limbs
(`Limbs4`); the definitions live in the zero-import module `Montgomery/Native64x4Defs`.  Each
word helper's specification exhibits the pair it returns, so a chain of `let (s, c) := ...`
bindings unfolds to a linear system over naturals that `omega` closes.

## Main results

* `condSub_toNat`, `condSubWide_toNat`, `add_toNat`, `sub_toNat`, `neg_toNat` — correctness
  of the raw operations
* `addLimbs_spec`, `subLimbs_spec` — the underlying carry/borrow chains
* `mac_spec`, `mulHi_spec` — the widening multiply-accumulate
-/

@[expose] public section

namespace Montgomery
namespace Native64x4

/-! ## Word-level specifications -/

/-- One wrapped addition with its overflow flag recomposes the exact sum. -/
private theorem addWord_value (a b : UInt64) :
    (a + b).toNat + 2 ^ 64 * (if a + b < a then (1 : UInt64) else 0).toNat =
      a.toNat + b.toNat := by
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have hmod := Nat.mod_add_div (a.toNat + b.toNat) (2 ^ 64)
  by_cases h : a + b < a
  · have h' := h
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h'
    rw [ite_eq_left h, UInt64.toNat_add, UInt64.toNat_one]
    omega
  · have h' := h
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h'
    rw [ite_eq_right h, UInt64.toNat_add, UInt64.toNat_zero]
    omega

/-- One wrapped subtraction with its borrow flag recomposes the exact difference. -/
private theorem subWord_value (a b : UInt64) :
    (a - b).toNat + b.toNat = a.toNat + 2 ^ 64 * (if a < b then (1 : UInt64) else 0).toNat := by
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have hmod := Nat.mod_add_div (2 ^ 64 - b.toNat + a.toNat) (2 ^ 64)
  by_cases h : a < b
  · have h' := h
    rw [UInt64.lt_iff_toNat_lt] at h'
    rw [ite_eq_left h, UInt64.toNat_sub, UInt64.toNat_one]
    omega
  · have h' := h
    rw [UInt64.lt_iff_toNat_lt] at h'
    rw [ite_eq_right h, UInt64.toNat_sub, UInt64.toNat_zero]
    omega

private theorem flag_le_one (p : Prop) [Decidable p] :
    (if p then (1 : UInt64) else 0).toNat ≤ 1 := by
  split <;> simp

private theorem flag_or_value (p q : Prop) [Decidable p] [Decidable q]
    (h : (if p then (1 : UInt64) else 0).toNat +
      (if q then (1 : UInt64) else 0).toNat ≤ 1) :
    ((if p then (1 : UInt64) else 0) ||| (if q then (1 : UInt64) else 0)).toNat =
      (if p then (1 : UInt64) else 0).toNat +
      (if q then (1 : UInt64) else 0).toNat := by
  by_cases hp : p <;> by_cases hq : q <;>
    simp only [hp, hq, ite_true, ite_false, UInt64.toNat_one, UInt64.toNat_zero] at *
  · omega
  all_goals rfl

/-- Add-with-carry, existential form: the exact sum identity with a one-bit carry. -/
theorem adc_spec (x y c : UInt64) (hc : c.toNat ≤ 1) :
    ∃ s co : UInt64, adc x y c = (s, co) ∧
      s.toNat + 2 ^ 64 * co.toNat = x.toNat + y.toNat + c.toNat ∧ co.toNat ≤ 1 := by
  have h1 := addWord_value x y
  have h2 := addWord_value (x + y) c
  have hf1 := flag_le_one (x + y < x)
  have hf2 := flag_le_one (x + y + c < x + y)
  have hx := UInt64.toNat_lt x
  have hy := UInt64.toNat_lt y
  have hs := UInt64.toNat_lt (x + y + c)
  have hsum : ((if x + y < x then (1 : UInt64) else 0) |||
      (if x + y + c < x + y then (1 : UInt64) else 0)).toNat =
      (if x + y < x then (1 : UInt64) else 0).toNat +
      (if x + y + c < x + y then (1 : UInt64) else 0).toNat := by
    exact flag_or_value _ _ (by omega)
  refine ⟨_, _, rfl, ?_, ?_⟩ <;> rw [hsum] <;> omega

/-- Subtract-with-borrow, existential form: the exact difference identity with a one-bit
borrow. -/
theorem sbb_spec (x y b : UInt64) (hb : b.toNat ≤ 1) :
    ∃ d bo : UInt64, sbb x y b = (d, bo) ∧
      d.toNat + y.toNat + b.toNat = x.toNat + 2 ^ 64 * bo.toNat ∧ bo.toNat ≤ 1 := by
  have h1 := subWord_value x y
  have h2 := subWord_value (x - y) b
  have hf1 := flag_le_one (x < y)
  have hf2 := flag_le_one (x - y < b)
  have hx := UInt64.toNat_lt x
  have hy := UInt64.toNat_lt y
  have hd := UInt64.toNat_lt (x - y - b)
  have hsum : ((if x < y then (1 : UInt64) else 0) |||
      (if x - y < b then (1 : UInt64) else 0)).toNat =
      (if x < y then (1 : UInt64) else 0).toNat +
      (if x - y < b then (1 : UInt64) else 0).toNat := by
    exact flag_or_value _ _ (by omega)
  refine ⟨_, _, rfl, ?_, ?_⟩ <;> rw [hsum] <;> omega

private theorem low32_value (x : UInt64) : (x &&& 0xffffffff).toNat = x.toNat % 2 ^ 32 := by
  rw [UInt64.toNat_and, show ((0xffffffff : UInt64).toNat) = 2 ^ 32 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem high32_value (x : UInt64) : (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight, show ((32 : UInt64).toNat % 64) = 32 from by decide,
    Nat.shiftRight_eq_div_pow]

/-- The low and high words recompose the exact `64 × 64` product. -/
theorem mulHi_spec (a b : UInt64) :
    (a * b).toNat + 2 ^ 64 * (mulHi a b).toNat = a.toNat * b.toNat := by
  let mask : UInt64 := 0xffffffff
  let a0 := a &&& mask
  let a1 := a >>> 32
  let b0 := b &&& mask
  let b1 := b >>> 32
  let w0 := a0 * b0
  let t := a1 * b0 + (w0 >>> 32)
  let w1 := (t &&& mask) + a0 * b1
  change (a * b).toNat + 2 ^ 64 * (a1 * b1 + (t >>> 32) + (w1 >>> 32)).toNat = _
  have lo32_lt : ∀ x : UInt64, (x &&& mask).toNat < 2 ^ 32 := fun x => by
    rw [low32_value]; exact Nat.mod_lt _ (by decide)
  have hi32_lt : ∀ x : UInt64, (x >>> 32).toNat < 2 ^ 32 := fun x => by
    rw [high32_value]; have := UInt64.toNat_lt x; omega
  have split : ∀ x : UInt64, x.toNat = (x &&& mask).toNat + 2 ^ 32 * (x >>> 32).toNat :=
    fun x => by rw [low32_value, high32_value]; exact (Nat.mod_add_div x.toNat (2 ^ 32)).symm
  -- Every fact below is phrased in the `let` names, so `omega` sees one atom per word.
  have ha : a.toNat = a0.toNat + 2 ^ 32 * a1.toNat := split a
  have hb : b.toNat = b0.toNat + 2 ^ 32 * b1.toNat := split b
  have ha0 : a0.toNat < 2 ^ 32 := lo32_lt a
  have ha1 : a1.toNat < 2 ^ 32 := hi32_lt a
  have hb0 : b0.toNat < 2 ^ 32 := lo32_lt b
  have hb1 : b1.toNat < 2 ^ 32 := hi32_lt b
  have tb : ∀ u v : ℕ, u < 2 ^ 32 → v < 2 ^ 32 → u * v ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    fun u v hu hv => Nat.mul_le_mul (by omega) (by omega)
  have p00 : a0.toNat * b0.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := tb _ _ ha0 hb0
  have p10 : a1.toNat * b0.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := tb _ _ ha1 hb0
  have p01 : a0.toNat * b1.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := tb _ _ ha0 hb1
  have p11 : a1.toNat * b1.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := tb _ _ ha1 hb1
  have gw0 : (w0 >>> 32).toNat < 2 ^ 32 := hi32_lt w0
  have gt : (t >>> 32).toNat < 2 ^ 32 := hi32_lt t
  have gw1 : (w1 >>> 32).toNat < 2 ^ 32 := hi32_lt w1
  have lt0 : (t &&& mask).toNat < 2 ^ 32 := lo32_lt t
  have lw0 : (w0 &&& mask).toNat < 2 ^ 32 := lo32_lt w0
  have lw1 : (w1 &&& mask).toNat < 2 ^ 32 := lo32_lt w1
  have e00 : a0.toNat * b0.toNat < 2 ^ 64 := by omega
  have hw0 : w0.toNat = a0.toNat * b0.toNat := by
    show (a0 * b0).toNat = _
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt e00]
  have e10 : a1.toNat * b0.toNat < 2 ^ 64 := by omega
  have e10' : a1.toNat * b0.toNat + (w0 >>> 32).toNat < 2 ^ 64 := by omega
  have ht : t.toNat = a1.toNat * b0.toNat + (w0 >>> 32).toNat := by
    show (a1 * b0 + (w0 >>> 32)).toNat = _
    rw [UInt64.toNat_add, UInt64.toNat_mul, Nat.mod_eq_of_lt e10, Nat.mod_eq_of_lt e10']
  have e01 : a0.toNat * b1.toNat < 2 ^ 64 := by omega
  have e01' : (t &&& mask).toNat + a0.toNat * b1.toNat < 2 ^ 64 := by omega
  have hw1 : w1.toNat = (t &&& mask).toNat + a0.toNat * b1.toNat := by
    show ((t &&& mask) + a0 * b1).toNat = _
    rw [UInt64.toNat_add, UInt64.toNat_mul, Nat.mod_eq_of_lt e01, Nat.mod_eq_of_lt e01']
  have e11 : a1.toNat * b1.toNat < 2 ^ 64 := by omega
  have e11' : a1.toNat * b1.toNat + (t >>> 32).toNat < 2 ^ 64 := by omega
  have e11'' : a1.toNat * b1.toNat + (t >>> 32).toNat + (w1 >>> 32).toNat < 2 ^ 64 := by omega
  have hhi : (a1 * b1 + (t >>> 32) + (w1 >>> 32)).toNat =
      a1.toNat * b1.toNat + (t >>> 32).toNat + (w1 >>> 32).toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, Nat.mod_eq_of_lt e11,
      Nat.mod_eq_of_lt e11', Nat.mod_eq_of_lt e11'']
  have hprod : a.toNat * b.toNat =
      a0.toNat * b0.toNat + 2 ^ 32 * (a1.toNat * b0.toNat) + 2 ^ 32 * (a0.toNat * b1.toNat) +
        2 ^ 64 * (a1.toNat * b1.toNat) := by
    rw [ha, hb]
    ring
  have sw0 : w0.toNat = (w0 &&& mask).toNat + 2 ^ 32 * (w0 >>> 32).toNat := split w0
  have st : t.toNat = (t &&& mask).toNat + 2 ^ 32 * (t >>> 32).toNat := split t
  have sw1 : w1.toNat = (w1 &&& mask).toNat + 2 ^ 32 * (w1 >>> 32).toNat := split w1
  rw [UInt64.toNat_mul, hprod, hhi]
  omega

/-- Multiply-accumulate, existential form: `t + a * b + c` never overflows two words. -/
theorem mac_spec (t a b c : UInt64) :
    ∃ lo hi : UInt64, mac t a b c = (lo, hi) ∧
      lo.toNat + 2 ^ 64 * hi.toNat = t.toNat + a.toNat * b.toNat + c.toNat := by
  refine ⟨_, _, rfl, ?_⟩
  have hp := mulHi_spec a b
  have h1 := addWord_value t (a * b)
  have h2 := addWord_value (t + a * b) c
  have hf1 := flag_le_one (t + a * b < t)
  have hf2 := flag_le_one (t + a * b + c < t + a * b)
  have ht := UInt64.toNat_lt t
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have hc := UInt64.toNat_lt c
  have hs := UInt64.toNat_lt (t + a * b + c)
  have hab : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  generalize a.toNat * b.toNat = P at *
  have hsum : (mulHi a b + (if t + a * b < t then (1 : UInt64) else 0) +
      (if t + a * b + c < t + a * b then (1 : UInt64) else 0)).toNat =
      (mulHi a b).toNat + (if t + a * b < t then (1 : UInt64) else 0).toNat +
      (if t + a * b + c < t + a * b then (1 : UInt64) else 0).toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [hsum]
  omega

/-- The Montgomery multiplier agrees with its natural-number specification. -/
theorem montM_toNat (s negInv : UInt64) :
    (montM s negInv).toNat = s.toNat * negInv.toNat % 2 ^ 64 := by
  simp only [montM, UInt64.toNat_mul]

/-! ## Four-limb values -/

namespace Limbs4

theorem zero_toNat : zero.toNat = 0 := by simp only [toNat, zero, UInt64.toNat_zero]

theorem one_toNat : one.toNat = 1 := by decide

theorem ofNat_toNat (n : ℕ) : (ofNat n).toNat = n % 2 ^ 256 := by
  simp only [toNat, ofNat, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  omega

/-- A four-limb value is below `2 ^ 256`. -/
theorem toNat_lt (x : Limbs4) : x.toNat < 2 ^ 256 := by
  have h0 := UInt64.toNat_lt x.l0
  have h1 := UInt64.toNat_lt x.l1
  have h2 := UInt64.toNat_lt x.l2
  have h3 := UInt64.toNat_lt x.l3
  simp only [toNat]
  omega

/-- The low limb of a value is its residue modulo `2 ^ 64`. -/
theorem toNat_mod (x : Limbs4) : x.toNat % 2 ^ 64 = x.l0.toNat := by
  have h0 := UInt64.toNat_lt x.l0
  simp only [toNat]
  omega

/-- Limb vectors are determined by their value. -/
theorem ext_of_toNat {x y : Limbs4} (h : x.toNat = y.toNat) : x = y := by
  have hx0 := UInt64.toNat_lt x.l0
  have hx1 := UInt64.toNat_lt x.l1
  have hx2 := UInt64.toNat_lt x.l2
  have hx3 := UInt64.toNat_lt x.l3
  have hy0 := UInt64.toNat_lt y.l0
  have hy1 := UInt64.toNat_lt y.l1
  have hy2 := UInt64.toNat_lt y.l2
  have hy3 := UInt64.toNat_lt y.l3
  simp only [toNat] at h
  have e0 : x.l0.toNat = y.l0.toNat := by omega
  have e1 : x.l1.toNat = y.l1.toNat := by omega
  have e2 : x.l2.toNat = y.l2.toNat := by omega
  have e3 : x.l3.toNat = y.l3.toNat := by omega
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp only [mk.injEq]
  exact ⟨UInt64.toNat_inj.mp e0, UInt64.toNat_inj.mp e1, UInt64.toNat_inj.mp e2,
    UInt64.toNat_inj.mp e3⟩

end Limbs4

/-! ### Chain lemmas -/

/-- Weighted telescoping of a four-step carry chain. -/
theorem carry_chain_sum {x0 x1 x2 x3 y0 y1 y2 y3 s0 s1 s2 s3 cin c0 c1 c2 c3 : ℕ}
    (e0 : s0 + 2 ^ 64 * c0 = x0 + y0 + cin)
    (e1 : s1 + 2 ^ 64 * c1 = x1 + y1 + c0)
    (e2 : s2 + 2 ^ 64 * c2 = x2 + y2 + c1)
    (e3 : s3 + 2 ^ 64 * c3 = x3 + y3 + c2) :
    s0 + 2 ^ 64 * s1 + 2 ^ 128 * s2 + 2 ^ 192 * s3 + 2 ^ 256 * c3 =
      (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) +
        (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) + cin := by
  omega

/-- Weighted telescoping of a four-step borrow chain. -/
theorem borrow_chain_sum {x0 x1 x2 x3 y0 y1 y2 y3 m0 m1 m2 m3 bin b0 b1 b2 b3 : ℕ}
    (e0 : m0 + y0 + bin = x0 + 2 ^ 64 * b0)
    (e1 : m1 + y1 + b0 = x1 + 2 ^ 64 * b1)
    (e2 : m2 + y2 + b1 = x2 + 2 ^ 64 * b2)
    (e3 : m3 + y3 + b2 = x3 + 2 ^ 64 * b3) :
    (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) +
        (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) + bin =
      x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 + 2 ^ 256 * b3 := by
  omega

/-! ### Branch lemmas -/

private theorem cond_of_borrow_zero {M Q T : ℕ} (h : M + Q = T) (hM : M < 2 ^ 256) :
    M = if T < Q then T else T - Q := by
  rw [ite_eq_right (by omega)]
  omega

private theorem cond_of_borrow_one {M Q T : ℕ} (h : M + Q = T + 2 ^ 256) (hM : M < 2 ^ 256) :
    T = if T < Q then T else T - Q := by
  rw [ite_eq_left (by omega)]

private theorem add_of_carry {S A B Q D bo : ℕ} (hchain : S + 2 ^ 256 * 1 = A + B)
    (hsub : D + Q = S + 2 ^ 256 * bo) (hbo : bo ≤ 1) (hD : D < 2 ^ 256) (hQ : Q < 2 ^ 256)
    (hA : A < Q) (hB : B < Q) : D = (A + B) % Q := by
  rw [show A + B = D + Q by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private theorem wide_of_head {T L t4 Q D bo : ℕ} (hdec : T = L + 2 ^ 256 * t4)
    (hsub : D + Q = L + 2 ^ 256 * bo) (hbo : bo ≤ 1) (hD : D < 2 ^ 256)
    (hQ : Q < 2 ^ 256) (hT : T < 2 * Q) (h : ¬t4 = 0) :
    D = if T < Q then T else T - Q := by
  rw [ite_eq_right (by omega)]
  omega

private theorem sub_of_borrow_zero {A B Q D : ℕ} (h : D + B = A + 2 ^ 256 * 0)
    (hB : B < Q) (hA : A < Q) : D = (A + (Q - B)) % Q := by
  conv_rhs => rw [show A + (Q - B) = D + Q by omega]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private theorem sub_of_borrow_one {A B Q D E c : ℕ} (hD : D + B = A + 2 ^ 256 * 1)
    (hE : E + 2 ^ 256 * c = D + Q) (hDlt : D < 2 ^ 256) (hElt : E < 2 ^ 256)
    (hB : B < Q) (hA : A < Q) (hQ : Q < 2 ^ 256) : E = (A + (Q - B)) % Q := by
  rw [show A + (Q - B) = E by omega, Nat.mod_eq_of_lt (by omega)]

/-! ## Limbwise addition and subtraction -/

/-- The limbwise sum and the top carry recompose the sum of the inputs. -/
theorem addLimbs_spec (a b : Limbs4) :
    ∃ s0 s1 s2 s3 c : UInt64, addLimbs a b = (s0, s1, s2, s3, c) ∧ c.toNat ≤ 1 ∧
      (⟨s0, s1, s2, s3⟩ : Limbs4).toNat + 2 ^ 256 * c.toNat = a.toNat + b.toNat := by
  obtain ⟨s0, c0, e0, h0, g0⟩ := adc_spec a.l0 b.l0 0 (by decide)
  obtain ⟨s1, c1, e1, h1, g1⟩ := adc_spec a.l1 b.l1 c0 g0
  obtain ⟨s2, c2, e2, h2, g2⟩ := adc_spec a.l2 b.l2 c1 g1
  obtain ⟨s3, c3, e3, h3, g3⟩ := adc_spec a.l3 b.l3 c2 g2
  refine ⟨s0, s1, s2, s3, c3, ?_, g3, ?_⟩
  · simp only [addLimbs, e0, e1, e2, e3]
  · rw [UInt64.toNat_zero] at h0
    simp only [Limbs4.toNat]
    have h := carry_chain_sum h0 h1 h2 h3
    simp only [Nat.add_zero] at h
    exact h

/-- The limbwise difference and the final borrow recompose the difference of the inputs. -/
theorem subLimbs_spec (a b : Limbs4) :
    ∃ d0 d1 d2 d3 bo : UInt64, subLimbs a b = (d0, d1, d2, d3, bo) ∧ bo.toNat ≤ 1 ∧
      (⟨d0, d1, d2, d3⟩ : Limbs4).toNat + b.toNat = a.toNat + 2 ^ 256 * bo.toNat := by
  obtain ⟨d0, b0, e0, h0, g0⟩ := sbb_spec a.l0 b.l0 0 (by decide)
  obtain ⟨d1, b1, e1, h1, g1⟩ := sbb_spec a.l1 b.l1 b0 g0
  obtain ⟨d2, b2, e2, h2, g2⟩ := sbb_spec a.l2 b.l2 b1 g1
  obtain ⟨d3, b3, e3, h3, g3⟩ := sbb_spec a.l3 b.l3 b2 g2
  refine ⟨d0, d1, d2, d3, b3, ?_, g3, ?_⟩
  · simp only [subLimbs, e0, e1, e2, e3]
  · rw [UInt64.toNat_zero] at h0
    simp only [Limbs4.toNat]
    have h := borrow_chain_sum h0 h1 h2 h3
    simp only [Nat.add_zero] at h
    exact h

/-! ## Conditional subtraction -/

/-- `condSub` subtracts the modulus exactly when the input is at least the modulus. -/
theorem condSub_toNat (q t : Limbs4) :
    (condSub q t).toNat = if t.toNat < q.toNat then t.toNat else t.toNat - q.toNat := by
  obtain ⟨d0, d1, d2, d3, bo, e, hbo, hchain⟩ := subLimbs_spec t q
  have hD := Limbs4.toNat_lt ⟨d0, d1, d2, d3⟩
  simp only [condSub, e, beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_zero]
  split
  case isTrue h =>
    rw [h, Nat.mul_zero, Nat.add_zero] at hchain
    exact cond_of_borrow_zero hchain hD
  case isFalse h =>
    rw [show bo.toNat = 1 by omega, Nat.mul_one] at hchain
    exact cond_of_borrow_one hchain hD

/-- `condSub` returns a canonical representative for inputs below `2 * q`. -/
theorem condSub_lt (q t : Limbs4) (h : t.toNat < 2 * q.toNat) :
    (condSub q t).toNat < q.toNat := by
  rw [condSub_toNat q t]
  split <;> omega

/-- `condSubWide` subtracts the modulus exactly when an accumulator below `2 * q` is at least
the modulus. -/
theorem condSubWide_toNat (q : Limbs4) (t : State5) (h : t.toNat < 2 * q.toNat) :
    (condSubWide q t).toNat = if t.toNat < q.toNat then t.toNat else t.toNat - q.toNat := by
  obtain ⟨d0, d1, d2, d3, bo, e, hbo, hsub⟩ := subLimbs_spec t.toLimbs4 q
  have hD := Limbs4.toNat_lt ⟨d0, d1, d2, d3⟩
  have hQ := Limbs4.toNat_lt q
  have hdec : t.toNat = t.toLimbs4.toNat + 2 ^ 256 * t.t4.toNat := rfl
  have hr : (⟨t.t0, t.t1, t.t2, t.t3⟩ : Limbs4) = t.toLimbs4 := rfl
  simp only [condSubWide, e, bne_iff_ne, ne_eq, beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_zero]
  split
  case isTrue hc => exact wide_of_head hdec hsub hbo hD hQ h hc
  case isFalse hc =>
    rw [show t.t4.toNat = 0 by omega, Nat.mul_zero, Nat.add_zero] at hdec
    rw [hdec]
    split
    case isTrue h0 =>
      rw [h0, Nat.mul_zero, Nat.add_zero] at hsub
      exact cond_of_borrow_zero hsub hD
    case isFalse h0 =>
      rw [show bo.toNat = 1 by omega, Nat.mul_one] at hsub
      rw [hr]
      exact cond_of_borrow_one hsub hD

/-- `condSubWide` returns a canonical representative for accumulators below `2 * q`. -/
theorem condSubWide_lt (q : Limbs4) (t : State5) (h : t.toNat < 2 * q.toNat) :
    (condSubWide q t).toNat < q.toNat := by
  rw [condSubWide_toNat q t h]
  split <;> omega

/-! ## Field operations -/

/-- Modular addition is correct for canonical inputs of any modulus. -/
theorem add_toNat (q a b : Limbs4) (haq : a.toNat < q.toNat) (hbq : b.toNat < q.toNat) :
    (add q a b).toNat = (a.toNat + b.toNat) % q.toNat := by
  obtain ⟨s0, s1, s2, s3, c, ea, hc, ha⟩ := addLimbs_spec a b
  obtain ⟨d0, d1, d2, d3, bo, es, hbo, hs⟩ := subLimbs_spec ⟨s0, s1, s2, s3⟩ q
  have hS := Limbs4.toNat_lt ⟨s0, s1, s2, s3⟩
  have hD := Limbs4.toNat_lt ⟨d0, d1, d2, d3⟩
  have hQ := Limbs4.toNat_lt q
  simp only [add, ea, es, bne_iff_ne, ne_eq, beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_zero]
  split
  case isTrue h =>
    rw [show c.toNat = 1 by omega] at ha
    exact add_of_carry ha hs hbo hD hQ haq hbq
  case isFalse h =>
    rw [show c.toNat = 0 by omega, Nat.mul_zero, Nat.add_zero] at ha
    rw [← ha]
    split
    case isTrue h0 =>
      rw [h0, Nat.mul_zero, Nat.add_zero] at hs
      rw [← hs, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    case isFalse h0 =>
      rw [show bo.toNat = 1 by omega, Nat.mul_one] at hs
      exact (Nat.mod_eq_of_lt (by omega)).symm

theorem add_lt (q a b : Limbs4) (haq : a.toNat < q.toNat) (hbq : b.toNat < q.toNat) :
    (add q a b).toNat < q.toNat := by
  rw [add_toNat q a b haq hbq]
  exact Nat.mod_lt _ (by omega)

/-- Modular subtraction is correct for canonical inputs of any modulus. -/
theorem sub_toNat (q a b : Limbs4) (haq : a.toNat < q.toNat) (hbq : b.toNat < q.toNat) :
    (sub q a b).toNat = (a.toNat + (q.toNat - b.toNat)) % q.toNat := by
  obtain ⟨d0, d1, d2, d3, bo, e, hbo, hchain⟩ := subLimbs_spec a b
  have hD := Limbs4.toNat_lt ⟨d0, d1, d2, d3⟩
  simp only [sub, e, beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_zero]
  split
  case isTrue h =>
    rw [h] at hchain
    exact sub_of_borrow_zero hchain hbq haq
  case isFalse h =>
    rw [show bo.toNat = 1 by omega] at hchain
    obtain ⟨r0, r1, r2, r3, c, er, _, hr⟩ := addLimbs_spec ⟨d0, d1, d2, d3⟩ q
    simp only [er]
    exact sub_of_borrow_one hchain hr hD (Limbs4.toNat_lt ⟨r0, r1, r2, r3⟩) hbq haq
      (Limbs4.toNat_lt q)

theorem sub_lt (q a b : Limbs4) (haq : a.toNat < q.toNat) (hbq : b.toNat < q.toNat) :
    (sub q a b).toNat < q.toNat := by
  rw [sub_toNat q a b haq hbq]
  exact Nat.mod_lt _ (by omega)

/-- Modular negation is correct for canonical inputs of any modulus. -/
theorem neg_toNat (q a : Limbs4) (haq : a.toNat < q.toNat) :
    (neg q a).toNat = (q.toNat - a.toNat) % q.toNat := by
  simp only [neg]
  rw [sub_toNat q Limbs4.zero a (by rw [Limbs4.zero_toNat]; omega) haq, Limbs4.zero_toNat,
    Nat.zero_add]

theorem neg_lt (q a : Limbs4) (haq : a.toNat < q.toNat) : (neg q a).toNat < q.toNat :=
  sub_lt q Limbs4.zero a (by rw [Limbs4.zero_toNat]; omega) haq

end Native64x4
end Montgomery
