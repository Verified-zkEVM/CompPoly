/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/

import CompPoly.Fields.Montgomery.Native64x8
import Mathlib.Tactic.Linarith

/-!
# Correctness of eight-limb CIOS Montgomery multiplication

A CIOS round is the composition of an accumulation and a reduction step:

* `mulAccum a bi t` accumulates `a * bi` into the accumulator without losing information,
  `⟦mulAccum a bi t⟧ = ⟦t⟧ + ⟦a⟧ * bi`;
* `mulReduce q negInv s` adds the multiple `m * q` of the modulus that cancels the low limb
  and drops that limb, `2 ^ 32 * ⟦mulReduce q negInv s⟧ = ⟦s⟧ + m * q`.

Composing them gives the round invariant `2 ^ 32 * ⟦mulRound⟧ = ⟦t⟧ + ⟦a⟧ * bi + m * q`, and
folding eight rounds gives `2 ^ 256 * ⟦t₈⟧ = ⟦a⟧ * ⟦b⟧ + M * q`, so the accumulator is the
Montgomery product up to the final conditional subtraction.

## Main results

* `mulAccum_spec`, `mulReduce_spec` — the two halves of a round
* `mulRound_spec` — the round invariant, with limb bounds and the `2 * q` bound
* `mul_spec` — `mul` is canonical and satisfies `2 ^ 256 * ⟦mul a b⟧ ≡ ⟦a⟧ * ⟦b⟧ [MOD q]`
-/

namespace Montgomery
namespace Native64x8

/-! ### Arithmetic helpers -/

/-- Scalar multiplication distributes over a limb recomposition. -/
theorem sum8_mul (a0 a1 a2 a3 a4 a5 a6 a7 b : ℕ) :
    (a0 + 2 ^ 32 * a1 + 2 ^ 64 * a2 + 2 ^ 96 * a3 + 2 ^ 128 * a4 + 2 ^ 160 * a5 +
        2 ^ 192 * a6 + 2 ^ 224 * a7) * b =
      a0 * b + 2 ^ 32 * (a1 * b) + 2 ^ 64 * (a2 * b) + 2 ^ 96 * (a3 * b) +
        2 ^ 128 * (a4 * b) + 2 ^ 160 * (a5 * b) + 2 ^ 192 * (a6 * b) + 2 ^ 224 * (a7 * b) := by
  ring

/-- Scalar multiplication distributes over a limb recomposition, from the left. -/
theorem mul_sum8 (b a0 a1 a2 a3 a4 a5 a6 a7 : ℕ) :
    b * (a0 + 2 ^ 32 * a1 + 2 ^ 64 * a2 + 2 ^ 96 * a3 + 2 ^ 128 * a4 + 2 ^ 160 * a5 +
        2 ^ 192 * a6 + 2 ^ 224 * a7) =
      b * a0 + 2 ^ 32 * (b * a1) + 2 ^ 64 * (b * a2) + 2 ^ 96 * (b * a3) +
        2 ^ 128 * (b * a4) + 2 ^ 160 * (b * a5) + 2 ^ 192 * (b * a6) + 2 ^ 224 * (b * a7) := by
  ring

/-- The low limb of a bounded value is its residue modulo `2 ^ 32`. -/
theorem Limbs8.toNat_mod (x : Limbs8) (h : x.l0.toNat < 2 ^ 32) :
    x.toNat % 2 ^ 32 = x.l0.toNat := by
  simp only [Limbs8.toNat]
  omega

/-- The Montgomery multiplier makes the low limb of the reduction vanish. -/
private theorem montM_low_zero {s negInv Q q0 w u : ℕ} (hs : s < 2 ^ 32)
    (hq0 : Q % 2 ^ 32 = q0) (hnq : negInv * Q % 2 ^ 32 = 2 ^ 32 - 1)
    (h : w + 2 ^ 32 * u = s + s * negInv % 2 ^ 32 * q0) (hw : w < 2 ^ 32) : w = 0 := by
  have hdvd : 2 ^ 32 ∣ s + s % 2 ^ 32 * negInv % 2 ^ 32 * Q :=
    Montgomery.dvd_add (2 ^ 32) Q negInv (by norm_num) hnq s
  rw [Nat.mod_eq_of_lt hs] at hdvd
  have hq0' : q0 % 2 ^ 32 = Q % 2 ^ 32 := by omega
  have hcong : (s + s * negInv % 2 ^ 32 * q0) % 2 ^ 32
      = (s + s * negInv % 2 ^ 32 * Q) % 2 ^ 32 :=
    Nat.ModEq.add_left s (Nat.ModEq.mul_left _ hq0')
  obtain ⟨c, hc⟩ := hdvd
  omega

/-- The accumulator stays below `2 * q` from one round to the next. -/
private theorem round_bound {T A bi m Q Tp : ℕ} (h : 2 ^ 32 * Tp = T + A * bi + m * Q)
    (hT : T < 2 * Q) (hA : A < Q) (hbi : bi < 2 ^ 32) (hm : m < 2 ^ 32) : Tp < 2 * Q := by
  nlinarith [h, hT, hA, hbi, hm]

/-- Assembling the limb chain of the accumulation step. -/
private theorem accum_assemble {Slow Tlow T Abi k7 t8 s8 : ℕ} (hT : T = Tlow + 2 ^ 256 * t8)
    (hchain : Slow + 2 ^ 256 * k7 = Tlow + Abi) (hs8 : s8 = t8 + k7) :
    Slow + 2 ^ 256 * s8 = T + Abi := by
  omega

/-- Assembling the limb chain of the reduction step. -/
private theorem reduce_assemble {V W Slow mQ S u7 v8 u8 s8 : ℕ}
    (hS : S = Slow + 2 ^ 256 * s8) (hW : W = 2 ^ 32 * V)
    (hchain : W + 2 ^ 256 * u7 = Slow + mQ) (hv8 : v8 + 2 ^ 32 * u8 = s8 + u7) :
    2 ^ 32 * (V + 2 ^ 224 * v8 + 2 ^ 256 * u8) = S + mQ := by
  omega

/-! ### The accumulator -/

theorem State9.zero_bounded : State9.zero.Bounded := by
  simp only [State9.Bounded, State9.toLimbs8, State9.zero, Limbs8.Bounded, UInt64.toNat_zero]
  norm_num

theorem State9.zero_toNat : State9.zero.toNat = 0 := by
  simp only [State9.toNat, State9.toLimbs8, State9.zero, Limbs8.toNat, UInt64.toNat_zero]

/-- The value of an accumulator in terms of its limbs. -/
theorem State9.toNat_eq (t : State9) :
    t.toNat = t.t0.toNat + 2 ^ 32 * t.t1.toNat + 2 ^ 64 * t.t2.toNat + 2 ^ 96 * t.t3.toNat +
      2 ^ 128 * t.t4.toNat + 2 ^ 160 * t.t5.toNat + 2 ^ 192 * t.t6.toNat +
      2 ^ 224 * t.t7.toNat + 2 ^ 256 * t.t8.toNat := by
  simp only [State9.toNat, State9.toLimbs8, Limbs8.toNat]

/-! ### The accumulation step -/

/-- `mulAccum` adds `a * bi` to the accumulator exactly: the carry out of the top limb is
retained in the head limb. -/
theorem mulAccum_spec (a : Limbs8) (bi : UInt64) (t : State9) (ha : a.Bounded)
    (ht : t.Bounded) (hbi : bi.toNat < 2 ^ 32) :
    (mulAccum a bi t).toLimbs8.Bounded ∧ (mulAccum a bi t).t8.toNat < 2 ^ 33 ∧
      (mulAccum a bi t).toNat = t.toNat + a.toNat * bi.toNat := by
  obtain ⟨⟨ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7⟩, ht8⟩ := ht
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := ha
  obtain ⟨s0, k0, ds0, dk0, e0, gk0, hs0⟩ :=
    mac_spec t.t0 a.l0 bi (0 : UInt64) ht0 ha0 hbi (by decide)
  obtain ⟨s1, k1, ds1, dk1, e1, gk1, hs1⟩ :=
    mac_spec t.t1 a.l1 bi _ ht1 ha1 hbi (dk0 ▸ gk0)
  obtain ⟨s2, k2, ds2, dk2, e2, gk2, hs2⟩ :=
    mac_spec t.t2 a.l2 bi _ ht2 ha2 hbi (dk1 ▸ gk1)
  obtain ⟨s3, k3, ds3, dk3, e3, gk3, hs3⟩ :=
    mac_spec t.t3 a.l3 bi _ ht3 ha3 hbi (dk2 ▸ gk2)
  obtain ⟨s4, k4, ds4, dk4, e4, gk4, hs4⟩ :=
    mac_spec t.t4 a.l4 bi _ ht4 ha4 hbi (dk3 ▸ gk3)
  obtain ⟨s5, k5, ds5, dk5, e5, gk5, hs5⟩ :=
    mac_spec t.t5 a.l5 bi _ ht5 ha5 hbi (dk4 ▸ gk4)
  obtain ⟨s6, k6, ds6, dk6, e6, gk6, hs6⟩ :=
    mac_spec t.t6 a.l6 bi _ ht6 ha6 hbi (dk5 ▸ gk5)
  obtain ⟨s7, k7, ds7, dk7, e7, gk7, hs7⟩ :=
    mac_spec t.t7 a.l7 bi _ ht7 ha7 hbi (dk6 ▸ gk6)
  simp only [dk0, dk1, dk2, dk3, dk4, dk5, dk6, UInt64.toNat_zero] at e0 e1 e2 e3 e4 e5 e6 e7
  have hchain := carry_chain_sum e0 e1 e2 e3 e4 e5 e6 e7
  rw [← sum8_mul, ← Limbs8.toNat, Nat.add_zero] at hchain
  have hk7 : ∀ x : UInt64, x.toNat = k7 → (t.t8 + x).toNat = t.t8.toNat + k7 := by
    intro x hx
    rw [UInt64.toNat_add, hx, Nat.mod_eq_of_lt (by omega)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact macLo_lt _ _ _ _
  · exact macLo_lt _ _ _ _
  · exact macLo_lt _ _ _ _
  · exact macLo_lt _ _ _ _
  · exact macLo_lt _ _ _ _
  · exact macLo_lt _ _ _ _
  · exact macLo_lt _ _ _ _
  · exact macLo_lt _ _ _ _
  · simp only [mulAccum]
    rw [hk7 _ dk7]
    omega
  · rw [State9.toNat_eq, State9.toNat_eq t]
    simp only [mulAccum, ds0, ds1, ds2, ds3, ds4, ds5, ds6, ds7]
    rw [hk7 _ dk7]
    exact accum_assemble rfl hchain rfl

/-! ### The reduction step -/

/-- `mulReduce` adds the multiple of the modulus that cancels the low limb, and the division
by `2 ^ 32` performed by dropping that limb is exact. -/
theorem mulReduce_spec (q : Limbs8) (negInv : UInt64) (s : State9) (hq : q.Bounded)
    (hs : s.toLimbs8.Bounded) (hs8 : s.t8.toNat < 2 ^ 33) (hn : negInv.toNat < 2 ^ 32)
    (hnq : negInv.toNat * q.toNat % 2 ^ 32 = 2 ^ 32 - 1) :
    (mulReduce q negInv s).Bounded ∧
      2 ^ 32 * (mulReduce q negInv s).toNat =
        s.toNat + (montM s.t0 negInv).toNat * q.toNat := by
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ := hs
  obtain ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7⟩ := hq
  have hmv : (montM s.t0 negInv).toNat = s.t0.toNat * negInv.toNat % 2 ^ 32 :=
    montM_toNat _ _ hs0 hn
  have hmv_lt : (montM s.t0 negInv).toNat < 2 ^ 32 := montM_lt _ _
  obtain ⟨w0, u0, dw0, du0, f0, gu0, hw0⟩ :=
    mac_spec s.t0 (montM s.t0 negInv) q.l0 (0 : UInt64) hs0 hmv_lt hq0 (by decide)
  obtain ⟨w1, u1, dw1, du1, f1, gu1, hw1⟩ :=
    mac_spec s.t1 (montM s.t0 negInv) q.l1 _ hs1 hmv_lt hq1 (du0 ▸ gu0)
  obtain ⟨w2, u2, dw2, du2, f2, gu2, hw2⟩ :=
    mac_spec s.t2 (montM s.t0 negInv) q.l2 _ hs2 hmv_lt hq2 (du1 ▸ gu1)
  obtain ⟨w3, u3, dw3, du3, f3, gu3, hw3⟩ :=
    mac_spec s.t3 (montM s.t0 negInv) q.l3 _ hs3 hmv_lt hq3 (du2 ▸ gu2)
  obtain ⟨w4, u4, dw4, du4, f4, gu4, hw4⟩ :=
    mac_spec s.t4 (montM s.t0 negInv) q.l4 _ hs4 hmv_lt hq4 (du3 ▸ gu3)
  obtain ⟨w5, u5, dw5, du5, f5, gu5, hw5⟩ :=
    mac_spec s.t5 (montM s.t0 negInv) q.l5 _ hs5 hmv_lt hq5 (du4 ▸ gu4)
  obtain ⟨w6, u6, dw6, du6, f6, gu6, hw6⟩ :=
    mac_spec s.t6 (montM s.t0 negInv) q.l6 _ hs6 hmv_lt hq6 (du5 ▸ gu5)
  obtain ⟨w7, u7, dw7, du7, f7, gu7, hw7⟩ :=
    mac_spec s.t7 (montM s.t0 negInv) q.l7 _ hs7 hmv_lt hq7 (du6 ▸ gu6)
  simp only [du0, du1, du2, du3, du4, du5, du6, UInt64.toNat_zero, hmv] at f0 f1 f2 f3 f4 f5 f6 f7
  have hw0zero : w0 = 0 :=
    montM_low_zero hs0 (Limbs8.toNat_mod q hq0) hnq (by rw [Nat.add_zero] at f0; exact f0) hw0
  rw [hw0zero] at f0
  have hchain := carry_chain_sum f0 f1 f2 f3 f4 f5 f6 f7
  rw [← mul_sum8, ← Limbs8.toNat, Nat.add_zero] at hchain
  obtain ⟨v8, u8, dv8, du8, g8, gu8, hv8⟩ :=
    adc_spec_wide s.t8 _ (0 : UInt64) hs8 (du7 ▸ gu7) (by decide)
  rw [UInt64.toNat_zero, Nat.add_zero, du7] at g8
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact macLo_lt _ _ _ _
  · exact macLo_lt _ _ _ _
  · exact macLo_lt _ _ _ _
  · exact macLo_lt _ _ _ _
  · exact macLo_lt _ _ _ _
  · exact macLo_lt _ _ _ _
  · exact macLo_lt _ _ _ _
  · exact adcLo_lt _ _ _
  · simp only [mulReduce]
    rw [du8]
    omega
  · rw [State9.toNat_eq, State9.toNat_eq s, hmv]
    simp only [mulReduce, dw1, dw2, dw3, dw4, dw5, dw6, dw7, dv8, du8]
    exact reduce_assemble rfl (by ring) hchain g8

/-! ### The round invariant -/

/-- The CIOS round invariant: one round accumulates `a * bi` and cancels the low limb against
a multiple `m` of the modulus; the accumulator stays limbwise bounded and below `2 * q`. -/
theorem mulRound_spec (q a : Limbs8) (negInv bi : UInt64) (t : State9)
    (hq : q.Bounded) (ha : a.Bounded) (ht : t.Bounded) (hbi : bi.toNat < 2 ^ 32)
    (hn : negInv.toNat < 2 ^ 32) (hnq : negInv.toNat * q.toNat % 2 ^ 32 = 2 ^ 32 - 1)
    (haq : a.toNat < q.toNat) (htq : t.toNat < 2 * q.toNat) :
    (mulRound q negInv a bi t).Bounded ∧ (mulRound q negInv a bi t).toNat < 2 * q.toNat ∧
      ∃ m : ℕ, m < 2 ^ 32 ∧
        2 ^ 32 * (mulRound q negInv a bi t).toNat =
          t.toNat + a.toNat * bi.toNat + m * q.toNat := by
  obtain ⟨hab, ha8, hav⟩ := mulAccum_spec a bi t ha ht hbi
  obtain ⟨hrb, hrv⟩ := mulReduce_spec q negInv (mulAccum a bi t) hq hab ha8 hn hnq
  rw [hav] at hrv
  have hinv : 2 ^ 32 * (mulRound q negInv a bi t).toNat =
      t.toNat + a.toNat * bi.toNat + (montM (mulAccum a bi t).t0 negInv).toNat * q.toNat := by
    rw [mulRound]
    exact hrv
  exact ⟨hrb, round_bound hinv htq haq hbi (montM_lt _ _), _, montM_lt _ _, hinv⟩

/-! ### The eight-round fold -/

/-- Folding the eight round invariants into a single Montgomery identity. -/
private theorem fold8 {T1 T2 T3 T4 T5 T6 T7 T8 A Q : ℕ}
    {B0 B1 B2 B3 B4 B5 B6 B7 m0 m1 m2 m3 m4 m5 m6 m7 : ℕ}
    (h0 : 2 ^ 32 * T1 = 0 + A * B0 + m0 * Q)
    (h1 : 2 ^ 32 * T2 = T1 + A * B1 + m1 * Q)
    (h2 : 2 ^ 32 * T3 = T2 + A * B2 + m2 * Q)
    (h3 : 2 ^ 32 * T4 = T3 + A * B3 + m3 * Q)
    (h4 : 2 ^ 32 * T5 = T4 + A * B4 + m4 * Q)
    (h5 : 2 ^ 32 * T6 = T5 + A * B5 + m5 * Q)
    (h6 : 2 ^ 32 * T7 = T6 + A * B6 + m6 * Q)
    (h7 : 2 ^ 32 * T8 = T7 + A * B7 + m7 * Q) :
    2 ^ 256 * T8 =
      (A * B0 + 2 ^ 32 * (A * B1) + 2 ^ 64 * (A * B2) + 2 ^ 96 * (A * B3) +
        2 ^ 128 * (A * B4) + 2 ^ 160 * (A * B5) + 2 ^ 192 * (A * B6) + 2 ^ 224 * (A * B7)) +
      (m0 * Q + 2 ^ 32 * (m1 * Q) + 2 ^ 64 * (m2 * Q) + 2 ^ 96 * (m3 * Q) +
        2 ^ 128 * (m4 * Q) + 2 ^ 160 * (m5 * Q) + 2 ^ 192 * (m6 * Q) +
        2 ^ 224 * (m7 * Q)) := by
  omega

/-- The final conditional subtraction of `mul`, given the folded Montgomery identity. -/
private theorem mul_finish (q : Limbs8) (t : State9) {A M : ℕ} (hq : q.Bounded)
    (hb : t.Bounded) (hlt : t.toNat < 2 * q.toNat) (hq2 : 2 * q.toNat < 2 ^ 256)
    (hfold : 2 ^ 256 * t.toNat = A + M * q.toNat) :
    (condSub q t.toLimbs8).Bounded ∧ (condSub q t.toLimbs8).toNat < q.toNat ∧
      2 ^ 256 * (condSub q t.toLimbs8).toNat ≡ A [MOD q.toNat] := by
  have hlimbs : t.toLimbs8.toNat = t.toNat := by
    have h1 := Limbs8.toNat_lt hb.1
    have h2 : t.toNat = t.toLimbs8.toNat + 2 ^ 256 * t.t8.toNat := rfl
    omega
  have hmod : 2 ^ 256 * t.toNat ≡ A [MOD q.toNat] := by
    unfold Nat.ModEq
    rw [hfold, Nat.add_mul_mod_self_right]
  refine ⟨condSub_bounded _ _ hb.1, condSub_lt q _ hq hb.1 (by omega), ?_⟩
  rw [condSub_toNat q _ hq hb.1, hlimbs]
  split
  · exact hmod
  · refine (Nat.ModEq.mul_left _ ?_).trans hmod
    exact (Nat.modEq_iff_dvd' (by omega)).2 ⟨1, by omega⟩

/-- Montgomery multiplication is canonical and computes `a * b * (2 ^ 256)⁻¹ mod q`. -/
theorem mul_spec (q : Limbs8) (negInv : UInt64) (a b : Limbs8)
    (hq : q.Bounded) (ha : a.Bounded) (hb : b.Bounded) (hn : negInv.toNat < 2 ^ 32)
    (hnq : negInv.toNat * q.toNat % 2 ^ 32 = 2 ^ 32 - 1)
    (haq : a.toNat < q.toNat) (hq2 : 2 * q.toNat < 2 ^ 256) :
    (mul q negInv a b).Bounded ∧ (mul q negInv a b).toNat < q.toNat ∧
      2 ^ 256 * (mul q negInv a b).toNat ≡ a.toNat * b.toNat [MOD q.toNat] := by
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hb
  obtain ⟨B1, L1, m0, hm0, r0⟩ :=
    mulRound_spec q a negInv b.l0 State9.zero hq ha State9.zero_bounded hb0 hn hnq haq
      (by rw [State9.zero_toNat]; omega)
  obtain ⟨B2, L2, m1, hm1, r1⟩ :=
    mulRound_spec q a negInv b.l1 _ hq ha B1 hb1 hn hnq haq
      L1
  obtain ⟨B3, L3, m2, hm2, r2⟩ :=
    mulRound_spec q a negInv b.l2 _ hq ha B2 hb2 hn hnq haq
      L2
  obtain ⟨B4, L4, m3, hm3, r3⟩ :=
    mulRound_spec q a negInv b.l3 _ hq ha B3 hb3 hn hnq haq
      L3
  obtain ⟨B5, L5, m4, hm4, r4⟩ :=
    mulRound_spec q a negInv b.l4 _ hq ha B4 hb4 hn hnq haq
      L4
  obtain ⟨B6, L6, m5, hm5, r5⟩ :=
    mulRound_spec q a negInv b.l5 _ hq ha B5 hb5 hn hnq haq
      L5
  obtain ⟨B7, L7, m6, hm6, r6⟩ :=
    mulRound_spec q a negInv b.l6 _ hq ha B6 hb6 hn hnq haq
      L6
  obtain ⟨B8, L8, m7, hm7, r7⟩ :=
    mulRound_spec q a negInv b.l7 _ hq ha B7 hb7 hn hnq haq
      L7
  rw [State9.zero_toNat] at r0
  have hfold := fold8 r0 r1 r2 r3 r4 r5 r6 r7
  rw [← mul_sum8, ← sum8_mul, ← Limbs8.toNat] at hfold
  simp only [mul]
  exact mul_finish q _ hq B8 L8 hq2 hfold

end Native64x8
end Montgomery
