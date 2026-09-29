/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPoly.Fields.Montgomery.Native64x4
public import Mathlib.Tactic.Linarith

/-!
# Correctness of four-limb CIOS Montgomery multiplication

A CIOS round is the composition of an accumulation and a reduction step:

* `mulAccum a bi t` accumulates `a * bi` into the accumulator exactly,
  `⟦mulAccum a bi t⟧ = ⟦t⟧ + ⟦a⟧ * bi`;
* `mulReduce q negInv s` adds the multiple `m * q` of the modulus that cancels the low limb
  and drops that limb, `2 ^ 64 * ⟦mulReduce q negInv s⟧ = ⟦s⟧ + m * q`.

Composing them gives the round invariant `2 ^ 64 * ⟦mulRound⟧ = ⟦t⟧ + ⟦a⟧ * bi + m * q`, and
folding four rounds gives `2 ^ 256 * ⟦t₄⟧ = ⟦a⟧ * ⟦b⟧ + M * q`, so the accumulator is the
Montgomery product up to the final conditional subtraction.

## Main results

* `mulAccum_spec`, `mulReduce_spec` — the two halves of a round
* `mulRound_spec` — the round invariant with the `2 * q` bound
* `mul_spec` — `mul` is canonical and satisfies `2 ^ 256 * ⟦mul a b⟧ ≡ ⟦a⟧ * ⟦b⟧ [MOD q]`
-/

@[expose] public section

namespace Montgomery
namespace Native64x4

/-! ### Arithmetic helpers -/

/-- Scalar multiplication distributes over a limb recomposition. -/
theorem sum4_mul (a0 a1 a2 a3 b : ℕ) :
    (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) * b =
      a0 * b + 2 ^ 64 * (a1 * b) + 2 ^ 128 * (a2 * b) + 2 ^ 192 * (a3 * b) := by
  ring

/-- Scalar multiplication distributes over a limb recomposition, from the left. -/
theorem mul_sum4 (b a0 a1 a2 a3 : ℕ) :
    b * (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) =
      b * a0 + 2 ^ 64 * (b * a1) + 2 ^ 128 * (b * a2) + 2 ^ 192 * (b * a3) := by
  ring

private theorem word_lt (x : UInt64) : x.toNat < 2 ^ 64 := by
  have := x.toNat_lt_size
  norm_num [UInt64.size] at this
  exact this

/-- The low limb of a value is its residue modulo `2 ^ 64`. -/
theorem Limbs4.toNat_mod (x : Limbs4) : x.toNat % 2 ^ 64 = x.l0.toNat := by
  have h0 := word_lt x.l0
  simp only [Limbs4.toNat]
  omega

/-- The Montgomery multiplier makes the low limb of the reduction vanish. -/
private theorem montM_low_zero {s negInv Q q0 w u : ℕ} (hs : s < 2 ^ 64)
    (hq0 : Q % 2 ^ 64 = q0) (hnq : negInv * Q % 2 ^ 64 = 2 ^ 64 - 1)
    (h : w + 2 ^ 64 * u = s + s * negInv % 2 ^ 64 * q0) (hw : w < 2 ^ 64) : w = 0 := by
  have hdvd : 2 ^ 64 ∣ s + s % 2 ^ 64 * negInv % 2 ^ 64 * Q :=
    Montgomery.dvd_add (2 ^ 64) Q negInv (by norm_num) hnq s
  rw [Nat.mod_eq_of_lt hs] at hdvd
  have hq0' : q0 % 2 ^ 64 = Q % 2 ^ 64 := by omega
  have hcong : (s + s * negInv % 2 ^ 64 * q0) % 2 ^ 64
      = (s + s * negInv % 2 ^ 64 * Q) % 2 ^ 64 :=
    Nat.ModEq.add_left s (Nat.ModEq.mul_left _ hq0')
  obtain ⟨c, hc⟩ := hdvd
  omega

/-- The accumulator stays below `2 * q` from one round to the next. -/
private theorem round_bound {T A bi m Q Tp : ℕ} (h : 2 ^ 64 * Tp = T + A * bi + m * Q)
    (hT : T < 2 * Q) (hA : A < Q) (hbi : bi < 2 ^ 64) (hm : m < 2 ^ 64) : Tp < 2 * Q := by
  nlinarith [h, hT, hA, hbi, hm]

/-! ### The accumulator -/

theorem State5.zero_toNat : State5.zero.toNat = 0 := by
  simp only [State5.toNat, State5.toLimbs4, State5.zero, Limbs4.toNat, UInt64.toNat_zero]

/-- The value of an accumulator in terms of its limbs. -/
theorem State5.toNat_eq (t : State5) :
    t.toNat = t.t0.toNat + 2 ^ 64 * t.t1.toNat + 2 ^ 128 * t.t2.toNat + 2 ^ 192 * t.t3.toNat +
      2 ^ 256 * t.t4.toNat := by
  simp only [State5.toNat, State5.toLimbs4, Limbs4.toNat]

/-! ### The accumulation step -/

/-- `mulAccum` adds `a * bi` to the accumulator exactly: the carry out of the head limb is
retained in the carry limb, and the carry limb is a bit. -/
theorem mulAccum_spec (a : Limbs4) (bi : UInt64) (t : State5) :
    (mulAccum a bi t).t5.toNat ≤ 1 ∧
      (mulAccum a bi t).toNat = t.toNat + a.toNat * bi.toNat := by
  obtain ⟨s0, k0, e0, h0⟩ := mac_spec t.t0 a.l0 bi 0
  obtain ⟨s1, k1, e1, h1⟩ := mac_spec t.t1 a.l1 bi k0
  obtain ⟨s2, k2, e2, h2⟩ := mac_spec t.t2 a.l2 bi k1
  obtain ⟨s3, k3, e3, h3⟩ := mac_spec t.t3 a.l3 bi k2
  obtain ⟨s4, s5, e4, h4, g4⟩ := adc_spec t.t4 k3 0 (by decide)
  rw [UInt64.toNat_zero] at h0 h4
  have hchain := carry_chain_sum h0 h1 h2 h3
  rw [← sum4_mul, ← Limbs4.toNat, Nat.add_zero] at hchain
  simp only [mulAccum, e0, e1, e2, e3, e4]
  refine ⟨g4, ?_⟩
  rw [State5.toNat_eq]
  simp only [State6.toNat, Limbs4.toNat] at hchain ⊢
  omega

/-! ### The reduction step -/

/-- `mulReduce` adds the multiple of the modulus that cancels the low limb, and the division
by `2 ^ 64` performed by dropping that limb is exact. -/
theorem mulReduce_spec (q : Limbs4) (negInv : UInt64) (s : State6) (hs5 : s.t5.toNat ≤ 1)
    (hnq : negInv.toNat * q.toNat % 2 ^ 64 = 2 ^ 64 - 1) :
    (mulReduce q negInv s).t4.toNat ≤ 2 ∧
      2 ^ 64 * (mulReduce q negInv s).toNat =
        s.toNat + (montM s.t0 negInv).toNat * q.toNat := by
  have hmv : (montM s.t0 negInv).toNat = s.t0.toNat * negInv.toNat % 2 ^ 64 :=
    montM_toNat _ _
  obtain ⟨w0, u0, f0, g0⟩ := mac_spec s.t0 (montM s.t0 negInv) q.l0 0
  obtain ⟨w1, u1, f1, g1⟩ := mac_spec s.t1 (montM s.t0 negInv) q.l1 u0
  obtain ⟨w2, u2, f2, g2⟩ := mac_spec s.t2 (montM s.t0 negInv) q.l2 u1
  obtain ⟨w3, u3, f3, g3⟩ := mac_spec s.t3 (montM s.t0 negInv) q.l3 u2
  obtain ⟨w4, u4, f4, g4, k4⟩ := adc_spec s.t4 u3 0 (by decide)
  rw [UInt64.toNat_zero] at g0 g4
  have hw0 : w0.toNat = 0 := by
    have hw := word_lt w0
    rw [hmv] at g0
    exact montM_low_zero (word_lt s.t0) (Limbs4.toNat_mod q) hnq
      (by rw [Nat.add_zero] at g0; exact g0) hw
  have hchain := carry_chain_sum g0 g1 g2 g3
  rw [← mul_sum4, ← Limbs4.toNat, Nat.add_zero] at hchain
  have hhead : (s.t5 + u4).toNat = s.t5.toNat + u4.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  simp only [mulReduce, f0, f1, f2, f3, f4]
  refine ⟨?_, ?_⟩
  · rw [hhead]; omega
  · rw [State5.toNat_eq]
    simp only [State6.toNat, hhead]
    omega

/-! ### The round invariant -/

/-- The CIOS round invariant: one round accumulates `a * bi` and cancels the low limb against
a multiple `m` of the modulus; the accumulator stays below `2 * q`. -/
theorem mulRound_spec (q a : Limbs4) (negInv bi : UInt64) (t : State5)
    (hnq : negInv.toNat * q.toNat % 2 ^ 64 = 2 ^ 64 - 1)
    (haq : a.toNat < q.toNat) (htq : t.toNat < 2 * q.toNat) :
    (mulRound q negInv a bi t).toNat < 2 * q.toNat ∧
      ∃ m : ℕ, m < 2 ^ 64 ∧
        2 ^ 64 * (mulRound q negInv a bi t).toNat =
          t.toNat + a.toNat * bi.toNat + m * q.toNat := by
  obtain ⟨ha5, hav⟩ := mulAccum_spec a bi t
  obtain ⟨-, hrv⟩ := mulReduce_spec q negInv (mulAccum a bi t) ha5 hnq
  rw [hav] at hrv
  have hinv : 2 ^ 64 * (mulRound q negInv a bi t).toNat =
      t.toNat + a.toNat * bi.toNat + (montM (mulAccum a bi t).t0 negInv).toNat * q.toNat := by
    rw [mulRound]
    exact hrv
  exact ⟨round_bound hinv htq haq (word_lt bi) (word_lt _), _, word_lt _, hinv⟩

/-! ### The four-round fold -/

/-- Folding the four round invariants into a single Montgomery identity. -/
private theorem fold4 {T1 T2 T3 T4 A Q B0 B1 B2 B3 m0 m1 m2 m3 : ℕ}
    (h0 : 2 ^ 64 * T1 = 0 + A * B0 + m0 * Q)
    (h1 : 2 ^ 64 * T2 = T1 + A * B1 + m1 * Q)
    (h2 : 2 ^ 64 * T3 = T2 + A * B2 + m2 * Q)
    (h3 : 2 ^ 64 * T4 = T3 + A * B3 + m3 * Q) :
    2 ^ 256 * T4 =
      (A * B0 + 2 ^ 64 * (A * B1) + 2 ^ 128 * (A * B2) + 2 ^ 192 * (A * B3)) +
      (m0 * Q + 2 ^ 64 * (m1 * Q) + 2 ^ 128 * (m2 * Q) + 2 ^ 192 * (m3 * Q)) := by
  omega

/-- The final conditional subtraction of `mul`, given the folded Montgomery identity. -/
private theorem mul_finish (q : Limbs4) (t : State5) {A M : ℕ}
    (hlt : t.toNat < 2 * q.toNat) (hfold : 2 ^ 256 * t.toNat = A + M * q.toNat) :
    (condSubWide q t).toNat < q.toNat ∧
      2 ^ 256 * (condSubWide q t).toNat ≡ A [MOD q.toNat] := by
  have hmod : 2 ^ 256 * t.toNat ≡ A [MOD q.toNat] := by
    unfold Nat.ModEq
    rw [hfold, Nat.add_mul_mod_self_right]
  refine ⟨condSubWide_lt q _ hlt, ?_⟩
  rw [condSubWide_toNat q _ hlt]
  split
  · exact hmod
  · refine (Nat.ModEq.mul_left _ ?_).trans hmod
    exact (Nat.modEq_iff_dvd' (by omega)).2 ⟨1, by omega⟩

/-- Montgomery multiplication is canonical and computes `a * b * (2 ^ 256)⁻¹ mod q`. -/
theorem mul_spec (q : Limbs4) (negInv : UInt64) (a b : Limbs4)
    (hnq : negInv.toNat * q.toNat % 2 ^ 64 = 2 ^ 64 - 1) (haq : a.toNat < q.toNat) :
    (mul q negInv a b).toNat < q.toNat ∧
      2 ^ 256 * (mul q negInv a b).toNat ≡ a.toNat * b.toNat [MOD q.toNat] := by
  obtain ⟨L1, m0, hm0, r0⟩ :=
    mulRound_spec q a negInv b.l0 State5.zero hnq haq (by rw [State5.zero_toNat]; omega)
  obtain ⟨L2, m1, hm1, r1⟩ := mulRound_spec q a negInv b.l1 _ hnq haq L1
  obtain ⟨L3, m2, hm2, r2⟩ := mulRound_spec q a negInv b.l2 _ hnq haq L2
  obtain ⟨L4, m3, hm3, r3⟩ := mulRound_spec q a negInv b.l3 _ hnq haq L3
  rw [State5.zero_toNat] at r0
  have hfold := fold4 r0 r1 r2 r3
  rw [← mul_sum4, ← sum4_mul, ← Limbs4.toNat] at hfold
  simp only [mul]
  exact mul_finish q _ L4 hfold

end Native64x4
end Montgomery
