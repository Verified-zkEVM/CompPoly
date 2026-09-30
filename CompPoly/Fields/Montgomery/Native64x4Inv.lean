/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPoly.Fields.Montgomery.Native64x4Field
public import CompPoly.Fields.Montgomery.Native64x4InvDefs
public import CompPoly.Fields.Montgomery.Native64x8Inv
public import Mathlib.Tactic.Ring

/-!
# Fast inversion for four-limb Montgomery fields

Correctness of the checked inversion of `Montgomery/Native64x4InvDefs`: `invGcdRaw`
computes the field inverse and `FastField.invGcd` is its proof-carrying wrapper.  The
divstep coefficient bound is shared with the eight-limb stack; the mac-width safety of the
candidate is proved here for the five-word linear combinations.
-/

@[expose] public section

namespace Montgomery.Native64x4

open Montgomery.Native64x8 (gcdInner gcdInner_natAbs_le_31)

/-! ## Order from the borrow chain -/

/-- The final borrow decides the numeric order. -/
theorem subLimbs_borrow_eq_one_iff {a b : Limbs4} {d0 d1 d2 d3 bo : UInt64}
    (e : subLimbs a b = (d0, d1, d2, d3, bo)) : bo = 1 ↔ a.toNat < b.toNat := by
  obtain ⟨d0', d1', d2', d3', bo', e', hbo, hchain⟩ := subLimbs_spec a b
  rw [e] at e'
  simp only [Prod.mk.injEq] at e'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := e'
  have hd := Limbs4.toNat_lt ⟨d0, d1, d2, d3⟩
  rw [← UInt64.toNat_inj, show (1 : UInt64).toNat = 1 from rfl]
  omega

/-! ## Five-word specifications -/

/-- `mulWord` is the exact five-word product. -/
theorem mulWord_spec (x : Limbs4) (k : UInt64) :
    ∃ w0 w1 w2 w3 w4 : UInt64, mulWord x k = (w0, w1, w2, w3, w4) ∧
      w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 * w2.toNat + 2 ^ 192 * w3.toNat +
        2 ^ 256 * w4.toNat = x.toNat * k.toNat := by
  obtain ⟨w0, c0, e0, h0⟩ := mac_spec 0 x.l0 k 0
  obtain ⟨w1, c1, e1, h1⟩ := mac_spec 0 x.l1 k c0
  obtain ⟨w2, c2, e2, h2⟩ := mac_spec 0 x.l2 k c1
  obtain ⟨w3, w4, e3, h3⟩ := mac_spec 0 x.l3 k c2
  refine ⟨w0, w1, w2, w3, w4, by simp only [mulWord, e0, e1, e2, e3], ?_⟩
  rw [UInt64.toNat_zero] at h0 h1 h2 h3
  rw [Limbs4.toNat, sum4_mul]
  omega

/-- `add5` is the exact five-word sum with a one-bit carry. -/
theorem add5_spec (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : UInt64) :
    ∃ s0 s1 s2 s3 s4 c : UInt64,
      add5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 = (s0, s1, s2, s3, s4, c) ∧ c.toNat ≤ 1 ∧
      s0.toNat + 2 ^ 64 * s1.toNat + 2 ^ 128 * s2.toNat + 2 ^ 192 * s3.toNat +
          2 ^ 256 * s4.toNat + 2 ^ 320 * c.toNat =
        (a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat +
          2 ^ 256 * a4.toNat) +
        (b0.toNat + 2 ^ 64 * b1.toNat + 2 ^ 128 * b2.toNat + 2 ^ 192 * b3.toNat +
          2 ^ 256 * b4.toNat) := by
  obtain ⟨s0, c0, e0, h0, g0⟩ := adc_spec a0 b0 0 (by decide)
  obtain ⟨s1, c1, e1, h1, g1⟩ := adc_spec a1 b1 c0 g0
  obtain ⟨s2, c2, e2, h2, g2⟩ := adc_spec a2 b2 c1 g1
  obtain ⟨s3, c3, e3, h3, g3⟩ := adc_spec a3 b3 c2 g2
  obtain ⟨s4, c4, e4, h4, g4⟩ := adc_spec a4 b4 c3 g3
  refine ⟨s0, s1, s2, s3, s4, c4, by simp only [add5, e0, e1, e2, e3, e4], g4, ?_⟩
  rw [UInt64.toNat_zero] at h0
  omega

/-! ## Mac-width safety of the candidate -/

section MacSafety

/-- The Montgomery linear combination stays canonical for magnitudes below the modulus. -/
theorem lincombTail_lt {q uS vS : Limbs4} {negInv F G : UInt64} (hq0 : 0 < q.toNat)
    (hnq : negInv.toNat * q.toNat % 2 ^ 64 = 2 ^ 64 - 1)
    (huS : uS.toNat ≤ q.toNat) (hvS : vS.toNat ≤ q.toNat)
    (hFG : F.toNat + G.toNat ≤ 2 ^ 31) :
    (lincombTail q negInv uS vS F G).toNat < q.toNat := by
  obtain ⟨a0, a1, a2, a3, a4, ea, ha⟩ := mulWord_spec uS F
  obtain ⟨b0, b1, b2, b3, b4, eb, hb⟩ := mulWord_spec vS G
  obtain ⟨s0, s1, s2, s3, s4, c, es, hc, hs⟩ := add5_spec a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  obtain ⟨n0, n1, n2, n3, n4, en, hn⟩ := mulWord_spec q (montM s0 negInv)
  obtain ⟨t0, t1, t2, t3, t4, t5, et, ht5, ht⟩ := add5_spec s0 s1 s2 s3 s4 n0 n1 n2 n3 n4
  simp only [lincombTail, ea, eb, es, en, et]
  -- The combination is at most `q * 2 ^ 31`.
  have hAB : uS.toNat * F.toNat + vS.toNat * G.toNat ≤ q.toNat * 2 ^ 31 :=
    calc uS.toNat * F.toNat + vS.toNat * G.toNat
        ≤ q.toNat * F.toNat + q.toNat * G.toNat :=
          Nat.add_le_add (Nat.mul_le_mul huS (Nat.le_refl _))
            (Nat.mul_le_mul hvS (Nat.le_refl _))
      _ = q.toNat * (F.toNat + G.toNat) := (Nat.mul_add _ _ _).symm
      _ ≤ q.toNat * 2 ^ 31 := Nat.mul_le_mul (Nat.le_refl _) hFG
  -- The Montgomery multiple of the modulus cancels the low word.
  rw [montM_toNat, Nat.mul_comm q.toNat] at hn
  have hdvd := Montgomery.dvd_add (2 ^ 64) q.toNat negInv.toNat (by norm_num) hnq s0.toNat
  rw [Nat.mod_eq_of_lt (UInt64.toNat_lt s0)] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  have hN : s0.toNat * negInv.toNat % 2 ^ 64 * q.toNat < 2 ^ 64 * q.toNat :=
    Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by decide)) hq0
  have hQ := Limbs4.toNat_lt q
  have w0 := UInt64.toNat_lt s0
  have w1 := UInt64.toNat_lt n0
  have w2 := UInt64.toNat_lt t0
  have w3 := UInt64.toNat_lt a4
  have w4 := UInt64.toNat_lt b4
  have w5 := UInt64.toNat_lt n4
  have w6 := UInt64.toNat_lt s4
  apply condSubWide_lt
  rw [State5.toNat_eq]
  dsimp only
  omega

/-- The Montgomery lincomb stays canonical for canonical inputs. -/
theorem gcdLinearCombMontyRed_lt {q : Limbs4} {negInv : UInt64} {u v : Limbs4} {f g : Int}
    (hq0 : 0 < q.toNat) (hnq : negInv.toNat * q.toNat % 2 ^ 64 = 2 ^ 64 - 1)
    (huq : u.toNat < q.toNat) (hvq : v.toNat < q.toNat)
    (hfg : f.natAbs + g.natAbs ≤ 2 ^ 31) :
    (gcdLinearCombMontyRed q negInv u v f g).toNat < q.toNat := by
  have hofF : (UInt64.ofNat f.natAbs).toNat = f.natAbs := by
    rw [UInt64.toNat_ofNat']
    omega
  have hofG : (UInt64.ofNat g.natAbs).toNat = g.natAbs := by
    rw [UInt64.toNat_ofNat']
    omega
  have hneg : ∀ {c : Limbs4}, c.toNat < q.toNat → (negMod q c).toNat ≤ q.toNat := by
    intro c hc
    obtain ⟨d0, d1, d2, d3, bo, e, hbo, hchain⟩ := subLimbs_spec q c
    simp only [negMod, e]
    have hD := Limbs4.toNat_lt ⟨d0, d1, d2, d3⟩
    omega
  unfold gcdLinearCombMontyRed
  apply lincombTail_lt hq0 hnq
  · split
    · exact hneg huq
    · exact Nat.le_of_lt huq
  · split
    · exact hneg hvq
    · exact Nat.le_of_lt hvq
  · rw [hofF, hofG]
    exact hfg

set_option maxRecDepth 4000 in
/-- The main loop keeps the Montgomery pair canonical. -/
theorem gcdMainLoop_bounded {q : Limbs4} {negInv : UInt64} {rounds : ℕ}
    {a u b v A U B V : Limbs4}
    (hq0 : 0 < q.toNat) (hnq : negInv.toNat * q.toNat % 2 ^ 64 = 2 ^ 64 - 1)
    (huq : u.toNat < q.toNat) (hvq : v.toNat < q.toNat)
    (heq : gcdMainLoop q negInv rounds a u b v = (A, U, B, V)) :
    U.toNat < q.toNat ∧ V.toNat < q.toNat := by
  induction rounds generalizing a u b v with
  | zero =>
    rw [show gcdMainLoop q negInv 0 a u b v = (a, u, b, v) from rfl] at heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    exact ⟨huq, hvq⟩
  | succ k ih =>
    simp only [gcdMainLoop] at heq
    rcases hnb : gcdNumBits a b with ⟨limbIdx, bits⟩
    rw [hnb] at heq
    dsimp only at heq
    rcases hI : gcdInner 31 (gcdApprox a limbIdx bits) (gcdApprox b limbIdx bits) 1 0 0 1
      with ⟨a1, b1, f0, g0, f1, g1⟩
    rw [hI] at heq
    dsimp only at heq
    rcases hdA : gcdLinearCombDiv a b f0 g0 with ⟨newA, signA⟩
    rw [hdA] at heq
    dsimp only at heq
    rcases hdB : gcdLinearCombDiv a b f1 g1 with ⟨newB, signB⟩
    rw [hdB] at heq
    dsimp only at heq
    obtain ⟨hrow0, hrow1⟩ := gcdInner_natAbs_le_31 (Nat.le_refl 31) hI
    have hc0 : (if signA < 0 then -f0 else f0).natAbs
        + (if signA < 0 then -g0 else g0).natAbs ≤ 2 ^ 31 := by
      split <;> simpa [Int.natAbs_neg] using hrow0
    have hc1 : (if signB < 0 then -f1 else f1).natAbs
        + (if signB < 0 then -g1 else g1).natAbs ≤ 2 ^ 31 := by
      split <;> simpa [Int.natAbs_neg] using hrow1
    have hU' := gcdLinearCombMontyRed_lt (f := if signA < 0 then -f0 else f0)
      (g := if signA < 0 then -g0 else g0) hq0 hnq huq hvq hc0
    have hV' := gcdLinearCombMontyRed_lt (f := if signB < 0 then -f1 else f1)
      (g := if signB < 0 then -g1 else g1) hq0 hnq huq hvq hc1
    exact ih hU' hV' heq

-- Tuple witnesses without evaluating `p`; a bare `rfl` witness would whnf-expand it.
private theorem exists_eq_tuple4 {α β γ δ : Type} (p : α × β × γ × δ) :
    ∃ a b c d, p = (a, b, c, d) :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2, by simp only [Prod.mk.eta]⟩

private theorem exists_eq_tuple6 {α β γ δ ε ζ : Type} (p : α × β × γ × δ × ε × ζ) :
    ∃ a b c d e f, p = (a, b, c, d, e, f) :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2, by simp only [Prod.mk.eta]⟩

/-- The final chunks stay canonical for canonical inputs. -/
theorem gcdFinalChunks_lt {q : Limbs4} {negInv : UInt64} {finalRounds : ℕ}
    {a u b v : Limbs4} (hfr : finalRounds ≤ 62)
    (hq0 : 0 < q.toNat) (hnq : negInv.toNat * q.toNat % 2 ^ 64 = 2 ^ 64 - 1)
    (huq : u.toNat < q.toNat) (hvq : v.toNat < q.toNat) :
    (gcdFinalChunks q negInv finalRounds a u b v).toNat < q.toNat := by
  obtain ⟨aw1, bw1, f0, g0, f1, g1, hI1⟩ :=
    exists_eq_tuple6 (gcdInner ((finalRounds + 1) / 2) a.l0 b.l0 1 0 0 1)
  obtain ⟨hrow0, hrow1⟩ := gcdInner_natAbs_le_31 (by omega) hI1
  have hu1 := gcdLinearCombMontyRed_lt (f := f0) (g := g0) hq0 hnq huq hvq hrow0
  have hv1 := gcdLinearCombMontyRed_lt (f := f1) (g := g1) hq0 hnq huq hvq hrow1
  obtain ⟨aw2, bw2, F0, G0, F1, G1, hI2⟩ :=
    exists_eq_tuple6 (gcdInner (finalRounds - (finalRounds + 1) / 2) aw1 bw1 1 0 0 1)
  obtain ⟨-, hrowF⟩ := gcdInner_natAbs_le_31 (by omega) hI2
  have hfinal := gcdLinearCombMontyRed_lt (f := F1) (g := G1) hq0 hnq hu1 hv1 hrowF
  have heq : gcdFinalChunks q negInv finalRounds a u b v
      = gcdLinearCombMontyRed q negInv
          (gcdLinearCombMontyRed q negInv u v f0 g0)
          (gcdLinearCombMontyRed q negInv u v f1 g1) F1 G1 := by
    rw [gcdFinalChunks.eq_def]
    dsimp only
    rw [hI1]
    dsimp only
    rw [hI2]
  rw [heq]
  exact hfinal

set_option maxRecDepth 4000 in
/-- The candidate is canonical. -/
theorem gcdInvCandidate_lt {modulus : ℕ} [P : GcdData modulus] {q x : Limbs4}
    {negInv : UInt64} (hqm : q.toNat = modulus) (hq0 : 0 < q.toNat)
    (hnq : negInv.toNat * q.toNat % 2 ^ 64 = 2 ^ 64 - 1) :
    (gcdInvCandidate modulus q negInv x).toNat < q.toNat := by
  have hu0 : P.initU.toNat < q.toNat := by
    rw [P.initU_toNat, hqm]
    exact Nat.mod_lt _ (by omega)
  have hv0 : Limbs4.zero.toNat < q.toNat := by
    rw [Limbs4.zero_toNat]
    omega
  obtain ⟨a, u, b, v, hML⟩ :=
    exists_eq_tuple4 (gcdMainLoop q negInv 15 x P.initU q Limbs4.zero)
  obtain ⟨hUq, hVq⟩ := gcdMainLoop_bounded hq0 hnq hu0 hv0 hML
  -- `unfold` only; generating `gcdInvCandidate.eq_def` times out on the 15-round loop.
  have hcand : gcdInvCandidate modulus q negInv x
      = gcdFinalChunks q negInv P.finalRounds a u b v := by
    unfold gcdInvCandidate
    rw [hML]
  rw [hcand]
  exact gcdFinalChunks_lt P.finalRounds_le hq0 hnq hUq hVq

variable {modulus : ℕ} [P : Mont64x4Field modulus]

/-- With the class data, the candidate is canonical for any input. -/
theorem gcdInvCandidate_lt_modulus [GcdData modulus] (x : Limbs4) :
    (gcdInvCandidate modulus P.modulusLimbs P.montgomeryNegInv x).toNat < modulus := by
  have h := gcdInvCandidate_lt (q := P.modulusLimbs) (negInv := P.montgomeryNegInv) (x := x)
    Mont64x4Field.q_toNat (by rw [Mont64x4Field.q_toNat]; exact Mont64x4Field.modulus_pos)
    Mont64x4Field.negInv_mul_q
  rwa [Mont64x4Field.q_toNat] at h

end MacSafety

/-! ## The Fermat fallback and the checked raw inversion -/

section

variable {modulus : ℕ} [P : Mont64x4Field modulus]

private theorem toField_hpow (x : FastField modulus) (n : ℕ) :
    (x ^ n).toField = x.toField ^ n :=
  FastField.toField_pow x n

/-- `montPow` computes `acc · xⁿ`. -/
theorem montPow_eq_mul_pow (acc x : FastField modulus) (n : ℕ) :
    montPow P.modulusLimbs P.montgomeryNegInv acc.val x.val n = (acc * x ^ n).val := by
  induction n using Nat.strong_induction_on generalizing acc x with
  | _ n ih =>
    rw [montPow.eq_def]
    split
    next h =>
      subst h
      refine congrArg Subtype.val (FastField.toField_injective ?_)
      rw [FastField.toField_mul, toField_hpow, pow_zero, mul_one]
    next h =>
      have hlt : n / 2 < n := by omega
      by_cases hodd : n % 2 == 1
      · rw [ite_eq_left hodd, ← FastField.val_mul, ← FastField.val_mul, ih _ hlt]
        simp only [beq_iff_eq] at hodd
        refine congrArg Subtype.val (FastField.toField_injective ?_)
        simp only [FastField.toField_mul, toField_hpow]
        conv_rhs => rw [show n = 2 * (n / 2) + 1 by omega]
        ring
      · rw [ite_eq_right hodd, ← FastField.val_mul, ih _ hlt]
        simp only [beq_iff_eq] at hodd
        refine congrArg Subtype.val (FastField.toField_injective ?_)
        simp only [FastField.toField_mul, toField_hpow]
        conv_rhs => rw [show n = 2 * (n / 2) by omega]
        ring

/-- The `montPow` fallback computes the field inverse. -/
theorem montPow_eq_inv (x : FastField modulus) :
    montPow P.modulusLimbs P.montgomeryNegInv P.rModModulus x.val (modulus - 2)
      = (x⁻¹).val := by
  rw [show P.rModModulus = (1 : FastField modulus).val from rfl, montPow_eq_mul_pow]
  have h1 : (1 : FastField modulus) * x ^ (modulus - 2) = x ^ (modulus - 2) :=
    FastField.toField_injective
      (by rw [FastField.toField_mul, FastField.toField_one, one_mul])
  -- The `rfl` holds since `x⁻¹` unfolds to `pow x (modulus - 2)`.
  exact congrArg Subtype.val (h1.trans rfl)

/-- Accept a raw candidate `z` for `x⁻¹` if it verifies, else fall back to `x⁻¹`. -/
private def invWithCandidate (x : FastField modulus) (z : Limbs4) : FastField modulus :=
  if h : (subLimbs z P.modulusLimbs).2.2.2.2 = 1 ∧
      Native64x4.mul P.modulusLimbs P.montgomeryNegInv z x.val = P.rModModulus then
    ⟨z, by
      obtain ⟨d0, d1, d2, d3, bo, e, -, -⟩ := subLimbs_spec z P.modulusLimbs
      have hb := h.1
      rw [e] at hb
      have hlt := (subLimbs_borrow_eq_one_iff e).mp hb
      rwa [Mont64x4Field.q_toNat] at hlt⟩
  else x⁻¹

private theorem invWithCandidate_eq_inv (x : FastField modulus) (z : Limbs4) :
    invWithCandidate x z = x⁻¹ := by
  unfold invWithCandidate
  split
  case isTrue h =>
    refine eq_inv_of_mul_eq_one_left (Subtype.ext ?_)
    show Native64x4.mul P.modulusLimbs P.montgomeryNegInv z x.val = P.rModModulus
    exact h.2
  case isFalse _ => rfl

-- Stated for a generic candidate: `rfl` against the GCD candidate would unfold it.
private theorem invGcdRaw_eq_invWithCandidate (x : FastField modulus) (z : Limbs4) :
    (if (subLimbs z P.modulusLimbs).2.2.2.2 = 1 ∧
        Native64x4.mul P.modulusLimbs P.montgomeryNegInv z x.val = P.rModModulus then z
      else montPow P.modulusLimbs P.montgomeryNegInv P.rModModulus x.val (modulus - 2))
      = (invWithCandidate x z).val := by
  unfold invWithCandidate
  split
  next h => rfl
  next h => exact montPow_eq_inv x

/-- `invGcdRaw` computes the field inverse. -/
theorem invGcdRaw_eq_inv [GcdData modulus] (x : FastField modulus) :
    invGcdRaw modulus P.modulusLimbs P.montgomeryNegInv P.rModModulus x.val
      = (x⁻¹).val :=
  (invGcdRaw_eq_invWithCandidate x _).trans
    (congrArg Subtype.val (invWithCandidate_eq_inv x _))

end

/-! ## The proof-carrying wrapper -/

namespace FastField

variable {modulus : ℕ} [P : Mont64x4Field modulus]

/-- The proof-carrying wrapper of the checked inversion `invGcdRaw`. -/
@[inline] def invGcd [GcdData modulus] (x : FastField modulus) : FastField modulus :=
  ⟨invGcdRaw modulus P.modulusLimbs P.montgomeryNegInv P.rModModulus x.val, by
    rw [invGcdRaw_eq_inv x]
    exact (x⁻¹).property⟩

/-- `invGcd` agrees with the `Field` inverse. -/
@[simp]
theorem invGcd_eq_inv [GcdData modulus] (x : FastField modulus) :
    invGcd x = x⁻¹ := by
  have hval : (invGcd x).val
      = invGcdRaw modulus P.modulusLimbs P.montgomeryNegInv P.rModModulus x.val := by
    simp only [invGcd]
  exact Subtype.ext (hval.trans (invGcdRaw_eq_inv x))

end FastField

end Montgomery.Native64x4
