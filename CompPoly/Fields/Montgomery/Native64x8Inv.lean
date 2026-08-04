/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPoly.Fields.Montgomery.Native64x8Field
public import CompPoly.Fields.Montgomery.Native64x8InvDefs
public import Mathlib.Tactic.Ring

/-!
# Fast inversion for eight-limb Montgomery fields

Correctness of the checked inversion of `Montgomery/Native64x8InvDefs`: `invGcdRaw`
computes the field inverse and `FastField.invGcd` is its proof-carrying wrapper.  Also
proves the divstep coefficient bound and the mac-width safety of the candidate.
-/

@[expose] public section

namespace Montgomery.Native64x8

/-! ## Divstep coefficient bounds -/

/-- Unfolding of the empty divstep run. -/
theorem gcdInner_zero (a b : UInt64) (f0 g0 f1 g1 : Int) :
    gcdInner 0 a b f0 g0 f1 g1 = (a, b, f0, g0, f1, g1) := rfl

/-- Unfolding of one divstep. -/
theorem gcdInner_succ (rounds : ℕ) (a b : UInt64) (f0 g0 f1 g1 : Int) :
    gcdInner (rounds + 1) a b f0 g0 f1 g1 =
      if a &&& 1 == 0 then
        gcdInner rounds (a >>> 1) b f0 g0 (f1 * 2) (g1 * 2)
      else if a < b then
        gcdInner rounds ((b - a) >>> 1) a (f1 - f0) (g1 - g0) (f0 * 2) (g0 * 2)
      else
        gcdInner rounds ((a - b) >>> 1) b (f0 - f1) (g0 - g1) (f1 * 2) (g1 * 2) := by
  simp only [gcdInner]
  by_cases h1 : a &&& 1 == 0
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : a < b
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]

/-- Transition entries at most double per divstep. -/
theorem gcdInner_natAbs_le {rounds : ℕ} {a b a' b' : UInt64}
    {f0 g0 f1 g1 f0' g0' f1' g1' : Int} {n : ℕ}
    (h0 : f0.natAbs + g0.natAbs ≤ n) (h1 : f1.natAbs + g1.natAbs ≤ n)
    (heq : gcdInner rounds a b f0 g0 f1 g1 = (a', b', f0', g0', f1', g1')) :
    f0'.natAbs + g0'.natAbs ≤ 2 ^ rounds * n ∧
      f1'.natAbs + g1'.natAbs ≤ 2 ^ rounds * n := by
  induction rounds generalizing a b f0 g0 f1 g1 n with
  | zero =>
    rw [gcdInner_zero] at heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨-, -, rfl, rfl, rfl, rfl⟩ := heq
    rw [Nat.pow_zero, Nat.one_mul]
    exact ⟨h0, h1⟩
  | succ k ih =>
    have step : ∀ {A B : UInt64} {F0 G0 F1 G1 : Int},
        F0.natAbs + G0.natAbs ≤ 2 * n → F1.natAbs + G1.natAbs ≤ 2 * n →
        gcdInner k A B F0 G0 F1 G1 = (a', b', f0', g0', f1', g1') →
        f0'.natAbs + g0'.natAbs ≤ 2 ^ (k + 1) * n ∧
          f1'.natAbs + g1'.natAbs ≤ 2 ^ (k + 1) * n := by
      intro A B F0 G0 F1 G1 hF hG hEq
      rw [Nat.pow_succ, Nat.mul_assoc]
      exact ih hF hG hEq
    rw [gcdInner_succ] at heq
    split at heq
    · exact step (by omega) (by omega) heq
    · split at heq
      · exact step (by omega) (by omega) heq
      · exact step (by omega) (by omega) heq

/-- Chunks of at most 31 divsteps satisfy the linear-combination bound. -/
theorem gcdInner_natAbs_le_31 {rounds : ℕ} (h31 : rounds ≤ 31) {a b a' b' : UInt64}
    {f0' g0' f1' g1' : Int}
    (heq : gcdInner rounds a b 1 0 0 1 = (a', b', f0', g0', f1', g1')) :
    f0'.natAbs + g0'.natAbs ≤ 2 ^ 31 ∧ f1'.natAbs + g1'.natAbs ≤ 2 ^ 31 := by
  have h := gcdInner_natAbs_le (n := 1) (by decide) (by decide) heq
  have hle : 2 ^ rounds ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) h31
  omega

/-! ## Order from the borrow chain -/

/-- The final borrow decides the numeric order. -/
theorem subBorrow_eq_one_iff {a b : Limbs8} (ha : a.Bounded) (hb : b.Bounded) :
    subBorrow a b = 1 ↔ a.toNat < b.toNat := by
  obtain ⟨hbo, hchain⟩ := subLimbs_spec a b ha hb
  have hd := Limbs8.toNat_lt (subLimbs_bounded a b)
  rw [← UInt64.toNat_inj, show (1 : UInt64).toNat = 1 from rfl]
  omega

/-! ## Mac-width safety of the candidate -/

section MacSafety

set_option maxRecDepth 4000

private theorem and_mask_toNat_lt (y : UInt64) : (y &&& 0xFFFFFFFF).toNat < 2 ^ 32 := by
  rw [UInt64.toNat_and, show ((0xFFFFFFFF : UInt64).toNat) = 2 ^ 32 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

/-- The division lincomb masks every output limb. -/
theorem gcdLinearCombDiv_bounded (a b : Limbs8) (f g : Int) :
    (gcdLinearCombDiv a b f g).1.Bounded := by
  simp only [gcdLinearCombDiv]
  repeat' split
  all_goals
    exact ⟨and_mask_toNat_lt _, and_mask_toNat_lt _, and_mask_toNat_lt _, and_mask_toNat_lt _,
      and_mask_toNat_lt _, and_mask_toNat_lt _, and_mask_toNat_lt _, and_mask_toNat_lt _⟩

private theorem lincomb_stack_lt {q aS bS : Limbs8} {negInv F G : UInt64}
    (hq : q.Bounded) (hq0 : 0 < q.toNat) (hq2 : 2 * q.toNat < 2 ^ 256)
    (hn : negInv.toNat < 2 ^ 32) (hnq : negInv.toNat * q.toNat % 2 ^ 32 = 2 ^ 32 - 1)
    (haS : aS.Bounded) (hbS : bS.Bounded)
    (haSq : aS.toNat ≤ q.toNat) (hbSq : bS.toNat ≤ q.toNat)
    (hFG : F.toNat + G.toNat ≤ 2 ^ 31) :
    (condSub q (mulReduce q negInv
        (mulAccum bS G (mulAccum aS F State9.zero))).toLimbs8).Bounded ∧
      (condSub q (mulReduce q negInv
        (mulAccum bS G (mulAccum aS F State9.zero))).toLimbs8).toNat < q.toNat := by
  obtain ⟨h1b, h1t8, h1v⟩ :=
    mulAccum_spec aS F State9.zero haS State9.zero_bounded (by omega)
  rw [State9.zero_toNat, Nat.zero_add] at h1v
  have hcap : aS.toNat * F.toNat ≤ (2 ^ 256 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by have := Limbs8.toNat_lt haS; omega) (by omega)
  have hdec1 : (mulAccum aS F State9.zero).toNat
      = (mulAccum aS F State9.zero).toLimbs8.toNat
        + 2 ^ 256 * (mulAccum aS F State9.zero).t8.toNat := rfl
  have h1t8' : (mulAccum aS F State9.zero).t8.toNat < 2 ^ 32 := by omega
  obtain ⟨h2b, h2t8, h2v⟩ := mulAccum_spec bS G _ hbS ⟨h1b, h1t8'⟩ (by omega)
  rw [h1v] at h2v
  obtain ⟨h3b, h3v⟩ := mulReduce_spec q negInv _ hq h2b h2t8 hn hnq
  have hs_le : (mulAccum bS G (mulAccum aS F State9.zero)).toNat ≤ q.toNat * 2 ^ 31 := by
    rw [h2v]
    calc aS.toNat * F.toNat + bS.toNat * G.toNat
        ≤ q.toNat * F.toNat + q.toNat * G.toNat :=
          Nat.add_le_add (Nat.mul_le_mul haSq (Nat.le_refl _))
            (Nat.mul_le_mul hbSq (Nat.le_refl _))
      _ = q.toNat * (F.toNat + G.toNat) := (Nat.mul_add _ _ _).symm
      _ ≤ q.toNat * 2 ^ 31 := Nat.mul_le_mul (Nat.le_refl _) hFG
  have hmq : (montM (mulAccum bS G (mulAccum aS F State9.zero)).t0 negInv).toNat * q.toNat
      ≤ (2 ^ 32 - 1) * q.toNat := by
    have := montM_lt (mulAccum bS G (mulAccum aS F State9.zero)).t0 negInv
    exact Nat.mul_le_mul (by omega) (Nat.le_refl _)
  have hdec2 : (mulReduce q negInv (mulAccum bS G (mulAccum aS F State9.zero))).toNat
      = (mulReduce q negInv
          (mulAccum bS G (mulAccum aS F State9.zero))).toLimbs8.toNat
        + 2 ^ 256
          * (mulReduce q negInv (mulAccum bS G (mulAccum aS F State9.zero))).t8.toNat := rfl
  exact ⟨condSub_bounded q _ h3b.1, condSub_lt q _ hq h3b.1 (by omega)⟩

/-- The Montgomery lincomb stays canonical for canonical inputs. -/
theorem gcdLinearCombMontyRed_lt {q : Limbs8} {negInv : UInt64} {a b : Limbs8} {f g : Int}
    (hq : q.Bounded) (hq0 : 0 < q.toNat) (hq2 : 2 * q.toNat < 2 ^ 256)
    (hn : negInv.toNat < 2 ^ 32) (hnq : negInv.toNat * q.toNat % 2 ^ 32 = 2 ^ 32 - 1)
    (ha : a.Bounded) (hb : b.Bounded) (haq : a.toNat < q.toNat) (hbq : b.toNat < q.toNat)
    (hfg : f.natAbs + g.natAbs ≤ 2 ^ 31) :
    (gcdLinearCombMontyRed q negInv a b f g).Bounded ∧
      (gcdLinearCombMontyRed q negInv a b f g).toNat < q.toNat := by
  have hofF : (UInt64.ofNat f.natAbs).toNat = f.natAbs := by
    rw [UInt64.toNat_ofNat']
    omega
  have hofG : (UInt64.ofNat g.natAbs).toNat = g.natAbs := by
    rw [UInt64.toNat_ofNat']
    omega
  have hsub_le : ∀ {c : Limbs8}, c.Bounded → c.toNat < q.toNat →
      (subLimbs q c).toNat ≤ q.toNat := by
    intro c hc hcq
    obtain ⟨hbo, hchain⟩ := subLimbs_spec q c hq hc
    have hlt := Limbs8.toNat_lt (subLimbs_bounded q c)
    have hqlt := Limbs8.toNat_lt hq
    omega
  simp only [gcdLinearCombMontyRed]
  refine lincomb_stack_lt hq hq0 hq2 hn hnq ?_ ?_ ?_ ?_ ?_
  · split
    · exact subLimbs_bounded q a
    · exact ha
  · split
    · exact subLimbs_bounded q b
    · exact hb
  · split
    · exact hsub_le ha haq
    · exact Nat.le_of_lt haq
  · split
    · exact hsub_le hb hbq
    · exact Nat.le_of_lt hbq
  · rw [hofF, hofG]
    exact hfg

/-- The main loop keeps both tracks at mac width and the Montgomery pair canonical. -/
theorem gcdMainLoop_bounded {q : Limbs8} {negInv : UInt64} {rounds : ℕ}
    {a u b v A U B V : Limbs8}
    (hq : q.Bounded) (hq0 : 0 < q.toNat) (hq2 : 2 * q.toNat < 2 ^ 256)
    (hn : negInv.toNat < 2 ^ 32) (hnq : negInv.toNat * q.toNat % 2 ^ 32 = 2 ^ 32 - 1)
    (ha : a.Bounded) (hb : b.Bounded) (hu : u.Bounded) (huq : u.toNat < q.toNat)
    (hv : v.Bounded) (hvq : v.toNat < q.toNat)
    (heq : gcdMainLoop q negInv rounds a u b v = (A, U, B, V)) :
    A.Bounded ∧ B.Bounded ∧ U.Bounded ∧ U.toNat < q.toNat ∧ V.Bounded ∧
      V.toNat < q.toNat := by
  induction rounds generalizing a u b v with
  | zero =>
    rw [show gcdMainLoop q negInv 0 a u b v = (a, u, b, v) from rfl] at heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    exact ⟨ha, hb, hu, huq, hv, hvq⟩
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
    have hA' : newA.Bounded := by
      have h := gcdLinearCombDiv_bounded a b f0 g0
      rw [hdA] at h
      exact h
    have hB' : newB.Bounded := by
      have h := gcdLinearCombDiv_bounded a b f1 g1
      rw [hdB] at h
      exact h
    have hc0 : (if signA < 0 then -f0 else f0).natAbs
        + (if signA < 0 then -g0 else g0).natAbs ≤ 2 ^ 31 := by
      split <;> simpa [Int.natAbs_neg] using hrow0
    have hc1 : (if signB < 0 then -f1 else f1).natAbs
        + (if signB < 0 then -g1 else g1).natAbs ≤ 2 ^ 31 := by
      split <;> simpa [Int.natAbs_neg] using hrow1
    have hU' := gcdLinearCombMontyRed_lt (f := if signA < 0 then -f0 else f0)
      (g := if signA < 0 then -g0 else g0) hq hq0 hq2 hn hnq hu hv huq hvq hc0
    have hV' := gcdLinearCombMontyRed_lt (f := if signB < 0 then -f1 else f1)
      (g := if signB < 0 then -g1 else g1) hq hq0 hq2 hn hnq hu hv huq hvq hc1
    exact ih hA' hB' hU'.1 hU'.2 hV'.1 hV'.2 heq

-- Tuple witnesses without evaluating `p`; a bare `rfl` witness would whnf-expand it.
private theorem exists_eq_tuple4 {α β γ δ : Type} (p : α × β × γ × δ) :
    ∃ a b c d, p = (a, b, c, d) :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2, by simp only [Prod.mk.eta]⟩

private theorem exists_eq_tuple6 {α β γ δ ε ζ : Type} (p : α × β × γ × δ × ε × ζ) :
    ∃ a b c d e f, p = (a, b, c, d, e, f) :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2, by simp only [Prod.mk.eta]⟩

/-- The candidate stays at mac width and canonical. -/
theorem gcdInvCandidate_lt {modulus : ℕ} [P : GcdData modulus] {q x : Limbs8}
    {negInv : UInt64}
    (hq : q.Bounded) (hqm : q.toNat = modulus) (hq0 : 0 < q.toNat)
    (hq2 : 2 * q.toNat < 2 ^ 256) (hn : negInv.toNat < 2 ^ 32)
    (hnq : negInv.toNat * q.toNat % 2 ^ 32 = 2 ^ 32 - 1) (hx : x.Bounded) :
    (gcdInvCandidate modulus q negInv x).Bounded ∧
      (gcdInvCandidate modulus q negInv x).toNat < q.toNat := by
  have hu0 : P.initU.toNat < q.toNat := by
    rw [P.initU_toNat, hqm]
    exact Nat.mod_lt _ (by omega)
  have hv0 : Limbs8.zero.toNat < q.toNat := by
    rw [Limbs8.zero_toNat]
    omega
  obtain ⟨a, u, b, v, hML⟩ :=
    exists_eq_tuple4 (gcdMainLoop q negInv 15 x P.initU q Limbs8.zero)
  obtain ⟨hA, hB, hU, hUq, hV, hVq⟩ := gcdMainLoop_bounded hq hq0 hq2 hn hnq hx hq
    P.initU_bounded hu0 Limbs8.zero_bounded hv0 hML
  obtain ⟨aw1, bw1, f0, g0, f1, g1, hI1⟩ :=
    exists_eq_tuple6 (gcdInner ((P.finalRounds + 1) / 2) ((a.l1 <<< 32) ||| a.l0)
      ((b.l1 <<< 32) ||| b.l0) 1 0 0 1)
  obtain ⟨hrow0, hrow1⟩ :=
    gcdInner_natAbs_le_31 (by have := P.finalRounds_le; omega) hI1
  have hu1 := gcdLinearCombMontyRed_lt (f := f0) (g := g0) hq hq0 hq2 hn hnq hU hV hUq
    hVq hrow0
  have hv1 := gcdLinearCombMontyRed_lt (f := f1) (g := g1) hq hq0 hq2 hn hnq hU hV hUq
    hVq hrow1
  obtain ⟨aw2, bw2, F0, G0, F1, G1, hI2⟩ :=
    exists_eq_tuple6 (gcdInner (P.finalRounds - (P.finalRounds + 1) / 2) aw1 bw1 1 0 0 1)
  obtain ⟨-, hrowF⟩ := gcdInner_natAbs_le_31 (by have := P.finalRounds_le; omega) hI2
  have hfinal := gcdLinearCombMontyRed_lt (f := F1) (g := G1) hq hq0 hq2 hn hnq
    hu1.1 hv1.1 hu1.2 hv1.2 hrowF
  -- Unfold syntactically; whnf of the 15-round main loop times out.
  have hcand : gcdInvCandidate modulus q negInv x
      = gcdLinearCombMontyRed q negInv
          (gcdLinearCombMontyRed q negInv u v f0 g0)
          (gcdLinearCombMontyRed q negInv u v f1 g1) F1 G1 := by
    rw [gcdInvCandidate.eq_def, hML]
    dsimp only
    rw [hI1]
    dsimp only
    rw [hI2]
  rw [hcand]
  exact hfinal

variable {modulus : ℕ} [P : Mont64x8Field modulus]

/-- With the class data, the candidate is bounded and canonical for any bounded input. -/
theorem gcdInvCandidate_lt_modulus [GcdData modulus] {x : Limbs8} (hx : x.Bounded) :
    (gcdInvCandidate modulus P.modulusLimbs P.montgomeryNegInv x).Bounded ∧
      (gcdInvCandidate modulus P.modulusLimbs P.montgomeryNegInv x).toNat < modulus := by
  have h := gcdInvCandidate_lt P.modulusLimbs_bounded Mont64x8Field.q_toNat
    (by rw [Mont64x8Field.q_toNat]; exact Mont64x8Field.modulus_pos)
    Mont64x8Field.two_mul_q_lt P.montgomeryNegInv_lt Mont64x8Field.negInv_mul_q hx
  rwa [Mont64x8Field.q_toNat] at h

end MacSafety

/-! ## The Fermat fallback and the checked raw inversion -/

section

variable {modulus : ℕ} [P : Mont64x8Field modulus]

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
      · rw [if_pos hodd,
          show Native64x8.mul P.modulusLimbs P.montgomeryNegInv acc.val x.val
            = (acc * x).val from rfl,
          show Native64x8.mul P.modulusLimbs P.montgomeryNegInv x.val x.val
            = (x * x).val from rfl,
          ih _ hlt]
        simp only [beq_iff_eq] at hodd
        refine congrArg Subtype.val (FastField.toField_injective ?_)
        simp only [FastField.toField_mul, toField_hpow]
        conv_rhs => rw [show n = 2 * (n / 2) + 1 by omega]
        ring
      · rw [if_neg hodd,
          show Native64x8.mul P.modulusLimbs P.montgomeryNegInv x.val x.val
            = (x * x).val from rfl,
          ih _ hlt]
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
private def invWithCandidate (x : FastField modulus) (z : Limbs8) : FastField modulus :=
  if h : z.Bounded ∧ subBorrow z P.modulusLimbs = 1 ∧
      Native64x8.mul P.modulusLimbs P.montgomeryNegInv z x.val = P.rModModulus then
    ⟨z, h.1, by
      have hlt := (subBorrow_eq_one_iff h.1 P.modulusLimbs_bounded).mp h.2.1
      rwa [Mont64x8Field.q_toNat] at hlt⟩
  else x⁻¹

private theorem invWithCandidate_eq_inv (x : FastField modulus) (z : Limbs8) :
    invWithCandidate x z = x⁻¹ := by
  unfold invWithCandidate
  split
  case isTrue h =>
    refine eq_inv_of_mul_eq_one_left (Subtype.ext ?_)
    show Native64x8.mul P.modulusLimbs P.montgomeryNegInv z x.val = P.rModModulus
    exact h.2.2
  case isFalse _ => rfl

/-- `invGcdRaw` computes the field inverse. -/
theorem invGcdRaw_eq_inv [GcdData modulus] (x : FastField modulus) :
    invGcdRaw modulus P.modulusLimbs P.montgomeryNegInv P.rModModulus x.val
      = (x⁻¹).val := by
  have hval : invGcdRaw modulus P.modulusLimbs P.montgomeryNegInv P.rModModulus x.val
      = (invWithCandidate x
          (gcdInvCandidate modulus P.modulusLimbs P.montgomeryNegInv x.val)).val := by
    simp only [invGcdRaw, invWithCandidate]
    split
    next h => rfl
    next h => exact montPow_eq_inv x
  rw [hval, invWithCandidate_eq_inv]

end

/-! ## The proof-carrying wrapper -/

namespace FastField

variable {modulus : ℕ} [P : Mont64x8Field modulus]

/-- The proof-carrying wrapper of the checked inversion `invGcdRaw`. -/
@[inline] def invGcd [GcdData modulus] (x : FastField modulus) : FastField modulus :=
  ⟨invGcdRaw modulus P.modulusLimbs P.montgomeryNegInv P.rModModulus x.val, by
    rw [invGcdRaw_eq_inv x]
    exact (x⁻¹).property⟩

/-- `invGcd` agrees with the `Field` inverse. -/
theorem invGcd_eq_inv [GcdData modulus] (x : FastField modulus) :
    invGcd x = x⁻¹ := by
  have hval : (invGcd x).val
      = invGcdRaw modulus P.modulusLimbs P.montgomeryNegInv P.rModModulus x.val := by
    simp only [invGcd]
  exact Subtype.ext (hval.trans (invGcdRaw_eq_inv x))

end FastField

end Montgomery.Native64x8
