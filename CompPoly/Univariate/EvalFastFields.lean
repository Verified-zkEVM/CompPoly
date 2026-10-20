/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.EvalFast
public import CompPoly.Fields.Goldilocks.Fast
public import CompPoly.Fields.KoalaBear.Fast
public import CompPoly.Fields.BN254.Fast
import all CompPoly.Fields.Montgomery.Native64x4Mul
import all CompPoly.Fields.Montgomery.Native64x4Field
import all CompPoly.Fields.Montgomery.Native32Field

/-! # Lazy arithmetic for parallel polynomial evaluation -/

@[expose] public section

namespace Goldilocks.Fast

/-- Multiply a redundant accumulator by the point and add a canonical coefficient. -/
@[inline]
def evalStep (x : Field) (a : Field) (acc : UInt64) : UInt64 :=
  let product := mulLazy acc x.val
  let sum := product + a.val
  if sum < product then sum + negModulus else sum

/-- Normalize once, after evaluating the entire leaf. -/
@[inline]
def evalLazyRange (p : Array Field) (x : Field) (lo hi : Nat) : Field :=
  reduceUInt64 (p.foldr (evalStep x) 0 hi lo)

private theorem evalStep_cast (x a : Field) (acc : UInt64) :
    ((evalStep x a acc).toNat : Goldilocks.Field) =
      (acc.toNat : Goldilocks.Field) * toField x + toField a := by
  have ha := a.property
  have hp := (mulLazy acc x.val).toNat_lt
  unfold evalStep
  rw [addOverflowBounded_cast]
  · rw [mulLazy_cast]; rfl
  · norm_num [UInt64.size, negModulus, Goldilocks.fieldSize] at *
    omega

/-- Lazy leaves represent the same field value as canonical Horner evaluation. -/
theorem evalLazyRange_eq (p : Array Field) (x : Field) (lo hi : Nat) :
    evalLazyRange p x lo hi = CompPoly.CPolynomial.evalRange p x lo hi := by
  apply toField_injective
  unfold evalLazyRange CompPoly.CPolynomial.evalRange
  change ((reduceUInt64 (p.foldr (evalStep x) 0 hi lo)).val.toNat : Goldilocks.Field) = _
  rw [reduceUInt64_cast]
  rw [Array.foldr_eq_foldr_extract (start := hi) (stop := lo),
    Array.foldr_eq_foldr_extract (start := hi) (stop := lo)]
  rw [← Array.foldr_toList, ← Array.foldr_toList]
  generalize (p.extract lo hi).toList = as
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldr_cons, evalStep_cast, toField_add, toField_mul, ih]

instance : CompPoly.CPolynomial.EvalKernel Field where
  range := evalLazyRange
  range_eq := evalLazyRange_eq

end Goldilocks.Fast

namespace Montgomery.Native32.Eval

open Montgomery Montgomery.Native32
/-- Bounded redundant Montgomery multiply-add on native words. -/
@[inline] def step (p twice : UInt64) (ni : UInt32) (x a acc : UInt32) : UInt32 :=
  let product := acc.toUInt64 * x.toUInt64
  let m := (product.toUInt32 * ni).toUInt64
  let quotient := (product + m * p) >>> 32
  let sum := quotient + a.toUInt64
  (if sum < twice then sum else sum - p).toUInt32

/-- The native multiply-add agrees with its natural-number formula. -/
theorem step_nat (p twice : UInt64) (ni x a acc : UInt32)
    (hp : 0 < p.toNat) (hsmall : p.toNat < 2^31)
    (htwice : twice.toNat = 2 * p.toNat) (hx : x.toNat < p.toNat) (ha : a.toNat < p.toNat) :
    let u := reduceNatQuotient (2^32) p.toNat ni.toNat (acc.toNat * x.toNat)
    (step p twice ni x a acc).toNat = if u + a.toNat < 2 * p.toNat then
      u + a.toNat else u + a.toNat - p.toNat := by
  have hc : acc.toNat < 2^32 := acc.toNat_lt
  have hprod : acc.toNat * x.toNat < p.toNat * 2^32 := by
    have := Nat.mul_le_mul_left acc.toNat (Nat.le_of_lt hx)
    nlinarith
  have hp64 : acc.toNat * x.toNat < 2^64 := by nlinarith
  have he : (acc.toUInt64 * x.toUInt64).toNat = acc.toNat * x.toNat := by
    simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    exact Nat.mod_eq_of_lt hp64
  have hq := reduceQuotient_toNat (negInv := ni) (p64 := p)
    (x := acc.toUInt64 * x.toUInt64) hp hsmall (by rw [he]; exact hprod)
  rw [he] at hq
  have hu := reduceNatQuotient_lt_two_mul (2^32) p.toNat ni.toNat
    (acc.toNat * x.toNat) (by decide) hp hprod
  let product := acc.toUInt64 * x.toUInt64
  let quotient := (product + (product.toUInt32 * ni).toUInt64 * p) >>> 32
  have hqn : quotient.toNat = reduceNatQuotient (2^32) p.toNat ni.toNat
      (acc.toNat * x.toNat) := by
    have hb : quotient.toNat < 2^32 := by
      dsimp only [quotient]
      rw [UInt64.toNat_shiftRight]
      norm_num only [UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod, Nat.reducePow]
      have ht : (product + (product.toUInt32 * ni).toUInt64 * p).toNat < 18446744073709551616 :=
        UInt64.toNat_lt _
      omega
    change quotient.toNat % 2^32 = _ at hq
    rwa [Nat.mod_eq_of_lt hb] at hq
  have hs : (quotient + a.toUInt64).toNat = quotient.toNat + a.toNat := by
    rw [UInt64.toNat_add, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt]
    rw [hqn]
    omega
  unfold step
  change ((if quotient + a.toUInt64 < twice then
    quotient + a.toUInt64 else quotient + a.toUInt64 - p).toUInt32).toNat = _
  simp only [UInt64.lt_iff_toNat_lt, hs, hqn, htwice]
  split <;> rename_i h
  · rw [UInt64.toNat_toUInt32, hs, hqn, Nat.mod_eq_of_lt (by omega)]
  · rw [UInt64.toNat_toUInt32, UInt64.toNat_sub_of_le]
    · rw [hs, hqn, Nat.mod_eq_of_lt (by omega)]
    · rw [UInt64.le_iff_toNat_le, hs, hqn]; omega
end Montgomery.Native32.Eval

namespace KoalaBear.Fast

open Montgomery Montgomery.Native32

/-- One Horner step with the accumulator below twice the modulus. -/
@[inline]
def evalStep (x a : Field) (acc : UInt32) : UInt32 :=
  Montgomery.Native32.Eval.step 0x7f000001 0xfe000002 0x7effffff x.val a.val acc

private theorem step_nat (x a : Field) (acc : UInt32) :
    let u := reduceNatQuotient (2^32) fieldSize 0x7effffff (acc.toNat * x.val.toNat)
    (evalStep x a acc).toNat = if u + a.val.toNat < 2 * fieldSize then
      u + a.val.toNat else u + a.val.toNat - fieldSize := by
  have h := Montgomery.Native32.Eval.step_nat (0x7f000001 : UInt64) (0xfe000002 : UInt64)
    (0x7effffff : UInt32) x.val a.val acc (by decide) (by decide) (by decide)
    x.property a.property
  simpa only [Montgomery.Native32.Eval.step, evalStep, UInt64.reduceToNat, UInt32.reduceToNat,
    fieldSize, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd] using h

private theorem step_bound (x a : Field) (acc : UInt32) :
    (evalStep x a acc).toNat < 2 * fieldSize := by
  have hx := x.property
  have ha := a.property
  have hc : acc.toNat < 2^32 := acc.toNat_lt
  have hp : acc.toNat * x.val.toNat < fieldSize * 2^32 := by
    have := Nat.mul_le_mul_left acc.toNat (Nat.le_of_lt hx)
    norm_num [fieldSize] at *
    nlinarith
  have hu := reduceNatQuotient_lt_two_mul (2^32) fieldSize 0x7effffff
    (acc.toNat * x.val.toNat) (by decide) (by decide) hp
  rw [step_nat]
  split <;> omega

private theorem step_cast (x a : Field) (acc : UInt32) :
    ((evalStep x a acc).toNat : KoalaBear.Field) =
      (acc.toNat : KoalaBear.Field) * FastField.toField x + (a.val.toNat : KoalaBear.Field) := by
  rw [step_nat]
  have hcast := reduceNatQuotient_cast (2^32) fieldSize 0x7effffff
    (by decide) (by decide) Mont32Field.two_pow_32_ne_zero (acc.toNat * x.val.toNat)
  have he : ((if reduceNatQuotient (2^32) fieldSize 0x7effffff (acc.toNat * x.val.toNat) +
      a.val.toNat < 2 * fieldSize
      then reduceNatQuotient (2^32) fieldSize 0x7effffff (acc.toNat * x.val.toNat) + a.val.toNat
      else reduceNatQuotient (2^32) fieldSize 0x7effffff (acc.toNat * x.val.toNat) +
        a.val.toNat - fieldSize : Nat) : KoalaBear.Field) =
      (reduceNatQuotient (2^32) fieldSize 0x7effffff (acc.toNat * x.val.toNat) : KoalaBear.Field) +
        (a.val.toNat : KoalaBear.Field) := by
    split
    · exact Nat.cast_add _ _
    · rw [Nat.cast_sub (by omega), Nat.cast_add]
      simp only [ZMod.natCast_self, sub_zero]
  rw [he, hcast, Nat.cast_mul, Montgomery.Native32.toField_eq_val_toNat_cast_mul_inv]
  ring

private theorem fold_bound (p : Array Field) (x : Field) (lo hi : Nat) :
    (p.foldr (evalStep x) 0 hi lo).toNat < 2 * fieldSize := by
  rw [Array.foldr_eq_foldr_extract, ← Array.foldr_toList]
  generalize (p.extract lo hi).toList = as
  cases as with
  | nil => change (0 : UInt32).toNat < 2 * fieldSize; decide
  | cons a as => exact step_bound x a _

private theorem fold_cast (p : Array Field) (x : Field) (lo hi : Nat) :
    ((p.foldr (evalStep x) 0 hi lo).toNat : KoalaBear.Field) * ((2^32 : Nat) : KoalaBear.Field)⁻¹ =
      FastField.toField (CompPoly.CPolynomial.evalRange p x lo hi) := by
  unfold CompPoly.CPolynomial.evalRange
  rw [Array.foldr_eq_foldr_extract (start := hi) (stop := lo),
    Array.foldr_eq_foldr_extract (start := hi) (stop := lo),
    ← Array.foldr_toList, ← Array.foldr_toList]
  generalize (p.extract lo hi).toList = as
  induction as with
  | nil => simp only [List.foldr_nil, UInt32.toNat_zero, Nat.cast_zero, zero_mul,
      Montgomery.Native32.toField_zero]
  | cons a as ih =>
    simp only [List.foldr_cons, step_cast, Montgomery.Native32.toField_add,
      Montgomery.Native32.toField_mul]
    rw [add_mul, ← mul_right_comm, ih,
      Montgomery.Native32.toField_eq_val_toNat_cast_mul_inv (x := a)]

/-- Lazy KoalaBear leaf: one range correction per step and one final normalization. -/
@[inline]
def evalLazyRange (p : Array Field) (x : Field) (lo hi : Nat) : Field :=
  let acc := p.foldr (evalStep x) 0 hi lo
  let word := Montgomery.Native32.conditionalSubtract 0x7f000001 acc
  ⟨word, by
    apply Montgomery.Native32.conditionalSubtract_lt
    exact fold_bound p x lo hi⟩

/-- Lazy evaluation agrees with canonical Horner evaluation. -/
theorem evalLazyRange_eq (p : Array Field) (x : Field) (lo hi : Nat) :
    evalLazyRange p x lo hi = CompPoly.CPolynomial.evalRange p x lo hi := by
  apply Montgomery.Native32.toField_injective
  rw [Montgomery.Native32.toField_eq_val_toNat_cast_mul_inv]
  change ((Montgomery.Native32.conditionalSubtract (0x7f000001 : UInt32)
    (p.foldr (evalStep x) 0 hi lo)).toNat : KoalaBear.Field) * _ = _
  rw [Montgomery.Native32.conditionalSubtract_cast]
  exact fold_cast p x lo hi

instance : CompPoly.CPolynomial.EvalKernel Field where
  range := evalLazyRange
  range_eq := evalLazyRange_eq

end KoalaBear.Fast

namespace BN254.Fast

open Montgomery.Native64x4

/-- Four Montgomery rounds without final normalization. The point stays canonical. -/
@[inline]
def evalProduct (x : ScalarField) (acc : Limbs4) : Limbs4 :=
  (mulUnreduced instMont64x4Field.modulusLimbs
    instMont64x4Field.montgomeryNegInv x.val acc).toLimbs4

/-- The product is below `2p`; adding a canonical coefficient stays below `3p < 2^256`. -/
@[inline]
def evalStep (x a : ScalarField) (acc : Limbs4) : Limbs4 :=
  let (s0, s1, s2, s3, _) := addLimbs (evalProduct x acc) a.val
  ⟨s0, s1, s2, s3⟩

private theorem product_spec_raw (q : Limbs4) (ni : UInt64) (x acc : Limbs4)
    (hn : ni.toNat * q.toNat % 2^64 = 2^64-1) (hx : x.toNat < q.toNat)
    (hq : 2 * q.toNat < 2^256) :
    ((mulUnreduced q ni x acc).toLimbs4).toNat < 2 * q.toNat ∧
    2^256 * ((mulUnreduced q ni x acc).toLimbs4).toNat ≡ x.toNat * acc.toNat [MOD q.toNat] := by
  have h := mulUnreduced_spec q ni x acc hn hx
  let t := mulUnreduced q ni x acc
  have ht : t.t4.toNat = 0 := by
    have hb := h.1
    change t.toNat < 2 * q.toNat at hb
    unfold State5.toNat at hb
    omega
  have he : t.toNat = t.toLimbs4.toNat := by
    change t.toLimbs4.toNat + 2^256 * t.t4.toNat = t.toLimbs4.toNat
    rw [ht, Nat.mul_zero, Nat.add_zero]
  change t.toNat < 2 * q.toNat ∧ 2^256 * t.toNat ≡ x.toNat * acc.toNat [MOD q.toNat] at h
  rw [he] at h
  exact h

private theorem product_spec (x : ScalarField) (acc : Limbs4) :
    (evalProduct x acc).toNat < 2 * scalarFieldSize ∧
    2^256 * (evalProduct x acc).toNat ≡ x.val.toNat * acc.toNat [MOD scalarFieldSize] := by
  have h := product_spec_raw instMont64x4Field.modulusLimbs
    instMont64x4Field.montgomeryNegInv x.val acc Mont64x4Field.negInv_mul_q
    (by rw [Mont64x4Field.q_toNat]; exact x.property)
    (by rw [Mont64x4Field.q_toNat]; decide)
  simpa only [Mont64x4Field.q_toNat, evalProduct] using h

private theorem step_nat (x a : ScalarField) (acc : Limbs4) :
    (evalStep x a acc).toNat = (evalProduct x acc).toNat + a.val.toNat := by
  have hb := (product_spec x acc).1
  have ha := a.property
  have hsum : (evalProduct x acc).toNat + a.val.toNat < 2^256 := by
    have hq : 3 * scalarFieldSize < 2^256 := by decide
    omega
  obtain ⟨s0, s1, s2, s3, c, e, hc, h⟩ := addLimbs_spec (evalProduct x acc) a.val
  have hz : c.toNat = 0 := by omega
  simp only [evalStep, e]
  simpa only [hz, Nat.mul_zero, Nat.add_zero] using h
private theorem fold_bound (p : Array ScalarField) (x : ScalarField) (lo hi : Nat) :
    (p.foldr (evalStep x) Limbs4.zero hi lo).toNat < 3 * scalarFieldSize := by
  rw [Array.foldr_eq_foldr_extract, ← Array.foldr_toList]
  generalize (p.extract lo hi).toList = as
  cases as with
  | nil => change Limbs4.zero.toNat < 3 * scalarFieldSize; decide
  | cons a as =>
    simp only [List.foldr_cons, step_nat]
    have h := (product_spec x (as.foldr (evalStep x) Limbs4.zero)).1
    have ha := a.property
    omega

private theorem step_cast (x a : ScalarField) (acc : Limbs4) :
    ((evalStep x a acc).toNat : BN254.ScalarField) =
      (acc.toNat : BN254.ScalarField) * FastField.toField x +
        (a.val.toNat : BN254.ScalarField) := by
  have hc := (ZMod.natCast_eq_natCast_iff _ _ _).2 (product_spec x acc).2
  rw [Nat.cast_mul, Nat.cast_mul] at hc
  have hm : ((evalProduct x acc).toNat : BN254.ScalarField) =
      (x.val.toNat : BN254.ScalarField) * (acc.toNat : BN254.ScalarField) *
        ((2^256 : Nat) : BN254.ScalarField)⁻¹ := by
    rw [← hc, mul_comm ((2^256 : Nat) : BN254.ScalarField), mul_assoc,
      mul_inv_cancel₀ Mont64x4Field.r_ne_zero, mul_one]
  rw [step_nat, Nat.cast_add, hm, FastField.toField_eq]
  ring

private theorem fold_cast (p : Array ScalarField) (x : ScalarField) (lo hi : Nat) :
    ((p.foldr (evalStep x) Limbs4.zero hi lo).toNat : BN254.ScalarField) *
      ((2^256 : Nat) : BN254.ScalarField)⁻¹ =
      FastField.toField (CompPoly.CPolynomial.evalRange p x lo hi) := by
  unfold CompPoly.CPolynomial.evalRange
  rw [Array.foldr_eq_foldr_extract (start := hi) (stop := lo),
    Array.foldr_eq_foldr_extract (start := hi) (stop := lo),
    ← Array.foldr_toList, ← Array.foldr_toList]
  generalize (p.extract lo hi).toList = as
  induction as with
  | nil => simp only [List.foldr_nil, Limbs4.zero_toNat, Nat.cast_zero, zero_mul,
      FastField.toField_zero]
  | cons a as ih =>
    simp only [List.foldr_cons, step_cast, FastField.toField_add, FastField.toField_mul]
    rw [add_mul, ← mul_right_comm, ih, FastField.toField_eq a]

private theorem normalize_bound (acc : Limbs4) (h : acc.toNat < 3 * scalarFieldSize) :
    (condSub instMont64x4Field.modulusLimbs
      (condSub instMont64x4Field.modulusLimbs acc)).toNat < scalarFieldSize := by
  apply condSub_lt
  rw [condSub_toNat, Mont64x4Field.q_toNat]
  split <;> omega

private theorem condSub_cast_bn (t : Limbs4) :
    ((condSub instMont64x4Field.modulusLimbs t).toNat : BN254.ScalarField) =
      (t.toNat : BN254.ScalarField) := by
  rw [condSub_toNat, Mont64x4Field.q_toNat]
  split
  · rfl
  · rw [Nat.cast_sub (by omega)]
    simp only [ZMod.natCast_self, sub_zero]

private theorem pred_toNat (i stop : USize) (h : stop < i) :
    (i - 1).toNat = i.toNat - 1 := by
  have hh : (1 : USize) ≤ i := by
    rw [USize.le_iff_toNat_le]
    have := USize.lt_iff_toNat_lt.mp h
    simp only [USize.toNat_one]
    omega
  rw [USize.toNat_sub_of_le _ _ hh, USize.toNat_one]

/-- Horner loop with machine-word indices and scalar accumulator arguments.
Keep the modulus as parameters and this function out of line: embedding constant modulus
limbs prevents clang from recognizing some widening products in the Montgomery reduction. -/
@[noinline]
def evalScalarLoop (q : Limbs4) (ni : UInt64) (p : Array ScalarField) (x : ScalarField)
    (stop : USize)
    (i : USize) (hi : i.toNat ≤ p.size) (a0 a1 a2 a3 : UInt64) : Limbs4 :=
  if h : stop < i then
    let j := i - 1
    let a := p.uget j (by
      dsimp only [j]
      rw [pred_toNat i stop h]
      have := USize.lt_iff_toNat_lt.mp h
      omega)
    let (r0, r1, r2, r3, _) :=
      addLimbs (mulUnreduced q ni x.val ⟨a0, a1, a2, a3⟩).toLimbs4 a.val
    let r : Limbs4 := ⟨r0, r1, r2, r3⟩
    evalScalarLoop q ni p x stop j (by
      dsimp only [j]
      rw [pred_toNat i stop h]
      omega) r.l0 r.l1 r.l2 r.l3
  else ⟨a0, a1, a2, a3⟩
termination_by i.toNat
decreasing_by
  rw [pred_toNat i stop h]
  have := USize.lt_iff_toNat_lt.mp h
  omega

/-- Use native indices when the range fits a machine word. -/
@[inline]
def evalScalarRange (p : Array ScalarField) (x : ScalarField) (lo hi : Nat) : Limbs4 :=
  let start := min hi p.size
  if lo < start then
    if h : start < USize.size then
      evalScalarLoop instMont64x4Field.modulusLimbs instMont64x4Field.montgomeryNegInv
        p x lo.toUSize start.toUSize (by
          rw [Nat.toUSize, USize.toNat_ofNat', Nat.mod_eq_of_lt h]
          exact Nat.min_le_right _ _) 0 0 0 0
    else p.foldr (evalStep x) Limbs4.zero hi lo
  else Limbs4.zero

private theorem fold_step (p : Array ScalarField) (x : ScalarField) (stop n : Nat)
    (hi : n ≤ p.size) (h : stop < n) (b : Limbs4) :
    Array.foldrM.fold (m := Id) (fun a b ↦ evalStep x a b) p stop n hi b =
      Array.foldrM.fold (m := Id) (fun a b ↦ evalStep x a b) p stop (n - 1) (by omega)
        (evalStep x p[n - 1] b) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [Array.foldrM.fold.eq_def]
    simp only [beq_iff_eq, ne_of_gt h, ↓reduceIte]
    rfl

private theorem loop_eq (p : Array ScalarField) (x : ScalarField) (stop i : USize)
    (hi : i.toNat ≤ p.size) (hs : stop.toNat ≤ i.toNat) (a0 a1 a2 a3 : UInt64) :
    evalScalarLoop instMont64x4Field.modulusLimbs instMont64x4Field.montgomeryNegInv
      p x stop i hi a0 a1 a2 a3 =
    Array.foldrM.fold (m := Id) (fun a b ↦ evalStep x a b) p stop.toNat i.toNat hi
      ⟨a0, a1, a2, a3⟩ := by
  rw [evalScalarLoop.eq_def]
  split
  · rename_i h
    have hn := USize.lt_iff_toNat_lt.mp h
    have hp := pred_toNat i stop h
    rw [fold_step p x stop.toNat i.toNat hi hn]
    dsimp only
    rw [loop_eq p x stop (i - 1) _ (by omega)]
    simp only [Array.uget, hp, evalStep, evalProduct]
  · rename_i h
    have hn : i.toNat ≤ stop.toNat := by
      rw [USize.lt_iff_toNat_lt] at h
      omega
    have he : i.toNat = stop.toNat := by omega
    rw [Array.foldrM.fold.eq_def]
    simp only [beq_iff_eq, he, ↓reduceIte, pure]
termination_by i.toNat
decreasing_by omega
private theorem evalScalarRange_eq (p : Array ScalarField) (x : ScalarField) (lo hi : Nat) :
    evalScalarRange p x lo hi = p.foldr (evalStep x) Limbs4.zero hi lo := by
  unfold evalScalarRange
  dsimp only
  split
  · rename_i hlt
    split
    · rename_i hword
      rw [loop_eq _ _ _ _ _ (by
        simp only [Nat.toUSize, USize.toNat_ofNat']
        simp only [Nat.mod_eq_of_lt hword, Nat.mod_eq_of_lt (lt_trans hlt hword)]
        omega)]
      simp only [Nat.toUSize, USize.toNat_ofNat']
      simp only [Nat.mod_eq_of_lt hword, Nat.mod_eq_of_lt (lt_trans hlt hword)]
      unfold Array.foldr Array.foldrM
      split
      · rename_i hsize
        simp only [Nat.min_eq_left hsize] at hlt ⊢
        simp only [hlt, ↓reduceIte]
        rfl
      · rename_i hsize
        simp only [Nat.min_eq_right (by omega : p.size ≤ hi)] at hlt ⊢
        simp only [hlt, ↓reduceIte]
        rfl
    · rfl
  · rename_i hlt
    unfold Array.foldr Array.foldrM
    split
    · rename_i hsize
      simp only [Nat.min_eq_left hsize] at hlt
      simp only [hlt, ↓reduceIte]
      rfl
    · rename_i hsize
      simp only [Nat.min_eq_right (by omega : p.size ≤ hi)] at hlt
      simp only [hlt, ↓reduceIte]
      rfl

/-- Normalize only at the leaf boundary, using at most two subtractions. -/
@[inline]
def evalLazyRange (p : Array ScalarField) (x : ScalarField) (lo hi : Nat) : ScalarField :=
  let acc := evalScalarRange p x lo hi
  let q := instMont64x4Field.modulusLimbs
  ⟨condSub q (condSub q acc), by exact normalize_bound acc (by
      dsimp only [acc]
      rw [evalScalarRange_eq]
      exact fold_bound p x lo hi)⟩

/-- Lazy evaluation agrees with canonical Horner evaluation. -/
theorem evalLazyRange_eq (p : Array ScalarField) (x : ScalarField) (lo hi : Nat) :
    evalLazyRange p x lo hi = CompPoly.CPolynomial.evalRange p x lo hi := by
  apply FastField.toField_injective
  rw [FastField.toField_eq]
  simp only [evalLazyRange, evalScalarRange_eq]
  change ((condSub instMont64x4Field.modulusLimbs
    (condSub instMont64x4Field.modulusLimbs (p.foldr (evalStep x) Limbs4.zero hi lo))).toNat :
      BN254.ScalarField) * _ = _
  rw [condSub_cast_bn, condSub_cast_bn]
  exact fold_cast p x lo hi

instance : CompPoly.CPolynomial.EvalKernel ScalarField where
  range := evalLazyRange
  range_eq := evalLazyRange_eq
  -- A BN254 multiplication costs about ten small-field ones, so smaller leaves pay off.
  minLeaf := 1024

end BN254.Fast
