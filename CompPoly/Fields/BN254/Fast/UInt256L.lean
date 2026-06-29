/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
import CompPoly.Fields.BN254.Fast.Limb
import CompPoly.Fields.BN254.Fast.UInt128L

namespace BN254.Fast
structure UInt256L where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64
deriving DecidableEq

def UInt256L.toNat (x : UInt256L) : Nat :=
  x.l0.toNat + (x.l1.toNat <<< 64) + (x.l2.toNat <<< 128) + (x.l3.toNat <<< 192)

@[inline] def UInt256L.addCarry (a b : UInt256L) (cin : UInt64) : UInt256L :=
  let (l0, c0) := addc a.l0 b.l0 cin
  let (l1, c1) := addc a.l1 b.l1 c0
  let (l2, c2) := addc a.l2 b.l2 c1
  let (l3, _ ) := addc a.l3 b.l3 c2
  ⟨l0, l1, l2, l3⟩

def UInt256L.add a b := UInt256L.addCarry a b 0

-- @[inline] def UInt256L.add (a b : UInt256L) : UInt256L :=
--   let (l0, c0) := addc a.l0 b.l0 0
--   let (l1, c1) := addc a.l1 b.l1 c0
--   let (l2, c2) := addc a.l2 b.l2 c1
--   let (l3, _) := addc a.l3 b.l3 c2
--   ⟨ l0, l1, l2, l3 ⟩

/-- One limb of subtract-with-borrow: `(dᵢ, borrow')`, with `borrow' ∈ {0,1}` when `borrow ∈ {0,1}`. -/
@[inline] def subb (a b borrow : UInt64) : UInt64 × UInt64 :=
  let s1 := a - b
  let b1 := if a < b then 1 else 0
  let s2 := s1 - borrow
  let b2 := if s1 < borrow then 1 else 0
  (s2, b1 + b2)

@[inline] def UInt256L.sub (a b : UInt256L) : UInt256L :=
  let (l0, brw0) := subb a.l0 b.l0 0
  let (l1, brw1) := subb a.l1 b.l1 brw0
  let (l2, brw2) := subb a.l2 b.l2 brw1
  let (l3, _) := subb a.l3 b.l3 brw2
  ⟨ l0, l1, l2, l3 ⟩


/-- Full 64×64→128 product as UInt128L. -/
@[inline] def mulLimb (a b : UInt64) : UInt128L :=
  let mask : UInt64 := 0xFFFFFFFF
  let aL := a &&& mask
  let aH := a >>> 32
  let bL := b &&& mask
  let bH := b >>> 32
  let ll := aL * bL
  let lh := aL * bH
  let hl := aH * bL
  let hh := aH * bH
  let cross := (ll >>> 32) + (lh &&& mask) + (hl &&& mask)
  let lo := (ll &&& mask) ||| (cross <<< 32)
  let hi := hh + (lh >>> 32) + (hl >>> 32) + (cross >>> 32)
  ⟨ lo, hi ⟩

/-- `lhs · rhs` with `lhs < 2^256`, `rhs < 2^64`. Returns the lowest limb and the
remaining four limbs of the 5-limb product. -/
@[inline] def mulSmall (lhs : UInt256L) (rhs : UInt64) : UInt64 × UInt256L :=
  let p0 : UInt128L := mulLimb lhs.l0 rhs
  let c0 : UInt128L := ⟨ p0.hi, 0 ⟩
  let p1 : UInt128L := c0 + (mulLimb lhs.l1 rhs)
  let c1 : UInt128L := ⟨p1.hi, 0 ⟩
  let p2 : UInt128L := c1 + (mulLimb lhs.l2 rhs)
  let c2 : UInt128L := ⟨ p2.hi, 0 ⟩
  let p3 : UInt128L := c2 + (mulLimb lhs.l3 rhs)
  (p0.lo, ⟨ p1.lo, p2.lo, p3.lo, p3.hi ⟩)


@[inline] def mulSmallAndAcc (lhs : UInt256L) (rhs: UInt64) (add : UInt256L) : UInt64 × UInt256L :=
  let p0 : UInt128L := ⟨add.l0, 0 ⟩  +  (mulLimb lhs.l0 rhs)
  let c0 : UInt128L := ⟨ p0.hi, 0 ⟩
  let p1 : UInt128L := c0 + (mulLimb lhs.l1 rhs) + ⟨ add.l1, 0 ⟩
  let c1 : UInt128L := ⟨p1.hi, 0 ⟩
  let p2 : UInt128L := c1 + (mulLimb lhs.l2 rhs) + ⟨ add.l2, 0 ⟩
  let c2 : UInt128L := ⟨ p2.hi, 0 ⟩
  let p3 : UInt128L := c2 + (mulLimb lhs.l3 rhs) + ⟨ add.l3, 0 ⟩
  (p0.lo, ⟨ p1.lo, p2.lo, p3.lo, p3.hi ⟩)




@[inline] def UInt256L.cmp (a b : UInt256L) : Ordering :=
  if a.l3 ≠ b.l3 then compare a.l3 b.l3
  else if a.l2 ≠ b.l2 then compare a.l2 b.l2
  else if a.l1 ≠ b.l1 then compare a.l1 b.l1
  else compare a.l0 b.l0


instance : Ord UInt256L where
  compare := UInt256L.cmp

instance : Add UInt256L := ⟨UInt256L.add⟩

instance : Sub UInt256L := ⟨UInt256L.sub⟩

instance : LT UInt256L := ⟨fun a b => compare a b = Ordering.lt⟩

instance (a b : UInt256L) : Decidable (a < b) :=
  inferInstanceAs (Decidable (compare a b = Ordering.lt))

instance : Zero UInt256L := ⟨⟨0, 0, 0, 0⟩⟩

instance : LE UInt256L := ⟨fun a b => ¬ b < a⟩

instance (a b : UInt256L) : Decidable (a ≤ b) := inferInstanceAs (Decidable (¬ b < a))

/-- The limb-wise lexicographic `<` agrees with the numeric order on `toNat`. -/
theorem UInt256L.lt_iff_toNat_lt {a b : UInt256L} : a < b ↔ a.toNat < b.toNat := by
  have key : ∀ x y : UInt64, (compare x y = Ordering.lt) ↔ (x.toNat < y.toNat) := by
    intro x y
    rw [show compare x y = compareOfLessAndEq x y from rfl, compareOfLessAndEq_eq_lt,
        UInt64.lt_iff_toNat_lt]
  have h0a := UInt64.toNat_lt a.l0; have h1a := UInt64.toNat_lt a.l1
  have h2a := UInt64.toNat_lt a.l2; have h3a := UInt64.toNat_lt a.l3
  have h0b := UInt64.toNat_lt b.l0; have h1b := UInt64.toNat_lt b.l1
  have h2b := UInt64.toNat_lt b.l2; have h3b := UInt64.toNat_lt b.l3
  show cmp a b = Ordering.lt ↔ a.toNat < b.toNat
  simp only [UInt256L.toNat, Nat.shiftLeft_eq]
  unfold cmp
  by_cases h3 : a.l3 = b.l3
  · rw [if_neg (fun h => h h3)]
    by_cases h2 : a.l2 = b.l2
    · rw [if_neg (fun h => h h2)]
      by_cases h1 : a.l1 = b.l1
      · rw [if_neg (fun h => h h1), key]
        have e3 := congrArg UInt64.toNat h3
        have e2 := congrArg UInt64.toNat h2
        have e1 := congrArg UInt64.toNat h1
        omega
      · rw [if_pos h1, key]
        have e3 := congrArg UInt64.toNat h3
        have e2 := congrArg UInt64.toNat h2
        have n1 : a.l1.toNat ≠ b.l1.toNat := fun h => h1 (UInt64.toNat_inj.mp h)
        omega
    · rw [if_pos h2, key]
      have e3 := congrArg UInt64.toNat h3
      have n2 : a.l2.toNat ≠ b.l2.toNat := fun h => h2 (UInt64.toNat_inj.mp h)
      omega
  · rw [if_pos h3, key]
    have n3 : a.l3.toNat ≠ b.l3.toNat := fun h => h3 (UInt64.toNat_inj.mp h)
    omega

/-- The numeric value of the zero limb word is `0`. -/
@[simp] theorem UInt256L.toNat_zero : (0 : UInt256L).toNat = 0 := by decide

/-- The limb-wise `≤` agrees with the numeric order on `toNat`. -/
theorem UInt256L.le_iff_toNat_le {a b : UInt256L} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  show ¬ b < a ↔ a.toNat ≤ b.toNat
  rw [UInt256L.lt_iff_toNat_lt]
  omega

/-- `toNat` is injective: two limb words with the same numeric value are equal. -/
theorem UInt256L.toNat_inj {a b : UInt256L} : a.toNat = b.toNat ↔ a = b := by
  constructor
  · intro h
    obtain ⟨a0, a1, a2, a3⟩ := a
    obtain ⟨b0, b1, b2, b3⟩ := b
    have ka0 := UInt64.toNat_lt a0; have ka1 := UInt64.toNat_lt a1
    have ka2 := UInt64.toNat_lt a2; have ka3 := UInt64.toNat_lt a3
    have kb0 := UInt64.toNat_lt b0; have kb1 := UInt64.toNat_lt b1
    have kb2 := UInt64.toNat_lt b2; have kb3 := UInt64.toNat_lt b3
    simp only [UInt256L.toNat, Nat.shiftLeft_eq] at h
    simp only [UInt256L.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply UInt64.toNat_inj.mp; omega)
  · intro h; rw [h]


/-- The ripple-carry add-with-carry agrees with `Nat` addition modulo `2 ^ 256`, given a
single-bit carry-in. The numeric contract for `UInt256L.addCarry`. -/
theorem UInt256L.toNat_addCarry (a b : UInt256L) (cin : UInt64) (hcin : cin.toNat ≤ 1) :
    (UInt256L.addCarry a b cin).toNat = (a.toNat + b.toNat + cin.toNat) % 2 ^ 256 := by
  unfold UInt256L.addCarry
  dsimp only
  -- Each limb's carry-out (`c·`) feeds the next limb's carry-in; `addc_spec` also
  -- supplies the result-limb bound (`hb·`), so the chain closes by `omega`.
  obtain ⟨e0, c0, hb0⟩ := addc_spec a.l0 b.l0 cin hcin
  obtain ⟨e1, c1, hb1⟩ := addc_spec a.l1 b.l1 (addc a.l0 b.l0 cin).2 c0
  obtain ⟨e2, c2, hb2⟩ := addc_spec a.l2 b.l2 (addc a.l1 b.l1 (addc a.l0 b.l0 cin).2).2 c1
  obtain ⟨e3, c3, hb3⟩ := addc_spec a.l3 b.l3
    (addc a.l2 b.l2 (addc a.l1 b.l1 (addc a.l0 b.l0 cin).2).2).2 c2
  simp only [UInt256L.toNat, Nat.shiftLeft_eq]
  omega

/-- The ripple-carry addition agrees with `Nat` addition modulo `2 ^ 256` (the numeric
analogue of `UInt64.toNat_add` for the 256-bit limb type). -/
theorem UInt256L.toNat_add (a b : UInt256L) :
    (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 256 := by
  show (UInt256L.add a b).toNat = _
  unfold UInt256L.add
  rw [UInt256L.toNat_addCarry a b 0 (by decide), show (0 : UInt64).toNat = 0 from rfl,
      Nat.add_zero]

/-- Wrapping subtraction on `UInt64`, as a `Nat` formula. -/
theorem u64_toNat_sub (a b : UInt64) :
    (a - b).toNat = (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 := by
  show (a.toBitVec - b.toBitVec).toNat = _
  rw [BitVec.toNat_sub]
  rfl

/-- One limb of subtract-with-borrow is correct: the low word plus what was subtracted
recovers the input plus the borrow-out times the base, and the borrow-out is a single bit
(given a single-bit borrow-in). -/
theorem subb_spec (a b borrow : UInt64) (hbor : borrow.toNat ≤ 1) :
    (subb a b borrow).1.toNat + b.toNat + borrow.toNat
      = a.toNat + (subb a b borrow).2.toNat * 2 ^ 64
    ∧ (subb a b borrow).2.toNat ≤ 1
    ∧ (subb a b borrow).1.toNat < 2 ^ 64 := by
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have l11 : ((1 : UInt64) + 1).toNat = 2 := by decide
  have l10 : ((1 : UInt64) + 0).toNat = 1 := by decide
  have l01 : ((0 : UInt64) + 1).toNat = 1 := by decide
  have l00 : ((0 : UInt64) + 0).toNat = 0 := by decide
  unfold subb
  dsimp only
  by_cases hab : a < b
  · by_cases hsb : a - b < borrow
    · simp only [if_pos hab, if_pos hsb, l11]
      rw [UInt64.lt_iff_toNat_lt] at hab hsb
      simp only [u64_toNat_sub] at hsb ⊢; omega
    · simp only [if_pos hab, if_neg hsb, l10]
      rw [UInt64.lt_iff_toNat_lt] at hab hsb
      simp only [u64_toNat_sub] at hsb ⊢; omega
  · by_cases hsb : a - b < borrow
    · simp only [if_neg hab, if_pos hsb, l01]
      rw [UInt64.lt_iff_toNat_lt] at hab hsb
      simp only [u64_toNat_sub] at hsb ⊢; omega
    · simp only [if_neg hab, if_neg hsb, l00]
      rw [UInt64.lt_iff_toNat_lt] at hab hsb
      simp only [u64_toNat_sub] at hsb ⊢; omega

/-- The ripple-borrow subtraction agrees with `Nat` subtraction when `b ≤ a` (no underflow).
The numeric analogue of `UInt64.toNat_sub_of_le` for the 256-bit limb type. -/
theorem UInt256L.toNat_sub_of_le {a b : UInt256L} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  show (sub a b).toNat = _
  unfold sub
  dsimp only
  -- Each limb's borrow-out (`c·`) feeds the next limb's borrow-in; `subb_spec` also
  -- supplies the result-limb bound (`hb·`), so the chain closes by `omega`.
  obtain ⟨e0, c0, hb0⟩ := subb_spec a.l0 b.l0 0 (by decide)
  obtain ⟨e1, c1, hb1⟩ := subb_spec a.l1 b.l1 (subb a.l0 b.l0 0).2 c0
  obtain ⟨e2, c2, hb2⟩ := subb_spec a.l2 b.l2 (subb a.l1 b.l1 (subb a.l0 b.l0 0).2).2 c1
  obtain ⟨e3, c3, hb3⟩ := subb_spec a.l3 b.l3
    (subb a.l2 b.l2 (subb a.l1 b.l1 (subb a.l0 b.l0 0).2).2).2 c2
  have hz : (0 : UInt64).toNat = 0 := rfl
  simp only [UInt256L.toNat, Nat.shiftLeft_eq] at h ⊢
  omega


end BN254.Fast
