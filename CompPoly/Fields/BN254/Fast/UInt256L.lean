/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
import CompPoly.Fields.BN254.Fast.Limb
import CompPoly.Fields.BN254.Fast.UInt128L
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# 256-bit limb word (`UInt256L`)

The four-`UInt64`-limb word backing the BN254 fast scalar field: ripple-carry add/subtract,
limb-wise comparison, the 64×64→128 product `mulLimb`, the scan-multiply helpers `mulSmall`
and `mulSmallAndAcc`, and their exact `Nat` correctness contracts.
-/

-- The schoolbook multiply proofs build deep `addc`/`mulLimb` carry chains; the default
-- elaborator recursion limit is too low for them.
set_option maxRecDepth 4000

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

/-- One limb of subtract-with-borrow: `(dᵢ, borrow')`, single-bit `borrow'` given single-bit
`borrow`. -/
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


/-- Commutativity of `Nat` bitwise-or (used to orient the `|||`→`+` rewrite in `mulLimb`). -/
private theorem lor_comm (x y : Nat) : x ||| y = y ||| x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_or, Bool.or_comm]

/-- The low word `(ll &&& mask) ||| (cross <<< 32)` of `mulLimb` is a disjoint-or, hence a
sum: the low half (`e % 2^32`) and the shifted high half do not share bits. -/
private theorem or_split (c e : Nat) :
    (e % 2 ^ 32 ||| c * 2 ^ 32 % 2 ^ 64) = e % 2 ^ 32 + c % 2 ^ 32 * 2 ^ 32 := by
  have hd : e % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hq : c * 2 ^ 32 % 2 ^ 64 = 2 ^ 32 * (c % 2 ^ 32) := by
    conv_lhs => rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from by decide, Nat.mul_comm c (2 ^ 32)]
    rw [Nat.mul_mod_mul_left]
  rw [hq, lor_comm, ← Nat.two_pow_add_eq_or_of_lt hd]
  omega

/-- The 64×64→128 widening product is exact: `(mulLimb a b).toNat = a.toNat * b.toNat`. -/
theorem mulLimb_toNat (a b : UInt64) :
    (mulLimb a b).toNat = a.toNat * b.toNat := by
  have ha : a.toNat < 2 ^ 64 := a.toNat_lt
  have hb : b.toNat < 2 ^ 64 := b.toNat_lt
  have h_and : ∀ x : UInt64, (x &&& 0xFFFFFFFF).toNat = x.toNat % 2 ^ 32 := by
    intro x
    rw [UInt64.toNat_and, show ((0xFFFFFFFF : UInt64).toNat) = 2 ^ 32 - 1 from by decide,
        Nat.and_two_pow_sub_one_eq_mod]
  have h_shr : ∀ x : UInt64, (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
    intro x
    rw [UInt64.toNat_shiftRight, show ((32 : UInt64).toNat % 64) = 32 from by decide,
        Nat.shiftRight_eq_div_pow]
  have tbound : ∀ u v : Nat, u < 2 ^ 32 → v < 2 ^ 32 → u * v ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    fun u v hu hv => Nat.mul_le_mul (by omega) (by omega)
  have hbound2 : ∀ u v : Nat, u < 2 ^ 32 → v < 2 ^ 32 → u * v < 2 ^ 64 :=
    fun u v hu hv => lt_of_le_of_lt (tbound u v hu hv) (by decide)
  have hexp : a.toNat * b.toNat =
      a.toNat / 2 ^ 32 * (b.toNat / 2 ^ 32) * 2 ^ 64
      + a.toNat / 2 ^ 32 * (b.toNat % 2 ^ 32) * 2 ^ 32
      + a.toNat % 2 ^ 32 * (b.toNat / 2 ^ 32) * 2 ^ 32
      + a.toNat % 2 ^ 32 * (b.toNat % 2 ^ 32) := by
    set ah := a.toNat / 2 ^ 32 with hah
    set al := a.toNat % 2 ^ 32 with hal
    set bh := b.toNat / 2 ^ 32 with hbh
    set bl := b.toNat % 2 ^ 32 with hbl
    have ea : a.toNat = ah * 2 ^ 32 + al := by rw [hah, hal]; omega
    have eb : b.toNat = bh * 2 ^ 32 + bl := by rw [hbh, hbl]; omega
    rw [ea, eb]; ring
  have hAl : a.toNat % 2 ^ 32 < 2 ^ 32 := by omega
  have hAh : a.toNat / 2 ^ 32 < 2 ^ 32 := by omega
  have hBl : b.toNat % 2 ^ 32 < 2 ^ 32 := by omega
  have hBh : b.toNat / 2 ^ 32 < 2 ^ 32 := by omega
  have hb_ll := hbound2 _ _ hAl hBl
  have hb_lh := hbound2 _ _ hAl hBh
  have hb_hl := hbound2 _ _ hAh hBl
  have hb_hh := hbound2 _ _ hAh hBh
  have ht_ll := tbound _ _ hAl hBl
  have ht_lh := tbound _ _ hAl hBh
  have ht_hl := tbound _ _ hAh hBl
  have ht_hh := tbound _ _ hAh hBh
  simp only [UInt128L.toNat, mulLimb, h_and, h_shr, UInt64.toNat_or, UInt64.toNat_mul,
    UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt hb_ll, Nat.mod_eq_of_lt hb_lh,
    Nat.mod_eq_of_lt hb_hl, Nat.mod_eq_of_lt hb_hh]
  rw [or_split]
  set LL := a.toNat % 2 ^ 32 * (b.toNat % 2 ^ 32)
  set LH := a.toNat % 2 ^ 32 * (b.toNat / 2 ^ 32)
  set HL := a.toNat / 2 ^ 32 * (b.toNat % 2 ^ 32)
  set HH := a.toNat / 2 ^ 32 * (b.toNat / 2 ^ 32)
  omega

/-- `mulSmall lhs rhs` returns the low limb and the top four limbs of the exact 5-limb
product `lhs.toNat * rhs.toNat`. -/
theorem mulSmall_toNat (lhs : UInt256L) (rhs : UInt64) :
    (mulSmall lhs rhs).1.toNat + (mulSmall lhs rhs).2.toNat * 2 ^ 64
      = lhs.toNat * rhs.toNat := by
  have hexp : lhs.toNat * rhs.toNat =
      lhs.l0.toNat * rhs.toNat + lhs.l1.toNat * rhs.toNat * 2 ^ 64
      + lhs.l2.toNat * rhs.toNat * 2 ^ 128 + lhs.l3.toNat * rhs.toNat * 2 ^ 192 := by
    simp only [UInt256L.toNat, Nat.shiftLeft_eq]; ring
  have tb : ∀ x : UInt64, x.toNat * rhs.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    fun x => Nat.mul_le_mul (by have := x.toNat_lt; omega) (by have := rhs.toNat_lt; omega)
  simp only [mulSmall]
  set Q0 := mulLimb lhs.l0 rhs with hQ0def
  set Q1 := (⟨Q0.hi, 0⟩ : UInt128L) + mulLimb lhs.l1 rhs with hQ1def
  set Q2 := (⟨Q1.hi, 0⟩ : UInt128L) + mulLimb lhs.l2 rhs with hQ2def
  set Q3 := (⟨Q2.hi, 0⟩ : UInt128L) + mulLimb lhs.l3 rhs with hQ3def
  clear_value Q3 Q2 Q1 Q0
  have hQ0 : Q0.lo.toNat + Q0.hi.toNat * 2 ^ 64 = lhs.l0.toNat * rhs.toNat := by
    have h := mulLimb_toNat lhs.l0 rhs; rw [← hQ0def] at h
    simpa [UInt128L.toNat, Nat.shiftLeft_eq] using h
  have hQ1 : Q1.lo.toNat + Q1.hi.toNat * 2 ^ 64
      = Q0.hi.toNat + lhs.l1.toNat * rhs.toNat := by
    have hb : Q0.hi.toNat + lhs.l1.toNat * rhs.toNat < 2 ^ 128 := by
      have := Q0.hi.toNat_lt; have := tb lhs.l1; omega
    have h := UInt128L.toNat_add (⟨Q0.hi, 0⟩ : UInt128L) (mulLimb lhs.l1 rhs)
    rw [← hQ1def, mulLimb_toNat] at h
    simp only [UInt128L.toNat, Nat.shiftLeft_eq, show (0 : UInt64).toNat = 0 from rfl,
      Nat.zero_mul, Nat.add_zero] at h
    rw [Nat.mod_eq_of_lt hb] at h; exact h
  have hQ2 : Q2.lo.toNat + Q2.hi.toNat * 2 ^ 64
      = Q1.hi.toNat + lhs.l2.toNat * rhs.toNat := by
    have hb : Q1.hi.toNat + lhs.l2.toNat * rhs.toNat < 2 ^ 128 := by
      have := Q1.hi.toNat_lt; have := tb lhs.l2; omega
    have h := UInt128L.toNat_add (⟨Q1.hi, 0⟩ : UInt128L) (mulLimb lhs.l2 rhs)
    rw [← hQ2def, mulLimb_toNat] at h
    simp only [UInt128L.toNat, Nat.shiftLeft_eq, show (0 : UInt64).toNat = 0 from rfl,
      Nat.zero_mul, Nat.add_zero] at h
    rw [Nat.mod_eq_of_lt hb] at h; exact h
  have hQ3 : Q3.lo.toNat + Q3.hi.toNat * 2 ^ 64
      = Q2.hi.toNat + lhs.l3.toNat * rhs.toNat := by
    have hb : Q2.hi.toNat + lhs.l3.toNat * rhs.toNat < 2 ^ 128 := by
      have := Q2.hi.toNat_lt; have := tb lhs.l3; omega
    have h := UInt128L.toNat_add (⟨Q2.hi, 0⟩ : UInt128L) (mulLimb lhs.l3 rhs)
    rw [← hQ3def, mulLimb_toNat] at h
    simp only [UInt128L.toNat, Nat.shiftLeft_eq, show (0 : UInt64).toNat = 0 from rfl,
      Nat.zero_mul, Nat.add_zero] at h
    rw [Nat.mod_eq_of_lt hb] at h; exact h
  rw [hexp]
  simp only [UInt256L.toNat, Nat.shiftLeft_eq]
  linarith [hQ0, hQ1, hQ2, hQ3]

/-- `mulSmallAndAcc lhs rhs add` computes the exact fused multiply-accumulate
`lhs.toNat * rhs.toNat + add.toNat` as a 5-limb value. -/
theorem mulSmallAndAcc_toNat (lhs : UInt256L) (rhs : UInt64) (add : UInt256L) :
    (mulSmallAndAcc lhs rhs add).1.toNat + (mulSmallAndAcc lhs rhs add).2.toNat * 2 ^ 64
      = lhs.toNat * rhs.toNat + add.toNat := by
  have hexp : lhs.toNat * rhs.toNat + add.toNat =
      (add.l0.toNat + lhs.l0.toNat * rhs.toNat)
      + (add.l1.toNat + lhs.l1.toNat * rhs.toNat) * 2 ^ 64
      + (add.l2.toNat + lhs.l2.toNat * rhs.toNat) * 2 ^ 128
      + (add.l3.toNat + lhs.l3.toNat * rhs.toNat) * 2 ^ 192 := by
    simp only [UInt256L.toNat, Nat.shiftLeft_eq]; ring
  have tb : ∀ x : UInt64, x.toNat * rhs.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    fun x => Nat.mul_le_mul (by have := x.toNat_lt; omega) (by have := rhs.toNat_lt; omega)
  simp only [mulSmallAndAcc]
  set Q0 := (⟨add.l0, 0⟩ : UInt128L) + mulLimb lhs.l0 rhs with hQ0def
  set Q1 := (⟨Q0.hi, 0⟩ : UInt128L) + mulLimb lhs.l1 rhs + ⟨add.l1, 0⟩ with hQ1def
  set Q2 := (⟨Q1.hi, 0⟩ : UInt128L) + mulLimb lhs.l2 rhs + ⟨add.l2, 0⟩ with hQ2def
  set Q3 := (⟨Q2.hi, 0⟩ : UInt128L) + mulLimb lhs.l3 rhs + ⟨add.l3, 0⟩ with hQ3def
  clear_value Q3 Q2 Q1 Q0
  have hQ0 : Q0.lo.toNat + Q0.hi.toNat * 2 ^ 64 = add.l0.toNat + lhs.l0.toNat * rhs.toNat := by
    have hb : add.l0.toNat + lhs.l0.toNat * rhs.toNat < 2 ^ 128 := by
      have := add.l0.toNat_lt; have := tb lhs.l0; omega
    have h := UInt128L.toNat_add (⟨add.l0, 0⟩ : UInt128L) (mulLimb lhs.l0 rhs)
    rw [← hQ0def, mulLimb_toNat] at h
    simp only [UInt128L.toNat, Nat.shiftLeft_eq, show (0 : UInt64).toNat = 0 from rfl,
      Nat.zero_mul, Nat.add_zero] at h
    rw [Nat.mod_eq_of_lt hb] at h; exact h
  have hQ1 : Q1.lo.toNat + Q1.hi.toNat * 2 ^ 64
      = Q0.hi.toNat + lhs.l1.toNat * rhs.toNat + add.l1.toNat := by
    have hinner : (⟨Q0.hi, 0⟩ + mulLimb lhs.l1 rhs : UInt128L).toNat
        = Q0.hi.toNat + lhs.l1.toNat * rhs.toNat := by
      have hb : Q0.hi.toNat + lhs.l1.toNat * rhs.toNat < 2 ^ 128 := by
        have := Q0.hi.toNat_lt; have := tb lhs.l1; omega
      rw [UInt128L.toNat_add, mulLimb_toNat]
      simp only [UInt128L.toNat, Nat.shiftLeft_eq, show (0 : UInt64).toNat = 0 from rfl,
        Nat.zero_mul, Nat.add_zero]
      exact Nat.mod_eq_of_lt hb
    have hb2 : Q0.hi.toNat + lhs.l1.toNat * rhs.toNat + add.l1.toNat < 2 ^ 128 := by
      have := Q0.hi.toNat_lt; have := tb lhs.l1; have := add.l1.toNat_lt; omega
    have h := UInt128L.toNat_add (⟨Q0.hi, 0⟩ + mulLimb lhs.l1 rhs : UInt128L)
      (⟨add.l1, 0⟩ : UInt128L)
    rw [← hQ1def, hinner] at h
    simp only [UInt128L.toNat, Nat.shiftLeft_eq, show (0 : UInt64).toNat = 0 from rfl,
      Nat.zero_mul, Nat.add_zero] at h
    rw [Nat.mod_eq_of_lt hb2] at h; exact h
  have hQ2 : Q2.lo.toNat + Q2.hi.toNat * 2 ^ 64
      = Q1.hi.toNat + lhs.l2.toNat * rhs.toNat + add.l2.toNat := by
    have hinner : (⟨Q1.hi, 0⟩ + mulLimb lhs.l2 rhs : UInt128L).toNat
        = Q1.hi.toNat + lhs.l2.toNat * rhs.toNat := by
      have hb : Q1.hi.toNat + lhs.l2.toNat * rhs.toNat < 2 ^ 128 := by
        have := Q1.hi.toNat_lt; have := tb lhs.l2; omega
      rw [UInt128L.toNat_add, mulLimb_toNat]
      simp only [UInt128L.toNat, Nat.shiftLeft_eq, show (0 : UInt64).toNat = 0 from rfl,
        Nat.zero_mul, Nat.add_zero]
      exact Nat.mod_eq_of_lt hb
    have hb2 : Q1.hi.toNat + lhs.l2.toNat * rhs.toNat + add.l2.toNat < 2 ^ 128 := by
      have := Q1.hi.toNat_lt; have := tb lhs.l2; have := add.l2.toNat_lt; omega
    have h := UInt128L.toNat_add (⟨Q1.hi, 0⟩ + mulLimb lhs.l2 rhs : UInt128L)
      (⟨add.l2, 0⟩ : UInt128L)
    rw [← hQ2def, hinner] at h
    simp only [UInt128L.toNat, Nat.shiftLeft_eq, show (0 : UInt64).toNat = 0 from rfl,
      Nat.zero_mul, Nat.add_zero] at h
    rw [Nat.mod_eq_of_lt hb2] at h; exact h
  have hQ3 : Q3.lo.toNat + Q3.hi.toNat * 2 ^ 64
      = Q2.hi.toNat + lhs.l3.toNat * rhs.toNat + add.l3.toNat := by
    have hinner : (⟨Q2.hi, 0⟩ + mulLimb lhs.l3 rhs : UInt128L).toNat
        = Q2.hi.toNat + lhs.l3.toNat * rhs.toNat := by
      have hb : Q2.hi.toNat + lhs.l3.toNat * rhs.toNat < 2 ^ 128 := by
        have := Q2.hi.toNat_lt; have := tb lhs.l3; omega
      rw [UInt128L.toNat_add, mulLimb_toNat]
      simp only [UInt128L.toNat, Nat.shiftLeft_eq, show (0 : UInt64).toNat = 0 from rfl,
        Nat.zero_mul, Nat.add_zero]
      exact Nat.mod_eq_of_lt hb
    have hb2 : Q2.hi.toNat + lhs.l3.toNat * rhs.toNat + add.l3.toNat < 2 ^ 128 := by
      have := Q2.hi.toNat_lt; have := tb lhs.l3; have := add.l3.toNat_lt; omega
    have h := UInt128L.toNat_add (⟨Q2.hi, 0⟩ + mulLimb lhs.l3 rhs : UInt128L)
      (⟨add.l3, 0⟩ : UInt128L)
    rw [← hQ3def, hinner] at h
    simp only [UInt128L.toNat, Nat.shiftLeft_eq, show (0 : UInt64).toNat = 0 from rfl,
      Nat.zero_mul, Nat.add_zero] at h
    rw [Nat.mod_eq_of_lt hb2] at h; exact h
  rw [hexp]
  simp only [UInt256L.toNat, Nat.shiftLeft_eq]
  linarith [hQ0, hQ1, hQ2, hQ3]

end BN254.Fast
