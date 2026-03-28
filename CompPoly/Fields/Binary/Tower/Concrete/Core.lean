/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Data.Classes.DCast
import CompPoly.Fields.Binary.Tower.Abstract.Basis

/-!
# Concrete Binary Tower Core

Core definitions for the concrete bitvector model of the binary tower.
-/

namespace ConcreteBinaryTower

open Polynomial

def ConcreteBTField : ℕ → Type := fun k => BitVec (2 ^ k)

section BitVecDCast
lemma cast_ConcreteBTField_eq (k m : ℕ) (h_eq : k = m) :
    ConcreteBTField k = ConcreteBTField m := by
  subst h_eq
  rfl

instance BitVec.instDCast : DCast Nat BitVec where
  dcast h := BitVec.cast h
  dcast_id := by
    intro n
    funext bv -- bv : BitVec n
    rw [BitVec.cast_eq, id_eq]

theorem BitVec.bitvec_cast_eq_dcast {n m : Nat} (h : n = m) (bv : BitVec n) :
    BitVec.cast h bv = DCast.dcast h bv := by
  simp only [BitVec.cast, BitVec.instDCast]

theorem BitVec.dcast_id {n : Nat} (bv : BitVec n) :
    DCast.dcast (Eq.refl n) bv = bv := by
  simp only [BitVec.instDCast.dcast_id, id_eq]

theorem BitVec.dcast_bitvec_eq {l r val : ℕ} (h_width_eq : l = r) :
    dcast h_width_eq (BitVec.ofNat l val) = BitVec.ofNat r val := by
  subst h_width_eq
  rw [dcast_eq]

@[simp] theorem BitVec.cast_zero {n m : ℕ} (h : n = m) : BitVec.cast h 0 = 0 := rfl
@[simp] theorem BitVec.cast_one {n m : ℕ} (h : n = m) : BitVec.cast h 1 = 1#m := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.cast_ofNat]
@[simp] theorem BitVec.dcast_zero {n m : ℕ} (h : n = m) : DCast.dcast h (0#n) = 0#m := rfl
@[simp] theorem BitVec.dcast_one {n m : ℕ} (h : n = m) : DCast.dcast h (1#n) = 1#m := by
  rw [←BitVec.bitvec_cast_eq_dcast]
  exact BitVec.cast_one (h:=h)

theorem BitVec.dcast_bitvec_toNat_eq {w w2 : ℕ} (x : BitVec w) (h_width_eq : w = w2) :
    BitVec.toNat x = BitVec.toNat (dcast (h_width_eq) x) := by
  subst h_width_eq
  rw [dcast_eq]

theorem BitVec.dcast_bitvec_eq_zero {l r : ℕ} (h_width_eq : l = r) :
    dcast (h_width_eq) 0#(l) = 0#(r) := by
  exact BitVec.dcast_bitvec_eq (l:=l) (r:=r) (val:=0) (h_width_eq:=h_width_eq)

theorem BitVec.dcast_bitvec_extractLsb_eq {w hi1 lo1 hi2 lo2 : ℕ}
    (x : BitVec w) (h_lo_eq : lo1 = lo2)
    (h_width_eq : hi1 - lo1 + 1 = hi2 - lo2 + 1) :
    dcast h_width_eq (BitVec.extractLsb (hi:=hi1) (lo:=lo1) x)
      = BitVec.extractLsb (hi:=hi2) (lo:=lo2) (x) := by
  unfold BitVec.extractLsb BitVec.extractLsb'
  have xToNat_eq : x.toNat >>> lo1 = x.toNat >>> lo2 := by rw [h_lo_eq]
  rw [xToNat_eq]
  rw! [h_width_eq]
  rw [BitVec.dcast_id]

theorem BitVec.dcast_dcast_bitvec_extractLsb_eq {w hi lo : ℕ} (x : BitVec w)
    (h_width_eq : w = hi - lo + 1) : dcast h_width_eq (dcast (h_width_eq.symm)
  (BitVec.extractLsb (hi:=hi) (lo:=lo) x)) = BitVec.extractLsb (hi:=hi) (lo:=lo) x := by
  simp only [dcast, BitVec.cast_cast, BitVec.cast_eq]

theorem BitVec.eq_mp_eq_dcast {w w2 : ℕ} (x : BitVec w) (h_width_eq : w = w2)
    (h_bitvec_eq : BitVec w = BitVec w2 := by rw [h_width_eq]) :
  Eq.mp (h:=h_bitvec_eq) (a:=x) = dcast (h_width_eq) (x) := by
  rw [eq_mp_eq_cast] -- convert Eq.mp into root.cast
  rw [dcast_eq_root_cast]

theorem BitVec.extractLsb_concat_hi {hi_size lo_size : ℕ} (hi : BitVec hi_size)
    (lo : BitVec lo_size) (h_hi : hi_size > 0) :
  BitVec.extractLsb (hi:=hi_size + lo_size - 1) (lo:=lo_size)
  (BitVec.append (msbs:=hi) (lsbs:=lo)) = dcast (by
    rw [←Nat.sub_add_comm (by omega), Nat.sub_add_cancel (by omega), Nat.add_sub_cancel]
  ) hi := by
  simp only [BitVec.extractLsb]
  simp [BitVec.extractLsb'_append_eq_of_le (Nat.le_refl lo_size)]
  simp only [BitVec.extractLsb', Nat.shiftRight_zero, BitVec.ofNat_toNat]
  have hi_eq : hi = BitVec.ofNat hi_size (hi.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hi_eq]
  rw [dcast_bitvec_eq] -- un - dcast
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem BitVec.extractLsb_concat_lo {hi_size lo_size : ℕ} (hi : BitVec hi_size)
    (lo : BitVec lo_size) (h_lo : lo_size > 0) : BitVec.extractLsb (hi:=lo_size - 1) (lo:=0)
  (BitVec.append (msbs:=hi) (lsbs:=lo)) = dcast (by
    rw [←Nat.sub_add_comm (h:=by omega), Nat.sub_add_cancel (h:=by omega), Nat.sub_zero]
  ) lo := by
  simp only [BitVec.extractLsb]
  simp only [Nat.sub_zero, BitVec.append_eq]
  simp only [BitVec.extractLsb', Nat.shiftRight_zero, BitVec.ofNat_toNat]
  have lo_eq : lo = BitVec.ofNat lo_size (lo.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [lo_eq]
  rw [dcast_bitvec_eq] -- un - dcast
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- ⊢ BitVec.setWidth (n - 1 + 1) (hi ++ lo) = BitVec.setWidth (n - 1 + 1) lo
  rw [BitVec.setWidth_append]
  have h_le : lo_size - 1 + 1 ≤ lo_size := by rw [Nat.sub_add_cancel (by omega)]
  simp only [h_le, ↓reduceDIte]

theorem Nat.shiftRight_eq_sub_mod_then_div_two_pow {n lo_len : ℕ} :
    n >>> lo_len = (n - n % 2 ^ lo_len) / 2 ^ lo_len := by
  rw [Nat.shiftRight_eq_div_pow]
  rw (occs := .pos [1]) [Nat.div_eq_sub_mod_div]

theorem Nat.shiftRight_lo_mod_2_pow_hi_shiftLeft_lo (n hi_len lo_len : ℕ)
    (h_n : n < 2 ^ (hi_len + lo_len)) :
  (((n >>> lo_len) % (2 ^ hi_len)) <<< lo_len) = (n - n % 2 ^ lo_len) := by
  rw [Nat.shiftLeft_eq]
  have n_shr_lo_mod_2_pow_hi : (n >>> lo_len) % 2 ^ hi_len = n >>> lo_len := by
    have shr_lt : n >>> lo_len < 2 ^ hi_len := by
      rw [Nat.shiftRight_eq_div_pow]
      have n_lt : n < 2 ^ lo_len * 2 ^ hi_len := by
        rw [←Nat.pow_add]
        rw [Nat.add_comm]
        exact h_n
      exact Nat.div_lt_of_lt_mul n_lt
    have shr_mod : (n >>> lo_len) % 2 ^ hi_len = n >>> lo_len := by
      rw [Nat.mod_eq_of_lt]
      exact shr_lt
    rw [shr_mod]

  rw [n_shr_lo_mod_2_pow_hi] -- ⊢ n = n >>> lo_len * 2 ^ lo_len + n % 2 ^ lo_len
  rw [Nat.shiftRight_eq_div_pow]
  -- ⊢ n = n / 2 ^ lo_len * 2 ^ lo_len + n % 2 ^ lo_len
  have n_div_eq : (n / 2 ^ lo_len) = (n - n % 2 ^ lo_len) / 2 ^ lo_len := by
    exact Nat.div_eq_sub_mod_div
  rw [n_div_eq]
  have h_div1 : 2 ^ lo_len ∣ n - n % 2 ^ lo_len := by
    exact Nat.dvd_sub_mod n
  rw [Nat.div_mul_cancel h_div1]

theorem Nat.reconstruct_from_hi_and_lo_parts (n hi_len lo_len : ℕ)
    (h_n : n < 2 ^ (hi_len + lo_len)) :
    n = (((n >>> lo_len) % (2 ^ hi_len)) <<< lo_len) + (n % (2 ^ lo_len)) := by
  rw [Nat.shiftRight_lo_mod_2_pow_hi_shiftLeft_lo (n:=n) (hi_len:=hi_len)
    (lo_len:=lo_len) (h_n:=h_n)]
  -- ⊢ n = n - n % 2 ^ lo_len + n % 2 ^ lo_len
  have h_mod_le : n % 2 ^ lo_len ≤ n := by
    exact Nat.mod_le n (2 ^ lo_len)
  rw [Nat.sub_add_cancel h_mod_le]

theorem Nat.reconstruct_from_hi_and_lo_parts_or_ver (n hi_len lo_len : ℕ)
    (h_n : n < 2 ^ (hi_len + lo_len)) :
    n = (((n >>> lo_len) % (2 ^ hi_len)) <<< lo_len) ||| (n % (2 ^ lo_len)) := by
  rw (occs := .pos [1]) [Nat.reconstruct_from_hi_and_lo_parts (n:=n) (hi_len:=hi_len)
    (lo_len:=lo_len) (h_n:=h_n)]
  -- ⊢ (n >>> lo_len % 2 ^ hi_len) <<< lo_len + n % 2 ^ lo_len
  -- = (n >>> lo_len % 2 ^ hi_len) <<< lo_len ||| n % 2 ^ lo_len
  rw [Nat.shiftLeft_add_eq_or_of_lt (a:=n >>> lo_len % 2 ^ hi_len) (b:=n % 2 ^ lo_len)
    (b_lt:=by exact Nat.mod_lt n (by norm_num))]

theorem BitVec.eq_append_iff_extract {lo_size hi_size : ℕ} (lo : BitVec lo_size)
    (hi : BitVec hi_size) (h_hi_gt_0 : hi_size > 0) (h_lo_gt_0 : lo_size > 0)
  (x : BitVec (hi_size + lo_size)) : x = dcast (by rfl) (BitVec.append (msbs:=hi) (lsbs:=lo)) ↔
  hi = dcast (by omega) (BitVec.extractLsb (hi:=hi_size + lo_size - 1) (lo:=lo_size) x) ∧
  lo = dcast (by omega) (BitVec.extractLsb (hi:=lo_size - 1) (lo:=0) x) := by
  -- idea : use BitVec.extractLsb_concat_hi and BitVec.extractLsb_concat_lo
  have h_hi := dcast_symm (hb:=(BitVec.extractLsb_concat_hi (hi:=hi) (lo:=lo)
    (h_hi:=h_hi_gt_0)).symm)
  have h_lo := dcast_symm (hb:=(BitVec.extractLsb_concat_lo (hi:=hi) (lo:=lo)
    (h_lo:=h_lo_gt_0)).symm)
  constructor
  · intro h_x -- x = dcast ⋯ (hi.append lo)
    rw [h_x]
    apply And.intro
    · -- rewrite only the first goal
      rw (occs := .pos [1]) [←h_hi]
      unfold BitVec.extractLsb BitVec.extractLsb'
      rw [←dcast_bitvec_toNat_eq] -- cancel INNER dcast via BitVec.toNat
    · rw (occs := .pos [1]) [←h_lo]
      unfold BitVec.extractLsb BitVec.extractLsb'
      rw [←dcast_bitvec_toNat_eq] -- cancel INNER dcast via BitVec.toNat
  · -- Right to left
    intro h_extract_eq_parts
    obtain ⟨h_hi_eq_extract, h_lo_eq_extract⟩ := h_extract_eq_parts
    apply BitVec.eq_of_toNat_eq (x:=x) (y:=(BitVec.append (n:=hi_size)
      (m:=lo_size) (msbs:=hi) (lsbs:=lo)))
    rw [BitVec.append_eq, BitVec.toNat_append]
    -- Convert goal to Nat equality : ⊢ x.toNat = hi.toNat <<< lo_size ||| lo.toNat
    rw [h_hi_eq_extract, h_lo_eq_extract]
    -- convert all BitVec.toNat (dcast bitvec) to Nat
    rw [←BitVec.dcast_bitvec_toNat_eq, ←BitVec.dcast_bitvec_toNat_eq]
    rw [BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', BitVec.extractLsb']
    rw [Nat.shiftRight_zero]
    rw [BitVec.ofNat_toNat]
    rw [BitVec.toNat_ofNat, Nat.sub_zero, BitVec.toNat_setWidth]
    -- ⊢ x.toNat = (x.toNat >>> lo_size % 2 ^ (hi_size + lo_size - 1 - lo_size + 1))
      --- <<< lo_size ||| x.toNat % 2 ^ (lo_size - 1 + 1)
    have h0 : lo_size ≤ hi_size + lo_size - 1 := by omega
    have h1 : 2 ^ (hi_size + lo_size - 1 - lo_size + 1) = 2 ^ hi_size := by
      rw [←Nat.sub_add_comm (h:=h0)]
      simp only [Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, pow_right_inj₀]
      omega
    have h2 : lo_size - 1 + 1 = lo_size := by rw [Nat.sub_add_cancel (h_lo_gt_0)]
    rw [h1, h2] -- ⊢ x.toNat = (x.toNat >>> lo_size % 2 ^ hi_size)
      --- <<< lo_size ||| x.toNat % 2 ^ lo_size
    exact Nat.reconstruct_from_hi_and_lo_parts_or_ver (n:=x.toNat)
      (hi_len:=hi_size) (lo_len:=lo_size) (h_n:=by exact BitVec.isLt (x:=x))

end BitVecDCast

/- Conversion utilities -/
section ConversionUtils

def bitVecToString (width : ℕ) (bv : BitVec width) : String :=
  Fin.foldl width (fun (s : String) (idx : Fin width) =>
    -- idx is the MSB - oriented loop index (0 to width - 1)
    -- Fin.rev idx converts it to an LSB - oriented index
    s.push (if BitVec.getLsb bv (Fin.rev idx) then '1' else '0')
  ) ""

def ConcreteBTField.toBitString {k : ℕ} (bv : ConcreteBTField k) : String :=
  bitVecToString (2 ^ k) (bv)

-- Helper : Bit width for ConcreteBTField
def width (k : ℕ) : ℕ := 2 ^ k

-- Convert Nat to ConcreteBTField
def fromNat {k : ℕ} (n : Nat) : ConcreteBTField k :=
  BitVec.ofNat (2 ^ k) n

@[simp] theorem fromNat_toNat_eq_self {k : ℕ} (bv : BitVec (2 ^ k)) :
  (fromNat (BitVec.toNat bv) : ConcreteBTField k) = bv := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, fromNat, ConcreteBTField]

instance ConcreteBTField.instDCast_local : DCast ℕ ConcreteBTField where
  dcast h_k_eq term_k1 := BitVec.cast (congrArg (fun n => 2 ^ n) h_k_eq) term_k1
  dcast_id := by
    intro k_idx; funext x
    simp only [id_eq, BitVec.cast, BitVec.ofNatLT_toNat]

end ConversionUtils

section NumericLemmas

lemma one_le_sub_middle_of_pow2 {k : ℕ} (h_k : 1 ≤ k) : 1 ≤ 2 ^ k - 2 ^ (k - 1) := by
  have l1 : 2 ^ (k - 1 + 1) = 2 ^ k := by congr 1; omega
  have res := one_le_sub_consecutive_two_pow (n:=k - 1)
  rw [l1] at res
  exact res

lemma sub_middle_of_pow2_with_one_canceled {k : ℕ} (h_k : 1 ≤ k) : 2 ^ k - 1 - 2 ^ (k - 1) + 1
    = 2 ^ (k - 1) := by
  calc 2 ^ k - 1 - 2 ^ (k - 1) + 1 = 2 ^ k - 2 ^ (k - 1) - 1 + 1 := by omega
    _ = 2 ^ k - 2 ^ (k - 1) := by
      rw [Nat.sub_add_cancel];exact one_le_sub_middle_of_pow2 (h_k:=h_k)
    _ = 2 ^ (k - 1) * 2 - 2 ^ (k - 1):= by
      congr 1
      rw [← Nat.pow_succ]
      congr
      simp only [Nat.succ_eq_add_one]
      rw [Nat.sub_add_cancel]
      omega
    _ = 2 ^ (k - 1) + 2 ^ (k - 1) - 2 ^ (k - 1) := by rw [Nat.mul_two]
    _ = 2 ^ (k - 1) := Nat.add_sub_self_left (2 ^ (k - 1)) (2 ^ (k - 1))

lemma h_sub_middle {k : ℕ} (h_pos : k > 0) : 2 ^ k - 1 - 2 ^ (k - 1) + 1 = 2 ^ (k - 1) := by
  exact sub_middle_of_pow2_with_one_canceled (k:=k) (h_k:=h_pos)

lemma h_middle_sub {k : ℕ} : 2 ^ (k - 1) - 1 - 0 + 1 = 2 ^ (k - 1) := by
  rw [Nat.sub_zero, Nat.sub_add_cancel (h:=one_le_two_pow_n (n:=k - 1))]

lemma h_sum_two_same_pow2 {k : ℕ} (h_pos : k > 0) : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
  rw [← Nat.mul_two, Nat.mul_comm, Nat.mul_comm, Nat.two_pow_pred_mul_two h_pos]

end NumericLemmas

/- Field arithmetic operations and structure -/
section FieldOperationsAndInstances

-- Zero element
def zero {k : ℕ} : ConcreteBTField k := BitVec.zero (2 ^ k)

-- One element
def one {k : ℕ} : ConcreteBTField k := 1#(2 ^ k)

instance instZeroConcreteBTField (k : ℕ) : Zero (ConcreteBTField k) where
  zero := zero
instance instOneConcreteBTField (k : ℕ) : One (ConcreteBTField k) where
  one := one

-- Basic operations
def add {k : ℕ} (x y : ConcreteBTField k) : ConcreteBTField k := BitVec.xor x y
def neg {k : ℕ} (x : ConcreteBTField k) : ConcreteBTField k := x

-- Type class instances
instance (k : ℕ) : HAdd (ConcreteBTField k) (ConcreteBTField k) (ConcreteBTField k)
  where hAdd := add

-- Type class instances
instance (k : ℕ) : Add (ConcreteBTField k) where
  add := add

theorem sum_fromNat_eq_from_xor_Nat {k : ℕ} (x y : Nat) :
    fromNat (k:=k) (x ^^^ y) = fromNat (k:=k) x + fromNat (k:=k) y := by
  unfold fromNat
  show BitVec.ofNat _ (x ^^^ y) = (BitVec.ofNat _ x) ^^^ (BitVec.ofNat _ y)
  rw [BitVec.ofNat_xor]

-- Basic lemmas for addition
lemma add_self_cancel {k : ℕ} (a : ConcreteBTField k) : a + a = 0 := by
  exact BitVec.xor_self (x:=a)

lemma add_eq_zero_iff_eq {k : ℕ} (a b : ConcreteBTField k) : a + b = 0 ↔ a = b := by
  exact BitVec.xor_eq_zero_iff

lemma add_assoc {k : ℕ} : ∀ (a b c : ConcreteBTField k), a + b + c = a + (b + c) := by
  exact BitVec.xor_assoc

-- Addition is commutative
lemma add_comm {k : ℕ} (a b : ConcreteBTField k) : a + b = b + a := by
  exact BitVec.xor_comm a b

-- Zero is identity
lemma zero_add {k : ℕ} (a : ConcreteBTField k) : 0 + a = a := by
  exact BitVec.zero_xor (x:=a)

lemma add_zero {k : ℕ} (a : ConcreteBTField k) : a + 0 = a := by
  exact BitVec.xor_zero (x:=a)

-- Negation is additive inverse (in char 2, neg = id)
lemma neg_add_cancel {k : ℕ} (a : ConcreteBTField k) : neg a + a = 0 := by
  exact BitVec.xor_self (x:=a)

lemma if_self_rfl {α : Type*} [DecidableEq α] (a b : α) :
    (if a = b then b else a) = a := by
  by_cases h : a = b
  · rw [if_pos h, h]
  · rw [if_neg h]

-- Isomorphism between ConcreteBTField 0 and GF(2)
-- Ensure GF(2) has decidable equality
noncomputable instance : DecidableEq (GF(2)) :=
  fun x y =>
    -- Use the isomorphism between GF(2) and ZMod 2
    let φ : GF(2) ≃ₐ[ZMod 2] ZMod 2 := GaloisField.equivZmodP 2
    -- ZMod 2 has decidable equality
    if h : φ x = φ y then
      isTrue (by
        -- φ is injective, so φ x = φ y implies x = y
        exact φ.injective h)
    else
      isFalse (by
        intro h_eq
        -- If x = y, then φ x = φ y
        apply h
        exact congrArg φ h_eq)

instance (k : ℕ) : DecidableEq (ConcreteBTField k) :=
  fun x y =>
    let p := BitVec.toNat x = BitVec.toNat y
    let q := x = y
    let hp : Decidable p := Nat.decEq (BitVec.toNat x) (BitVec.toNat y)
    let h_iff_pq : p ↔ q := (BitVec.toNat_eq).symm -- p is (toNat x = toNat y), q is (x = y)
    match hp with
    | isTrue (proof_p : p) =>
      -- We have a proof of p (toNat x = toNat y). We need a proof of q (x = y).
      -- h_iff_pq.mp gives p → q. So, (h_iff_pq.mp proof_p) is a proof of q.
      isTrue (h_iff_pq.mp proof_p)
    | isFalse (nproof_p : ¬p) =>
      -- We have a proof of ¬p. We need a proof of ¬q (which is q → False).
      -- So, assume proof_q : q. We need to derive False.
      -- h_iff_pq.mpr gives q → p. So, (h_iff_pq.mpr proof_q) is a proof of p.
      -- This contradicts nproof_p.
      isFalse (fun (proof_q : q) => nproof_p (h_iff_pq.mpr proof_q))

noncomputable def toConcreteBTF0 : GF(2) → ConcreteBTField 0 :=
  fun x => if decide (x = 0) then zero else one -- it depends on 'instFieldGaloisField'

noncomputable def fromConcreteBTF0 : ConcreteBTField 0 → (GF(2)) :=
  fun x => if decide (x = zero) then 0 else 1

lemma nsmul_succ {k : ℕ} (n : ℕ) (x : ConcreteBTField k) :
    (if ↑n.succ % 2 = 0 then zero else x) = (if ↑n % 2 = 0 then zero else x) + x := by
  have h : ↑n.succ % 2 = (↑n % 2 + 1) % 2 := by
    simp only [Nat.succ_eq_add_one, Nat.mod_add_mod]
  have zero_is_0 : (zero : ConcreteBTField k) = 0 := by rfl
  have h_n_mod_le : n % 2 < 2 := Nat.mod_lt n (by norm_num)
  match h_n_mod : n % 2 with
  | Nat.zero =>
    rw [h]
    have h1 : (n + 1) % 2 = 1 := by simp [Nat.add_mod, h_n_mod]
    simp [h1]; rw [(add_zero x).symm]; rw [←add_assoc, ←add_comm];
    rw [zero_is_0];
    rw [zero_add];
    rw [add_zero]
  | Nat.succ x' => -- h_n_mod : n % 2 = x'.succ
    match x' with
    | Nat.zero => -- h_n_mod : n % 2 = Nat.zero.succ => h_n_mod automatically updates
      rw [h]
      have h_n_mod_eq_1 : n % 2 = 1 := by rw [h_n_mod]
      rw [h_n_mod_eq_1]
      have h1 : (1 + 1 : ℤ) % 2 = 0 := by norm_num
      simp only [Nat.reduceAdd, Nat.mod_self, ↓reduceIte, Nat.zero_eq, Nat.succ_eq_add_one,
        _root_.zero_add, one_ne_zero]
      rw [zero_is_0, add_self_cancel]
    | Nat.succ _ => -- h_n_mod : n % 2 = n✝.succ.succ
      have h_n_mod_ge_2 : n % 2 ≥ 2 := by
        rw [h_n_mod]
        apply Nat.le_add_left
      rw [h_n_mod] at h_n_mod_le
      linarith

lemma zsmul_succ {k : ℕ} (n : ℕ) (x : ConcreteBTField k) :
    (if (↑n.succ : ℤ) % 2 = 0 then zero else x) = (if (↑n : ℤ) % 2 = 0 then zero else x) + x := by
  norm_cast
  exact nsmul_succ n x

lemma neg_mod_2_eq_0_iff_mod_2_eq_0 {n : ℤ} : ( - n) % 2 = 0 ↔ n % 2 = 0 := by
  constructor
  · intro h
    apply Int.dvd_iff_emod_eq_zero.mp
    apply Int.dvd_neg.mp
    exact Int.dvd_iff_emod_eq_zero.mpr h
  · intro h
    apply Int.dvd_iff_emod_eq_zero.mp
    apply Int.dvd_neg.mpr
    exact Int.dvd_iff_emod_eq_zero.mpr h

-- Int.negSucc n = - (n + 1)
lemma zsmul_neg' {k : ℕ} (n : ℕ) (a : ConcreteBTField k) :
    (if ((Int.negSucc n) : ℤ) % (2 : ℤ) = (0 : ℤ) then zero else a) =
    neg (if (↑n.succ : ℤ) % (2 : ℤ) = (0 : ℤ) then zero else a) := by
  have negSucc_eq_minus_of_n_plus_1 : Int.negSucc n = - (n + 1) := by rfl
  rw [negSucc_eq_minus_of_n_plus_1]
  have n_succ_eq_n_plus_1 : (↑n.succ : ℤ) = (↑n : ℤ) + 1 := by rfl
  rw [n_succ_eq_n_plus_1]
  -- Split on two cases of the `if ... else` statement
  by_cases h : (n + 1) % 2 = 0
  { -- h : (n + 1) % 2 = 0
    have n_succ_mod_2_eq_0 : ((↑n : ℤ) + 1) % 2 = 0 := by norm_cast
    rw [n_succ_mod_2_eq_0]
    -- ⊢ (if - (↑n + 1) % 2 = 0 then zero else a) = neg (if 0 = 0 then zero else a)
    have neg_n_succ_mod_2_eq_0 : ( - ((↑n : ℤ) + 1)) % 2 = 0 := by
      exact (neg_mod_2_eq_0_iff_mod_2_eq_0 (n:=((n : ℤ) + 1))).mpr n_succ_mod_2_eq_0
    -- ⊢ (if 0 = 0 then zero else a) = neg (if 0 = 0 then zero else a)
    rw [neg_n_succ_mod_2_eq_0]
    simp only [↓reduceIte]
    rfl
  }
  { -- h : ¬(n + 1) % 2 = 0
    push_neg at h -- h : (n + 1) % 2 ≠ 0
    have n_succ_mod_2_ne_1 : ((↑n : ℤ) + 1) % 2 = 1 := by
      have h_mod : (n + 1) % 2 = 1 := by -- prove the ℕ - version of the hypothesis & use norm_cast
        have tmp := Nat.mod_two_eq_zero_or_one (n:=n + 1)
        match tmp with
        | Or.inl h_mod_eq_0 =>
          rw [h_mod_eq_0]
          contradiction
        | Or.inr h_mod_eq_1 =>
          rw [h_mod_eq_1]
      norm_cast
    rw [n_succ_mod_2_ne_1]
    have neg_n_succ_mod_2_ne_0 : ( - ((↑n : ℤ) + 1)) % 2 ≠ 0 := by
      by_contra h_eq_0
      have neg_succ_mod_2_eq_0 : ((↑n : ℤ) + 1) % 2 = 0 :=
        (neg_mod_2_eq_0_iff_mod_2_eq_0 (n:=((n : ℤ) + 1))).mp h_eq_0
      have neg_succ_mod_2_eq_0_nat : (n + 1) % 2 = 0 := by
        have : ↑((n + 1) % 2) = ((↑n : ℤ) + 1) % 2 := by norm_cast
        rw [neg_succ_mod_2_eq_0] at this
        apply Int.ofNat_eq_zero.mp -- simp [Int.ofNat_emod]
        exact this
      rw [neg_succ_mod_2_eq_0_nat] at h
      contradiction
    -- ⊢ (if - (↑n + 1) % 2 = 0 then zero else a) = neg (if 1 = 0 then zero else a)
    rw [if_neg one_ne_zero, neg]
    rw [if_neg neg_n_succ_mod_2_ne_0]
  }

-- Split a field element into high and low parts
def split {k : ℕ} (h : k > 0) (x : ConcreteBTField k) :
    ConcreteBTField (k - 1) × ConcreteBTField (k - 1) :=
  let lo_bits : BitVec (2 ^ (k - 1) - 1 - 0 + 1) :=
    BitVec.extractLsb (hi := 2 ^ (k - 1) - 1) (lo := 0) x
  let hi_bits : BitVec (2 ^ k - 1 - 2 ^ (k - 1) + 1) :=
    BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x
  have h_lo : 2 ^ (k - 1) - 1 - 0 + 1 = 2 ^ (k - 1) := by
    calc 2 ^ (k - 1) - 1 - 0 + 1 = 2 ^ (k - 1) - 1 + 1 := by norm_num
      _ = 2 ^ (k - 1) := by rw [Nat.sub_add_cancel]; exact one_le_two_pow_n (n:=k - 1)
  have h_hi := sub_middle_of_pow2_with_one_canceled (k:=k) (h_k:=by omega)
  -- Use cast to avoid overuse of fromNat & toNat
  let lo : BitVec (2 ^ (k - 1)) := dcast h_lo lo_bits
  let hi : BitVec (2 ^ (k - 1)) := dcast h_hi hi_bits
  (hi, lo)

def join {k : ℕ} (h_pos : k > 0) (hi lo : ConcreteBTField (k - 1)) : ConcreteBTField k := by
  let res := BitVec.append (msbs:=hi) (lsbs:=lo)
  rw [h_sum_two_same_pow2 (h_pos:=h_pos)] at res
  exact res

scoped[ConcreteBinaryTower] notation "《" hi ", " lo "》" => join (h_pos:=by omega) hi lo

lemma cast_join {k n : ℕ} (h_pos : k > 0) (hi lo : ConcreteBTField (k - 1)) (heq : k = n) :
    join (k:=k) h_pos hi lo = cast (by rw [heq])
    (join (k:=n) (by omega) (cast (by subst heq; rfl) hi) (lo:=cast (by subst heq; rfl) lo)) := by
  subst heq
  rfl

-------------------------------------------------------------------------------------------
structure ConcreteBTFAddCommGroupProps (k : ℕ) where
  add_assoc : ∀ a b c : ConcreteBTField k, (a + b) + c = a + (b + c) := add_assoc
  add_comm : ∀ a b : ConcreteBTField k, a + b = b + a := add_comm
  add_zero : ∀ a : ConcreteBTField k, a + zero = a := add_zero
  zero_add : ∀ a : ConcreteBTField k, zero + a = a := zero_add
  add_neg : ∀ a : ConcreteBTField k, a + (neg a) = zero := neg_add_cancel

lemma zero_is_0 {k : ℕ} : (zero (k:=k)) = (0 : ConcreteBTField k) := by rfl
lemma one_is_1 {k : ℕ} : (one (k:=k)) = 1 := by rfl
lemma concrete_one_ne_zero {k : ℕ} : (one (k:=k)) ≠ (zero (k:=k)) := by
  intro h_eq
  have h_toNat_eq : (one (k:=k)).toNat = (zero (k:=k)).toNat := congrArg BitVec.toNat h_eq
  simp [one, zero, BitVec.toNat_ofNat] at h_toNat_eq

instance {k : ℕ} : NeZero (1 : ConcreteBTField k) := by
  unfold ConcreteBTField
  exact {out := concrete_one_ne_zero (k:=k) }

@[reducible] def mkAddCommGroupInstance {k : ℕ} : AddCommGroup (ConcreteBTField k) := {
  zero := zero
  neg := neg
  sub := fun x y => add x y
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := fun n x => if n % 2 = (0 : ℕ) then zero else x
  zsmul := fun (n : ℤ) x => if n % 2 = 0 then zero else x  -- Changed to n : ℤ
  neg_add_cancel := neg_add_cancel
  nsmul_succ := nsmul_succ
  zsmul_succ' := fun n a => zsmul_succ n a
  add := add
  zsmul_neg' := zsmul_neg' (k := k)
}

instance (k : ℕ) : AddCommGroup (ConcreteBTField k) := mkAddCommGroupInstance

theorem BitVec.extractLsb_eq_shift_ofNat {n : Nat} (x : BitVec n) (l r : Nat) :
    BitVec.extractLsb r l x = BitVec.ofNat (r - l + 1) (x.toNat >>> l) := by
  unfold BitVec.extractLsb BitVec.extractLsb'
  rfl

theorem setWidth_eq_ofNat_mod {n num_bits : Nat} (x : BitVec n) :
    BitVec.setWidth num_bits x = BitVec.ofNat num_bits (x.toNat % 2 ^ num_bits) := by
  simp only [BitVec.ofNat_toNat, ← BitVec.toNat_setWidth, BitVec.setWidth_eq]

theorem BitVec.extractLsb_eq_and_pow_2_minus_1_ofNat {n num_bits : Nat}
    (h_num_bits : num_bits > 0) (x : BitVec n) :
  BitVec.extractLsb (hi:= num_bits - 1) (lo := 0) x =
    BitVec.ofNat (num_bits - 1 - 0 + 1) (x.toNat &&& (2 ^ num_bits - 1)) := by
  unfold BitVec.extractLsb BitVec.extractLsb'
  simp only [Nat.sub_zero, Nat.shiftRight_zero]
  have eq : num_bits - 1 + 1 = num_bits := Nat.sub_add_cancel (h:=h_num_bits)
  rw [eq]
  have lhs : BitVec.ofNat num_bits x.toNat = BitVec.ofNat num_bits (x.toNat % 2 ^ num_bits) := by
    simp only [BitVec.ofNat_toNat, setWidth_eq_ofNat_mod]
  have rhs : BitVec.ofNat num_bits (x.toNat &&& 2 ^ num_bits - 1) =
    BitVec.ofNat num_bits (x.toNat % 2 ^ num_bits) := by
    congr
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat num_bits
  rw [lhs, ←rhs]

theorem split_bitvec_eq_iff_fromNat {k : ℕ} (h_pos : k > 0) (x : ConcreteBTField k)
    (hi_btf lo_btf : ConcreteBTField (k - 1)) :
  split h_pos x = (hi_btf, lo_btf) ↔
  (hi_btf = fromNat (k:=k - 1) (x.toNat >>> 2 ^ (k - 1)) ∧
  lo_btf = fromNat (k:=k - 1) (x.toNat &&& (2 ^ (2 ^ (k - 1)) - 1))) := by
  have lhs_lo_case := BitVec.extractLsb_eq_and_pow_2_minus_1_ofNat (num_bits:=2 ^ (k - 1))
    (n:=2 ^ k) (Nat.two_pow_pos (k - 1)) (x:=x)
  have rhs_hi_case_bitvec_eq := BitVec.extractLsb_eq_shift_ofNat (n:=2 ^ k) (r:=2 ^ k - 1)
    (l:=2 ^ (k - 1)) (x:=x)
  constructor
  · -- Forward direction : split x = (hi_btf, lo_btf) → bitwise operations
    intro h_split
    unfold split at h_split
    have ⟨h_hi, h_lo⟩ := Prod.ext_iff.mp h_split
    simp only at h_hi h_lo
    have hi_eq : hi_btf = fromNat (k:=k - 1) (x.toNat >>> 2 ^ (k - 1)) := by
      unfold fromNat
      rw [←h_hi]
      rw [dcast_symm (h_sub_middle h_pos).symm]
      rw [rhs_hi_case_bitvec_eq]
      rw [BitVec.dcast_bitvec_eq]
    have lo_eq : lo_btf = fromNat (k:=k - 1) (x.toNat &&& ((2 ^ (2 ^ (k - 1)) - 1))) := by
      unfold fromNat
      rw [←h_lo]
      have rhs_lo_case_bitvec_eq :=
        BitVec.extractLsb_eq_shift_ofNat (n:=2 ^ k) (r:=2 ^ (k - 1) - 1) (l:=0) (x:=x)
      rw [dcast_symm (h_middle_sub).symm]
      rw [rhs_lo_case_bitvec_eq]
      rw [BitVec.dcast_bitvec_eq] -- remove dcast
      rw [←lhs_lo_case]
      exact rhs_lo_case_bitvec_eq
    exact ⟨hi_eq, lo_eq⟩
  · -- Backward direction : bitwise operations → split x = (hi_btf, lo_btf)
    intro h_bits
    unfold split
    have ⟨h_hi, h_lo⟩ := h_bits
    have hi_extract_eq : dcast (h_sub_middle h_pos) (BitVec.extractLsb (hi := 2 ^ k - 1)
      (lo := 2 ^ (k - 1)) x) = fromNat (k:=k - 1) (x.toNat >>> 2 ^ (k - 1)) := by
      unfold fromNat
      rw [dcast_symm (h_sub_middle h_pos).symm]
      rw [rhs_hi_case_bitvec_eq]
      rw [BitVec.dcast_bitvec_eq]

    have lo_extract_eq : dcast (h_middle_sub) (BitVec.extractLsb (hi := 2 ^ (k - 1) - 1)
      (lo := 0) x) = fromNat (k:=k - 1) (x.toNat &&& ((2 ^ (2 ^ (k - 1)) - 1))) := by
      unfold fromNat
      rw [lhs_lo_case]
      rw [BitVec.dcast_bitvec_eq]

    simp only [hi_extract_eq, Nat.sub_zero, lo_extract_eq, Nat.and_two_pow_sub_one_eq_mod, h_hi,
      h_lo]

theorem BitVec.extractLsb_dcast_eq {w w2 hi lo : ℕ} (x : BitVec w) (h : w = w2) :
    BitVec.extractLsb (hi:=hi) (lo:=lo) (dcast h x) =
      BitVec.extractLsb (hi:=hi) (lo:=lo) x := by
  unfold BitVec.extractLsb BitVec.extractLsb'
  have h_toNat : BitVec.toNat (dcast h x) = BitVec.toNat x := by
    simpa using (BitVec.dcast_bitvec_toNat_eq (x:=x) (h_width_eq:=h)).symm
  rw [h_toNat]

theorem join_eq_dcast_append {k : ℕ} (h_pos : k > 0) (hi lo : ConcreteBTField (k - 1)) :
    join (k:=k) h_pos hi lo =
      dcast (h_sum_two_same_pow2 (k:=k) (h_pos:=h_pos))
        (BitVec.append (msbs:=hi) (lsbs:=lo)) := by
  unfold join
  simp [dcast_eq_root_cast]

theorem eq_join_iff_dcast_eq_append {k : ℕ} (h_pos : k > 0) (x : ConcreteBTField k)
    (hi lo : ConcreteBTField (k - 1)) :
    x = join (k:=k) h_pos hi lo ↔
      dcast (h_sum_two_same_pow2 (k:=k) (h_pos:=h_pos)).symm x =
        BitVec.append (msbs:=hi) (lsbs:=lo) := by
  classical
  constructor
  · intro hx
    have hx' := hx
    rw [join_eq_dcast_append (k:=k) (h_pos:=h_pos) (hi:=hi) (lo:=lo)] at hx'
    -- hx' : x = dcast sum (append ..)
    exact
      dcast_symm (ha := h_sum_two_same_pow2 (k:=k) (h_pos:=h_pos)) (hb := hx'.symm)
  · intro hx
    have hx' :
        dcast (h_sum_two_same_pow2 (k:=k) (h_pos:=h_pos))
            (BitVec.append (msbs:=hi) (lsbs:=lo)) =
          x :=
      dcast_symm (ha := (h_sum_two_same_pow2 (k:=k) (h_pos:=h_pos)).symm) (hb := hx)
    have hx'' :
        x =
          dcast (h_sum_two_same_pow2 (k:=k) (h_pos:=h_pos))
            (BitVec.append (msbs:=hi) (lsbs:=lo)) :=
      hx'.symm
    rw [← join_eq_dcast_append (k:=k) (h_pos:=h_pos) (hi:=hi) (lo:=lo)] at hx''
    exact hx''


theorem join_eq_iff_dcast_extractLsb {k : ℕ} (h_pos : k > 0) (x : ConcreteBTField k)
    (hi_btf lo_btf : ConcreteBTField (k - 1)) :
  x = 《 hi_btf, lo_btf 》 ↔
  (hi_btf = dcast (h_sub_middle h_pos)
      (BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x) ∧
    lo_btf = dcast (h_middle_sub)
      (BitVec.extractLsb (hi := 2 ^ (k - 1) - 1) (lo := 0) x)) := by
  classical
  have hpos_eq : h_pos = (by omega : k > 0) := Subsingleton.elim _ _
  cases hpos_eq
  -- unfold the join notation
  change x = join (k := k) h_pos hi_btf lo_btf ↔
    (hi_btf = dcast (h_sub_middle h_pos)
        (BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x) ∧
      lo_btf = dcast (h_middle_sub)
        (BitVec.extractLsb (hi := 2 ^ (k - 1) - 1) (lo := 0) x))

  let sum := h_sum_two_same_pow2 (k := k) (h_pos := h_pos)
  have hpow : 2 ^ (k - 1) > 0 := Nat.two_pow_pos (k - 1)

  -- main chain of iff's
  have h_join :
      x = join (k := k) h_pos hi_btf lo_btf ↔
        dcast sum.symm x = BitVec.append (msbs := hi_btf) (lsbs := lo_btf) := by
    -- avoid simp (which may use the target theorem as a simp lemma)
    dsimp [sum]
    exact (eq_join_iff_dcast_eq_append (k := k) (h_pos := h_pos) (x := x)
      (hi := hi_btf) (lo := lo_btf))

  have h_extract' :
      dcast sum.symm x = BitVec.append (msbs := hi_btf) (lsbs := lo_btf) ↔
        (hi_btf = dcast (by omega)
            (BitVec.extractLsb (hi := 2 ^ (k - 1) + 2 ^ (k - 1) - 1) (lo := 2 ^ (k - 1)) x) ∧
          lo_btf = dcast (by omega)
            (BitVec.extractLsb (hi := 2 ^ (k - 1) - 1) (lo := 0) x)) := by
    -- use BitVec.eq_append_iff_extract on the casted x
    have h := (BitVec.eq_append_iff_extract (lo_size := 2 ^ (k - 1)) (hi_size := 2 ^ (k - 1))
      (lo := lo_btf) (hi := hi_btf)
      (h_hi_gt_0 := hpow)
      (h_lo_gt_0 := hpow)
      (x := dcast sum.symm x))
    have h1 :
        dcast sum.symm x = BitVec.append (msbs := hi_btf) (lsbs := lo_btf) ↔
          (hi_btf = dcast (by omega)
              (BitVec.extractLsb (hi := 2 ^ (k - 1) + 2 ^ (k - 1) - 1) (lo := 2 ^ (k - 1))
                (dcast sum.symm x)) ∧
            lo_btf = dcast (by omega)
              (BitVec.extractLsb (hi := 2 ^ (k - 1) - 1) (lo := 0) (dcast sum.symm x))) := by
      simpa using h
    -- now rewrite the extractLsb of dcast sum.symm x into extractLsb of x
    simpa [BitVec.extractLsb_dcast_eq (x := x) (h := sum.symm)] using h1

  have h_final :
      (hi_btf = dcast (by omega)
            (BitVec.extractLsb (hi := 2 ^ (k - 1) + 2 ^ (k - 1) - 1) (lo := 2 ^ (k - 1)) x) ∧
          lo_btf = dcast (by omega)
            (BitVec.extractLsb (hi := 2 ^ (k - 1) - 1) (lo := 0) x)) ↔
        (hi_btf = dcast (h_sub_middle h_pos)
            (BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x) ∧
          lo_btf = dcast (h_middle_sub)
            (BitVec.extractLsb (hi := 2 ^ (k - 1) - 1) (lo := 0) x)) := by
    -- prepare the cast equality for the hi-part
    have h_hi1_eq :
        2 ^ (k - 1) + 2 ^ (k - 1) - 1 = 2 ^ k - 1 := by
      omega

    have h_width_eq :
        (2 ^ (k - 1) + 2 ^ (k - 1) - 1) - 2 ^ (k - 1) + 1 = (2 ^ k - 1) - 2 ^ (k - 1) + 1 := by
      simp [h_hi1_eq]

    have h_extract_cast :
        dcast h_width_eq
            (BitVec.extractLsb (hi := 2 ^ (k - 1) + 2 ^ (k - 1) - 1) (lo := 2 ^ (k - 1)) x)
          = BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x := by
      simpa using
        (BitVec.dcast_bitvec_extractLsb_eq (x := x) (h_lo_eq := rfl) (h_width_eq := h_width_eq))

    have h_extract_cast_symm :
        dcast h_width_eq.symm
            (BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x)
          = BitVec.extractLsb (hi := 2 ^ (k - 1) + 2 ^ (k - 1) - 1) (lo := 2 ^ (k - 1)) x := by
      exact dcast_symm (ha := h_width_eq) (hb := h_extract_cast)

    have h_hi_term :
        dcast (by omega :
              (2 ^ (k - 1) + 2 ^ (k - 1) - 1) - 2 ^ (k - 1) + 1 = 2 ^ (k - 1))
            (BitVec.extractLsb (hi := 2 ^ (k - 1) + 2 ^ (k - 1) - 1) (lo := 2 ^ (k - 1)) x)
          =
          dcast (h_sub_middle h_pos)
            (BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x) := by
      -- rewrite extractLsb hi-parameter and compose casts
      calc
        dcast (by omega :
              (2 ^ (k - 1) + 2 ^ (k - 1) - 1) - 2 ^ (k - 1) + 1 = 2 ^ (k - 1))
            (BitVec.extractLsb (hi := 2 ^ (k - 1) + 2 ^ (k - 1) - 1) (lo := 2 ^ (k - 1)) x)
            =
            dcast (by omega :
              (2 ^ (k - 1) + 2 ^ (k - 1) - 1) - 2 ^ (k - 1) + 1 = 2 ^ (k - 1))
              (dcast h_width_eq.symm
                (BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x)) := by
              -- replace the extracted bits using the casted equality
              rw [← h_extract_cast_symm]
        _ =
            dcast (h_width_eq.symm.trans (by omega :
              (2 ^ (k - 1) + 2 ^ (k - 1) - 1) - 2 ^ (k - 1) + 1 = 2 ^ (k - 1)))
              (BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x) := by
              -- compose the two casts
              simp [dcast_trans]
        _ =
            dcast (h_sub_middle h_pos)
              (BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x) := by
              -- proof irrelevance for the cast proof
              have hproof :
                  h_width_eq.symm.trans (by omega :
                    (2 ^ (k - 1) + 2 ^ (k - 1) - 1) - 2 ^ (k - 1) + 1 = 2 ^ (k - 1))
                    = h_sub_middle h_pos := by
                exact Subsingleton.elim _ _
              simp only

    -- proof irrelevance for the lo-part cast proof
    have h_lo_proof :
        (by omega : 2 ^ (k - 1) - 1 - 0 + 1 = 2 ^ (k - 1)) = h_middle_sub (k := k) := by
      exact Subsingleton.elim _ _

    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · -- hi part
        simpa [h_hi_term] using h.1
      · -- lo part
        simpa [h_lo_proof] using h.2
    · intro h
      refine ⟨?_, ?_⟩
      · -- hi part
        simpa [h_hi_term.symm] using h.1
      · -- lo part
        simpa [h_lo_proof.symm] using h.2

  calc
    x = join (k := k) h_pos hi_btf lo_btf ↔
        dcast sum.symm x = BitVec.append (msbs := hi_btf) (lsbs := lo_btf) := h_join
    _ ↔
        (hi_btf = dcast (by omega)
            (BitVec.extractLsb (hi := 2 ^ (k - 1) + 2 ^ (k - 1) - 1) (lo := 2 ^ (k - 1)) x) ∧
          lo_btf = dcast (by omega)
            (BitVec.extractLsb (hi := 2 ^ (k - 1) - 1) (lo := 0) x)) := h_extract'
    _ ↔
        (hi_btf = dcast (h_sub_middle h_pos)
            (BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x) ∧
          lo_btf = dcast (h_middle_sub)
            (BitVec.extractLsb (hi := 2 ^ (k - 1) - 1) (lo := 0) x)) := h_final

theorem join_eq_join_iff {k : ℕ} (h_pos : k > 0) (hi₀ lo₀ hi₁ lo₁ : ConcreteBTField (k - 1)) :
    《 hi₀, lo₀ 》 = 《 hi₁, lo₁ 》 ↔ (hi₀ = hi₁ ∧ lo₀ = lo₁) := by
  constructor
  · intro h_join
    let x₀ := 《 hi₀, lo₀ 》
    let x₁ := 《 hi₁, lo₁ 》
    have h_x₀ : x₀ = 《 hi₀, lo₀ 》 := by rfl
    have h_x₁ : x₁ = 《 hi₁, lo₁ 》 := by rfl
    have h₀ := join_eq_iff_dcast_extractLsb h_pos x₀ hi₀ lo₀
    have h₁ := join_eq_iff_dcast_extractLsb h_pos x₁ hi₁ lo₁
    have h_x₀_eq_x₁ : x₀ = x₁ := by rw [h_x₀, h_x₁, h_join]
    have ⟨h_hi₀, h_lo₀⟩ := h₀.mp h_x₀
    have ⟨h_hi₁, h_lo₁⟩ := h₁.mp h_x₁
    rw [h_hi₁, h_hi₀, h_lo₀, h_lo₁]
    rw [h_x₀_eq_x₁]
    exact ⟨rfl, rfl⟩
  · intro h_eq
    rw [h_eq.1, h_eq.2]

theorem join_eq_bitvec_iff_fromNat {k : ℕ} (h_pos : k > 0) (x : ConcreteBTField k)
    (hi_btf lo_btf : ConcreteBTField (k - 1)) :
  x = 《 hi_btf, lo_btf 》 ↔
  (hi_btf = fromNat (k:=k - 1) (x.toNat >>> 2 ^ (k - 1)) ∧
  lo_btf = fromNat (k:=k - 1) (x.toNat &&& (2 ^ (2 ^ (k - 1)) - 1))) := by
  -- Idea : derive from theorem join_eq_iff_dcast_extractLsb
  constructor
  · -- Forward direction
    intro h_join
    have h := join_eq_iff_dcast_extractLsb h_pos x hi_btf lo_btf
    have ⟨h_hi, h_lo⟩ := h.mp h_join
    have hi_eq : hi_btf = fromNat (k:=k - 1) (x.toNat >>> 2 ^ (k - 1)) := by
      rw [h_hi]
      have := BitVec.extractLsb_eq_shift_ofNat (n:=2 ^ k) (r:=2 ^ k - 1) (l:=2 ^ (k - 1)) (x:=x)
      rw [this]
      unfold fromNat
      rw [BitVec.dcast_bitvec_eq]
    have lo_eq : lo_btf = fromNat (k:=k - 1) (x.toNat &&& (2 ^ (2 ^ (k - 1)) - 1)) := by
      rw [h_lo]
      have := BitVec.extractLsb_eq_and_pow_2_minus_1_ofNat (num_bits:=2 ^ (k - 1)) (n:=2 ^ k)
                (Nat.two_pow_pos (k - 1)) (x:=x)
      rw [this]
      unfold fromNat
      rw [BitVec.dcast_bitvec_eq]
    exact ⟨hi_eq, lo_eq⟩
  · -- Backward direction
    intro h_bits
    have ⟨h_hi, h_lo⟩ := h_bits
    have h := join_eq_iff_dcast_extractLsb h_pos x hi_btf lo_btf
    have hi_eq : hi_btf = dcast (h_sub_middle h_pos)
      (BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x) := by
      rw [h_hi]
      unfold fromNat
      have := BitVec.extractLsb_eq_shift_ofNat (n:=2 ^ k) (r:=2 ^ k - 1) (l:=2 ^ (k - 1)) (x:=x)
      rw [this]
      rw [BitVec.dcast_bitvec_eq]
    have lo_eq : lo_btf = dcast (h_middle_sub)
      (BitVec.extractLsb (hi := 2 ^ (k - 1) - 1) (lo := 0) x) := by
      rw [h_lo]
      unfold fromNat
      have := BitVec.extractLsb_eq_and_pow_2_minus_1_ofNat (num_bits:=2 ^ (k - 1)) (n:=2 ^ k)
                (Nat.two_pow_pos (k - 1)) (x:=x)
      rw [this]
      rw [BitVec.dcast_bitvec_eq]
    exact h.mpr ⟨hi_eq, lo_eq⟩

theorem join_of_split {k : ℕ} (h_pos : k > 0) (x : ConcreteBTField k)
    (hi_btf lo_btf : ConcreteBTField (k - 1))
    (h_split_eq : split h_pos x = (hi_btf, lo_btf)) :
    x = 《 hi_btf, lo_btf 》 := by
  have h_split := (split_bitvec_eq_iff_fromNat (k:=k) (h_pos:=h_pos) x hi_btf lo_btf).mp h_split_eq
  obtain ⟨h_hi, h_lo⟩ := h_split
  exact (join_eq_bitvec_iff_fromNat h_pos x hi_btf lo_btf).mpr ⟨h_hi, h_lo⟩

theorem split_of_join {k : ℕ} (h_pos : k > 0) (x : ConcreteBTField k)
    (hi_btf lo_btf : ConcreteBTField (k - 1))
    (h_join : x = 《hi_btf, lo_btf》) :
    (hi_btf, lo_btf) = split h_pos x := by
  have ⟨h_hi, h_lo⟩ := (join_eq_bitvec_iff_fromNat h_pos x hi_btf lo_btf).mp h_join
  exact ((split_bitvec_eq_iff_fromNat h_pos x hi_btf lo_btf).mpr ⟨h_hi, h_lo⟩).symm

lemma split_join_eq_split {k : ℕ} (h_pos : k > 0)
    (hi_btf lo_btf : ConcreteBTField (k - 1)) :
    split h_pos (《 hi_btf, lo_btf 》) = (hi_btf, lo_btf) := by
  exact (split_of_join h_pos (《 hi_btf, lo_btf 》) hi_btf lo_btf rfl).symm

lemma join_split_eq_join {k : ℕ} (h_pos : k > 0) (x : ConcreteBTField k) :
    《 (split h_pos x).fst, (split h_pos x).snd 》 = x := by
  exact (join_of_split h_pos x (split h_pos x).fst (split h_pos x).snd rfl).symm

theorem eq_iff_split_eq {k : ℕ} (h_pos : k > 0) (x₀ x₁ : ConcreteBTField k) :
    x₀ = x₁ ↔ (split h_pos x₀ = split h_pos x₁) := by
  constructor
  · intro h_eq
    rw [h_eq]
  · intro h_split
    let p₀ := split h_pos x₀
    let hi₀ := p₀.fst
    let lo₀ := p₀.snd
    have h_split_x₀ : split h_pos x₀ = (hi₀, lo₀) := by rfl
    have h_split_x₁ : split h_pos x₁ = (hi₀, lo₀) := by
      rw [h_split.symm]
    have h_x₀ := (split_bitvec_eq_iff_fromNat h_pos x₀ hi₀ lo₀).mp h_split_x₀
    have h_x₁ := (split_bitvec_eq_iff_fromNat h_pos x₁ hi₀ lo₀).mp h_split_x₁
    -- now prove that x₀ is join of hi₀ and lo₀, similarly for x₁, so they are equal
    have h_x₀_eq_join := join_of_split h_pos x₀ hi₀ lo₀ h_split_x₀
    have h_x₁_eq_join := join_of_split h_pos x₁ hi₀ lo₀ h_split_x₁
    rw [h_x₀_eq_join, h_x₁_eq_join]

theorem split_sum_eq_sum_split {k : ℕ} (h_pos : k > 0) (x₀ x₁ : ConcreteBTField k)
    (hi₀ lo₀ hi₁ lo₁ : ConcreteBTField (k - 1))
  (h_split_x₀ : split h_pos x₀ = (hi₀, lo₀))
  (h_split_x₁ : split h_pos x₁ = (hi₁, lo₁)) :
  split h_pos (x₀ + x₁) = (hi₀ + hi₁, lo₀ + lo₁) := by
  have h_x₀ := join_of_split h_pos x₀ hi₀ lo₀ h_split_x₀
  have h_x₁ := join_of_split h_pos x₁ hi₁ lo₁ h_split_x₁
  -- Approach : convert equation to Nat realm for simple proof
  have h₀ := (split_bitvec_eq_iff_fromNat (k:=k) (h_pos:=h_pos) x₀ hi₀ lo₀).mp h_split_x₀
  have h₁ := (split_bitvec_eq_iff_fromNat (k:=k) (h_pos:=h_pos) x₁ hi₁ lo₁).mp h_split_x₁
  have h_sum_hi : (hi₀ + hi₁) = fromNat (BitVec.toNat (x₀ + x₁) >>> 2 ^ (k - 1)) := by
    rw [h₀.1, h₁.1]
    rw [←sum_fromNat_eq_from_xor_Nat]
    have h_nat_eq : BitVec.toNat x₀ >>> 2 ^ (k - 1) ^^^ BitVec.toNat x₁ >>> 2 ^ (k - 1)
      = BitVec.toNat (x₀ + x₁) >>> 2 ^ (k - 1) := by
      -- unfold Concrete BTF addition into BitVec.xor
      erw [BitVec.toNat_xor]
      rw [Nat.shiftRight_xor_distrib.symm]
    rw [h_nat_eq]
  have h_sum_lo : (lo₀ + lo₁) = fromNat (BitVec.toNat (x₀ + x₁) &&& 2 ^ 2 ^ (k - 1) - 1) := by
    rw [h₀.2, h₁.2]
    rw [←sum_fromNat_eq_from_xor_Nat]
    have h_nat_eq : BitVec.toNat x₀ &&& 2 ^ 2 ^ (k - 1) - 1 ^^^ BitVec.toNat x₁
      &&& 2 ^ 2 ^ (k - 1) - 1 = BitVec.toNat (x₀ + x₁) &&& 2 ^ 2 ^ (k - 1) - 1 := by
      erw [BitVec.toNat_xor]
      rw [Nat.and_xor_distrib_right.symm]
    rw [h_nat_eq]
  have h_sum_hi_lo : (hi₀ + hi₁, lo₀ + lo₁) = split h_pos (x₀ + x₁) := by
    rw [(split_bitvec_eq_iff_fromNat (k:=k) (h_pos:=h_pos) (x₀ + x₁)
      (hi₀ + hi₁) (lo₀ + lo₁)).mpr ⟨h_sum_hi, h_sum_lo⟩]
  exact h_sum_hi_lo.symm

theorem join_add_join {k : ℕ} (h_pos : k > 0) (hi₀ lo₀ hi₁ lo₁ : ConcreteBTField (k - 1)) :
    《 hi₀, lo₀ 》 + 《 hi₁, lo₁ 》 = 《 hi₀ + hi₁, lo₀ + lo₁ 》 := by
  set x₀ := 《 hi₀, lo₀ 》
  set x₁ := 《 hi₁, lo₁ 》
  set x₂ := 《 hi₀ + hi₁, lo₀ + lo₁ 》
  have h_x₀ : x₀ = 《 hi₀, lo₀ 》 := by rfl
  have h_x₁ : x₁ = 《 hi₁, lo₁ 》 := by rfl
  have h_x₂ : x₂ = 《 hi₀ + hi₁, lo₀ + lo₁ 》 := by rfl
  -- proof : x₀ + x₁ = x₂, utilize split_sum_eq_sum_split and eq_iff_split_eq
  have h_split_x₀ := split_of_join h_pos x₀ hi₀ lo₀ h_x₀
  have h_split_x₁ := split_of_join h_pos x₁ hi₁ lo₁ h_x₁
  have h_split_x₂ := split_of_join h_pos x₂ (hi₀ + hi₁) (lo₀ + lo₁) h_x₂
  have h_split_x₂_via_sum := split_sum_eq_sum_split h_pos x₀ x₁ hi₀ lo₀ hi₁
    lo₁ h_split_x₀.symm h_split_x₁.symm
  rw [h_split_x₂_via_sum.symm] at h_split_x₂
  have h_eq := (eq_iff_split_eq h_pos (x₀ + x₁) x₂).mpr h_split_x₂
  exact h_eq

theorem split_zero {k : ℕ} (h_pos : k > 0) : split h_pos zero = (zero, zero) := by
  rw [split]
  simp only [zero, BitVec.zero_eq, BitVec.extractLsb_ofNat, Nat.zero_mod, Nat.zero_shiftRight,
    Nat.sub_zero, Nat.shiftRight_zero, BitVec.dcast_bitvec_eq_zero]

-- Special element Z_k for each level k
def Z (k : ℕ) : ConcreteBTField k :=
  if h_k : k = 0 then one
  else
    《 one (k:=k-1), zero (k:=k-1) 》

theorem split_Z {k : ℕ} (h_pos : k > 0) :
    split h_pos (Z k) = (one (k:=k - 1), zero (k:=k - 1)) := by
  apply Eq.symm
  apply split_of_join
  unfold Z
  have h_k_ne_0 : k ≠ 0 := by omega
  simp only [h_k_ne_0, ↓reduceDIte]

lemma one_bitvec_toNat {width : ℕ} (h_width : width > 0) : (1#width).toNat = 1 := by
  simp only [BitVec.toNat_ofNat, Nat.one_mod_two_pow_eq_one, h_width]

lemma one_bitvec_shiftRight {d : ℕ} (h_d : d > 0) : 1 >>> d = 0 := by
  apply Nat.shiftRight_eq_zero
  rw [Nat.one_lt_two_pow_iff]
  exact Nat.ne_zero_of_lt h_d

lemma split_one {k : ℕ} (h_k : k > 0) :
    split h_k (one (k:=k)) = (zero (k:=k - 1), one (k:=k - 1)) := by
  rw [split]
  let lo_bits := BitVec.extractLsb (hi := 2 ^ (k - 1) - 1) (lo := 0) (one (k:=k))
  let hi_bits := BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) (one (k:=k))
  apply Prod.ext
  · simp only
    simp only [BitVec.extractLsb, BitVec.extractLsb']
    rw [one]
    have one_toNat_eq := one_bitvec_toNat (width:=2 ^ k)
      (h_width:=zero_lt_pow_n (m:=2) (n:=k) (h_m:=Nat.zero_lt_two))
    rw [one_toNat_eq]
    have one_shiftRight_eq : 1 >>> 2 ^ (k - 1) = 0 :=
      one_bitvec_shiftRight (d:=2 ^ (k - 1)) (h_d:=by exact Nat.two_pow_pos (k - 1))
    rw [one_shiftRight_eq]
    rw [zero, BitVec.zero_eq]
    have h_sub_middle := sub_middle_of_pow2_with_one_canceled (k:=k) (h_k:=h_k)
    rw [BitVec.dcast_bitvec_eq_zero]
  · simp only
    simp only [BitVec.extractLsb, BitVec.extractLsb']
    simp only [Nat.sub_zero, one, BitVec.toNat_ofNat, Nat.ofNat_pos, pow_pos, Nat.one_mod_two_pow,
      Nat.shiftRight_zero] -- converts BitVec.toNat one >>> 0 into 1#(2 ^ (k - 1))
    rw [BitVec.dcast_bitvec_eq]

lemma join_zero_zero {k : ℕ} (h_k : k > 0) :
    《 zero (k:=k - 1), zero (k:=k - 1) 》 = zero (k:=k) := by
  have h_1 := split_zero h_k
  exact (join_of_split h_k (zero) (zero) (zero) (h_1)).symm

theorem join_zero_one {k : ℕ} (h_k : k > 0) :
    《 zero (k:=k - 1), one (k:=k - 1) 》 = one (k:=k) := by
  have h_1 := split_one h_k
  have res := join_of_split (h_pos:=h_k) (x:=one) (hi_btf:=zero) (lo_btf:=one) (h_1)
  exact res.symm

def equivProd {k : ℕ} (h_k_pos : k > 0) :
    ConcreteBTField k ≃ ConcreteBTField (k - 1) × ConcreteBTField (k - 1) where
  toFun := split h_k_pos
  invFun := fun (hi, lo) => 《 hi, lo 》
  left_inv := fun x => Eq.symm (join_of_split h_k_pos x _ _ rfl)
  right_inv := fun ⟨hi, lo⟩ => Eq.symm (split_of_join h_k_pos _ hi lo rfl)

lemma Z_ne_zero {k : ℕ} : Z k ≠ zero := by
  unfold Z
  simp only [ne_eq]
  if h_k : k = 0 then
    simp only [h_k, ↓reduceDIte]
    exact concrete_one_ne_zero
  else
    have h_k_ne_0 : k ≠ 0 := by omega
    simp only [h_k_ne_0, ↓reduceDIte, ne_eq]
    by_contra h_eq
    conv_rhs at h_eq =>
      rw [←join_zero_zero (k:=k) (h_k:=by omega)]
    rw [join_eq_join_iff] at h_eq
    have h_0_eq_1 := h_eq.1
    have h_0_ne_1 : one (k:=k-1) ≠ zero (k:=k-1) := by exact concrete_one_ne_zero
    contradiction
instance Z_NeZero {k : ℕ} : NeZero (Z k) := { out := Z_ne_zero (k:=k) }

lemma mul_trans_inequality {k : ℕ} (x : ℕ) (h_k : k ≤ 2) (h_x : x ≤ 2 ^ (2 ^ k) - 1) : x < 16 := by
  have x_le_1 : x ≤ 2 ^ (2 ^ k) - 1 := by omega
  have x_le_2 : x ≤ 2 ^ (2 ^ 2) - 1 := by
    apply le_trans x_le_1 -- 2 ^ (2 ^ k) - 1 ≤ 2 ^ (2 ^ 2) - 1
    rw [Nat.sub_le_sub_iff_right]
    rw [Nat.pow_le_pow_iff_right, Nat.pow_le_pow_iff_right]
    exact h_k
    norm_num
    norm_num
    norm_num
  have x_le_15 : x ≤ 15 := by omega
  have x_lt_16 : x < 16 := by omega
  exact x_lt_16

-- Helper : Convert coefficients back to BitVec
def coeffsToBitVec {n : ℕ} (coeffs : List (ZMod 2)) : BitVec n :=
  let val := List.foldr (fun c acc => acc * 2 + c.val) 0 (coeffs.take n)
  BitVec.ofNat n val

-- Karatsuba - like multiplication for binary tower fields
def concrete_mul {k : ℕ} (a b : ConcreteBTField k) : ConcreteBTField k :=
  if h_k_zero : k = 0 then
    if a = zero then zero
    else if b = zero then zero
    else if a = one then b
    else if b = one then a
    else zero -- This case never happens in GF(2)
  else
    have h_k_gt_0 : k > 0 := by omega
    let (a₁, a₀) := split h_k_gt_0 a -- (hi, lo)
    let (b₁, b₀) := split h_k_gt_0 b
    let a_sum := a₁ + a₀
    let b_sum := b₁ + b₀
    let sum_mul := concrete_mul a_sum b_sum
    let prevX := Z (k - 1)
    -- Karatsuba - like step
    let mult_hi := concrete_mul a₁ b₁  -- Recursive call at k - 1
    let mult_lo := concrete_mul a₀ b₀  -- Recursive call at k - 1
    let lo_res := mult_lo + mult_hi -- a₀b₀ + a₁b₁
    let hi_res := sum_mul + lo_res + (concrete_mul mult_hi prevX)
    have h_eq : k - 1 + 1 = k := by omega
    -- Use the proof to cast the type
    have res := 《 hi_res, lo_res 》
    res
termination_by (k, a.toNat, b.toNat)

-- Multiplication instance
instance (k : ℕ) : HMul (ConcreteBTField k) (ConcreteBTField k) (ConcreteBTField k)
  where hMul := concrete_mul

-- Multiplicative inverse
def concrete_inv {k : ℕ} (a : ConcreteBTField k) : ConcreteBTField k :=
  if h_k_zero : k = 0 then
    if a = 0 then 0 else 1
  else
    if h_a_zero : a = 0 then 0
    else if h_a_one : a = 1 then 1
    else
      let h_k_gt_0 : k > 0 := Nat.zero_lt_of_ne_zero h_k_zero
      let (a_hi, a_lo) := split (k:=k) (h:=h_k_gt_0) a
      let prevZ := Z (k - 1)
      let a_lo_next := a_lo + concrete_mul a_hi prevZ
      let delta := concrete_mul a_lo a_lo_next + concrete_mul a_hi a_hi
      let delta_inverse := concrete_inv delta
      let out_hi := concrete_mul delta_inverse a_hi
      let out_lo := concrete_mul delta_inverse a_lo_next
      let res := 《 out_hi, out_lo 》
      res

def concrete_pow_nat {k : ℕ} (x : ConcreteBTField k) (n : ℕ) : ConcreteBTField k :=
  if n = 0 then one
  else if n % 2 = 0 then concrete_pow_nat (concrete_mul x x) (n / 2)
  else concrete_mul x (concrete_pow_nat (concrete_mul x x) (n / 2))

lemma cast_mul (m n : ℕ) {x y : ConcreteBTField m} (h_eq : m = n) :
    (cast (by exact cast_ConcreteBTField_eq m n h_eq) (x * y)) =
  (cast (by exact cast_ConcreteBTField_eq m n h_eq) x) *
  (cast (by exact cast_ConcreteBTField_eq m n h_eq) y) := by
  subst h_eq
  rfl

/- Typeclass instances for algebraic structures -/

instance {k : ℕ} : Mul (ConcreteBTField k) where
  mul := concrete_mul

instance (k : ℕ) : LT (ConcreteBTField k) where
  lt := fun x y => by
    unfold ConcreteBTField at x y
    exact x < y

instance (k : ℕ) : LE (ConcreteBTField k) where
  le := fun x y => by
    unfold ConcreteBTField at x y
    exact x ≤ y

instance (k : ℕ) : Preorder (ConcreteBTField k) where
  le_refl := fun x => BitVec.le_refl x
  le_trans := fun x y z hxy hyz => BitVec.le_trans hxy hyz
  lt := fun x y => x < y
  lt_iff_le_not_ge := fun x y => by
    unfold ConcreteBTField at x y
    have bitvec_statement := (BitVec.not_lt : ¬x < y ↔ y ≤ x)
    -- We need to prove : x < y ↔ x ≤ y ∧ ¬y ≤ x
    constructor
    · -- Forward direction : x < y → x ≤ y ∧ ¬y ≤ x
      intro h_lt
      constructor
      · -- x < y → x ≤ y
        exact BitVec.le_of_lt h_lt
      · -- x < y → ¬y ≤ x
        intro h_le_yx
        have h_not_le := mt bitvec_statement.mpr
        push_neg at h_not_le
        have neg_y_le_x := h_not_le h_lt
        contradiction
    · -- Reverse direction : x ≤ y ∧ ¬y ≤ x → x < y
      intro h
      cases h with | intro h_le_xy h_not_le_yx =>
      have x_lt_y:= mt bitvec_statement.mp h_not_le_yx
      push_neg at x_lt_y
      exact x_lt_y

theorem toNatInRange {k : ℕ} (b : ConcreteBTField k) :
    BitVec.toNat b ≤ 2 ^ (2 ^ k) * 1 := by
  unfold ConcreteBTField at b
  have le_symm : 2 ^ k ≤ 2 ^ k := by omega
  have toNat_le_2pow:= BitVec.toNat_lt_twoPow_of_le (m:=2 ^ k) (n:=(2 ^ k))
  have b_le := toNat_le_2pow le_symm (x:=b)
  omega

theorem eq_zero_or_eq_one {a : ConcreteBTField 0} : a = zero ∨ a = one := by
  unfold ConcreteBTField at a -- Now a is a BitVec (2 ^ 0) = BitVec 1
  have h := BitVec.eq_zero_or_eq_one a
  cases h with
  | inl h_zero =>
    left
    unfold zero
    exact h_zero
  | inr h_one =>
    right
    unfold one
    exact h_one

theorem concrete_eq_zero_or_eq_one {k : ℕ} {a : ConcreteBTField k} (h_k_zero : k = 0) :
    a = zero ∨ a = one := by
  if h_k_zero : k = 0 then
    have h_2_pow_k_eq_1 : 2 ^ k = 1 := by rw [h_k_zero]; norm_num
    let a0 : ConcreteBTField 0 := Eq.mp (congrArg ConcreteBTField h_k_zero) a
    have a0_is_eq_mp_a : a0 = Eq.mp (congrArg ConcreteBTField h_k_zero) a := by rfl
    -- Approach : convert to BitVec.cast and derive equality of the cast for 0 and 1
    rcases eq_zero_or_eq_one (a := a0) with (ha0 | ha1)
    · -- a0 = zero
      left
      -- Transport equality back to ConcreteBTField k
      have : a = Eq.mpr (congrArg ConcreteBTField h_k_zero) a0 := by
        simp only [a0_is_eq_mp_a, eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast, cast_eq]
      rw [this, ha0]
      -- zero (k:=k) = Eq.mpr ... (zero (k:=0))
      have : zero = Eq.mpr (congrArg ConcreteBTField h_k_zero) (zero (k:=0)) := by
        simp only [zero, eq_mpr_eq_cast, BitVec.zero]
        erw [←dcast_eq_root_cast]
        simp only [BitVec.ofNatLT_zero, Nat.pow_zero]
        rw [BitVec.dcast_zero] -- ⊢ 1 = 2 ^ k
        exact h_2_pow_k_eq_1.symm
      rw [this]
    · -- a0 = one
      right
      have : a = Eq.mpr (congrArg ConcreteBTField h_k_zero) a0 := by
        simp only [a0_is_eq_mp_a, eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast, cast_eq]
      rw [this, ha1]
      have : one = Eq.mpr (congrArg ConcreteBTField h_k_zero) (one (k:=0)) := by
        simp only [one, eq_mpr_eq_cast]
        erw [←dcast_eq_root_cast]
        simp only [Nat.pow_zero]
        rw [BitVec.dcast_one] -- ⊢ 1 = 2 ^ k
        exact h_2_pow_k_eq_1.symm
      rw [this]
  else
    contradiction

lemma add_eq_one_iff (a b : ConcreteBTField 0) :
    a + b = 1 ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  rcases eq_zero_or_eq_one (a := a) with (ha | ha) <;>
    rcases eq_zero_or_eq_one (a := b) with (hb | hb) <;>
    simp_all [zero_is_0, one_is_1, add_self_cancel]

instance instInvConcreteBTF {k : ℕ} : Inv (ConcreteBTField k) where
  inv := concrete_inv

lemma concrete_inv_zero {k : ℕ} : concrete_inv (k:=k) 0 = 0 := by
  unfold concrete_inv
  by_cases h_k_zero : k = 0
  · rw [dif_pos h_k_zero]; norm_num
  · rw [dif_neg h_k_zero]; norm_num

lemma concrete_exists_pair_ne {k : ℕ} : ∃ x y : ConcreteBTField k, x ≠ y :=
  ⟨zero (k:=k), one (k:=k), (concrete_one_ne_zero (k:=k)).symm⟩

section FieldLemmasOfLevel0

lemma concrete_zero_mul0 (b : ConcreteBTField 0) :
    concrete_mul (zero (k:=0)) b = zero (k:=0) := by
  unfold concrete_mul
  simp only [↓reduceDIte, zero, Nat.pow_zero, BitVec.zero_eq, ↓reduceIte]

lemma concrete_mul_zero0 (a : ConcreteBTField 0) :
    concrete_mul a (zero (k:=0)) = zero (k:=0) := by
  unfold concrete_mul
  by_cases h : a = zero
  · simp only [↓reduceDIte, h, ↓reduceIte]
  · simp only [↓reduceDIte, zero, Nat.pow_zero, BitVec.zero_eq, ↓reduceIte, ite_self]

lemma concrete_one_mul0 (a : ConcreteBTField 0) :
    concrete_mul (one (k:=0)) a = a := by
  unfold concrete_mul
  by_cases h : a = zero
  · simp [h, zero]
  · norm_num; simp only [concrete_one_ne_zero, ↓reduceIte, h]

lemma concrete_mul_one0 (a : ConcreteBTField 0) :
    concrete_mul a (one (k:=0)) = a := by
  unfold concrete_mul
  by_cases h : a = zero
  · simp [h]
  · norm_num; simp [h, concrete_one_ne_zero]; intro h_eq; exact h_eq.symm

lemma concrete_mul_assoc0 (a b c : ConcreteBTField 0) :
    concrete_mul (concrete_mul a b) c = concrete_mul a (concrete_mul b c) := by
  rcases eq_zero_or_eq_one (a := a) with (ha | ha)
  · simp [ha, concrete_mul]  -- a = zero case
  · rcases eq_zero_or_eq_one (a := b) with (hb | hb)
    · simp [ha, hb, concrete_mul]  -- a = one, b = zero
    · rcases eq_zero_or_eq_one (a := c) with (hc | hc)
      · simp [ha, hb, hc, concrete_mul]  -- a = one, b = one, c = zero
      · simp [ha, hb, hc, concrete_mul, concrete_one_ne_zero]  -- a = one, b = one, c = one

lemma concrete_mul_comm0 (a b : ConcreteBTField 0) :
    concrete_mul a b = concrete_mul b a := by
  rcases eq_zero_or_eq_one (a := a) with (ha | ha)
  · simp [ha, concrete_mul]  -- a = zero
  · rcases eq_zero_or_eq_one (a := b) with (hb | hb)
    · simp [ha, hb, concrete_mul]  -- a = one, b = zero
    · simp [ha, hb, concrete_mul]  -- a = one, b = one

-- Helper lemma : For GF(2), `if x = 0 then 0 else x` is just `x`.
lemma if_zero_then_zero_else_self (x : ConcreteBTField 0) :
    (if x = zero then zero else x) = x := by
  rcases eq_zero_or_eq_one (a := x) with (hx_zero | hx_one)
  · simp only [hx_zero, ↓reduceIte]
  · simp only [hx_one, concrete_one_ne_zero, ↓reduceIte]

lemma concrete_mul_left_distrib0 (a b c : ConcreteBTField 0) :
    concrete_mul a (b + c) = concrete_mul a b + concrete_mul a c := by
  rcases eq_zero_or_eq_one (a := a) with (ha | ha)
  · simp [ha, concrete_mul, zero_is_0]  -- a = zero
  · simp [ha, concrete_mul, zero_is_0, one_is_1];
    rcases eq_zero_or_eq_one (a := b + c) with (hb_add_c | hb_add_c)
    · simp [hb_add_c, zero_is_0];
      rw [zero_is_0] at hb_add_c
      have b_eq_c : b = c := (add_eq_zero_iff_eq b c).mp hb_add_c
      simp only [b_eq_c, add_self_cancel]
    · simp [hb_add_c, one_is_1];
      have c_cases := (add_eq_one_iff b c).mp hb_add_c
      rcases eq_zero_or_eq_one (a := b) with (hb | hb)
      · simp [hb, zero_is_0];
        rw [one_is_1] at hb_add_c
        rw [zero_is_0] at hb
        simp [hb] at c_cases
        have c_ne_0 : c ≠ 0 := by
          simp only [c_cases, ne_eq, one_ne_zero, not_false_eq_true]
        rw [if_neg c_ne_0]
        exact c_cases.symm
      · rw [one_is_1] at hb; simp [hb] at c_cases; simp [hb, c_cases]

lemma concrete_mul_right_distrib0 (a b c : ConcreteBTField 0) :
    concrete_mul (a + b) c = concrete_mul a c + concrete_mul b c := by
  rw [concrete_mul_comm0 (a:=(a + b)) (b:=c)]
  rw [concrete_mul_comm0 (a:=a) (b:=c)]
  rw [concrete_mul_comm0 (a:=b) (b:=c)]
  exact concrete_mul_left_distrib0 (a:=c) (b:=a) (c:=b)

end FieldLemmasOfLevel0

section NumericCasting

-- Natural number casting
def natCast {k : ℕ} (n : ℕ) : ConcreteBTField k := if n % 2 = 0 then zero else one
def natCast_zero {k : ℕ} : natCast (k:=k) 0 = zero := by rfl

def natCast_succ {k : ℕ} (n : ℕ) : natCast (k:=k) (n + 1) = natCast (k:=k) n + 1 := by
  by_cases h : n % 2 = 0
  · -- If n % 2 = 0, then (n + 1) % 2 = 1
    have h_succ : (n + 1) % 2 = 1 := by omega
    simp only [natCast, h, h_succ]; norm_num; rw [one_is_1, zero_is_0, zero_add]
  · -- If n % 2 = 1, then (n + 1) % 2 = 0
    have h_succ : (n + 1) % 2 = 0 := by omega
    simp only [natCast, h, h_succ]; norm_num; rw [one_is_1, zero_is_0, add_self_cancel]

instance {k : ℕ} : NatCast (ConcreteBTField k) where
  natCast n:= natCast n

@[simp]
lemma concrete_natCast_zero_eq_zero {k : ℕ} : natCast 0 = (0 : ConcreteBTField k) := by
  simp only [natCast, Nat.zero_mod, ↓reduceIte, zero_is_0]

@[simp]
lemma concrete_natCast_one_eq_one {k : ℕ} : natCast 1 = (1 : ConcreteBTField k) := by
  simp only [natCast, Nat.mod_succ, one_ne_zero, ↓reduceIte, one_is_1]

-- help simp recognize the NatCast coercion
@[simp] lemma natCast_eq {k : ℕ} (n : ℕ) : (↑n : ConcreteBTField k) = natCast n := rfl

-- Integer casting
def intCast {k : ℕ} (n : ℤ) : ConcreteBTField k := if n % 2 = 0 then zero else one

instance {k : ℕ} : IntCast (ConcreteBTField k) where
  intCast n:= intCast n

def intCast_ofNat {k : ℕ} (n : ℕ) : intCast (k:=k) (n : ℤ) = natCast n := by
  have h_mod_eq : (n : ℤ) % 2 = 0 ↔ n % 2 = 0 := by omega
  by_cases h : n % 2 = 0
  · -- Case : n % 2 = 0
    have h_int : (n : ℤ) % 2 = 0 := h_mod_eq.mpr h
    simp only [intCast, natCast, h, h_int]
  · -- Case : n % 2 ≠ 0
    have h' : n % 2 = 1 := by omega  -- For n : ℕ, if not 0, then 1
    have h_int : (n : ℤ) % 2 = 1 := by omega  -- Coercion preserves modulo
    simp only [intCast, natCast, h_int, h']
    rfl

@[simp] lemma my_neg_mod_two (m : ℤ) : ( - m) % 2 = if m % 2 = 0 then 0 else 1 := by omega
@[simp] lemma mod_two_eq_zero (m : ℤ) : m % 2 = ( - m) % 2 := by omega

def intCast_negSucc {k : ℕ} (n : ℕ) : intCast (k:=k) (Int.negSucc n)
  = - (↑(n + 1) : ConcreteBTField k) := by
  by_cases h_mod : (n + 1) % 2 = 0
  · -- ⊢ intCast (Int.negSucc n) = - ↑(n + 1)
    have h_neg : ( - (n + 1 : ℤ)) % 2 = 0 := by omega
    unfold intCast
    have int_neg_succ : Int.negSucc n = - (n + 1 : ℤ) := by rfl
    rw [int_neg_succ]
    simp only [h_neg]
    have h_nat : (↑(n + 1) : ConcreteBTField k) = (zero : ConcreteBTField k) := by
      simp only [natCast_eq, natCast, h_mod]
      rfl
    rw [h_nat]
    rfl
  · -- ⊢ intCast (Int.negSucc n) = - ↑(n + 1)
    have h_neg : ( - (n + 1 : ℤ)) % 2 = 1 := by omega
    unfold intCast
    have int_neg_succ : Int.negSucc n = - (n + 1 : ℤ) := by rfl
    rw [int_neg_succ]
    simp only [h_neg]
    rw [if_neg (by simp)]
    have h_nat : (↑(n + 1) : ConcreteBTField k) = (one : ConcreteBTField k) := by
      simp only [natCast_eq, natCast, h_mod]
      rfl
    rw [h_nat]
    rfl

instance instHDivConcreteBTF {k : ℕ} : HDiv (ConcreteBTField k) (ConcreteBTField k)
  (ConcreteBTField k) where hDiv a b := a * (concrete_inv b)

lemma concrete_div_eq_mul_inv {k : ℕ} (a b : ConcreteBTField k) : a / b = a * (concrete_inv b) := by
  rfl

instance instHPowConcreteBTFℤ {k : ℕ} : HPow (ConcreteBTField k) ℤ (ConcreteBTField k) where
  hPow a n :=
    match n with
    | Int.ofNat m => concrete_pow_nat a m
    | Int.negSucc m =>
      -- n = - (m + 1)
      if a = 0 then 0
      else concrete_pow_nat (concrete_inv a) (m + 1) -- a ^ ( - (m + 1)) = (a ^ ( - 1)) ^ (m + 1)

end NumericCasting

instance instDivConcreteBTF {k : ℕ} : Div (ConcreteBTField k) where
  div a b := a * (concrete_inv b)

-- Ring properties structure
structure ConcreteBTFRingProps (k : ℕ) extends (ConcreteBTFAddCommGroupProps k) where
  -- Multiplication equations and basic properties
  mul_eq : ∀ (a b : ConcreteBTField k) (h_k : k > 0)
    {a₁ a₀ b₁ b₀ : ConcreteBTField (k - 1)}
    (_h_a : (a₁, a₀) = split h_k a) (_h_b : (b₁, b₀) = split h_k b),
    concrete_mul a b =
      《 concrete_mul a₀ b₁ + concrete_mul b₀ a₁ + concrete_mul (concrete_mul a₁ b₁) (Z (k - 1)),
      concrete_mul a₀ b₀ + concrete_mul a₁ b₁ 》

  -- Zero and one laws
  zero_mul : ∀ a : ConcreteBTField k, concrete_mul zero a = zero
  zero_mul' : ∀ a : ConcreteBTField k, concrete_mul 0 a = 0
  mul_zero : ∀ a : ConcreteBTField k, concrete_mul a zero = zero
  mul_zero' : ∀ a : ConcreteBTField k, concrete_mul a 0 = 0
  one_mul : ∀ a : ConcreteBTField k, concrete_mul one a = a
  mul_one : ∀ a : ConcreteBTField k, concrete_mul a one = a

  -- Associativity and distributivity (Ring axioms)
  mul_assoc : ∀ a b c : ConcreteBTField k, concrete_mul (concrete_mul a b) c
    = concrete_mul a (concrete_mul b c)
  mul_left_distrib : ∀ a b c : ConcreteBTField k, concrete_mul a (b + c)
    = concrete_mul a b + concrete_mul a c
  mul_right_distrib : ∀ a b c : ConcreteBTField k, concrete_mul (a + b) c
    = concrete_mul a c + concrete_mul b c

-- DivisionRing properties structure (extends Ring properties)
structure ConcreteBTFDivisionRingProps (k : ℕ) extends (ConcreteBTFRingProps k) where
  -- Multiplicative inverse property
  mul_inv_cancel : ∀ a : ConcreteBTField k, a ≠ zero → concrete_mul a (concrete_inv a) = one

-- Field properties structure (extends DivisionRing properties)
structure ConcreteBTFieldProps (k : ℕ) extends (ConcreteBTFDivisionRingProps k) where
  -- Commutativity (what makes it a Field vs just a DivisionRing)
  mul_comm : ∀ a b : ConcreteBTField k, concrete_mul a b = concrete_mul b a

@[reducible] def mkRingInstance {k : ℕ} (props : ConcreteBTFieldProps k) : Ring (ConcreteBTField k) where
  toAddCommGroup := mkAddCommGroupInstance
  toOne := inferInstance
  mul := concrete_mul
  mul_assoc := props.mul_assoc
  one_mul := props.one_mul
  mul_one := props.mul_one
  left_distrib := props.mul_left_distrib
  right_distrib := props.mul_right_distrib
  zero_mul := props.zero_mul
  mul_zero := props.mul_zero

  natCast n := natCast n
  natCast_zero := natCast_zero
  natCast_succ n := natCast_succ n
  intCast n := intCast n
  intCast_ofNat n := intCast_ofNat n
  intCast_negSucc n := intCast_negSucc n

@[reducible] def mkDivisionRingInstance {k : ℕ} (props : ConcreteBTFieldProps k) :
    DivisionRing (ConcreteBTField k) where
  toRing := mkRingInstance (k:=k) props
  inv := concrete_inv
  exists_pair_ne := concrete_exists_pair_ne (k := k)
  mul_inv_cancel := props.mul_inv_cancel
  inv_zero := concrete_inv_zero
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)

@[reducible] def mkFieldInstance {k : ℕ} (props : ConcreteBTFieldProps k) : Field (ConcreteBTField k) where
  toDivisionRing := mkDivisionRingInstance (k:=k) props
  mul_comm := props.mul_comm

structure ConcreteBTFStepResult (k : ℕ) extends (ConcreteBTFieldProps k) where
  instFintype : Fintype (ConcreteBTField k)
  fieldFintypeCard : Fintype.card (ConcreteBTField k) = 2^(2^k)
  -- Additional field theory properties for irreducibility proof
  sumZeroIffEq : ∀ (x y : ConcreteBTField k), x + y = 0 ↔ x = y
  traceMapEvalAtRootsIs1 :
    letI := mkFieldInstance (k:=k) (props:=toConcreteBTFieldProps)
    TraceMapProperty (ConcreteBTField k) (u:=Z k) k
  instIrreduciblePoly :
    letI := mkFieldInstance (k:=k) (props:=toConcreteBTFieldProps)
    (Irreducible (p := (definingPoly (s:=(Z k)))))

end FieldOperationsAndInstances

end ConcreteBinaryTower
