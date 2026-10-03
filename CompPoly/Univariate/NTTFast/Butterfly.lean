/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Plan
/-! # Bounds-proved radix-four DIF butterflies

Check array ranges once per stage and use machine-word indices inside the loop.
The refinement theorems preserve the existing total functions, including invalid ranges.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Plan

variable {R : Type*}

/-- DIF inner loop with array bounds checked once by its caller. -/
def boundedDIF [Add R] [Sub R] [Mul R] (th tl : Array R) (limit j i0 i1 i2 i3 : Nat) (a : Array R)
    (ht : 2 * limit ≤ th.size ∧ limit ≤ tl.size)
    (ha : i0 + (limit - j) ≤ a.size ∧ i1 + (limit - j) ≤ a.size ∧
      i2 + (limit - j) ≤ a.size ∧ i3 + (limit - j) ≤ a.size) : Array R :=
  if hj : j < limit then
    let w0 := th[j]'(by omega)
    let w1 := th[j + limit]'(by omega)
    let wl := tl[j]'(by omega)
    let x0 := a[i0]'(by omega)
    let x1 := a[i1]'(by omega)
    let x2 := a[i2]'(by omega)
    let x3 := a[i3]'(by omega)
    let a0 := x0 + x2
    let a2 := w0 * (x0 - x2)
    let a1 := x1 + x3
    let a3 := w1 * (x1 - x3)
    let b := a.set i0 (a0 + a1) (by omega)
    have hb : b.size = a.size := Array.size_set ..
    let c := b.set i1 (wl * (a0 - a1)) (by omega)
    have hc : c.size = a.size := (Array.size_set ..).trans hb
    let d := c.set i2 (a2 + a3) (by omega)
    have hd : d.size = a.size := (Array.size_set ..).trans hc
    let e := d.set i3 (wl * (a2 - a3)) (by omega)
    have he : e.size = a.size := (Array.size_set ..).trans hd
    boundedDIF th tl limit (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1) e ht
      (by omega)
  else a
termination_by limit - j
decreasing_by omega

/-- Bounds proofs change execution costs, not butterfly results. -/
theorem boundedDIF_eq [Field R] (th tl : Array R) (limit j i0 i1 i2 i3 : Nat) (a : Array R)
    (ht : 2 * limit ≤ th.size ∧ limit ≤ tl.size)
    (ha : i0 + (limit - j) ≤ a.size ∧ i1 + (limit - j) ≤ a.size ∧
      i2 + (limit - j) ≤ a.size ∧ i3 + (limit - j) ≤ a.size) :
    boundedDIF th tl limit j i0 i1 i2 i3 a ht ha =
      butterflyDIFRadix4Inner th tl limit j i0 i1 i2 i3 a := by
  rw [boundedDIF, butterflyDIFRadix4Inner]
  split
  · rename_i hj
    rw [boundedDIF_eq]
    have h0 : i0 < a.size := by omega
    have h1 : i1 < a.size := by omega
    have h2 : i2 < a.size := by omega
    have h3 : i3 < a.size := by omega
    have hw0 : j < th.size := by omega
    have hw1 : j + limit < th.size := by omega
    have hwl : j < tl.size := by omega
    simp only [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem h0, Array.getElem?_eq_getElem h1,
      Array.getElem?_eq_getElem h2, Array.getElem?_eq_getElem h3,
      Array.getElem?_eq_getElem hw0, Array.getElem?_eq_getElem hw1,
      Array.getElem?_eq_getElem hwl, Option.getD_some,
      Array.set!_eq_setIfInBounds, Array.setIfInBounds, Array.size_set,
      h0, h1, h2, h3, ↓reduceDIte]
  · rfl
termination_by limit - j
decreasing_by omega

theorem usize_add_one (i : USize) (h : i.toNat + 1 < USize.size) :
    (i + 1).toNat = i.toNat + 1 := by
  simp only [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt h]

/-- Machine-word indices for the bounds-proved butterfly loop. -/
def boundedUDIF [Add R] [Sub R] [Mul R] (th tl : Array R)
    (limit j i0 i1 i2 i3 : USize) (a : Array R)
    (ht : 2 * limit.toNat ≤ th.size ∧ limit.toNat ≤ tl.size)
    (ha : i0.toNat + (limit.toNat - j.toNat) ≤ a.size ∧
      i1.toNat + (limit.toNat - j.toNat) ≤ a.size ∧
      i2.toNat + (limit.toNat - j.toNat) ≤ a.size ∧
      i3.toNat + (limit.toNat - j.toNat) ≤ a.size)
    (hu : a.size < USize.size ∧ th.size < USize.size) : Array R :=
  if hj : j < limit then
    have hjn : j.toNat < limit.toNat := hj
    have hsum : (j + limit).toNat = j.toNat + limit.toNat := by
      rw [USize.toNat_add]
      exact Nat.mod_eq_of_lt (show j.toNat + limit.toNat < USize.size by omega)
    let w0 := th.uget j (by omega)
    let w1 := th.uget (j + limit) (by omega)
    let wl := tl.uget j (by omega)
    let x0 := a.uget i0 (by omega)
    let x1 := a.uget i1 (by omega)
    let x2 := a.uget i2 (by omega)
    let x3 := a.uget i3 (by omega)
    let a0 := x0 + x2
    let a2 := w0 * (x0 - x2)
    let a1 := x1 + x3
    let a3 := w1 * (x1 - x3)
    let b := a.uset i0 (a0 + a1) (by omega)
    have hb : b.size = a.size := Array.size_uset ..
    let c := b.uset i1 (wl * (a0 - a1)) (by omega)
    have hc : c.size = a.size := (Array.size_uset ..).trans hb
    let d := c.uset i2 (a2 + a3) (by omega)
    have hd : d.size = a.size := (Array.size_uset ..).trans hc
    let e := d.uset i3 (wl * (a2 - a3)) (by omega)
    have he : e.size = a.size := (Array.size_uset ..).trans hd
    have hj' := usize_add_one j (by omega)
    have h0' := usize_add_one i0 (by omega)
    have h1' := usize_add_one i1 (by omega)
    have h2' := usize_add_one i2 (by omega)
    have h3' := usize_add_one i3 (by omega)
    boundedUDIF th tl limit (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1) e ht
      (by omega) (by omega)
  else a
termination_by limit.toNat - j.toNat
decreasing_by omega

/-- Machine indices refine the natural-index implementation. -/
theorem boundedUDIF_eq [Field R] (th tl : Array R) (limit j i0 i1 i2 i3 : USize) (a : Array R)
    (ht : 2 * limit.toNat ≤ th.size ∧ limit.toNat ≤ tl.size)
    (ha : i0.toNat + (limit.toNat - j.toNat) ≤ a.size ∧
      i1.toNat + (limit.toNat - j.toNat) ≤ a.size ∧
      i2.toNat + (limit.toNat - j.toNat) ≤ a.size ∧
      i3.toNat + (limit.toNat - j.toNat) ≤ a.size)
    (hu : a.size < USize.size ∧ th.size < USize.size) :
    boundedUDIF th tl limit j i0 i1 i2 i3 a ht ha hu =
      boundedDIF th tl limit.toNat j.toNat i0.toNat i1.toNat i2.toNat i3.toNat a ht ha := by
  rw [boundedUDIF, boundedDIF]
  split
  · rename_i hj
    have hjn : j.toNat < limit.toNat := hj
    have hsum : (j + limit).toNat = j.toNat + limit.toNat := by
      rw [USize.toNat_add]
      exact Nat.mod_eq_of_lt (show j.toNat + limit.toNat < USize.size by omega)
    have hj' := usize_add_one j (by omega)
    have h0' := usize_add_one i0 (by omega)
    have h1' := usize_add_one i1 (by omega)
    have h2' := usize_add_one i2 (by omega)
    have h3' := usize_add_one i3 (by omega)
    rw [boundedUDIF_eq]
    simp only [hjn, ↓reduceDIte, hj', h0', h1', h2', h3',
      Array.uget, Array.uset_eq_set, hsum]
  · rename_i hj
    have hjn : ¬ j.toNat < limit.toNat := hj
    simp only [hjn, ↓reduceDIte]
termination_by limit.toNat - j.toNat
decreasing_by omega

/-- Use the checked loop for valid ranges, preserving the general API otherwise. -/
@[inline] def checkedDIF [Field R] (th tl : Array R)
    (limit j i0 i1 i2 i3 : Nat) (a : Array R) : Array R :=
  if ht : 2 * limit ≤ th.size ∧ limit ≤ tl.size then
    if ha : i0 + (limit - j) ≤ a.size ∧ i1 + (limit - j) ≤ a.size ∧
        i2 + (limit - j) ≤ a.size ∧ i3 + (limit - j) ≤ a.size then
      if hu : a.size < USize.size ∧ th.size < USize.size then
        if hj : j < limit then
          boundedUDIF th tl (USize.ofNatLT limit (by omega)) (USize.ofNatLT j (by omega))
            (USize.ofNatLT i0 (by omega)) (USize.ofNatLT i1 (by omega))
            (USize.ofNatLT i2 (by omega)) (USize.ofNatLT i3 (by omega)) a ht ha hu
        else a
      else boundedDIF th tl limit j i0 i1 i2 i3 a ht ha
    else butterflyDIFRadix4Inner th tl limit j i0 i1 i2 i3 a
  else butterflyDIFRadix4Inner th tl limit j i0 i1 i2 i3 a

/-- The range-checked entry point preserves the existing total function. -/
@[simp] theorem checkedDIF_eq [Field R] (th tl : Array R)
    (limit j i0 i1 i2 i3 : Nat) (a : Array R) :
    checkedDIF th tl limit j i0 i1 i2 i3 a =
      butterflyDIFRadix4Inner th tl limit j i0 i1 i2 i3 a := by
  unfold checkedDIF
  split
  · split
    · split
      · split
        · exact (boundedUDIF_eq ..).trans (boundedDIF_eq ..)
        · rw [butterflyDIFRadix4Inner]; simp_all only [↓reduceIte]
      · exact boundedDIF_eq ..
    · rfl
  · rfl

/-- Process independent radix-four blocks through the checked inner loop. -/
def checkedBlocks [Field R] (th tl : Array R) (blockSize quarter blocks block : Nat)
    (a : Array R) : Array R :=
  if block < blocks then
    let base := block * blockSize
    let a := checkedDIF th tl quarter 0 base (base + quarter)
      (base + 2 * quarter) (base + 3 * quarter) a
    checkedBlocks th tl blockSize quarter blocks (block + 1) a
  else a
termination_by blocks - block
decreasing_by omega

/-- Block traversal retains the original butterfly schedule. -/
@[simp] theorem checkedBlocks_eq [Field R] (th tl : Array R) (blockSize quarter blocks block : Nat)
    (a : Array R) : checkedBlocks th tl blockSize quarter blocks block a =
      butterflyDIFRadix4Blocks th tl blockSize quarter blocks block a := by
  rw [checkedBlocks, butterflyDIFRadix4Blocks]
  split
  · rw [checkedBlocks_eq, checkedDIF_eq]
  · rfl
termination_by blocks - block
decreasing_by omega

/-- The scalar butterfly loop changes coefficients only. -/
@[simp] theorem size_boundedDIF [Add R] [Sub R] [Mul R]
    (th tl : Array R) (limit j i0 i1 i2 i3 : Nat) (a : Array R) (ht) (ha) :
    (boundedDIF th tl limit j i0 i1 i2 i3 a ht ha).size = a.size := by
  rw [boundedDIF]
  split
  · rw [size_boundedDIF]
    simp only [Array.size_set]
  · rfl
termination_by limit - j
decreasing_by omega

/-- Machine-index butterflies preserve the array length. -/
@[simp] theorem size_boundedUDIF [Add R] [Sub R] [Mul R] (th tl : Array R)
    (limit j i0 i1 i2 i3 : USize) (a : Array R) (ht) (ha) (hu) :
    (boundedUDIF th tl limit j i0 i1 i2 i3 a ht ha hu).size = a.size := by
  rw [boundedUDIF]
  split
  · rw [size_boundedUDIF]
    simp only [Array.size_uset]
  · rfl
termination_by limit.toNat - j.toNat
decreasing_by
  have _hj : j.toNat < limit.toNat := ‹j < limit›
  have _hn := usize_add_one j (by omega)
  omega

/-- Machine-index block traversal, with the complete stage range checked once. -/
def stageUBlocksDIF [Add R] [Sub R] [Mul R] (th tl : Array R) (q base : USize) (a : Array R)
    (ht : 2 * q.toNat ≤ th.size ∧ q.toNat ≤ tl.size)
    (hu : a.size < USize.size ∧ th.size < USize.size)
    (remaining : Nat) (ha : base.toNat + remaining * (4 * q.toNat) ≤ a.size) : Array R :=
  match remaining with
  | 0 => a
  | remaining + 1 =>
    have hstep : base.toNat + 4 * q.toNat ≤ a.size := by
      have hm : 4 * q.toNat ≤ (remaining + 1) * (4 * q.toNat) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    have h1 : (base + q).toNat = base.toNat + q.toNat := by
      rw [USize.toNat_add]
      exact Nat.mod_eq_of_lt (show base.toNat + q.toNat < USize.size by omega)
    have h2 : (base + q + q).toNat = base.toNat + 2 * q.toNat := by
      rw [USize.toNat_add, h1]
      exact (Nat.mod_eq_of_lt (show base.toNat + q.toNat + q.toNat < USize.size by omega)).trans
        (by omega)
    have h3 : (base + q + q + q).toNat = base.toNat + 3 * q.toNat := by
      rw [USize.toNat_add, h2]
      exact (Nat.mod_eq_of_lt (show base.toNat + 2 * q.toNat + q.toNat < USize.size by omega)).trans
        (by omega)
    have h4 : (base + q + q + q + q).toNat = base.toNat + 4 * q.toNat := by
      rw [USize.toNat_add, h3]
      exact (Nat.mod_eq_of_lt (show base.toNat + 3 * q.toNat + q.toNat < USize.size by omega)).trans
        (by omega)
    let b := boundedUDIF th tl q 0 base (base + q) (base + q + q)
      (base + q + q + q) a ht (by simp only [USize.toNat_zero]; omega) hu
    have hs : b.size = a.size := size_boundedUDIF ..
    stageUBlocksDIF th tl q (base + q + q + q + q) b ht (by omega) remaining
      (by simp only [h4, hs]; rw [Nat.succ_mul] at ha; omega)
termination_by remaining

/-- Hoisting range checks preserves the complete block traversal. -/
theorem stageUBlocksDIF_eq [Field R] (th tl : Array R) (q base : USize) (a : Array R)
    (ht) (hu) (remaining : Nat) (ha) (block : Nat)
    (hb : base.toNat = block * (4 * q.toNat)) :
    stageUBlocksDIF th tl q base a ht hu remaining ha =
      butterflyDIFRadix4Blocks th tl (4 * q.toNat) q.toNat (block + remaining) block a := by
  induction remaining generalizing base a block with
  | zero => simp only [stageUBlocksDIF, butterflyDIFRadix4Blocks, Nat.add_zero, Nat.lt_irrefl,
      ↓reduceIte]
  | succ remaining ih =>
    have hstep : base.toNat + 4 * q.toNat ≤ a.size := by
      have hm : 4 * q.toNat ≤ (remaining + 1) * (4 * q.toNat) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    have h1 : (base + q).toNat = base.toNat + q.toNat := by
      rw [USize.toNat_add]
      exact Nat.mod_eq_of_lt (show base.toNat + q.toNat < USize.size by omega)
    have h2 : (base + q + q).toNat = base.toNat + 2 * q.toNat := by
      rw [USize.toNat_add, h1]
      exact (Nat.mod_eq_of_lt (show base.toNat + q.toNat + q.toNat < USize.size by omega)).trans
        (by omega)
    have h3 : (base + q + q + q).toNat = base.toNat + 3 * q.toNat := by
      rw [USize.toNat_add, h2]
      exact (Nat.mod_eq_of_lt (show base.toNat + 2 * q.toNat + q.toNat < USize.size by omega)).trans
        (by omega)
    have h4 : (base + q + q + q + q).toNat = base.toNat + 4 * q.toNat := by
      rw [USize.toNat_add, h3]
      exact (Nat.mod_eq_of_lt (show base.toNat + 3 * q.toNat + q.toNat < USize.size by omega)).trans
        (by omega)
    rw [stageUBlocksDIF, butterflyDIFRadix4Blocks]
    simp only [show block < block + (remaining + 1) by omega, ↓reduceIte]
    rw [ih (base + q + q + q + q) _ _ _ (block + 1) (by rw [h4, hb, Nat.add_mul, Nat.one_mul])]
    simp only [boundedUDIF_eq, boundedDIF_eq, USize.toNat_zero, h1, h2, h3, hb,
      show block + 1 + remaining = block + (remaining + 1) by omega]

/-- Radix-four blocks with the three unit-twiddle products removed. -/
def unitUBlocksDIF [Add R] [Sub R] [Mul R] (w : R) (base : USize) (a : Array R)
    (hu : a.size < USize.size) (remaining : Nat)
    (ha : base.toNat + 4 * remaining ≤ a.size) : Array R :=
  match remaining with
  | 0 => a
  | remaining + 1 =>
    have hstep : base.toNat + 4 ≤ a.size := by omega
    have h1 : (base + 1).toNat = base.toNat + 1 := usize_add_one base (by omega)
    have h2 : (base + 1 + 1).toNat = base.toNat + 2 := by
      rw [usize_add_one (base + 1) (by omega), h1]
    have h3 : (base + 1 + 1 + 1).toNat = base.toNat + 3 := by
      rw [usize_add_one (base + 1 + 1) (by omega), h2]
    have h4 : (base + 1 + 1 + 1 + 1).toNat = base.toNat + 4 := by
      rw [usize_add_one (base + 1 + 1 + 1) (by omega), h3]
    let x0 := a.uget base (by omega)
    let x1 := a.uget (base + 1) (by omega)
    let x2 := a.uget (base + 1 + 1) (by omega)
    let x3 := a.uget (base + 1 + 1 + 1) (by omega)
    let a0 := x0 + x2
    let a2 := x0 - x2
    let a1 := x1 + x3
    let a3 := w * (x1 - x3)
    let y0 := a0 + a1
    let y1 := a0 - a1
    let y2 := a2 + a3
    let y3 := a2 - a3
    let b := a.uset base y0 (by omega)
    have hb : b.size = a.size := Array.size_uset ..
    let c := b.uset (base + 1) y1 (by omega)
    have hc : c.size = a.size := (Array.size_uset ..).trans hb
    let d := c.uset (base + 1 + 1) y2 (by omega)
    have hd : d.size = a.size := (Array.size_uset ..).trans hc
    let e := d.uset (base + 1 + 1 + 1) y3 (by omega)
    have he : e.size = a.size := (Array.size_uset ..).trans hd
    unitUBlocksDIF w (base + 1 + 1 + 1 + 1) e (by omega) remaining (by omega)
termination_by remaining

/-- Unit-twiddle blocks compute the same checked butterflies. -/
theorem unitUBlocksDIF_eq [Field R] (th tl : Array R) (base : USize) (a : Array R)
    (ht : 2 ≤ th.size ∧ 1 ≤ tl.size) (hu : a.size < USize.size ∧ th.size < USize.size)
    (remaining : Nat) (ha : base.toNat + 4 * remaining ≤ a.size)
    (hw : (th.getD 0 0) = 1 ∧ (tl.getD 0 0) = 1) :
    unitUBlocksDIF (th.getD 1 0) base a hu.1 remaining ha =
      stageUBlocksDIF th tl 1 base a (by simpa only [USize.toNat_one] using ht) hu remaining
        (by simpa only [USize.toNat_one, Nat.mul_comm] using ha) := by
  induction remaining generalizing base a with
  | zero => simp only [unitUBlocksDIF, stageUBlocksDIF]
  | succ remaining ih =>
    have hstep : base.toNat + 4 ≤ a.size := by omega
    have h1 : (base + 1).toNat = base.toNat + 1 := usize_add_one base (by omega)
    have h2 : (base + 1 + 1).toNat = base.toNat + 2 := by
      rw [usize_add_one (base + 1) (by omega), h1]
    have h3 : (base + 1 + 1 + 1).toNat = base.toNat + 3 := by
      rw [usize_add_one (base + 1 + 1) (by omega), h2]
    have h4 : (base + 1 + 1 + 1 + 1).toNat = base.toNat + 4 := by
      rw [usize_add_one (base + 1 + 1 + 1) (by omega), h3]
    rw [unitUBlocksDIF, stageUBlocksDIF]
    rw [ih _ _ (by simpa only [Array.size_uset] using hu)]
    simp only [boundedUDIF, USize.lt_iff_toNat_lt, USize.toNat_zero, USize.toNat_one,
      Nat.zero_lt_one, Nat.lt_irrefl, USize.zero_add, ↓reduceDIte,
      Array.uget, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (show 0 < th.size by omega),
      Array.getElem?_eq_getElem (show 1 < th.size by omega),
      Array.getElem?_eq_getElem (show 0 < tl.size by omega), Option.getD_some] at hw ⊢
    simp only [hw.1, hw.2, one_mul]

/-- Check a complete radix-four stage before its machine-index traversal. -/
def stageBlocksDIF [Field R] [DecidableEq R] (th tl : Array R)
    (blockSize quarter blocks block : Nat) (a : Array R) : Array R :=
  if hh : blockSize = 4 * quarter ∧ 0 < quarter ∧ block ≤ blocks ∧
      blocks * blockSize ≤ a.size ∧ 2 * quarter ≤ th.size ∧ quarter ≤ tl.size ∧
      a.size < USize.size ∧ th.size < USize.size then
    if hz : quarter = 1 ∧ (th.getD 0 0) = 1 ∧ (tl.getD 0 0) = 1 then
      unitUBlocksDIF (th.getD 1 0) (USize.ofNatLT (block * blockSize) (by
        have := Nat.mul_le_mul_right blockSize hh.2.2.1; omega)) a hh.2.2.2.2.2.2.1
        (blocks - block) (by
          simp only [USize.toNat_ofNatLT]
          have he : block * blockSize + (blocks - block) * blockSize = blocks * blockSize := by
            rw [← Nat.add_mul, Nat.add_sub_of_le hh.2.2.1]
          have hb : blockSize = 4 := by simp only [hh.1, hz.1, Nat.mul_one]
          rw [Nat.mul_comm 4, ← hb, he]; exact hh.2.2.2.1)
    else
      stageUBlocksDIF th tl (USize.ofNatLT quarter (by omega))
        (USize.ofNatLT (block * blockSize) (by
          have := Nat.mul_le_mul_right blockSize hh.2.2.1
          omega)) a ⟨hh.2.2.2.2.1, hh.2.2.2.2.2.1⟩
        ⟨hh.2.2.2.2.2.2.1, hh.2.2.2.2.2.2.2⟩ (blocks - block) (by
          simp only [USize.toNat_ofNatLT]
          have he : block * blockSize + (blocks - block) * blockSize = blocks * blockSize := by
            rw [← Nat.add_mul, Nat.add_sub_of_le hh.2.2.1]
          rw [← hh.1, he]; exact hh.2.2.2.1)
  else checkedBlocks th tl blockSize quarter blocks block a

@[simp] theorem stageBlocksDIF_eq [Field R] [DecidableEq R] (th tl : Array R)
    (blockSize quarter blocks block : Nat) (a : Array R) :
    stageBlocksDIF th tl blockSize quarter blocks block a =
      checkedBlocks th tl blockSize quarter blocks block a := by
  unfold stageBlocksDIF
  split
  · rename_i hh
    split
    · rename_i hz
      rw [unitUBlocksDIF_eq (th := th) (tl := tl)
        (ht := by simpa only [hz.1, Nat.mul_one] using
          And.intro hh.2.2.2.2.1 hh.2.2.2.2.2.1)
        (hu := ⟨hh.2.2.2.2.2.2.1, hh.2.2.2.2.2.2.2⟩) (hw := hz.2)]
      rw [stageUBlocksDIF_eq (block := block) (hb := by
        simp only [USize.toNat_ofNatLT, USize.toNat_one]; rw [hh.1, hz.1])]
      simp only [USize.toNat_one, Nat.mul_one,
        show blockSize = 4 by simp only [hh.1, hz.1, Nat.mul_one], hz.1,
        Nat.add_sub_of_le hh.2.2.1, checkedBlocks_eq]
    · rw [stageUBlocksDIF_eq (block := block) (hb := by
        simp only [USize.toNat_ofNatLT]; rw [hh.1])]
      simp only [USize.toNat_ofNatLT, ← hh.1,
        Nat.add_sub_of_le hh.2.2.1, checkedBlocks_eq]
  · rfl

/-- Planned DIF transform with bounds outside the hot butterfly loops. -/
def checkedStages [Field R] [DecidableEq R] (D : NTT.Domain R) (tw : Array (Array R))
    (a : Array R) : Array R := Id.run do
  let mut a := a
  for pass in [0:D.logN / 2] do
    let high := D.logN - 1 - 2 * pass
    let low := high - 1
    let blockSize := 2 ^ (low + 2)
    let quarter := 2 ^ low
    a := stageBlocksDIF (tw.getD high #[]) (tw.getD low #[])
      blockSize quarter (D.n / blockSize) 0 a
  if D.logN % 2 = 1 then
    a := butterflyStageDIFWithTwiddles D 0 (tw.getD 0 #[]) a
  return a

/-- The checked transform agrees with the verified planned transform. -/
theorem checkedStages_eq [Field R] [DecidableEq R] (D : NTT.Domain R)
    (tw : Array (Array R)) (a : Array R) :
    checkedStages D tw a = runStagesDIFRadix4WithTwiddles D tw a := by
  simp only [checkedStages, runStagesDIFRadix4WithTwiddles,
    butterflyRadix4StageDIFWithTwiddles, stageBlocksDIF_eq, checkedBlocks_eq]

/-- Forward variant using the bounds-proved DIF loops. -/
@[inline] def checkedForward [Field R] [DecidableEq R] (P : Plan R) (a : Array R) : Array R :=
  checkedStages P.domain P.twiddles (NTT.loadNaturalArray P.domain a)

/-- The bounds-proved variant agrees with the existing plan entry point. -/
theorem forwardImpl_eq_checked [Field R] [DecidableEq R] (P : Plan R) (a : Array R) :
    forwardImpl P a = checkedForward P a := by
  simp only [forwardImpl, checkedForward, checkedStages_eq]

end CompPoly.CPolynomial.NTTFast.Plan
