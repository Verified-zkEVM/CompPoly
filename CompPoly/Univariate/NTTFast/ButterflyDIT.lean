/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Butterfly
/-! # Bounds-proved radix-four DIT butterflies

Check array ranges once per stage and use machine-word indices inside the loop.
The refinement theorems preserve the existing total functions, including invalid ranges.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Plan

variable {R : Type*}

/-- DIT inner loop with array bounds checked once by its caller. -/
def boundedDIT [Add R] [Sub R] [Mul R] (th tl : Array R) (limit j i0 i1 i2 i3 : Nat) (a : Array R)
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
    let t1 := wl * x1
    let t3 := wl * x3
    let a0 := x0 + t1
    let a1 := x0 - t1
    let a2 := x2 + t3
    let a3 := x2 - t3
    let u2 := w0 * a2
    let u3 := w1 * a3
    let b := a.set i0 (a0 + u2) (by omega)
    have hb : b.size = a.size := Array.size_set ..
    let c := b.set i1 (a1 + u3) (by omega)
    have hc : c.size = a.size := (Array.size_set ..).trans hb
    let d := c.set i2 (a0 - u2) (by omega)
    have hd : d.size = a.size := (Array.size_set ..).trans hc
    let e := d.set i3 (a1 - u3) (by omega)
    have he : e.size = a.size := (Array.size_set ..).trans hd
    boundedDIT th tl limit (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1) e ht
      (by omega)
  else a
termination_by limit - j
decreasing_by omega

/-- Bounds proofs change execution costs, not butterfly results. -/
theorem boundedDIT_eq [Field R] (th tl : Array R) (limit j i0 i1 i2 i3 : Nat) (a : Array R)
    (ht : 2 * limit ≤ th.size ∧ limit ≤ tl.size)
    (ha : i0 + (limit - j) ≤ a.size ∧ i1 + (limit - j) ≤ a.size ∧
      i2 + (limit - j) ≤ a.size ∧ i3 + (limit - j) ≤ a.size) :
    boundedDIT th tl limit j i0 i1 i2 i3 a ht ha =
      butterflyDITRadix4Inner tl th limit j i0 i1 i2 i3 a := by
  rw [boundedDIT, butterflyDITRadix4Inner]
  split
  · rename_i hj
    rw [boundedDIT_eq]
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

/-- Machine-word indices for the bounds-proved butterfly loop. -/
def boundedUDIT [Add R] [Sub R] [Mul R] (th tl : Array R)
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
    let t1 := wl * x1
    let t3 := wl * x3
    let a0 := x0 + t1
    let a1 := x0 - t1
    let a2 := x2 + t3
    let a3 := x2 - t3
    let u2 := w0 * a2
    let u3 := w1 * a3
    let b := a.uset i0 (a0 + u2) (by omega)
    have hb : b.size = a.size := Array.size_uset ..
    let c := b.uset i1 (a1 + u3) (by omega)
    have hc : c.size = a.size := (Array.size_uset ..).trans hb
    let d := c.uset i2 (a0 - u2) (by omega)
    have hd : d.size = a.size := (Array.size_uset ..).trans hc
    let e := d.uset i3 (a1 - u3) (by omega)
    have he : e.size = a.size := (Array.size_uset ..).trans hd
    have hj' := usize_add_one j (by omega)
    have h0' := usize_add_one i0 (by omega)
    have h1' := usize_add_one i1 (by omega)
    have h2' := usize_add_one i2 (by omega)
    have h3' := usize_add_one i3 (by omega)
    boundedUDIT th tl limit (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1) e ht
      (by omega) (by omega)
  else a
termination_by limit.toNat - j.toNat
decreasing_by omega

/-- Machine indices refine the natural-index implementation. -/
theorem boundedUDIT_eq [Field R] (th tl : Array R) (limit j i0 i1 i2 i3 : USize) (a : Array R)
    (ht : 2 * limit.toNat ≤ th.size ∧ limit.toNat ≤ tl.size)
    (ha : i0.toNat + (limit.toNat - j.toNat) ≤ a.size ∧
      i1.toNat + (limit.toNat - j.toNat) ≤ a.size ∧
      i2.toNat + (limit.toNat - j.toNat) ≤ a.size ∧
      i3.toNat + (limit.toNat - j.toNat) ≤ a.size)
    (hu : a.size < USize.size ∧ th.size < USize.size) :
    boundedUDIT th tl limit j i0 i1 i2 i3 a ht ha hu =
      boundedDIT th tl limit.toNat j.toNat i0.toNat i1.toNat i2.toNat i3.toNat a ht ha := by
  rw [boundedUDIT, boundedDIT]
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
    rw [boundedUDIT_eq]
    simp only [hjn, ↓reduceDIte, hj', h0', h1', h2', h3',
      Array.uget, Array.uset_eq_set, hsum]
  · rename_i hj
    have hjn : ¬ j.toNat < limit.toNat := hj
    simp only [hjn, ↓reduceDIte]
termination_by limit.toNat - j.toNat
decreasing_by omega

/-- Use the checked loop for valid ranges, preserving the general API otherwise. -/
@[inline] def checkedDIT [Field R] (th tl : Array R)
    (limit j i0 i1 i2 i3 : Nat) (a : Array R) : Array R :=
  if ht : 2 * limit ≤ th.size ∧ limit ≤ tl.size then
    if ha : i0 + (limit - j) ≤ a.size ∧ i1 + (limit - j) ≤ a.size ∧
        i2 + (limit - j) ≤ a.size ∧ i3 + (limit - j) ≤ a.size then
      if hu : a.size < USize.size ∧ th.size < USize.size then
        if hj : j < limit then
          boundedUDIT th tl (USize.ofNatLT limit (by omega)) (USize.ofNatLT j (by omega))
            (USize.ofNatLT i0 (by omega)) (USize.ofNatLT i1 (by omega))
            (USize.ofNatLT i2 (by omega)) (USize.ofNatLT i3 (by omega)) a ht ha hu
        else a
      else boundedDIT th tl limit j i0 i1 i2 i3 a ht ha
    else butterflyDITRadix4Inner tl th limit j i0 i1 i2 i3 a
  else butterflyDITRadix4Inner tl th limit j i0 i1 i2 i3 a

/-- The range-checked entry point preserves the existing total function. -/
@[simp] theorem checkedDIT_eq [Field R] (th tl : Array R)
    (limit j i0 i1 i2 i3 : Nat) (a : Array R) :
    checkedDIT th tl limit j i0 i1 i2 i3 a =
      butterflyDITRadix4Inner tl th limit j i0 i1 i2 i3 a := by
  unfold checkedDIT
  split
  · split
    · split
      · split
        · exact (boundedUDIT_eq ..).trans (boundedDIT_eq ..)
        · rw [butterflyDITRadix4Inner]; simp_all only [↓reduceIte]
      · exact boundedDIT_eq ..
    · rfl
  · rfl

/-- Process independent radix-four blocks through the checked inner loop. -/
def checkedDITBlocks [Field R] (th tl : Array R) (blockSize quarter blocks block : Nat)
    (a : Array R) : Array R :=
  if block < blocks then
    let base := block * blockSize
    let a := checkedDIT th tl quarter 0 base (base + quarter)
      (base + 2 * quarter) (base + 3 * quarter) a
    checkedDITBlocks th tl blockSize quarter blocks (block + 1) a
  else a
termination_by blocks - block
decreasing_by omega

/-- Block traversal retains the original butterfly schedule. -/
@[simp] theorem checkedDITBlocks_eq [Field R] (th tl : Array R)
    (blockSize quarter blocks block : Nat)
    (a : Array R) : checkedDITBlocks th tl blockSize quarter blocks block a =
      butterflyDITRadix4Blocks tl th blockSize quarter blocks block a := by
  rw [checkedDITBlocks, butterflyDITRadix4Blocks]
  split
  · rw [checkedDITBlocks_eq, checkedDIT_eq]
  · rfl
termination_by blocks - block
decreasing_by omega

/-- The scalar butterfly loop changes coefficients only. -/
@[simp] theorem size_boundedDIT [Add R] [Sub R] [Mul R]
    (th tl : Array R) (limit j i0 i1 i2 i3 : Nat) (a : Array R) (ht) (ha) :
    (boundedDIT th tl limit j i0 i1 i2 i3 a ht ha).size = a.size := by
  rw [boundedDIT]
  split
  · rw [size_boundedDIT]
    simp only [Array.size_set]
  · rfl
termination_by limit - j
decreasing_by omega

/-- Machine-index butterflies preserve the array length. -/
@[simp] theorem size_boundedUDIT [Add R] [Sub R] [Mul R] (th tl : Array R)
    (limit j i0 i1 i2 i3 : USize) (a : Array R) (ht) (ha) (hu) :
    (boundedUDIT th tl limit j i0 i1 i2 i3 a ht ha hu).size = a.size := by
  rw [boundedUDIT]
  split
  · rw [size_boundedUDIT]
    simp only [Array.size_uset]
  · rfl
termination_by limit.toNat - j.toNat
decreasing_by
  have _hj : j.toNat < limit.toNat := ‹j < limit›
  have _hn := usize_add_one j (by omega)
  omega

/-- Machine-index block traversal, with the complete stage range checked once. -/
def stageUBlocksDIT [Add R] [Sub R] [Mul R] (th tl : Array R) (q base : USize) (a : Array R)
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
    let b := boundedUDIT th tl q 0 base (base + q) (base + q + q)
      (base + q + q + q) a ht (by simp only [USize.toNat_zero]; omega) hu
    have hs : b.size = a.size := size_boundedUDIT ..
    stageUBlocksDIT th tl q (base + q + q + q + q) b ht (by omega) remaining
      (by simp only [h4, hs]; rw [Nat.succ_mul] at ha; omega)
termination_by remaining

/-- Hoisting range checks preserves the complete block traversal. -/
theorem stageUBlocksDIT_eq [Field R] (th tl : Array R) (q base : USize) (a : Array R)
    (ht) (hu) (remaining : Nat) (ha) (block : Nat)
    (hb : base.toNat = block * (4 * q.toNat)) :
    stageUBlocksDIT th tl q base a ht hu remaining ha =
      butterflyDITRadix4Blocks tl th (4 * q.toNat) q.toNat (block + remaining) block a := by
  induction remaining generalizing base a block with
  | zero => simp only [stageUBlocksDIT, butterflyDITRadix4Blocks, Nat.add_zero, Nat.lt_irrefl,
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
    rw [stageUBlocksDIT, butterflyDITRadix4Blocks]
    simp only [show block < block + (remaining + 1) by omega, ↓reduceIte]
    rw [ih (base + q + q + q + q) _ _ _ (block + 1) (by rw [h4, hb, Nat.add_mul, Nat.one_mul])]
    simp only [boundedUDIT_eq, boundedDIT_eq, USize.toNat_zero, h1, h2, h3, hb,
      show block + 1 + remaining = block + (remaining + 1) by omega]

/-- Radix-four blocks with the three unit-twiddle products removed. -/
def unitUBlocksDIT [Add R] [Sub R] [Mul R] (w : R) (base : USize) (a : Array R)
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
    let a0 := x0 + x1
    let a1 := x0 - x1
    let a2 := x2 + x3
    let a3 := w * (x2 - x3)
    let y0 := a0 + a2
    let y1 := a1 + a3
    let y2 := a0 - a2
    let y3 := a1 - a3
    let b := a.uset base y0 (by omega)
    have hb : b.size = a.size := Array.size_uset ..
    let c := b.uset (base + 1) y1 (by omega)
    have hc : c.size = a.size := (Array.size_uset ..).trans hb
    let d := c.uset (base + 1 + 1) y2 (by omega)
    have hd : d.size = a.size := (Array.size_uset ..).trans hc
    let e := d.uset (base + 1 + 1 + 1) y3 (by omega)
    have he : e.size = a.size := (Array.size_uset ..).trans hd
    unitUBlocksDIT w (base + 1 + 1 + 1 + 1) e (by omega) remaining (by omega)
termination_by remaining

/-- Unit-twiddle blocks compute the same checked butterflies. -/
theorem unitUBlocksDIT_eq [Field R] (th tl : Array R) (base : USize) (a : Array R)
    (ht : 2 ≤ th.size ∧ 1 ≤ tl.size) (hu : a.size < USize.size ∧ th.size < USize.size)
    (remaining : Nat) (ha : base.toNat + 4 * remaining ≤ a.size)
    (hw : (th.getD 0 0) = 1 ∧ (tl.getD 0 0) = 1) :
    unitUBlocksDIT (th.getD 1 0) base a hu.1 remaining ha =
      stageUBlocksDIT th tl 1 base a (by simpa only [USize.toNat_one] using ht) hu remaining
        (by simpa only [USize.toNat_one, Nat.mul_comm] using ha) := by
  induction remaining generalizing base a with
  | zero => simp only [unitUBlocksDIT, stageUBlocksDIT]
  | succ remaining ih =>
    have hstep : base.toNat + 4 ≤ a.size := by omega
    have h1 : (base + 1).toNat = base.toNat + 1 := usize_add_one base (by omega)
    have h2 : (base + 1 + 1).toNat = base.toNat + 2 := by
      rw [usize_add_one (base + 1) (by omega), h1]
    have h3 : (base + 1 + 1 + 1).toNat = base.toNat + 3 := by
      rw [usize_add_one (base + 1 + 1) (by omega), h2]
    have h4 : (base + 1 + 1 + 1 + 1).toNat = base.toNat + 4 := by
      rw [usize_add_one (base + 1 + 1 + 1) (by omega), h3]
    rw [unitUBlocksDIT, stageUBlocksDIT]
    rw [ih _ _ (by simpa only [Array.size_uset] using hu)]
    simp only [boundedUDIT, USize.lt_iff_toNat_lt, USize.toNat_zero, USize.toNat_one,
      Nat.zero_lt_one, Nat.lt_irrefl, USize.zero_add, ↓reduceDIte,
      Array.uget, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (show 0 < th.size by omega),
      Array.getElem?_eq_getElem (show 1 < th.size by omega),
      Array.getElem?_eq_getElem (show 0 < tl.size by omega), Option.getD_some] at hw ⊢
    simp only [hw.1, hw.2, one_mul]

/-- Check a complete radix-four stage before its machine-index traversal. -/
def stageBlocksDIT [Field R] [DecidableEq R] (th tl : Array R)
    (blockSize quarter blocks block : Nat) (a : Array R) : Array R :=
  if hh : blockSize = 4 * quarter ∧ 0 < quarter ∧ block ≤ blocks ∧
      blocks * blockSize ≤ a.size ∧ 2 * quarter ≤ th.size ∧ quarter ≤ tl.size ∧
      a.size < USize.size ∧ th.size < USize.size then
    if hz : quarter = 1 ∧ (th.getD 0 0) = 1 ∧ (tl.getD 0 0) = 1 then
      unitUBlocksDIT (th.getD 1 0) (USize.ofNatLT (block * blockSize) (by
        have := Nat.mul_le_mul_right blockSize hh.2.2.1; omega)) a hh.2.2.2.2.2.2.1
        (blocks - block) (by
          simp only [USize.toNat_ofNatLT]
          have he : block * blockSize + (blocks - block) * blockSize = blocks * blockSize := by
            rw [← Nat.add_mul, Nat.add_sub_of_le hh.2.2.1]
          have hb : blockSize = 4 := by simp only [hh.1, hz.1, Nat.mul_one]
          rw [Nat.mul_comm 4, ← hb, he]; exact hh.2.2.2.1)
    else
      stageUBlocksDIT th tl (USize.ofNatLT quarter (by omega))
        (USize.ofNatLT (block * blockSize) (by
          have := Nat.mul_le_mul_right blockSize hh.2.2.1
          omega)) a ⟨hh.2.2.2.2.1, hh.2.2.2.2.2.1⟩
        ⟨hh.2.2.2.2.2.2.1, hh.2.2.2.2.2.2.2⟩ (blocks - block) (by
          simp only [USize.toNat_ofNatLT]
          have he : block * blockSize + (blocks - block) * blockSize = blocks * blockSize := by
            rw [← Nat.add_mul, Nat.add_sub_of_le hh.2.2.1]
          rw [← hh.1, he]; exact hh.2.2.2.1)
  else checkedDITBlocks th tl blockSize quarter blocks block a

@[simp] theorem stageBlocksDIT_eq [Field R] [DecidableEq R] (th tl : Array R)
    (blockSize quarter blocks block : Nat) (a : Array R) :
    stageBlocksDIT th tl blockSize quarter blocks block a =
      checkedDITBlocks th tl blockSize quarter blocks block a := by
  unfold stageBlocksDIT
  split
  · rename_i hh
    split
    · rename_i hz
      rw [unitUBlocksDIT_eq (th := th) (tl := tl)
        (ht := by simpa only [hz.1, Nat.mul_one] using
          And.intro hh.2.2.2.2.1 hh.2.2.2.2.2.1)
        (hu := ⟨hh.2.2.2.2.2.2.1, hh.2.2.2.2.2.2.2⟩) (hw := hz.2)]
      rw [stageUBlocksDIT_eq (block := block) (hb := by
        simp only [USize.toNat_ofNatLT, USize.toNat_one]; rw [hh.1, hz.1])]
      simp only [USize.toNat_one, Nat.mul_one,
        show blockSize = 4 by simp only [hh.1, hz.1, Nat.mul_one], hz.1,
        Nat.add_sub_of_le hh.2.2.1, checkedDITBlocks_eq]
    · rw [stageUBlocksDIT_eq (block := block) (hb := by
        simp only [USize.toNat_ofNatLT]; rw [hh.1])]
      simp only [USize.toNat_ofNatLT, ← hh.1,
        Nat.add_sub_of_le hh.2.2.1, checkedDITBlocks_eq]
  · rfl

/-- Planned DIT transform with bounds outside the hot butterfly loops. -/
def checkedDITStages [Field R] [DecidableEq R] (D : NTT.Domain R) (tw : Array (Array R))
    (a : Array R) : Array R := Id.run do
  let mut a := a
  for pass in [0:D.logN / 2] do
    let low := 2 * pass
    let high := low + 1
    let blockSize := 2 ^ (low + 2)
    let quarter := 2 ^ low
    a := stageBlocksDIT (tw.getD high #[]) (tw.getD low #[])
      blockSize quarter (D.n / blockSize) 0 a
  if D.logN % 2 = 1 then
    a := butterflyStageWithTwiddles D (D.logN - 1) (tw.getD (D.logN - 1) #[]) a
  return a

/-- The checked transform agrees with the verified planned transform. -/
theorem checkedDITStages_eq [Field R] [DecidableEq R] (D : NTT.Domain R)
    (tw : Array (Array R)) (a : Array R) :
    checkedDITStages D tw a = runStagesRadix4WithTwiddles D tw a := by
  simp only [checkedDITStages, runStagesRadix4WithTwiddles,
    butterflyRadix4StageWithTwiddles, stageBlocksDIT_eq, checkedDITBlocks_eq]

/-- Inverse variant using the bounds-proved DIT loops. -/
@[inline] def checkedInverse [Field R] [DecidableEq R] (P : Plan R) (a : Array R) : Array R :=
  P.normalize (checkedDITStages P.inverseDomain P.inverseTwiddles a)

/-- The bounds-proved variant agrees with the existing plan entry point. -/
theorem inverseImpl_eq_checked [Field R] [DecidableEq R] (P : Plan R) (a : Array R) :
    inverseImpl P a = checkedInverse P a := by
  simp only [inverseImpl, checkedInverse, checkedDITStages_eq]

end CompPoly.CPolynomial.NTTFast.Plan
