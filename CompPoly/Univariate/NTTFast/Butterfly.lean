/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Plan
/-! # Bounds-proved radix-four DIF butterflies

Check array ranges once per block and use machine-word indices inside the loop.
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

/-- Planned DIF transform with bounds outside the hot butterfly loops. -/
def checkedStages [Field R] (D : NTT.Domain R) (tw : Array (Array R))
    (a : Array R) : Array R := Id.run do
  let mut a := a
  for pass in [0:D.logN / 2] do
    let high := D.logN - 1 - 2 * pass
    let low := high - 1
    let blockSize := 2 ^ (low + 2)
    let quarter := 2 ^ low
    a := checkedBlocks (tw.getD high #[]) (tw.getD low #[])
      blockSize quarter (D.n / blockSize) 0 a
  if D.logN % 2 = 1 then
    a := butterflyStageDIFWithTwiddles D 0 (tw.getD 0 #[]) a
  return a

/-- The checked transform agrees with the verified planned transform. -/
theorem checkedStages_eq [Field R] (D : NTT.Domain R) (tw : Array (Array R)) (a : Array R) :
    checkedStages D tw a = runStagesDIFRadix4WithTwiddles D tw a := by
  simp only [checkedStages, runStagesDIFRadix4WithTwiddles,
    butterflyRadix4StageDIFWithTwiddles, checkedBlocks_eq]

/-- Existing planned DIF entry point using the bounds-proved loops. -/
@[inline] def checkedForward [Field R] (P : Plan R) (a : Array R) : Array R :=
  checkedStages P.domain P.twiddles (NTT.loadNaturalArray P.domain a)

/-- Compile the public plan entry point through the checked loop. -/
@[csimp] theorem forwardImpl_eq_checked : @forwardImpl = @checkedForward := by
  funext R inst P a
  simp only [forwardImpl, checkedForward, checkedStages_eq]

end CompPoly.CPolynomial.NTTFast.Plan
