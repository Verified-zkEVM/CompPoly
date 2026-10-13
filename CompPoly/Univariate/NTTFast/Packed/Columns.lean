/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.NativeLast
public import CompPoly.Univariate.NTTFast.Columns

/-! # The packed column-parallel transform

The packed plan runs the same pipeline as `Columns.transformPacked`, on packed words throughout:
column tasks run the top two radix-four passes of the transform, viewed as a `16 × M` matrix, on
their columns; sixteen leaf tasks run the remaining layers of one row each with `leafNatural`,
which also reverses and scales it; and `naturalLeaves` interleaves the leaves into natural order.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed.Native

/-- Words `j0, …, j0 + cs - 1` of rows `0, …, r - 1` of a row-major matrix with rows of `M`
words, as an `r × cs` matrix. -/
def gatherWords (src : @& ByteArray) (M j0 cs r : Nat) : ByteArray :=
  (List.range r).foldl (fun out k ↦ src.copySlice (4 * (k * M + j0)) out out.size (4 * cs))
    (ByteArray.emptyWithCapacity (4 * (r * cs)))

/-- The top two radix-four passes of a `16 × M` transform on columns `j0, …, j0 + cs - 1`. -/
def columnWords (tw : @& Array ByteArray) (logN M cs j0 : Nat) (x : @& ByteArray) : ByteArray :=
  let a := radix4Blocks (gatherWords (tw.getD (logN - 1) .empty) M j0 cs 8)
    (gatherWords (tw.getD (logN - 2) .empty) M j0 cs 4) (4 * cs) 1 (gatherWords x M j0 cs 16)
  radix4Blocks (gatherWords (tw.getD (logN - 3) .empty) M j0 cs 2)
    (gatherWords (tw.getD (logN - 4) .empty) M j0 cs 1) cs 4 a

/-- Row `l` of the column results, in column order. -/
def leafWords (cols : @& Array ByteArray) (cs l : Nat) : ByteArray :=
  cols.foldl (fun out col ↦ col.copySlice (4 * (l * cs)) out out.size (4 * cs))
    (ByteArray.emptyWithCapacity (4 * (cols.size * cs)))

/-- The column-parallel transform of `2 ^ logN` packed words: `S` column tasks run the top two
radix-four passes, sixteen leaf tasks the remaining layers in natural order, and sixteen tasks
interleave the leaves. -/
def runColumns (tw : Array ByteArray) (logN S : Nat) (nInv : UInt32) (inverse : Bool)
    (a : ByteArray) : ByteArray :=
  let M := 2 ^ (logN - 4)
  let cs := M / S
  let cols := Tasks.spawnAll S fun s ↦ columnWords tw logN M cs (s * cs) a
  let leaves := Tasks.spawnAfter cols 16 fun cols l ↦
    leafNatural tw (logN - 4) nInv inverse (leafWords cols cs l)
  naturalLeaves (leaves.map Task.get) logN

/-- The complete transform of `2 ^ logN` packed words in natural order: if `parallel`, the column
transform from `2 ^ 15` words, otherwise one leaf. -/
def run (tw : Array ByteArray) (logN : Nat) (parallel : Bool) (nInv : UInt32) (inverse : Bool)
    (a : ByteArray) : ByteArray :=
  if parallel ∧ 15 ≤ logN then
    runColumns tw logN (Columns.columnCount logN) nInv inverse a
  else leafNatural tw logN nInv inverse a

end CompPoly.CPolynomial.NTTFast.Packed.Native
