/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis

/-!
# Partial-Linearization Parameters

Small executable helpers used by diagonal modular-equation solvers to size the
expanded X-adic problem without using one global oversized order.
-/

namespace CompPoly

namespace PolynomialMatrix

namespace Approximant

variable {F : Type*}

/-- Ceiling division with `1` as the zero-width fallback. -/
def ceilDivFallback (n d : Nat) : Nat :=
  if d == 0 then 1 else (n + d - 1) / d

/-- Degree mass of diagonal moduli. -/
def modulusDegreeMass [Zero F] (moduli : Array (CPolynomial F)) : Nat :=
  moduli.foldl (fun acc modulus ↦ acc + modulus.natDegree) 0

/-- Chunk size `Delta = ceil(sigma / m)` used for partial linearization. -/
def chunkDelta [Zero F] (solutionWidth : Nat)
    (moduli : Array (CPolynomial F)) : Nat :=
  max 1 (ceilDivFallback (modulusDegreeMass moduli) solutionWidth)

/-- X-adic orders for the exact-nullspace lift, using the local chunk size. -/
def linearizedOrders [Zero F] (solutionWidth : Nat)
    (moduli : Array (CPolynomial F)) : Array Nat :=
  let delta := chunkDelta solutionWidth moduli
  moduli.map fun modulus ↦ modulus.natDegree + delta + 1

/-- Maximum shifted-degree offset in a principal-coordinate shift. -/
def maxShiftDegree (shift : Array Nat) : Nat :=
  (List.range shift.size).foldl
    (fun acc i ↦ max acc (shift.getD i 0)) 0

/-- Offset added to every principal coordinate when lifting to exact-nullspace
coordinates.  Adding the same positive offset to every principal coordinate
preserves their relative shifted degrees; quotient coordinates are shifted
separately above the principal search window. -/
def principalShiftOffset (_shift : Array Nat) (delta : Nat) : Nat :=
  delta + 1

/-- Quotient-coordinate shift used by the exact-nullspace lift.  It is kept at
the chunk degree so quotient coordinates do not dominate the shifted degree of
principal relation rows.  Rows that compress to zero are removed later by the
principal-row filter. -/
def quotientShift (_shift : Array Nat) (delta : Nat) : Nat :=
  delta

/-- Principal-coordinate shift used inside the exact-nullspace lift. -/
def liftedPrincipalShift (shift : Array Nat) (delta : Nat) : Array Nat :=
  shift.map fun degree ↦ degree + principalShiftOffset shift delta

/-- Extend the principal solution shift with low quotient shifts. -/
def exactNullspaceShift (shift : Array Nat) (quotientWidth delta : Nat) :
    Array Nat :=
  liftedPrincipalShift shift delta ++
    Array.replicate quotientWidth (quotientShift shift delta)

/-- One chunk of a principal solution coordinate.  It represents
`X^offset * chunkPoly` in coordinate `coord`. -/
structure PrincipalChunk where
  coord : Nat
  offset : Nat
deriving Repr, BEq, DecidableEq

/-- Number of chunks used for one principal coordinate from a shifted-degree
profile. -/
def principalChunkCount (solutionWidth : Nat) (shift : Array Nat)
    (delta j : Nat) : Nat :=
  let maxShift := (List.range solutionWidth).foldl
    (fun acc i ↦ max acc (shift.getD i 0)) 0
  max 1 (ceilDivFallback (maxShift + 1 - shift.getD j 0) delta)

/-- Principal chunks induced by the known shifted-degree profile. -/
def principalChunks (solutionWidth : Nat) (shift : Array Nat)
    (delta : Nat) : Array PrincipalChunk := Id.run do
  let mut chunks := #[]
  for j in [0:solutionWidth] do
    let count := principalChunkCount solutionWidth shift delta j
    for c in [0:count] do
      chunks := chunks.push { coord := j, offset := c * delta }
  pure chunks

/-- One unshifted chunk for each principal coordinate. -/
def principalUnitChunks (solutionWidth : Nat) : Array PrincipalChunk :=
  (List.range solutionWidth).map
    (fun coord ↦ { coord := coord, offset := 0 }) |>.toArray

/-- Fallback shifted pivot degree used before discovery has produced a degree for
one coordinate. -/
def fallbackPivotDegree (solutionWidth : Nat) (shift : Array Nat) : Nat :=
  (List.range solutionWidth).foldl
    (fun acc i ↦ max acc (shift.getD i 0)) 0

/-- Pivot degree for one coordinate, falling back to the shift spread when the
profile has not discovered that coordinate. -/
def pivotDegreeAt (solutionWidth : Nat) (shift : Array Nat)
    (pivotDegrees : Array (Option Nat)) (j : Nat) : Nat :=
  match pivotDegrees.getD j none with
  | some degree => degree
  | none => fallbackPivotDegree solutionWidth shift

/-- Number of chunks for one principal coordinate from a discovered shifted
pivot-degree profile. -/
def principalChunkCountFromPivotDegree (shift : Array Nat)
    (delta j pivotDegree : Nat) : Nat :=
  max 1 (ceilDivFallback (pivotDegree + 1 - shift.getD j 0) delta)

/-- Principal chunks induced by a discovered shifted pivot-degree profile. -/
def principalChunksFromPivotDegrees (solutionWidth : Nat) (shift : Array Nat)
    (delta : Nat) (pivotDegrees : Array (Option Nat)) :
    Array PrincipalChunk := Id.run do
  let mut chunks := #[]
  for j in [0:solutionWidth] do
    let degree := pivotDegreeAt solutionWidth shift pivotDegrees j
    let count := principalChunkCountFromPivotDegree shift delta j degree
    for c in [0:count] do
      chunks := chunks.push { coord := j, offset := c * delta }
  pure chunks

/-- Executable partial-linearization plan for the exact-nullspace lift. -/
structure PartialLinearizationPlan where
  solutionWidth : Nat
  quotientWidth : Nat
  delta : Nat
  chunks : Array PrincipalChunk

/-- Build a chunk plan from the modular shape and shifted-degree profile. -/
def partialLinearizationPlan [Zero F] (solutionWidth quotientWidth : Nat)
    (moduli : Array (CPolynomial F)) (shift : Array Nat) :
    PartialLinearizationPlan :=
  let delta := chunkDelta solutionWidth moduli
  { solutionWidth := solutionWidth
    quotientWidth := quotientWidth
    delta := delta
    chunks := principalChunks solutionWidth shift delta }

/-- Build a chunk plan from a discovered shifted pivot-degree profile. -/
def partialLinearizationPlanFromPivotDegrees [Zero F]
    (solutionWidth quotientWidth : Nat) (moduli : Array (CPolynomial F))
    (shift : Array Nat) (pivotDegrees : Array (Option Nat)) :
    PartialLinearizationPlan :=
  let delta := chunkDelta solutionWidth moduli
  { solutionWidth := solutionWidth
    quotientWidth := quotientWidth
    delta := delta
    chunks := principalChunksFromPivotDegrees solutionWidth shift delta pivotDegrees }

/-- Plan with partial linearization disabled for the principal coordinates. -/
def unchunkedPartialLinearizationPlan [Zero F]
    (solutionWidth quotientWidth : Nat) (moduli : Array (CPolynomial F)) :
    PartialLinearizationPlan :=
  { solutionWidth := solutionWidth
    quotientWidth := quotientWidth
    delta := chunkDelta solutionWidth moduli
    chunks := principalUnitChunks solutionWidth }

/-- Monomial `X^offset` as a canonical polynomial, built without requiring the
`CPolynomial.X` nontriviality instance. -/
def xPowPolynomial [Zero F] [One F] [BEq F] [LawfulBEq F]
    (offset : Nat) : CPolynomial F :=
  CPolynomial.ofArray ((Array.replicate offset 0).push 1)

/-- Multiply a polynomial by `X^offset` by shifting its coefficient array.
This is an `O(offset + deg p)` array operation; it must not go through generic
polynomial multiplication, which would cost `O(offset * deg p)`. -/
def shiftPolynomialX [Semiring F] [BEq F] [LawfulBEq F]
    (offset : Nat) (p : CPolynomial F) : CPolynomial F :=
  if p == 0 then
    0
  else
    CPolynomial.ofArray ((List.replicate offset (0 : F) ++ p.val.toList).toArray)

/-- Shift every entry of a row by `X^offset`. -/
def shiftRowX [Semiring F] [BEq F] [LawfulBEq F]
    (offset : Nat) (row : PolynomialRow F) : PolynomialRow F :=
  row.map fun p ↦ shiftPolynomialX offset p

/-- Shift for the chunked exact-nullspace problem. -/
def chunkedExactNullspaceShift (plan : PartialLinearizationPlan)
    (shift : Array Nat) : Array Nat :=
  plan.chunks.map
    (fun chunk ↦
      shift.getD chunk.coord 0 + chunk.offset +
        principalShiftOffset shift plan.delta) ++
    Array.replicate plan.quotientWidth (quotientShift shift plan.delta)

/-- Compress one row in chunked coordinates back to the principal solution
coordinates. -/
def compressChunkedPrincipalRow [Semiring F] [BEq F] [LawfulBEq F]
    (plan : PartialLinearizationPlan) (row : PolynomialRow F) :
    PolynomialRow F :=
  (List.range plan.solutionWidth).map
    (fun coord ↦
      (List.range plan.chunks.size).foldl
        (fun acc chunkIdx ↦
          let chunk := plan.chunks.getD chunkIdx { coord := 0, offset := 0 }
          if chunk.coord == coord then
            acc + shiftPolynomialX chunk.offset (rowGet row chunkIdx)
          else
            acc)
        0) |>.toArray

/-- Compress every row in a chunked basis back to the principal coordinates. -/
def compressChunkedPrincipalRows [Semiring F] [BEq F] [LawfulBEq F]
    (plan : PartialLinearizationPlan) (basis : PolynomialMatrix F) :
    PolynomialMatrix F :=
  basis.map fun row ↦ compressChunkedPrincipalRow plan row

end Approximant

end PolynomialMatrix

end CompPoly
