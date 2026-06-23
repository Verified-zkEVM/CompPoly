/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.Basic
import CompPoly.Univariate.NTT.FastMul

/-!
# Planned NTTFast multiplication

This file adds a reusable `NTTFast` plan that caches domain-derived data for
repeated NTT-based multiplication.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast

variable {R : Type*} [Field R]

/-- Cached domain data for repeated NTTFast multiplications. -/
structure Plan (R : Type*) [Field R] where
  domain : NTT.Domain R
  inverseDomain : NTT.Domain R
  nInv : R
  twiddles : Array (Array R)
  inverseTwiddles : Array (Array R)

namespace Plan

/-- Precompute the twiddle powers used by one radix-2 stage. -/
def twiddlePowers (D : NTT.Domain R) (stage : Nat) : Array R := Id.run do
  let blockSize : Nat := 2 ^ (stage + 1)
  let half : Nat := 2 ^ stage
  let wm := D.omega ^ (D.n / blockSize)
  let mut powers := #[]
  let mut w := (1 : R)
  for _ in [0:half] do
    powers := powers.push w
    w := w * wm
  return powers

/-- Precompute the per-stage twiddle table for a domain. -/
def twiddleTable (D : NTT.Domain R) : Array (Array R) :=
  Array.ofFn (fun stage : Fin D.logN ↦ twiddlePowers D stage.1)

/-- Build a reusable plan from an NTT domain. -/
def ofDomain (D : NTT.Domain R) : Plan R :=
  { domain := D
    inverseDomain := D.inverse
    nInv := D.nInv
    twiddles := twiddleTable D
    inverseTwiddles := twiddleTable D.inverse }

/-- Inner DIT butterfly loop for one block. -/
def butterflyDITInner
    (twiddles : Array R) (limit : Nat) (j i0 i1 : Nat) (acc : Array R) : Array R :=
  if j < limit then
    let w := twiddles.getD j 0
    let u := acc.getD i0 0
    let t := w * acc.getD i1 0
    let acc := (acc.set! i0 (u + t)).set! i1 (u - t)
    butterflyDITInner twiddles limit (j + 1) (i0 + 1) (i1 + 1) acc
  else
    acc
termination_by limit - j
decreasing_by omega

/-- Outer DIT butterfly loop over blocks. -/
def butterflyDITBlocks
    (twiddles : Array R) (blockSize half blocks : Nat) (block : Nat) (acc : Array R) :
    Array R :=
  if block < blocks then
    let base := block * blockSize
    let acc := butterflyDITInner twiddles half 0 base (base + half) acc
    butterflyDITBlocks twiddles blockSize half blocks (block + 1) acc
  else
    acc
termination_by blocks - block
decreasing_by omega

/-- One butterfly stage using precomputed twiddle powers for that stage. -/
def butterflyStageWithTwiddles
    (D : NTT.Domain R) (stage : Nat) (twiddles : Array R) (a : Array R) : Array R :=
  let blockSize : Nat := 2 ^ (stage + 1)
  let half : Nat := 2 ^ stage
  butterflyDITBlocks twiddles blockSize half (D.n / blockSize) 0 a

/-- Run all radix-2 stages using a precomputed per-stage twiddle table. -/
def runStagesWithTwiddles (D : NTT.Domain R) (twiddles : Array (Array R)) (a : Array R) :
    Array R := Id.run do
  let mut acc := a
  for stage in [0:D.logN] do
    acc := butterflyStageWithTwiddles D stage (twiddles.getD stage #[]) acc
  return acc

/-- Inner fused DIT loop for two adjacent radix-2 stages. -/
def butterflyDITRadix4Inner
    (twiddlesLow twiddlesHigh : Array R) (limit : Nat) (j i0 i1 i2 i3 : Nat)
    (acc : Array R) : Array R :=
  if j < limit then
    let wLow := twiddlesLow.getD j 0
    let wHigh0 := twiddlesHigh.getD j 0
    let wHigh1 := twiddlesHigh.getD (j + limit) 0
    let x0 := acc.getD i0 0
    let x1 := acc.getD i1 0
    let x2 := acc.getD i2 0
    let x3 := acc.getD i3 0
    let t1 := wLow * x1
    let t3 := wLow * x3
    let a0 := x0 + t1
    let a1 := x0 - t1
    let a2 := x2 + t3
    let a3 := x2 - t3
    let u2 := wHigh0 * a2
    let u3 := wHigh1 * a3
    let acc := (((acc.set! i0 (a0 + u2)).set! i1 (a1 + u3)).set! i2 (a0 - u2)).set! i3
      (a1 - u3)
    butterflyDITRadix4Inner twiddlesLow twiddlesHigh limit (j + 1) (i0 + 1) (i1 + 1)
      (i2 + 1) (i3 + 1) acc
  else
    acc
termination_by limit - j
decreasing_by omega

/-- Outer fused DIT loop over radix-4 blocks. -/
def butterflyDITRadix4Blocks
    (twiddlesLow twiddlesHigh : Array R) (blockSize quarter blocks block : Nat)
    (acc : Array R) : Array R :=
  if block < blocks then
    let base := block * blockSize
    let acc := butterflyDITRadix4Inner twiddlesLow twiddlesHigh quarter 0 base
      (base + quarter) (base + 2 * quarter) (base + 3 * quarter) acc
    butterflyDITRadix4Blocks twiddlesLow twiddlesHigh blockSize quarter blocks (block + 1) acc
  else
    acc
termination_by blocks - block
decreasing_by omega

/-- Run two adjacent DIT radix-2 stages as one radix-4 pass. -/
def butterflyRadix4StageWithTwiddles
    (D : NTT.Domain R) (lowStage : Nat) (twiddlesLow twiddlesHigh : Array R)
    (a : Array R) : Array R :=
  let blockSize : Nat := 2 ^ (lowStage + 2)
  let quarter : Nat := 2 ^ lowStage
  butterflyDITRadix4Blocks twiddlesLow twiddlesHigh blockSize quarter (D.n / blockSize) 0 a

/-- Run DIT stages using fused radix-4 passes where possible. -/
def runStagesRadix4WithTwiddles (D : NTT.Domain R) (twiddles : Array (Array R)) (a : Array R) :
    Array R := Id.run do
  let mut acc := a
  let pairs := D.logN / 2
  for pass in [0:pairs] do
    let lowStage := 2 * pass
    let highStage := lowStage + 1
    acc := butterflyRadix4StageWithTwiddles D lowStage (twiddles.getD lowStage #[])
      (twiddles.getD highStage #[]) acc
  if D.logN % 2 = 1 then
    acc := butterflyStageWithTwiddles D (D.logN - 1) (twiddles.getD (D.logN - 1) #[]) acc
  return acc

/-- Inner DIF butterfly loop for one block. -/
def butterflyDIFInner
    (twiddles : Array R) (limit : Nat) (j i0 i1 : Nat) (acc : Array R) : Array R :=
  if j < limit then
    let w := twiddles.getD j 0
    let u := acc.getD i0 0
    let v := acc.getD i1 0
    let acc := (acc.set! i0 (u + v)).set! i1 (w * (u - v))
    butterflyDIFInner twiddles limit (j + 1) (i0 + 1) (i1 + 1) acc
  else
    acc
termination_by limit - j
decreasing_by omega

/-- Outer DIF butterfly loop over blocks. -/
def butterflyDIFBlocks
    (twiddles : Array R) (blockSize half blocks : Nat) (block : Nat) (acc : Array R) :
    Array R :=
  if block < blocks then
    let base := block * blockSize
    let acc := butterflyDIFInner twiddles half 0 base (base + half) acc
    butterflyDIFBlocks twiddles blockSize half blocks (block + 1) acc
  else
    acc
termination_by blocks - block
decreasing_by omega

/--
One decimation-in-frequency butterfly stage using precomputed twiddle powers.

This accepts natural-order data and, when run from large stages down to small
stages, produces bit-reversed evaluation order.
-/
def butterflyStageDIFWithTwiddles
    (D : NTT.Domain R) (stage : Nat) (twiddles : Array R) (a : Array R) : Array R :=
  let blockSize : Nat := 2 ^ (stage + 1)
  let half : Nat := 2 ^ stage
  butterflyDIFBlocks twiddles blockSize half (D.n / blockSize) 0 a

/-- Run decimation-in-frequency stages, producing bit-reversed evaluation order. -/
def runStagesDIFWithTwiddles (D : NTT.Domain R) (twiddles : Array (Array R)) (a : Array R) :
    Array R := Id.run do
  let mut acc := a
  for pass in [0:D.logN] do
    let stage := D.logN - pass - 1
    acc := butterflyStageDIFWithTwiddles D stage (twiddles.getD stage #[]) acc
  return acc

/-- Inner paired DIF butterfly loop for one block. -/
def butterflyDIFPairInner
    (twiddles : Array R) (limit : Nat) (j i0 i1 : Nat) (accA accB : Array R) :
    Array R × Array R :=
  if j < limit then
    let w := twiddles.getD j 0
    let uA := accA.getD i0 0
    let vA := accA.getD i1 0
    let accA := (accA.set! i0 (uA + vA)).set! i1 (w * (uA - vA))
    let uB := accB.getD i0 0
    let vB := accB.getD i1 0
    let accB := (accB.set! i0 (uB + vB)).set! i1 (w * (uB - vB))
    butterflyDIFPairInner twiddles limit (j + 1) (i0 + 1) (i1 + 1) accA accB
  else
    (accA, accB)
termination_by limit - j
decreasing_by omega

/-- Outer paired DIF butterfly loop over blocks. -/
def butterflyDIFPairBlocks
    (twiddles : Array R) (blockSize half blocks block : Nat) (accA accB : Array R) :
    Array R × Array R :=
  if block < blocks then
    let base := block * blockSize
    let (accA, accB) := butterflyDIFPairInner twiddles half 0 base (base + half) accA accB
    butterflyDIFPairBlocks twiddles blockSize half blocks (block + 1) accA accB
  else
    (accA, accB)
termination_by blocks - block
decreasing_by omega

/-- One paired DIF butterfly stage using precomputed twiddle powers. -/
def butterflyStageDIFPairWithTwiddles
    (D : NTT.Domain R) (stage : Nat) (twiddles : Array R) (a b : Array R) :
    Array R × Array R :=
  let blockSize : Nat := 2 ^ (stage + 1)
  let half : Nat := 2 ^ stage
  butterflyDIFPairBlocks twiddles blockSize half (D.n / blockSize) 0 a b

/-- Inner fused DIF loop for two adjacent radix-2 stages. -/
def butterflyDIFRadix4Inner
    (twiddlesHigh twiddlesLow : Array R) (limit : Nat) (j i0 i1 i2 i3 : Nat)
    (acc : Array R) : Array R :=
  if j < limit then
    let wHigh0 := twiddlesHigh.getD j 0
    let wHigh1 := twiddlesHigh.getD (j + limit) 0
    let wLow := twiddlesLow.getD j 0
    let x0 := acc.getD i0 0
    let x1 := acc.getD i1 0
    let x2 := acc.getD i2 0
    let x3 := acc.getD i3 0
    let a0 := x0 + x2
    let a2 := wHigh0 * (x0 - x2)
    let a1 := x1 + x3
    let a3 := wHigh1 * (x1 - x3)
    let acc := (((acc.set! i0 (a0 + a1)).set! i1 (wLow * (a0 - a1))).set! i2
      (a2 + a3)).set! i3 (wLow * (a2 - a3))
    butterflyDIFRadix4Inner twiddlesHigh twiddlesLow limit (j + 1) (i0 + 1) (i1 + 1)
      (i2 + 1) (i3 + 1) acc
  else
    acc
termination_by limit - j
decreasing_by omega

/-- Outer fused DIF loop over radix-4 blocks. -/
def butterflyDIFRadix4Blocks
    (twiddlesHigh twiddlesLow : Array R) (blockSize quarter blocks block : Nat)
    (acc : Array R) : Array R :=
  if block < blocks then
    let base := block * blockSize
    let acc := butterflyDIFRadix4Inner twiddlesHigh twiddlesLow quarter 0 base
      (base + quarter) (base + 2 * quarter) (base + 3 * quarter) acc
    butterflyDIFRadix4Blocks twiddlesHigh twiddlesLow blockSize quarter blocks (block + 1) acc
  else
    acc
termination_by blocks - block
decreasing_by omega

/-- Run two adjacent DIF radix-2 stages as one radix-4 pass. -/
def butterflyRadix4StageDIFWithTwiddles
    (D : NTT.Domain R) (lowStage : Nat) (twiddlesHigh twiddlesLow : Array R)
    (a : Array R) : Array R :=
  let blockSize : Nat := 2 ^ (lowStage + 2)
  let quarter : Nat := 2 ^ lowStage
  butterflyDIFRadix4Blocks twiddlesHigh twiddlesLow blockSize quarter (D.n / blockSize) 0 a

/-- Run DIF stages using fused radix-4 passes where possible. -/
def runStagesDIFRadix4WithTwiddles
    (D : NTT.Domain R) (twiddles : Array (Array R)) (a : Array R) : Array R := Id.run do
  let mut acc := a
  let pairs := D.logN / 2
  for pass in [0:pairs] do
    let highStage := D.logN - 1 - 2 * pass
    let lowStage := highStage - 1
    acc := butterflyRadix4StageDIFWithTwiddles D lowStage (twiddles.getD highStage #[])
      (twiddles.getD lowStage #[]) acc
  if D.logN % 2 = 1 then
    acc := butterflyStageDIFWithTwiddles D 0 (twiddles.getD 0 #[]) acc
  return acc

/-- Inner paired fused DIF loop for two adjacent radix-2 stages. -/
def butterflyDIFRadix4PairInner
    (twiddlesHigh twiddlesLow : Array R) (limit : Nat) (j i0 i1 i2 i3 : Nat)
    (accA accB : Array R) : Array R × Array R :=
  if j < limit then
    let wHigh0 := twiddlesHigh.getD j 0
    let wHigh1 := twiddlesHigh.getD (j + limit) 0
    let wLow := twiddlesLow.getD j 0
    let x0A := accA.getD i0 0
    let x1A := accA.getD i1 0
    let x2A := accA.getD i2 0
    let x3A := accA.getD i3 0
    let a0A := x0A + x2A
    let a2A := wHigh0 * (x0A - x2A)
    let a1A := x1A + x3A
    let a3A := wHigh1 * (x1A - x3A)
    let accA := (((accA.set! i0 (a0A + a1A)).set! i1 (wLow * (a0A - a1A))).set! i2
      (a2A + a3A)).set! i3 (wLow * (a2A - a3A))
    let x0B := accB.getD i0 0
    let x1B := accB.getD i1 0
    let x2B := accB.getD i2 0
    let x3B := accB.getD i3 0
    let a0B := x0B + x2B
    let a2B := wHigh0 * (x0B - x2B)
    let a1B := x1B + x3B
    let a3B := wHigh1 * (x1B - x3B)
    let accB := (((accB.set! i0 (a0B + a1B)).set! i1 (wLow * (a0B - a1B))).set! i2
      (a2B + a3B)).set! i3 (wLow * (a2B - a3B))
    butterflyDIFRadix4PairInner twiddlesHigh twiddlesLow limit (j + 1) (i0 + 1)
      (i1 + 1) (i2 + 1) (i3 + 1) accA accB
  else
    (accA, accB)
termination_by limit - j
decreasing_by omega

/-- Outer paired fused DIF loop over radix-4 blocks. -/
def butterflyDIFRadix4PairBlocks
    (twiddlesHigh twiddlesLow : Array R) (blockSize quarter blocks block : Nat)
    (accA accB : Array R) : Array R × Array R :=
  if block < blocks then
    let base := block * blockSize
    let (accA, accB) := butterflyDIFRadix4PairInner twiddlesHigh twiddlesLow quarter 0
      base (base + quarter) (base + 2 * quarter) (base + 3 * quarter) accA accB
    butterflyDIFRadix4PairBlocks twiddlesHigh twiddlesLow blockSize quarter blocks
      (block + 1) accA accB
  else
    (accA, accB)
termination_by blocks - block
decreasing_by omega

/-- Run two adjacent paired DIF radix-2 stages as one radix-4 pass. -/
def butterflyRadix4StageDIFPairWithTwiddles
    (D : NTT.Domain R) (lowStage : Nat) (twiddlesHigh twiddlesLow : Array R)
    (a b : Array R) : Array R × Array R :=
  let blockSize : Nat := 2 ^ (lowStage + 2)
  let quarter : Nat := 2 ^ lowStage
  butterflyDIFRadix4PairBlocks twiddlesHigh twiddlesLow blockSize quarter (D.n / blockSize)
    0 a b

/-- Run paired DIF stages using fused radix-4 passes where possible. -/
def runStagesDIFRadix4PairWithTwiddles
    (D : NTT.Domain R) (twiddles : Array (Array R)) (a b : Array R) :
    Array R × Array R := Id.run do
  let mut accA := a
  let mut accB := b
  let pairs := D.logN / 2
  for pass in [0:pairs] do
    let highStage := D.logN - 1 - 2 * pass
    let lowStage := highStage - 1
    let (nextA, nextB) := butterflyRadix4StageDIFPairWithTwiddles D lowStage
      (twiddles.getD highStage #[]) (twiddles.getD lowStage #[]) accA accB
    accA := nextA
    accB := nextB
  if D.logN % 2 = 1 then
    let (nextA, nextB) := butterflyStageDIFPairWithTwiddles D 0 (twiddles.getD 0 #[]) accA
      accB
    accA := nextA
    accB := nextB
  return (accA, accB)

/-- Forward transform through a reusable plan. -/
@[inline] def forwardImpl (P : Plan R) (p : CPolynomial.Raw R) : Array R :=
  runStagesDIFRadix4WithTwiddles P.domain P.twiddles (NTT.loadNaturalArray P.domain p)

/-- Forward-transform two multiplication inputs through the same stage loops. -/
@[inline] def forwardPairImpl (P : Plan R) (p q : CPolynomial.Raw R) : Array R × Array R :=
  runStagesDIFRadix4PairWithTwiddles P.domain P.twiddles (NTT.loadNaturalArray P.domain p)
    (NTT.loadNaturalArray P.domain q)

/-- Apply the cached inverse-domain normalization factor. -/
@[inline] def normalize (P : Plan R) (a : Array R) : Array R :=
  Array.ofFn (fun i : P.domain.Idx ↦ P.nInv * a.getD i.1 0)

/-- Inverse transform through a reusable plan. -/
@[inline] def inverseImpl (P : Plan R) (v : Array R) : CPolynomial.Raw R :=
  normalize P (runStagesRadix4WithTwiddles P.inverseDomain P.inverseTwiddles v)

namespace Raw

/-- Raw planned pipeline for NTT-based multiplication. -/
@[inline] def fastMulImpl [BEq R]
    (P : Plan R) (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  let (pHat, qHat) := forwardPairImpl P p q
  let cHat := NTT.FastMul.pointwiseMul P.domain pHat qHat
  let c := inverseImpl P cHat
  NTT.Domain.truncate (NTT.Domain.requiredLength p q) c

end Raw

/-- Planned pipeline for NTT-based multiplication as a canonical polynomial. -/
@[inline] def fastMulImpl [BEq R] [LawfulBEq R]
    (P : Plan R) (p q : CPolynomial R) : CPolynomial R :=
  let raw := Raw.fastMulImpl P p.val q.val
  ⟨raw.trim, CPolynomial.Raw.Trim.isCanonical_trim raw⟩

end Plan
end NTTFast
end CPolynomial
end CompPoly
