/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.Basic
import CompPoly.Univariate.NTTFast.FastMulImpl
import CompPoly.Univariate.NTTFast.Transform

/-!
# Experimental planned NTT multiplication

This file adds a reusable `NTTFast` plan that caches domain-derived data for
benchmark experiments. The proved baseline remains under
`CompPoly.Univariate.NTT`.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast

variable {R : Type*} [Field R]

/-- Cached domain data for repeated experimental NTT multiplications. -/
structure Plan (R : Type*) [Field R] where
  domain : NTT.Domain R
  inverseDomain : NTT.Domain R
  nInv : R
  bitRevIndices : Array Nat
  twiddles : Array (Array R)
  inverseTwiddles : Array (Array R)

namespace Plan

/-- Precompute bit-reversed source indices for a domain. -/
def bitRevTable (D : NTT.Domain R) : Array Nat :=
  Array.ofFn (fun i : D.Idx => Transform.bitRevNat D.logN i.1)

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
  Array.ofFn (fun stage : Fin D.logN => twiddlePowers D stage.1)

/-- Build a reusable experimental plan from an NTT domain. -/
def ofDomain (D : NTT.Domain R) : Plan R :=
  { domain := D
    inverseDomain := D.inverse
    nInv := D.nInv
    bitRevIndices := bitRevTable D
    twiddles := twiddleTable D
    inverseTwiddles := twiddleTable D.inverse }

/-- Apply a bit-reversal permutation using precomputed source indices. -/
@[inline] def bitRevPermuteWithTable
    (D : NTT.Domain R) (indices : Array Nat) (a : Array R) : Array R :=
  Array.ofFn (fun i : D.Idx => a.getD (indices.getD i.1 0) 0)

/-- One butterfly stage using precomputed twiddle powers for that stage. -/
def butterflyStageWithTwiddles
    (D : NTT.Domain R) (stage : Nat) (twiddles : Array R) (a : Array R) : Array R :=
  Id.run do
    let blockSize : Nat := 2 ^ (stage + 1)
    let half : Nat := 2 ^ stage
    let mut acc := a
    for block in [0:D.n / blockSize] do
      for j in [0:half] do
        let w := twiddles.getD j 0
        let i0 := block * blockSize + j
        let i1 := i0 + half
        let u := acc.getD i0 0
        let t := w * acc.getD i1 0
        acc := (acc.set! i0 (u + t)).set! i1 (u - t)
    return acc

/-- Run all radix-2 stages using a precomputed per-stage twiddle table. -/
def runStagesWithTwiddles (D : NTT.Domain R) (twiddles : Array (Array R)) (a : Array R) :
    Array R := Id.run do
  let mut acc := a
  for stage in [0:D.logN] do
    acc := butterflyStageWithTwiddles D stage (twiddles.getD stage #[]) acc
  return acc

/-- Forward transform through a reusable plan. -/
@[inline] def forwardImpl (P : Plan R) (p : CPolynomial.Raw R) : Array R :=
  runStagesWithTwiddles P.domain P.twiddles
    (bitRevPermuteWithTable P.domain P.bitRevIndices p)

/-- Apply the cached inverse-domain normalization factor. -/
@[inline] def normalize (P : Plan R) (a : Array R) : Array R :=
  Array.ofFn (fun i : P.domain.Idx => P.nInv * a.getD i.1 0)

/-- Inverse transform through a reusable plan. -/
@[inline] def inverseImpl (P : Plan R) (v : Array R) : CPolynomial.Raw R :=
  normalize P
    (runStagesWithTwiddles P.inverseDomain P.inverseTwiddles
      (bitRevPermuteWithTable P.inverseDomain P.bitRevIndices v))

namespace Raw

/-- Raw experimental planned pipeline for NTT-based multiplication. -/
@[inline] def fastMulImpl [BEq R]
    (P : Plan R) (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  let pHat := forwardImpl P p
  let qHat := forwardImpl P q
  let cHat := pointwiseMul P.domain pHat qHat
  let c := inverseImpl P cHat
  NTT.Domain.truncate (NTT.Domain.requiredLength p q) c

end Raw

/-- Experimental planned pipeline for NTT-based multiplication as a canonical polynomial. -/
@[inline] def fastMulImpl [BEq R] [LawfulBEq R]
    (P : Plan R) (p q : CPolynomial R) : CPolynomial R :=
  let raw := Raw.fastMulImpl P p.val q.val
  ⟨raw.trim, CPolynomial.Raw.Trim.isCanonical_trim raw⟩

end Plan
end NTTFast
end CPolynomial
end CompPoly
