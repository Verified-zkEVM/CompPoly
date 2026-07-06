/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Native256Field

/-!
# Extern-backed 256-bit Montgomery operations (opt-in)

Opt-in native backends for the shared 256-bit Montgomery stack
(`CompPoly.Fields.Montgomery.Native256Field`); the verified pure-Lean operations and
instances remain the default. Two granularities are offered, mirroring
`CompPoly.Fields.Goldilocks.FastExt`:

* **Primitive** (`Ext.mulHi`, entry point `Ext.mulWithMulHi`): only the high word of
  each 64×64 partial product is native; the CIOS algorithm stays compiled-from-Lean.
* **Whole operation** (`Ext.montgomeryMulNative`, entry points `Ext.mulNative`,
  `Ext.squareNative`, `Ext.invNative`, `Ext.divNative`).

Unlike `Goldilocks.FastExt`, the `@[extern]` declarations carry the verified Lean
implementation as their body: proofs and the kernel see only the body, and each
operation is provably equal to its verified counterpart (`Ext.mulNative_eq_mul` and
friends), so the `FastField` bound needs no runtime re-checking. Trust is
runtime-only: `native/comppoly_mont256.c`, a line-by-line transcription of these
bodies, must agree with them.

The module interpreter cannot call project-local externs, so `#eval`/`#guard` on
these functions fails; runtime checks live in `lake exe CompPolyMont256ExtTests`.
-/

namespace Montgomery
namespace Native256
namespace Ext

/-! ## Extern widening-multiplication primitive -/

/-- High 64 bits of the 64×64 widening product. The body is the verified cut-and-glue
high word; compiled code calls the trusted native `comppoly_uint64_mul_hi` instead. -/
@[extern "comppoly_uint64_mul_hi"]
def mulHi (a b : UInt64) : UInt64 := (mulLimb a b).hi

/-- Full 64×64→128 product: native wrapping low word plus extern `mulHi` high word. -/
@[inline] def mulLimbHi (a b : UInt64) : UInt128L := ⟨a * b, mulHi a b⟩

/-- The primitive-backed wide product agrees with the verified `mulLimb`. -/
theorem mulLimbHi_eq (a b : UInt64) : mulLimbHi a b = mulLimb a b := by
  have h := mulLimb_toNat a b
  have hlo : (mulLimb a b).lo = a * b := by
    apply UInt64.toNat_inj.mp
    have hl := (mulLimb a b).lo.toNat_lt
    rw [UInt64.toNat_mul]
    simp only [UInt128L.toNat, Nat.shiftLeft_eq] at h
    omega
  show UInt128L.mk (a * b) (mulLimb a b).hi = mulLimb a b
  rw [← hlo]

/-! ## CIOS over the extern primitive

Twins of the verified CIOS chain with `mulLimb` replaced by `mulLimbHi`, each proved
equal to the original: only the 64×64 high words are trusted on this path. -/

/-- `mulSmall` with `mulLimbHi` partial products. -/
@[inline] def mulSmallHi (lhs : UInt256L) (rhs : UInt64) : UInt64 × UInt256L :=
  let p0 : UInt128L := mulLimbHi lhs.l0 rhs
  let c0 : UInt128L := ⟨p0.hi, 0⟩
  let p1 : UInt128L := c0 + (mulLimbHi lhs.l1 rhs)
  let c1 : UInt128L := ⟨p1.hi, 0⟩
  let p2 : UInt128L := c1 + (mulLimbHi lhs.l2 rhs)
  let c2 : UInt128L := ⟨p2.hi, 0⟩
  let p3 : UInt128L := c2 + (mulLimbHi lhs.l3 rhs)
  (p0.lo, ⟨p1.lo, p2.lo, p3.lo, p3.hi⟩)

/-- `mulSmallHi` agrees with the verified `mulSmall`. -/
theorem mulSmallHi_eq (lhs : UInt256L) (rhs : UInt64) :
    mulSmallHi lhs rhs = mulSmall lhs rhs := by
  simp only [mulSmallHi, mulSmall, mulLimbHi_eq]

/-- `mulSmallAndAcc` with `mulLimbHi` partial products. -/
@[inline] def mulSmallAndAccHi (lhs : UInt256L) (rhs : UInt64) (add : UInt256L) :
    UInt64 × UInt256L :=
  let p0 : UInt128L := ⟨add.l0, 0⟩ + (mulLimbHi lhs.l0 rhs)
  let c0 : UInt128L := ⟨p0.hi, 0⟩
  let p1 : UInt128L := c0 + (mulLimbHi lhs.l1 rhs) + ⟨add.l1, 0⟩
  let c1 : UInt128L := ⟨p1.hi, 0⟩
  let p2 : UInt128L := c1 + (mulLimbHi lhs.l2 rhs) + ⟨add.l2, 0⟩
  let c2 : UInt128L := ⟨p2.hi, 0⟩
  let p3 : UInt128L := c2 + (mulLimbHi lhs.l3 rhs) + ⟨add.l3, 0⟩
  (p0.lo, ⟨p1.lo, p2.lo, p3.lo, p3.hi⟩)

/-- `mulSmallAndAccHi` agrees with the verified `mulSmallAndAcc`. -/
theorem mulSmallAndAccHi_eq (lhs : UInt256L) (rhs : UInt64) (add : UInt256L) :
    mulSmallAndAccHi lhs rhs add = mulSmallAndAcc lhs rhs add := by
  simp only [mulSmallAndAccHi, mulSmallAndAcc, mulLimbHi_eq]

/-- `interleavedMontgomeryReduction` with `mulSmallHi` partial products. -/
@[inline] def interleavedMontgomeryReductionHi {F : Type} [P : Mont256Field F]
    (acc0 : UInt64) (acc : UInt256L) : UInt256L :=
  let t := P.montgomeryNegInv * acc0
  let prod := mulSmallHi P.modulus t
  let cin := (addc acc0 prod.1 0).2
  let sc := UInt256L.addCarryOut acc prod.2 cin
  reduceWideRaw (F := F) sc.1 sc.2

/-- `interleavedMontgomeryReductionHi` agrees with the verified reduction step. -/
theorem interleavedMontgomeryReductionHi_eq {F : Type} [P : Mont256Field F]
    (acc0 : UInt64) (acc : UInt256L) :
    interleavedMontgomeryReductionHi (F := F) acc0 acc
      = interleavedMontgomeryReduction (F := F) acc0 acc := by
  simp only [interleavedMontgomeryReductionHi, interleavedMontgomeryReduction,
    mulSmallHi_eq]

/-- CIOS Montgomery product with extern `mulHi` partial products; the rest is the
verified code. -/
def montgomeryMulHi {F : Type} [P : Mont256Field F] (lhs rhs : UInt256L) : UInt256L :=
  let (a0, a) := mulSmallHi lhs rhs.l0
  let r0 := interleavedMontgomeryReductionHi (F := F) a0 a
  let (b0, b) := mulSmallAndAccHi lhs rhs.l1 r0
  let r1 := interleavedMontgomeryReductionHi (F := F) b0 b
  let (c0, c) := mulSmallAndAccHi lhs rhs.l2 r1
  let r2 := interleavedMontgomeryReductionHi (F := F) c0 c
  let (d0, d) := mulSmallAndAccHi lhs rhs.l3 r2
  interleavedMontgomeryReductionHi (F := F) d0 d

/-- `montgomeryMulHi` agrees with the verified `montgomeryMul`. -/
theorem montgomeryMulHi_eq {F : Type} [P : Mont256Field F] (lhs rhs : UInt256L) :
    montgomeryMulHi (F := F) lhs rhs = montgomeryMul (F := F) lhs rhs := by
  simp only [montgomeryMulHi, montgomeryMul, interleavedMontgomeryReductionHi_eq,
    mulSmallHi_eq, mulSmallAndAccHi_eq]

/- Facts flow through `montgomeryMulHi_eq`; keep the unifier out of the CIOS unfolding. -/
attribute [irreducible] montgomeryMulHi

/-! ## Whole-operation native Montgomery multiplication

Explicit-constant copies of the reduction chain, so the extern signature carries
`modulus`/`montgomeryNegInv` directly (C cannot see the typeclass). -/

/-- `reduceUInt256Lt2ModulusRaw` with an explicit modulus word. -/
@[inline] def reduceUInt256Lt2ModulusRawWith (m x : UInt256L) : UInt256L :=
  if x < m then x else x - m

/-- `reduceWideRaw` with an explicit modulus word. -/
@[inline] def reduceWideRawWith (m lo : UInt256L) (carry : UInt64) : UInt256L :=
  if carry = 0 then reduceUInt256Lt2ModulusRawWith m lo else lo - m

/-- `interleavedMontgomeryReduction` with explicit modulus and multiplier words. -/
@[inline] def interleavedMontgomeryReductionWith (m : UInt256L) (ni : UInt64)
    (acc0 : UInt64) (acc : UInt256L) : UInt256L :=
  let t := ni * acc0
  let prod := mulSmall m t
  let cin := (addc acc0 prod.1 0).2
  let sc := UInt256L.addCarryOut acc prod.2 cin
  reduceWideRawWith m sc.1 sc.2

/-- The 4-round CIOS Montgomery product `lhs · rhs · (2²⁵⁶)⁻¹ mod m` with explicit
modulus `m` and per-limb multiplier `ni`. The body is the verified algorithm
(`montgomeryMulNative_eq`); compiled code calls the trusted native
`comppoly_mont256_mul`, one symbol for every `Mont256Field` instance. -/
@[extern "comppoly_mont256_mul"]
def montgomeryMulNative (m : @& UInt256L) (ni : UInt64) (lhs : @& UInt256L)
    (rhs : @& UInt256L) : UInt256L :=
  let (a0, a) := mulSmall lhs rhs.l0
  let r0 := interleavedMontgomeryReductionWith m ni a0 a
  let (b0, b) := mulSmallAndAcc lhs rhs.l1 r0
  let r1 := interleavedMontgomeryReductionWith m ni b0 b
  let (c0, c) := mulSmallAndAcc lhs rhs.l2 r1
  let r2 := interleavedMontgomeryReductionWith m ni c0 c
  let (d0, d) := mulSmallAndAcc lhs rhs.l3 r2
  interleavedMontgomeryReductionWith m ni d0 d

/-- At a field's own constants, the explicit-constant reduction step is the verified
`interleavedMontgomeryReduction`. -/
theorem interleavedMontgomeryReductionWith_eq {F : Type} [P : Mont256Field F]
    (acc0 : UInt64) (acc : UInt256L) :
    interleavedMontgomeryReductionWith P.modulus P.montgomeryNegInv acc0 acc
      = interleavedMontgomeryReduction (F := F) acc0 acc := by
  simp only [interleavedMontgomeryReductionWith, interleavedMontgomeryReduction,
    reduceWideRawWith, reduceWideRaw, reduceUInt256Lt2ModulusRawWith,
    reduceUInt256Lt2ModulusRaw]

/-- At a field's own constants, the explicit-constant native model is the verified
`montgomeryMul`. -/
theorem montgomeryMulNative_eq {F : Type} [P : Mont256Field F] (lhs rhs : UInt256L) :
    montgomeryMulNative P.modulus P.montgomeryNegInv lhs rhs
      = montgomeryMul (F := F) lhs rhs := by
  simp only [montgomeryMulNative, montgomeryMul, interleavedMontgomeryReductionWith_eq]

/- As for `montgomeryMulHi`: downstream facts flow through `montgomeryMulNative_eq`. -/
attribute [irreducible] montgomeryMulNative

/-! ## Field-level operations

The subtype bound of each result is discharged through the equalities above, so no
runtime canonicalization is needed. -/

/-- Multiplication in Montgomery form where only the widening-product high words are
native. -/
@[inline] def mulWithMulHi {F : Type} [P : Mont256Field F] (x y : FastField F) :
    FastField F :=
  ⟨montgomeryMulHi (F := F) x.val y.val, by
    rw [montgomeryMulHi_eq]
    exact (montgomeryMul_spec (F := F) x.val y.val x.property).1⟩

/-- Squaring via `mulWithMulHi`. -/
@[inline] def squareWithMulHi {F : Type} [P : Mont256Field F] (x : FastField F) :
    FastField F :=
  mulWithMulHi x x

/-- `mulWithMulHi` agrees with the verified `mul`. -/
theorem mulWithMulHi_eq_mul {F : Type} [P : Mont256Field F] (x y : FastField F) :
    mulWithMulHi x y = mul x y :=
  Subtype.ext (montgomeryMulHi_eq (F := F) x.val y.val)

/-- Multiplication in Montgomery form where the whole CIOS product is native. -/
@[inline] def mulNative {F : Type} [P : Mont256Field F] (x y : FastField F) :
    FastField F :=
  ⟨montgomeryMulNative P.modulus P.montgomeryNegInv x.val y.val, by
    rw [montgomeryMulNative_eq (F := F)]
    exact (montgomeryMul_spec (F := F) x.val y.val x.property).1⟩

/-- Squaring via `mulNative`. -/
@[inline] def squareNative {F : Type} [P : Mont256Field F] (x : FastField F) :
    FastField F :=
  mulNative x x

/-- Repeated native squaring: `squareNNative x n` computes `x^(2^n)`. -/
def squareNNative {F : Type} [P : Mont256Field F] (x : FastField F) :
    Nat → FastField F
  | 0 => x
  | n + 1 => squareNNative (squareNative x) n

/-- `mulNative` agrees with the verified `mul`. -/
theorem mulNative_eq_mul {F : Type} [P : Mont256Field F] (x y : FastField F) :
    mulNative x y = mul x y :=
  Subtype.ext (montgomeryMulNative_eq (F := F) x.val y.val)

/-- `squareNative` agrees with the verified `square`. -/
theorem squareNative_eq_square {F : Type} [P : Mont256Field F] (x : FastField F) :
    squareNative x = square x :=
  mulNative_eq_mul x x

/-- `invWithCandidate` with the candidate check done by native multiplication; the
fallback (taken only for `x = 0` or a candidate miss) stays on the verified path. -/
@[inline] def invWithCandidateNative {F : Type} [P : Mont256Field F] (x : FastField F)
    (z : UInt256L) : FastField F :=
  if h : z < P.modulus ∧
      montgomeryMulNative P.modulus P.montgomeryNegInv z x.val = P.rModModulus then
    ⟨z, by rw [← P.modulus_toNat]; exact UInt256L.lt_iff_toNat_lt.mp h.1⟩
  else invWindow x

/-- Inversion in Montgomery form: the Pornin binary-GCD candidate, checked by one
native Montgomery multiplication, with the verified windowed Fermat fallback. -/
@[inline] def invNative {F : Type} [P : Mont256Field F] (x : FastField F) :
    FastField F :=
  invWithCandidateNative x (gcdInvCandidate (F := F) x.val)

/-- `invWithCandidateNative` agrees with the verified `invWithCandidate`. -/
theorem invWithCandidateNative_eq {F : Type} [P : Mont256Field F] (x : FastField F)
    (z : UInt256L) :
    invWithCandidateNative x z = invWithCandidate x z := by
  simp only [invWithCandidateNative, invWithCandidate, montgomeryMulNative_eq (F := F)]

/-- `invNative` agrees with the verified `inv`. -/
theorem invNative_eq_inv {F : Type} [P : Mont256Field F] (x : FastField F) :
    invNative x = inv x :=
  invWithCandidateNative_eq x (gcdInvCandidate (F := F) x.val)

/-- Division through native inversion and native multiplication. -/
@[inline] def divNative {F : Type} [P : Mont256Field F] (x y : FastField F) :
    FastField F :=
  mulNative x (invNative y)

/-- `divNative` agrees with the verified `div`. -/
theorem divNative_eq_div {F : Type} [P : Mont256Field F] (x y : FastField F) :
    divNative x y = div x y := by
  simp only [divNative, div, mulNative_eq_mul, invNative_eq_inv]

end Ext
end Native256
end Montgomery
