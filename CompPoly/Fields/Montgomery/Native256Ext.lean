/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Native256Field

/-!
# Extern-Backed 256-bit Montgomery Operations (opt-in)

Native backend for the shared 256-bit stack; the verified pure-Lean operations remain the
default. The single extern primitive is the 64×64 widening-product high word `mulHi`: its
`@[extern]` declaration carries the verified Lean implementation as its body, so trust is
runtime-only and `native/comppoly_mont256.c` must transcribe it. Everything above the
primitive is the verified CIOS chain, proved equal to the default operations. The module
interpreter cannot call project-local externs, so runtime checks live in
`lake exe CompPolyMont256ExtTests`.
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
@[inline] def interleavedMontgomeryReductionHi {modulus : ℕ} [P : Mont256Field modulus]
    (acc0 : UInt64) (acc : UInt256L) : UInt256L :=
  let t := P.montgomeryNegInv * acc0
  let prod := mulSmallHi P.modulus256 t
  let cin := (addc acc0 prod.1 0).2
  let sc := UInt256L.addCarryOut acc prod.2 cin
  reduceWideRaw (modulus := modulus) sc.1 sc.2

/-- `interleavedMontgomeryReductionHi` agrees with the verified reduction step. -/
theorem interleavedMontgomeryReductionHi_eq {modulus : ℕ} [P : Mont256Field modulus]
    (acc0 : UInt64) (acc : UInt256L) :
    interleavedMontgomeryReductionHi (modulus := modulus) acc0 acc
      = interleavedMontgomeryReduction (modulus := modulus) acc0 acc := by
  simp only [interleavedMontgomeryReductionHi, interleavedMontgomeryReduction,
    mulSmallHi_eq]

/-- CIOS Montgomery product with extern `mulHi` partial products; the rest is the
verified code. -/
def montgomeryMulHi {modulus : ℕ} [P : Mont256Field modulus] (lhs rhs : UInt256L) : UInt256L :=
  let (a0, a) := mulSmallHi lhs rhs.l0
  let r0 := interleavedMontgomeryReductionHi (modulus := modulus) a0 a
  let (b0, b) := mulSmallAndAccHi lhs rhs.l1 r0
  let r1 := interleavedMontgomeryReductionHi (modulus := modulus) b0 b
  let (c0, c) := mulSmallAndAccHi lhs rhs.l2 r1
  let r2 := interleavedMontgomeryReductionHi (modulus := modulus) c0 c
  let (d0, d) := mulSmallAndAccHi lhs rhs.l3 r2
  interleavedMontgomeryReductionHi (modulus := modulus) d0 d

/-- `montgomeryMulHi` agrees with the verified `montgomeryMul`. -/
theorem montgomeryMulHi_eq {modulus : ℕ} [P : Mont256Field modulus] (lhs rhs : UInt256L) :
    montgomeryMulHi (modulus := modulus) lhs rhs = montgomeryMul (modulus := modulus) lhs rhs := by
  simp only [montgomeryMulHi, montgomeryMul, interleavedMontgomeryReductionHi_eq,
    mulSmallHi_eq, mulSmallAndAccHi_eq]

/- Facts flow through `montgomeryMulHi_eq`; keep the unifier out of the CIOS unfolding. -/
attribute [irreducible] montgomeryMulHi

/-! ## Field-level operations

The subtype bound of each result is discharged through the equalities above, so no
runtime canonicalization is needed. -/

/-- Multiplication in Montgomery form where only the widening-product high words are
native. -/
@[inline] def mulWithMulHi {modulus : ℕ} [P : Mont256Field modulus] (x y : FastField modulus) :
    FastField modulus :=
  ⟨montgomeryMulHi (modulus := modulus) x.val y.val, by
    rw [montgomeryMulHi_eq]
    exact (montgomeryMul_spec (modulus := modulus) x.val y.val x.property).1⟩

/-- Squaring via `mulWithMulHi`. -/
@[inline] def squareWithMulHi {modulus : ℕ} [P : Mont256Field modulus] (x : FastField modulus) :
    FastField modulus :=
  mulWithMulHi x x

/-- `mulWithMulHi` agrees with the verified `mul`. -/
theorem mulWithMulHi_eq_mul {modulus : ℕ} [P : Mont256Field modulus] (x y : FastField modulus) :
    mulWithMulHi x y = mul x y :=
  Subtype.ext (montgomeryMulHi_eq (modulus := modulus) x.val y.val)

end Ext
end Native256
end Montgomery
