/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.Aes.Basic
public import CompPoly.Fields.Binary.BF128Ghash.Impl

/-!
# The selected AES embedding into GHASH

AES byte bit `i` represents the coefficient of `X^i`. The selected embedding evaluates
these eight coefficients at GHASH word `0x0dcb364640a222fe6b8330483c2e9849`, whose bit `i`
likewise represents the coefficient of `X^i`. This sends AES byte 2 to that root, rather
than interpreting the byte as the same GHASH word.

The public ring homomorphism executes the finite coefficient evaluation. Its laws follow
from the quotient universal property and a kernel-checked root identity. The selected root
matches the field tables in the following pinned implementations; this module establishes
the mathematical field embedding, not a proof of either implementation or a basis theorem
for protocol weights.

## References

* Binius64, revision `6e75a2d1d2e716578ae3ccb62806413fb1615176`,
  `crates/field/src/fields/ghash.rs`.
  https://github.com/binius-zk/binius64/blob/6e75a2d1d2e716578ae3ccb62806413fb1615176/crates/field/src/fields/ghash.rs
* Flock, revision `387768741ce97386f4926786d59015e6cf3f73b4`,
  `crates/flock-field/src/phi8.rs`.
  https://github.com/succinctlabs/flock/blob/387768741ce97386f4926786d59015e6cf3f73b4/crates/flock-field/src/phi8.rs
-/

@[expose] public section

namespace AesField

open CompPoly.Extension BF128Ghash Polynomial

/-- The selected root of the AES modulus, in GHASH polynomial-basis coordinates. -/
def ghashRoot : ConcreteBF128Ghash :=
  BF128Ghash.ofBitVec (0x0dcb364640a222fe6b8330483c2e9849#128)

/-- The selected GHASH element satisfies the AES defining relation. -/
theorem ghashRoot_relation :
    ghashRoot ^ 8 + ghashRoot ^ 4 + ghashRoot ^ 3 + ghashRoot + 1 = 0 := by
  decide +kernel

private def baseHom : ZMod 2 →+* ConcreteBF128Ghash :=
  ZMod.castHom (dvd_refl 2) ConcreteBF128Ghash

private theorem eval₂_ghashRoot : params.poly.eval₂ baseHom ghashRoot = 0 := by
  rw [params_poly, modulus]
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one]
  exact ghashRoot_relation

private noncomputable def quotientToGhash : AdjoinRoot params.poly →+* ConcreteBF128Ghash :=
  AdjoinRoot.lift baseHom ghashRoot eval₂_ghashRoot

private def evalGhash (a : AesField) : ConcreteBF128Ghash :=
  ∑ i : Fin params.d, baseHom (Ext.coeff a i) * ghashRoot ^ (i : ℕ)

private theorem quotientToGhash_toQuot (a : AesField) :
    quotientToGhash (Ext.toQuot a) = evalGhash a := by
  simp only [Ext.toQuot, map_sum, map_mul, map_pow, Ext.rt, quotientToGhash,
    AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, AdjoinRoot.lift_root, evalGhash]

/-- Embed AES coefficients into GHASH by evaluating them at the selected AES root. -/
def toGhash : AesField →+* ConcreteBF128Ghash where
  toFun a := ∑ i : Fin params.d,
    ZMod.castHom (dvd_refl 2) ConcreteBF128Ghash (Ext.coeff a i) * ghashRoot ^ (i : ℕ)
  map_zero' := by
    change evalGhash 0 = 0
    rw [← quotientToGhash_toQuot, Ext.toQuot_zero, map_zero]
  map_one' := by
    change evalGhash 1 = 1
    rw [← quotientToGhash_toQuot, Ext.toQuot_one, map_one]
  map_add' a b := by
    change evalGhash (a + b) = evalGhash a + evalGhash b
    simp only [← quotientToGhash_toQuot, Ext.toQuot_add, map_add]
  map_mul' a b := by
    change evalGhash (a * b) = evalGhash a * evalGhash b
    simp only [← quotientToGhash_toQuot, Ext.toQuot_mul, map_mul]

/-- The embedding evaluates the eight ascending polynomial coefficients at the selected root. -/
theorem toGhash_apply (a : AesField) :
    toGhash a = ∑ i : Fin params.d,
      ZMod.castHom (dvd_refl 2) ConcreteBF128Ghash (Ext.coeff a i) * ghashRoot ^ (i : ℕ) := rfl

/-- The AES polynomial generator maps to the selected GHASH root. -/
@[simp] theorem toGhash_gen : toGhash gen = ghashRoot := by
  change evalGhash gen = ghashRoot
  rw [← quotientToGhash_toQuot]
  change quotientToGhash (Ext.toQuot (Ext.gen : AesField)) = ghashRoot
  rw [Ext.toQuot_gen]
  exact AdjoinRoot.lift_root eval₂_ghashRoot

/-- The selected field embedding identifies no distinct AES elements. -/
theorem toGhash_injective : Function.Injective toGhash := toGhash.injective

end AesField
