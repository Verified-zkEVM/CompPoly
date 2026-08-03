#include <stdint.h>
#include <lean/lean.h>

/*
 * Native backend for the 256-bit Montgomery fields, called through the
 * @[extern] declaration in CompPoly/Fields/Montgomery/Native256Ext.lean.
 * That declaration carries the verified Lean implementation as its body;
 * proofs and the kernel only ever see the Lean side, and the default field
 * operations never call this code. This file is trusted at runtime to agree
 * with that body: the Lean model is the cut-and-glue high word
 * `(mulLimb a b).hi`, computed here with the compiler's widening
 * multiplication (`unsigned __int128`); `mulLimb_toNat` proves the Lean
 * cut-and-glue computes the same product.
 */

typedef unsigned __int128 comppoly_u128;

/* High 64 bits of the 64x64 widening product: the Lean model is
 * `(mulLimb a b).hi` (CompPoly/Fields/Montgomery/Native256/UInt256L.lean). */
LEAN_EXPORT uint64_t comppoly_uint64_mul_hi(uint64_t a, uint64_t b) {
    return (uint64_t)(((comppoly_u128)a * b) >> 64);
}
