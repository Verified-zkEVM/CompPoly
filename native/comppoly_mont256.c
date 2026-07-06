#include <stdint.h>
#include <lean/lean.h>

/*
 * Native backends for the 256-bit Montgomery fields, called through the
 * @[extern] declarations in CompPoly/Fields/Montgomery/Native256Ext.lean.
 * Those declarations carry the verified Lean implementations as their bodies;
 * proofs and the kernel only ever see the Lean side, and the default field
 * operations never call this code. This file is trusted at runtime to agree
 * with those bodies, and stays reviewable by being a line-by-line
 * transcription of them (on ALL inputs, not only canonical residues): each
 * helper names the Lean definition it mirrors. The one sanctioned difference
 * is using the compiler's widening multiplication (`unsigned __int128`) for
 * the 64x64->128 partial products; `mulLimb_toNat` proves the Lean
 * cut-and-glue computes the same product.
 */

typedef unsigned __int128 comppoly_u128;

/* High 64 bits of the 64x64 widening product: the Lean model is
 * `(mulLimb a b).hi` (CompPoly/Fields/Montgomery/Native256/UInt256L.lean). */
LEAN_EXPORT uint64_t comppoly_uint64_mul_hi(uint64_t a, uint64_t b) {
    return (uint64_t)(((comppoly_u128)a * b) >> 64);
}

/* `addc` (CompPoly/Fields/Montgomery/Native256/Limb.lean): one limb of
 * add-with-carry. Returns the carry-out, stores the sum limb in `*sum`. */
static inline uint64_t comppoly_addc(uint64_t a, uint64_t b, uint64_t c,
                                     uint64_t *sum) {
    uint64_t s1 = a + b;
    uint64_t c1 = s1 < a ? 1 : 0;
    uint64_t s2 = s1 + c;
    uint64_t c2 = s2 < s1 ? 1 : 0;
    *sum = s2;
    return c1 + c2;
}

/* `mulSmall` (UInt256L.lean): 256x64 product. Stores the high four limbs of
 * the 5-limb product in `out`, returns the lowest limb. */
static inline uint64_t comppoly_mul_small(const uint64_t lhs[4], uint64_t rhs,
                                          uint64_t out[4]) {
    comppoly_u128 p0 = (comppoly_u128)lhs[0] * rhs;
    comppoly_u128 p1 = (p0 >> 64) + (comppoly_u128)lhs[1] * rhs;
    comppoly_u128 p2 = (p1 >> 64) + (comppoly_u128)lhs[2] * rhs;
    comppoly_u128 p3 = (p2 >> 64) + (comppoly_u128)lhs[3] * rhs;
    out[0] = (uint64_t)p1;
    out[1] = (uint64_t)p2;
    out[2] = (uint64_t)p3;
    out[3] = (uint64_t)(p3 >> 64);
    return (uint64_t)p0;
}

/* `mulSmallAndAcc` (UInt256L.lean): 256x64 product accumulated with a 256-bit
 * addend. Same output convention as `comppoly_mul_small`. */
static inline uint64_t comppoly_mul_small_acc(const uint64_t lhs[4],
                                              uint64_t rhs,
                                              const uint64_t add[4],
                                              uint64_t out[4]) {
    comppoly_u128 p0 = (comppoly_u128)add[0] + (comppoly_u128)lhs[0] * rhs;
    comppoly_u128 p1 = (p0 >> 64) + (comppoly_u128)lhs[1] * rhs + add[1];
    comppoly_u128 p2 = (p1 >> 64) + (comppoly_u128)lhs[2] * rhs + add[2];
    comppoly_u128 p3 = (p2 >> 64) + (comppoly_u128)lhs[3] * rhs + add[3];
    out[0] = (uint64_t)p1;
    out[1] = (uint64_t)p2;
    out[2] = (uint64_t)p3;
    out[3] = (uint64_t)(p3 >> 64);
    return (uint64_t)p0;
}

/* `UInt256L.sub` via `subb` (UInt256L.lean): wrapping 256-bit subtraction. */
static inline void comppoly_sub256(const uint64_t a[4], const uint64_t b[4],
                                   uint64_t out[4]) {
    uint64_t brw = 0;
    for (int i = 0; i < 4; i++) {
        uint64_t s1 = a[i] - b[i];
        uint64_t b1 = a[i] < b[i] ? 1 : 0;
        uint64_t s2 = s1 - brw;
        uint64_t b2 = s1 < brw ? 1 : 0;
        out[i] = s2;
        brw = b1 + b2;
    }
}

/* `UInt256L.cmp`-based `<` (UInt256L.lean): limb-lexicographic from the top
 * limb, which agrees with the numeric order (`UInt256L.lt_iff_toNat_lt`). */
static inline int comppoly_lt256(const uint64_t a[4], const uint64_t b[4]) {
    for (int i = 3; i >= 0; i--) {
        if (a[i] != b[i])
            return a[i] < b[i];
    }
    return 0;
}

/* `reduceWideRawWith` (Native256Ext.lean), i.e. `reduceWideRaw`
 * (Native256.lean) with an explicit modulus: fold `lo + carry * 2^256` into
 * canonical range. A zero carry takes the one conditional subtract of
 * `reduceUInt256Lt2ModulusRawWith`; a set carry always subtracts (the
 * top-bit-set-modulus branch). */
static inline void comppoly_reduce_wide(const uint64_t m[4],
                                        const uint64_t lo[4], uint64_t carry,
                                        uint64_t out[4]) {
    if (carry == 0) {
        if (comppoly_lt256(lo, m)) {
            out[0] = lo[0];
            out[1] = lo[1];
            out[2] = lo[2];
            out[3] = lo[3];
        } else {
            comppoly_sub256(lo, m, out);
        }
    } else {
        comppoly_sub256(lo, m, out);
    }
}

/* `interleavedMontgomeryReductionWith` (Native256Ext.lean): one CIOS step on
 * the 5-limb accumulator `(acc0, acc)`. */
static inline void comppoly_interleaved_reduction(const uint64_t m[4],
                                                  uint64_t ni, uint64_t acc0,
                                                  const uint64_t acc[4],
                                                  uint64_t out[4]) {
    uint64_t t = ni * acc0;
    uint64_t prod[4];
    uint64_t prod0 = comppoly_mul_small(m, t, prod);
    uint64_t dropped;
    uint64_t cin = comppoly_addc(acc0, prod0, 0, &dropped);
    /* `UInt256L.addCarryOut acc prod cin` */
    uint64_t sc[4];
    uint64_t carry = cin;
    for (int i = 0; i < 4; i++) {
        carry = comppoly_addc(acc[i], prod[i], carry, &sc[i]);
    }
    comppoly_reduce_wide(m, sc, carry, out);
}

/* `montgomeryMulNative` (Native256Ext.lean), i.e. `montgomeryMul`
 * (Native256.lean) with explicit modulus `m` and per-limb multiplier `ni`:
 * the 4-round CIOS Montgomery product `lhs * rhs * (2^256)^-1 mod m`.
 *
 * `UInt256L` is a Lean constructor with no pointer fields and four `UInt64`
 * scalar fields `l0..l3`, so the limbs live at byte offsets 0/8/16/24 of the
 * scalar area. Arguments are borrowed (`@&` in the Lean signature); the
 * result is a fresh constructor. */
LEAN_EXPORT lean_object *comppoly_mont256_mul(b_lean_obj_arg m_obj,
                                              uint64_t ni,
                                              b_lean_obj_arg lhs_obj,
                                              b_lean_obj_arg rhs_obj) {
    uint64_t m[4], lhs[4], rhs[4];
    for (int i = 0; i < 4; i++) {
        m[i] = lean_ctor_get_uint64(m_obj, i * 8);
        lhs[i] = lean_ctor_get_uint64(lhs_obj, i * 8);
        rhs[i] = lean_ctor_get_uint64(rhs_obj, i * 8);
    }

    uint64_t r[4], acc[4];
    uint64_t a0 = comppoly_mul_small(lhs, rhs[0], acc);
    comppoly_interleaved_reduction(m, ni, a0, acc, r);
    for (int i = 1; i < 4; i++) {
        uint64_t b0 = comppoly_mul_small_acc(lhs, rhs[i], r, acc);
        comppoly_interleaved_reduction(m, ni, b0, acc, r);
    }

    lean_object *res = lean_alloc_ctor(0, 0, 4 * sizeof(uint64_t));
    for (int i = 0; i < 4; i++) {
        lean_ctor_set_uint64(res, i * 8, r[i]);
    }
    return res;
}
