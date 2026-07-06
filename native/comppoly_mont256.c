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

/*
 * Pornin binary-GCD inverse candidate (CompPoly/Fields/Montgomery/Native256Gcd.lean,
 * explicit-constant copies in Native256Ext.lean). The result is a *candidate*: Lean
 * verifies it with a Montgomery multiplication and falls back to the proven Fermat
 * window, so nothing here is load-bearing for correctness — only for the fast-path
 * hit rate. Variable shift counts are masked (`& 63`) to match Lean's mod-64
 * `UInt64` shift semantics.
 */

static inline void comppoly_copy4(uint64_t dst[4], const uint64_t src[4]) {
    dst[0] = src[0];
    dst[1] = src[1];
    dst[2] = src[2];
    dst[3] = src[3];
}

/* `subb` (UInt256L.lean): one limb of subtract-with-borrow. */
static inline uint64_t comppoly_subb(uint64_t a, uint64_t b, uint64_t borrow,
                                     uint64_t *diff) {
    uint64_t s1 = a - b;
    uint64_t b1 = a < b ? 1 : 0;
    uint64_t s2 = s1 - borrow;
    uint64_t b2 = s1 < borrow ? 1 : 0;
    *diff = s2;
    return b1 + b2;
}

/* `gcdBitLen`: word bit length by binary search. */
static inline size_t comppoly_gcd_bit_len(uint64_t x) {
    if (x == 0)
        return 0;
    uint64_t v = x;
    size_t r = 1;
    if (v >> 32) { v >>= 32; r += 32; }
    if (v >> 16) { v >>= 16; r += 16; }
    if (v >> 8)  { v >>= 8;  r += 8; }
    if (v >> 4)  { v >>= 4;  r += 4; }
    if (v >> 2)  { v >>= 2;  r += 2; }
    if (v >> 1)  { r += 1; }
    return r;
}

/* `gcdNumBits`: highest nonzero limb index among limbs 1..3 and its bit length. */
static inline void comppoly_gcd_num_bits(uint64_t l1, uint64_t l2, uint64_t l3,
                                         size_t *limb, size_t *bits) {
    size_t v3 = comppoly_gcd_bit_len(l3);
    if (v3 != 0) { *limb = 3; *bits = v3; return; }
    size_t v2 = comppoly_gcd_bit_len(l2);
    if (v2 != 0) { *limb = 2; *bits = v2; return; }
    *limb = 1;
    *bits = comppoly_gcd_bit_len(l1);
}

/* `gcdApprox`: top 33 bits (relative to the shared bit length) glued above the
 * bottom 31 bits. The `limb - 1` index replicates Lean's saturating `Nat`
 * subtraction, and `gcdLimb` clamps indexes above 3 to the top limb. */
static inline uint64_t comppoly_gcd_approx(const uint64_t val[4], size_t limb,
                                           size_t bits) {
    uint64_t hi = val[limb > 3 ? 3 : limb];
    size_t lo_i = limb == 0 ? 0 : limb - 1;
    uint64_t lo = val[lo_i > 3 ? 3 : lo_i];
    size_t s = bits + 31;
    uint64_t top;
    if (s < 64)
        top = (lo >> (s & 63)) | (hi << ((64 - s) & 63));
    else
        top = hi >> ((s - 64) & 63);
    return (top << 31) | (val[0] & 0x7FFFFFFFULL);
}

/* `gcdInner`: the word-sized divstep loop accumulating the transition matrix
 * `(f0, g0, f1, g1)` from the initial matrix passed in. Lean carries the entries
 * as `Int`; they satisfy `|f| + |g| <= 2^rounds`, and every call keeps
 * `rounds <= 62` (31 in the main loop, `gcdFinalRounds <= 62` by the class
 * contract), so `int64_t` never overflows. The final `a`, `b` are not returned:
 * no caller uses them. */
static inline void comppoly_gcd_inner(size_t rounds, uint64_t a, uint64_t b,
                                      int64_t f0, int64_t g0, int64_t f1, int64_t g1,
                                      int64_t out[4]) {
    for (; rounds > 0; rounds--) {
        if (a & 1) {
            if (a < b) {
                uint64_t tw = a; a = b; b = tw;
                int64_t t;
                t = f0; f0 = f1; f1 = t;
                t = g0; g0 = g1; g1 = t;
            }
            a -= b;
            f0 -= f1;
            g0 -= g1;
        }
        a >>= 1;
        f1 *= 2;
        g1 *= 2;
    }
    out[0] = f0; out[1] = g0; out[2] = f1; out[3] = g1;
}

/* `Int.natAbs` of an `int64_t` whose magnitude fits (unsigned negate avoids UB). */
static inline uint64_t comppoly_int64_abs(int64_t f) {
    return f < 0 ? (uint64_t)0 - (uint64_t)f : (uint64_t)f;
}

/* `gcdMul5`: `a * f` as a 5-limb unsigned value, via `mulSmall`. */
static inline void comppoly_gcd_mul5(const uint64_t a[4], uint64_t f, uint64_t out[5]) {
    uint64_t hi[4];
    out[0] = comppoly_mul_small(a, f, hi);
    out[1] = hi[0]; out[2] = hi[1]; out[3] = hi[2]; out[4] = hi[3];
}

/* `gcdAdd5`: 5-limb ripple-carry add, top carry discarded. */
static inline void comppoly_gcd_add5(const uint64_t p[5], const uint64_t q[5],
                                     uint64_t out[5]) {
    uint64_t c = 0;
    for (int i = 0; i < 5; i++) {
        c = comppoly_addc(p[i], q[i], c, &out[i]);
    }
}

/* `gcdSub5`: 5-limb subtract with borrow; returns the final borrow. */
static inline uint64_t comppoly_gcd_sub5(const uint64_t p[5], const uint64_t q[5],
                                         uint64_t out[5]) {
    uint64_t brw = 0;
    for (int i = 0; i < 5; i++) {
        brw = comppoly_subb(p[i], q[i], brw, &out[i]);
    }
    return brw;
}

/* `gcdLinearCombDiv`: `(f*a + g*b) / 2^k` via a positive - negative split; writes
 * the magnitude and returns the sign (0 or -1). The shift pair replicates Lean's
 * saturating `64 - k` and mod-64 shifts. */
static inline int comppoly_gcd_lincomb_div(const uint64_t a[4], const uint64_t b[4],
                                           int64_t f, int64_t g, size_t k,
                                           uint64_t out[4]) {
    static const uint64_t zero5[5] = {0, 0, 0, 0, 0};
    uint64_t fa[5], gb[5], pos[5], neg[5], pmn[5], d[5];
    comppoly_gcd_mul5(a, comppoly_int64_abs(f), fa);
    comppoly_gcd_mul5(b, comppoly_int64_abs(g), gb);
    int f_neg = f < 0;
    int g_neg = g < 0;
    comppoly_gcd_add5(f_neg ? zero5 : fa, g_neg ? zero5 : gb, pos);
    comppoly_gcd_add5(f_neg ? fa : zero5, g_neg ? gb : zero5, neg);
    uint64_t borrow = comppoly_gcd_sub5(pos, neg, pmn);
    int sign;
    if (borrow == 0) {
        for (int i = 0; i < 5; i++) d[i] = pmn[i];
        sign = 0;
    } else {
        comppoly_gcd_sub5(neg, pos, d);
        sign = -1;
    }
    size_t shk = k & 63;
    size_t shc = (k >= 64 ? 0 : 64 - k) & 63;
    out[0] = (d[0] >> shk) | (d[1] << shc);
    out[1] = (d[1] >> shk) | (d[2] << shc);
    out[2] = (d[2] >> shk) | (d[3] << shc);
    out[3] = (d[3] >> shk) | (d[4] << shc);
    return sign;
}

/* `gcdLinearCombUnsigned`: `a*f + b*g` as a 5-limb value, split as
 * (lowest limb, high four limbs) ready for the reduction step. */
static inline uint64_t comppoly_gcd_lincomb_unsigned(const uint64_t a[4],
                                                     const uint64_t b[4], uint64_t f,
                                                     uint64_t g, uint64_t out_hi[4]) {
    uint64_t ph[4], qh[4], r0;
    uint64_t p0 = comppoly_mul_small(a, f, ph);
    uint64_t q0 = comppoly_mul_small(b, g, qh);
    uint64_t c = comppoly_addc(p0, q0, 0, &r0);
    for (int i = 0; i < 4; i++) {
        c = comppoly_addc(ph[i], qh[i], c, &out_hi[i]);
    }
    return r0;
}

/* `gcdLinearCombMontyRedWith`: `f*a + g*b` folded through one Montgomery
 * reduction step, negative coefficients absorbed via `m - a` / `m - b`. */
static inline void comppoly_gcd_lincomb_montyred(const uint64_t m[4], uint64_t ni,
                                                 const uint64_t a[4],
                                                 const uint64_t b[4], int64_t f,
                                                 int64_t g, uint64_t out[4]) {
    uint64_t a_signed[4], b_signed[4], acc[4];
    if (f < 0) comppoly_sub256(m, a, a_signed); else comppoly_copy4(a_signed, a);
    if (g < 0) comppoly_sub256(m, b, b_signed); else comppoly_copy4(b_signed, b);
    uint64_t acc0 = comppoly_gcd_lincomb_unsigned(a_signed, b_signed,
                                                  comppoly_int64_abs(f),
                                                  comppoly_int64_abs(g), acc);
    comppoly_interleaved_reduction(m, ni, acc0, acc, out);
}

/* `gcdMainLoopWith`: the outer rounds — one-word approximations, 31 divsteps,
 * matrix application to `(a, b)` and to the Montgomery pair `(u, v)`. */
static void comppoly_gcd_main_loop(const uint64_t m[4], uint64_t ni, size_t rounds,
                                   uint64_t a[4], uint64_t u[4], uint64_t b[4],
                                   uint64_t v[4]) {
    for (; rounds > 0; rounds--) {
        size_t limb, bits;
        comppoly_gcd_num_bits(a[1] | b[1], a[2] | b[2], a[3] | b[3], &limb, &bits);
        uint64_t a_tilde = comppoly_gcd_approx(a, limb, bits);
        uint64_t b_tilde = comppoly_gcd_approx(b, limb, bits);
        int64_t fg[4];
        comppoly_gcd_inner(31, a_tilde, b_tilde, 1, 0, 0, 1, fg);
        int64_t f0 = fg[0], g0 = fg[1], f1 = fg[2], g1 = fg[3];
        uint64_t new_a[4], new_b[4], new_u[4], new_v[4];
        int sign_a = comppoly_gcd_lincomb_div(a, b, f0, g0, 31, new_a);
        if (sign_a < 0) { f0 = -f0; g0 = -g0; }
        int sign_b = comppoly_gcd_lincomb_div(a, b, f1, g1, 31, new_b);
        if (sign_b < 0) { f1 = -f1; g1 = -g1; }
        comppoly_gcd_lincomb_montyred(m, ni, u, v, f0, g0, new_u);
        comppoly_gcd_lincomb_montyred(m, ni, u, v, f1, g1, new_v);
        comppoly_copy4(a, new_a);
        comppoly_copy4(b, new_b);
        comppoly_copy4(u, new_u);
        comppoly_copy4(v, new_v);
    }
}

/* `gcdInvCandidateNative` (Native256Ext.lean): 15 outer rounds from
 * `(input, initU, m, 0)`, then `finalRounds` exact divsteps on the one-word
 * remainders and a last Montgomery fold. `finalRounds` is a Lean `Nat`, always
 * word-sized here (<= 62 by the class contract). */
LEAN_EXPORT lean_object *comppoly_mont256_gcd_inv(b_lean_obj_arg m_obj, uint64_t ni,
                                                  b_lean_obj_arg init_u_obj,
                                                  b_lean_obj_arg final_rounds_obj,
                                                  b_lean_obj_arg input_obj) {
    uint64_t m[4], a[4], u[4], b[4], v[4] = {0, 0, 0, 0};
    for (int i = 0; i < 4; i++) {
        m[i] = lean_ctor_get_uint64(m_obj, i * 8);
        a[i] = lean_ctor_get_uint64(input_obj, i * 8);
        u[i] = lean_ctor_get_uint64(init_u_obj, i * 8);
    }
    comppoly_copy4(b, m);
    size_t final_rounds = lean_usize_of_nat(final_rounds_obj);

    comppoly_gcd_main_loop(m, ni, 15, a, u, b, v);
    int64_t fg[4];
    comppoly_gcd_inner(final_rounds, a[0], b[0], 1, 0, 0, 1, fg);
    uint64_t r[4];
    comppoly_gcd_lincomb_montyred(m, ni, u, v, fg[2], fg[3], r);

    lean_object *res = lean_alloc_ctor(0, 0, 4 * sizeof(uint64_t));
    for (int i = 0; i < 4; i++) {
        lean_ctor_set_uint64(res, i * 8, r[i]);
    }
    return res;
}
