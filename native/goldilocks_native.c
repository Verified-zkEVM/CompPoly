#include <stdint.h>
#include <lean/lean.h>

/*
 * Native performance primitives for Goldilocks fast arithmetic.
 *
 * These functions are called from Lean through @[extern] declarations in
 * CompPoly/Fields/Goldilocks/FastExt.lean. Lean verifies only the types of the
 * extern declarations, not the arithmetic performed here. This file is
 * therefore part of the trusted native boundary for the extern-backed API.
 *
 * The verified Lean implementation remains the default field implementation;
 * this native code is used only by the opt-in FastExt module.
 */

// Return the high 64 bits of a 64-by-64 unsigned multiplication.
LEAN_EXPORT uint64_t lean_uint64_mul_hi(uint64_t a, uint64_t b) {
    return (uint64_t)(((unsigned __int128)a * b) >> 64);
}

static const uint64_t GOLDILOCKS_NEG_MODULUS = 0x00000000FFFFFFFFULL;

static inline uint64_t goldilocks_add_no_canonicalize(uint64_t x, uint64_t y) {
    uint64_t res = x + y;
    return res + (res < x ? GOLDILOCKS_NEG_MODULUS : 0);
}

// Goldilocks multiplication modulo p = 2^64 - 2^32 + 1.
LEAN_EXPORT uint64_t lean_goldilocks_mul(uint64_t a, uint64_t b) {
    unsigned __int128 prod = (unsigned __int128)a * b;
    uint64_t lo = (uint64_t)prod;
    uint64_t hi = (uint64_t)(prod >> 64);

    uint64_t hi_hi = hi >> 32;
    uint64_t hi_lo = hi & GOLDILOCKS_NEG_MODULUS;

    uint64_t t0 = lo - hi_hi;
    if (lo < hi_hi) {
        t0 -= GOLDILOCKS_NEG_MODULUS;
    }

    uint64_t t1 = hi_lo * GOLDILOCKS_NEG_MODULUS;
    return goldilocks_add_no_canonicalize(t0, t1);
}
