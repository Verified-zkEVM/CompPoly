#!/usr/bin/env python3
"""Generate a kernel-checkable Rabin irreducibility certificate for a monic
polynomial `f` over a prime field `F_p`.

This is a TCB-external generator: it computes the certificate data (the
quotient/remainder of every repeated-squaring step, and the Euclidean gcd
chain) and emits it as JSON. Nothing here is trusted — the Lean side re-checks
every step in the kernel via `rfl`.

Rabin's test for a monic `f` of *prime* degree `d` over `F_p` reduces to:
  (A trace)   f | X^(p^d) - X      i.e.   X^(p^d) mod f == X
  (B coprime) gcd(f, X^p - X) == 1  i.e.  no linear factors

Polynomials are little-endian coefficient lists over `range(p)`.

Usage (default: KoalaBear, f = x^5 + x^2 - 1):
    python3 scripts/gen_rabin_certificate.py
"""
from __future__ import annotations
import argparse, json, sys


def poly_trim(a: list[int]) -> list[int]:
    a = a[:]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def poly_degree(a: list[int]) -> int:
    a = poly_trim(a)
    return len(a) - 1 if any(a) else -1


def poly_mul(a: list[int], b: list[int], p: int) -> list[int]:
    if not any(a) or not any(b):
        return [0]
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                res[i + j] = (res[i + j] + ai * bj) % p
    return poly_trim(res)


def divmod_monic(a: list[int], f: list[int], p: int) -> tuple[list[int], list[int]]:
    """Return (q, r) with a = q*f + r, deg r < deg f. `f` must be monic."""
    assert f[-1] == 1, "modulus must be monic"
    a = poly_trim(a)
    df = len(f) - 1
    q = [0] * max(1, len(a) - df)
    r = a[:]
    while poly_degree(r) >= df and any(r):
        dr = poly_degree(r)
        c = r[dr]  # leading coeff of r; f monic so no inverse needed
        shift = dr - df
        q[shift] = (q[shift] + c) % p
        for i in range(len(f)):
            r[dr - df + i] = (r[dr - df + i] - c * f[i]) % p
        r = poly_trim(r)
    return poly_trim(q), poly_trim(r)


def poly_mod(a: list[int], f: list[int], p: int) -> list[int]:
    return divmod_monic(a, f, p)[1]


def poly_gcd_steps(a: list[int], b: list[int], p: int):
    """Euclid on (a, b); record steps a_k = q_k * b_k + r_k. Returns (monic gcd, steps)."""
    steps = []
    a, b = poly_trim(a), poly_trim(b)
    while any(b):
        q, r = divmod_monic_general(a, b, p)
        steps.append({"a": a, "b": b, "q": q, "r": r})
        a, b = b, r
    # normalize gcd to monic
    if any(a):
        inv = pow(a[-1], p - 2, p)
        a = poly_trim([(c * inv) % p for c in a])
    return a, steps


def divmod_monic_general(a: list[int], b: list[int], p: int) -> tuple[list[int], list[int]]:
    """General polynomial division a = q*b + r (b need not be monic)."""
    a = poly_trim(a)
    b = poly_trim(b)
    db = poly_degree(b)
    inv = pow(b[db], p - 2, p)
    q = [0] * max(1, len(a) - db)
    r = a[:]
    while poly_degree(r) >= db and any(r):
        dr = poly_degree(r)
        c = (r[dr] * inv) % p
        shift = dr - db
        q[shift] = (q[shift] + c) % p
        for i in range(len(b)):
            r[dr - db + i] = (r[dr - db + i] - c * b[i]) % p
        r = poly_trim(r)
    return poly_trim(q), poly_trim(r)


def poly_bezout(a: list[int], b: list[int], p: int):
    """Extended Euclid: return (g, u, v) with u*a + v*b = g, g the monic gcd."""
    r0, r1 = poly_trim(a), poly_trim(b)
    u0, u1 = [1], [0]
    v0, v1 = [0], [1]
    while any(r1):
        q, r = divmod_monic_general(r0, r1, p)
        r0, r1 = r1, r
        qq = poly_mul(q, u1, p)
        u0, u1 = u1, poly_trim([(x - y) % p for x, y in zip_pad(u0, qq)])
        qq = poly_mul(q, v1, p)
        v0, v1 = v1, poly_trim([(x - y) % p for x, y in zip_pad(v0, qq)])
    # normalize gcd to monic
    if any(r0):
        inv = pow(r0[-1], p - 2, p)
        r0 = poly_trim([(c * inv) % p for c in r0])
        u0 = poly_trim([(c * inv) % p for c in u0])
        v0 = poly_trim([(c * inv) % p for c in v0])
    return r0, u0, v0


def zip_pad(a: list[int], b: list[int]):
    n = max(len(a), len(b))
    return zip(a + [0] * (n - len(a)), b + [0] * (n - len(b)))


def xpow_mod_cert(e: int, f: list[int], p: int):
    """Compute X^e mod f by MSB-first square-and-multiply, recording each step.

    Each step is either a squaring (u -> u^2 = q*f + r) or a multiply-by-X
    (u -> u*X = q*f + r). Returns (final remainder, steps)."""
    steps = []
    bits = bin(e)[2:]  # MSB first
    cur = poly_mod([0, 1], f, p)  # X^1 mod f (first bit is always 1 for X^e, e>=1)
    for bit in bits[1:]:
        # square
        sq = poly_mul(cur, cur, p)
        q, r = divmod_monic(sq, f, p)
        steps.append({"op": "sq", "u": cur, "q": q, "r": r})
        cur = r
        if bit == "1":
            # multiply by X
            mx = poly_mul(cur, [0, 1], p)
            q, r = divmod_monic(mx, f, p)
            steps.append({"op": "mulX", "u": cur, "q": q, "r": r})
            cur = r
    return cur, steps


def steps_to_lean(steps) -> str:
    """Render a step list as a Lean `List CompPoly.RabinCert.Step` literal,
    wrapping each step across two lines to respect the 100-column style limit."""
    rows = []
    for s in steps:
        mulx = "true" if s["op"] == "mulX" else "false"
        q = ", ".join(str(c) for c in s["q"])
        r = ", ".join(str(c) for c in s["r"])
        one_line = f"  ⟨{mulx}, [{q}], [{r}]⟩"
        if len(one_line) <= 98:
            rows.append(one_line)
        else:
            rows.append(f"  ⟨{mulx}, [{q}],\n    [{r}]⟩")
    return "[\n" + ",\n".join(rows) + "]"


def poly_to_lean(l: list[int]) -> str:
    return "[" + ", ".join(str(c) for c in l) + "]"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--p", type=int, default=2**31 - 2**24 + 1)  # KoalaBear
    ap.add_argument("--f", type=str, default="-1,0,1,0,0,1",
                    help="little-endian coeffs of monic f (leading 1 included)")
    ap.add_argument("--out", type=str, default=None, help="write full JSON certificate here")
    ap.add_argument("--lean", type=str, default=None,
                    help="write Lean data definitions (steps + Bezout) here")
    ap.add_argument("--namespace", type=str, default="QuinticCert",
                    help="namespace for the emitted Lean definitions")
    args = ap.parse_args()
    p = args.p
    f = [c % p for c in map(int, args.f.split(","))]
    assert f[-1] == 1, "f must be monic (leading coeff 1)"
    d = len(f) - 1

    # Cond B: X^p mod f = rp; then Bezout u*f + v*w = 1 for w = rp - X.
    rp, xp_steps = xpow_mod_cert(p, f, p)
    rp = poly_trim(rp)
    w = rp[:]
    while len(w) < 2:
        w.append(0)
    w[1] = (w[1] - 1) % p
    w = poly_trim(w)
    g, u, v = poly_bezout(f, w, p)
    condB = (g == [1])
    # sanity: u*f + v*w == 1 (mod p)
    lhs = poly_trim([(x + y) % p for x, y in
                     zip_pad(poly_mul(u, f, p), poly_mul(v, w, p))])
    assert lhs == [1], f"Bezout check failed: {lhs}"
    # sanity: rp == w + X coefficientwise mod p
    assert poly_trim([c % p for c in rp]) == poly_trim(
        [(x + y) % p for x, y in zip_pad(w, [0, 1])]), "rp != w + X"

    # Cond A: X^(p^d) mod f == X.
    xpd, xpd_steps = xpow_mod_cert(p ** d, f, p)
    condA = (poly_trim(xpd) == [0, 1])

    irreducible = condA and condB
    summary = {
        "p": p, "f": f, "degree": d,
        "condA_trace_ok": condA, "condA_steps": len(xpd_steps),
        "condB_coprime_ok": condB, "condB_xp_steps": len(xp_steps),
        "condB_rp": rp, "condB_w": w, "condB_u": u, "condB_v": v,
        "IRREDUCIBLE": irreducible,
    }
    print(json.dumps(summary, indent=2))

    if args.out:
        with open(args.out, "w") as fh:
            json.dump({"summary": summary,
                       "condA": {"steps": xpd_steps},
                       "condB": {"xp_steps": xp_steps}}, fh)
        print(f"full certificate written to {args.out}", file=sys.stderr)

    if args.lean:
        ns = args.namespace
        lines = [
            "/-",
            "Copyright (c) 2026 CompPoly Contributors. All rights reserved.",
            "Released under Apache 2.0 license as described in the file LICENSE.",
            "Authors: Derek Sorensen",
            "-/",
            "module",
            "",
            "public import CompPoly.Data.Polynomial.RabinCertificate",
            "",
            "/-!",
            f"# Rabin certificate data for `p = {p}`",
            "",
            f"The modulus `f` has little-endian coefficients `{f}`.",
            "",
            f"GENERATED by `scripts/gen_rabin_certificate.py --p {p} --f {args.f!r}`.",
            "Do not edit by hand; regenerate instead. Nothing here is trusted — the kernel",
            "re-checks every step through `CompPoly.RabinCert.runChain`.",
            "-/",
            "",
            "@[expose] public section",
            "",
            f"namespace {ns}",
            "",
            "open CompPoly.RabinCert",
            "",
            f"/-- Square-and-multiply chain for `X^(p^{d}) mod f` "
            f"({len(xpd_steps)} steps). -/",
            f"def traceSteps : List Step := {steps_to_lean(xpd_steps)}",
            "",
            f"/-- Square-and-multiply chain for `X^p mod f` ({len(xp_steps)} steps). -/",
            f"def frobSteps : List Step := {steps_to_lean(xp_steps)}",
            "",
            "/-- The residue `X^p mod f`. -/",
            f"def rp : List ℕ := {poly_to_lean(rp)}",
            "",
            "/-- `w = (X^p mod f) - X`, the reduced form of `X^p - X`. -/",
            f"def w : List ℕ := {poly_to_lean(w)}",
            "",
            "/-- Bézout coefficient: `u·f + v·w = 1`. -/",
            f"def u : List ℕ := {poly_to_lean(u)}",
            "",
            "/-- Bézout coefficient: `u·f + v·w = 1`. -/",
            f"def v : List ℕ := {poly_to_lean(v)}",
            "",
            f"end {ns}",
            "",
        ]
        with open(args.lean, "w") as fh:
            fh.write("\n".join(lines))
        print(f"Lean data written to {args.lean}", file=sys.stderr)
    return 0 if irreducible else 1


if __name__ == "__main__":
    raise SystemExit(main())
