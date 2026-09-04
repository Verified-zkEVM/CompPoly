#!/usr/bin/env python3
"""Generate a kernel-checkable Rabin irreducibility certificate for a monic
polynomial `f` over a prime field `F_p`.

This is a TCB-external generator: it computes the certificate data (the
quotient/remainder of every repeated-squaring step, and a Bezout identity in
place of a Euclidean gcd chain) and emits it as JSON. Nothing here is trusted —
the Lean side re-checks every step in the kernel via `rfl`.

Rabin's test for a monic `f` of degree `d` over `F_p` reduces to:
  (A trace)    f | X^(p^d) - X            i.e.  X^(p^d) mod f == X
  (B coprime)  gcd(f, X^(p^(d/l)) - X) == 1   for every prime l | d

Condition B must be checked once *per prime factor* of `d`. At prime `d` there
is a single factor and `d/l = 1`, so B collapses to `gcd(f, X^p - X) == 1` —
"no linear factors". At composite `d` that collapsed form is **not sufficient**:
a product of equal-degree factors satisfies both A and the `d/l = 1` check. For
instance over KoalaBear, `(X^3 + X + 4)(X^3 + X - 4)` has no root in `F_p` and
all its roots lie in `F_(p^6)`, so it passes A and the linear-factor check while
being visibly reducible. Only the `d/3 = 2` and `d/2 = 3` checks reject it.

Polynomials are little-endian coefficient lists over `range(p)`.

Usage (default: KoalaBear, f = x^5 + x^2 - 1):
    python3 scripts/gen_rabin_certificate.py

Self-test over the known-answer cases in `SELF_TESTS`:
    python3 scripts/gen_rabin_certificate.py --self-test
"""
from __future__ import annotations
import argparse, json, sys
import textwrap


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


def prime_factors(n: int) -> list[int]:
    """The distinct prime factors of `n`, ascending. Mirrors `Nat.primeFactors` in Lean."""
    out, m, q = [], n, 2
    while q * q <= m:
        if m % q == 0:
            out.append(q)
            while m % q == 0:
                m //= q
        q += 1
    if m > 1:
        out.append(m)
    return out


def coprime_cert(f: list[int], p: int, m: int):
    """Certificate that `gcd(f, X^(p^m) - X) == 1`.

    Computes `rp = X^(p^m) mod f`, sets `w = rp - X` (the reduced form of
    `X^(p^m) - X`), and finds a Bezout pair with `u*f + v*w = 1`. Coprimality
    holds exactly when the gcd is a unit. Returns a dict of the certificate
    data plus an `ok` flag.
    """
    rp, steps = xpow_mod_cert(p ** m, f, p)
    rp = poly_trim(rp)
    w = rp[:]
    while len(w) < 2:
        w.append(0)
    w[1] = (w[1] - 1) % p
    w = poly_trim(w)
    g, u, v = poly_bezout(f, w, p)
    ok = (g == [1])
    if ok:
        # sanity: u*f + v*w == 1 (mod p)
        lhs = poly_trim([(x + y) % p for x, y in
                         zip_pad(poly_mul(u, f, p), poly_mul(v, w, p))])
        assert lhs == [1], f"Bezout check failed at m={m}: {lhs}"
    # sanity: rp == w + X coefficientwise mod p
    assert poly_trim([c % p for c in rp]) == poly_trim(
        [(x + y) % p for x, y in zip_pad(w, [0, 1])]), f"rp != w + X at m={m}"
    return {"m": m, "ok": ok, "steps": steps, "rp": rp, "w": w, "u": u, "v": v}


def build_certificate(p: int, f: list[int]) -> dict:
    """Run Rabin's test on monic `f` over `F_p`, returning all certificate data.

    Condition A is the trace check. Condition B is checked once per prime factor
    of `d = deg f`, at exponent `p^(d/l)`. `f` is irreducible iff all hold.
    """
    assert f[-1] == 1, "f must be monic (leading coeff 1)"
    d = len(f) - 1
    # d >= 2 keeps `X` in reduced form, so the trace residue can be compared against the
    # literal [0, 1]. This matches `ExtensionParams.two_le` on the Lean side.
    assert d >= 2, "f must have degree at least 2"

    # Cond A: X^(p^d) mod f == X.
    xpd, xpd_steps = xpow_mod_cert(p ** d, f, p)
    condA = (poly_trim(xpd) == [0, 1])

    # Cond B: one coprimality certificate per prime factor of d, at m = d/l.
    factors = prime_factors(d)
    coprimes = [coprime_cert(f, p, d // ell) for ell in factors]
    condB = all(c["ok"] for c in coprimes)

    return {
        "p": p, "f": f, "degree": d, "prime_factors": factors,
        "condA_trace_ok": condA, "condA_steps": len(xpd_steps),
        "condB_coprime_ok": condB,
        "condB": [{"prime": ell, "m": c["m"], "ok": c["ok"], "steps": len(c["steps"]),
                   "rp": c["rp"], "w": c["w"], "u": c["u"], "v": c["v"]}
                  for ell, c in zip(factors, coprimes)],
        "IRREDUCIBLE": condA and condB,
        "_trace_steps": xpd_steps, "_coprimes": coprimes,
    }


# (p, coeff string, expected verdict, note) — known answers guarding the generator.
SELF_TESTS = [
    (5, "1,1,1", True, "X^2+X+1 over F_5, the RabinCertificate.lean test vector"),
    (2130706433, "-1,0,1,0,0,1", True, "KoalaBear quintic X^5+X^2-1 (Ext5)"),
    (2130706433, "1,0,0,1,0,0,1", True, "KoalaBear sextic X^6+X^3+1 = Phi_9 (Ext6)"),
    (2130706433, "-16,0,1,0,2,0,1", False,
     "(X^3+X+4)(X^3+X-4): passes trace + linear-factor check, but is reducible"),
    (2130706433, "-3,0,0,0,0,0,1", False, "X^6-3: no sextic binomial exists over KoalaBear"),
    (2130706433, "-3,0,0,0,1", True, "KoalaBear quartic X^4-3 (Ext4), composite degree"),
]


def self_test() -> int:
    """Check the generator against known-answer cases. Returns a process exit code."""
    failures = 0
    for p, fstr, expected, note in SELF_TESTS:
        f = [c % p for c in map(int, fstr.split(","))]
        got = build_certificate(p, f)["IRREDUCIBLE"]
        status = "ok  " if got == expected else "FAIL"
        if got != expected:
            failures += 1
        print(f"[{status}] p={p} f={fstr!r} irreducible={got} (expected {expected})  {note}")
    print(f"\n{len(SELF_TESTS) - failures}/{len(SELF_TESTS)} passed")
    return 1 if failures else 0


def _wrap_coeffs(coeffs: list[int], indent: str, limit: int = 98) -> str:
    """Render a coefficient list as a bracketed Lean literal, filling lines up to
    `limit` columns and continuing on `indent`-prefixed lines. Long lists (high-degree
    moduli, or small primes with many terms) do not fit on one or two lines."""
    body_lines: list[str] = []
    cur = indent + "["
    first = True
    for c in coeffs:
        tok = str(c) if first else ", " + str(c)
        # +1 leaves room for the closing bracket or a trailing comma.
        if not first and len(cur) + len(tok) + 1 > limit:
            body_lines.append(cur + ",")
            cur = indent + " " + str(c)
        else:
            cur += tok
        first = False
    body_lines.append(cur + "]")
    return "\n".join(body_lines).lstrip()


def steps_to_lean(steps) -> str:
    """Render a step list as a Lean `List CompPoly.RabinCert.Step` literal, wrapping
    each step so that every emitted line respects the 100-column style limit."""
    rows = []
    for s in steps:
        mulx = "true" if s["op"] == "mulX" else "false"
        q = ", ".join(str(c) for c in s["q"])
        r = ", ".join(str(c) for c in s["r"])
        one_line = f"  ⟨{mulx}, [{q}], [{r}]⟩"
        if len(one_line) <= 98:
            rows.append(one_line)
            continue
        two_line = f"  ⟨{mulx}, [{q}],\n    [{r}]⟩"
        if all(len(ln) <= 98 for ln in two_line.split("\n")):
            rows.append(two_line)
            continue
        # Both halves still overflow: wrap each coefficient list over as many
        # lines as it needs.
        q_wrapped = _wrap_coeffs(s["q"], "    ")
        r_wrapped = _wrap_coeffs(s["r"], "    ")
        rows.append(f"  ⟨{mulx},\n    {q_wrapped},\n    {r_wrapped}⟩")
    return "[\n" + ",\n".join(rows) + "]"


def _wrap_command(p: int, f_arg: str, ns: str, authors: str) -> list[str]:
    """Emit the regeneration command as shell lines, none exceeding the style limit.
    The `--f` argument is a single unbreakable token, so it is split across
    backslash-continued lines the way a shell accepts them."""
    lines = ["python3 scripts/gen_rabin_certificate.py --p %d \\" % p]
    head = "  --f '"
    budget = 96
    chunks: list[str] = []
    cur = ""
    for piece in f_arg.split(","):
        tok = piece if not cur else "," + piece
        if cur and len(cur) + len(tok) > budget - 4:
            chunks.append(cur)
            cur = piece
        else:
            cur += tok
    if cur:
        chunks.append(cur)
    if len(chunks) == 1:
        lines.append(head + chunks[0] + "' \\")
    else:
        lines.append(head + chunks[0] + ",\\")
        for c in chunks[1:-1]:
            lines.append(c + ",\\")
        lines.append(chunks[-1] + "' \\")
    lines.append("  --lean <this file> --namespace %s \\" % ns)
    lines.append("  --authors '%s'" % authors)
    return lines


def poly_to_lean(l: list[int], prefix_len: int = 0, indent: str = "  ") -> str:
    """Render a coefficient list, wrapping if the rendered `def` line would overflow.
    `prefix_len` is the width of the `def <name> : List ℕ := ` text preceding it."""
    one_line = "[" + ", ".join(str(c) for c in l) + "]"
    if prefix_len + len(one_line) <= 98:
        return one_line
    return _wrap_coeffs(l, indent, limit=98 - prefix_len if prefix_len else 98)


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
    ap.add_argument("--authors", type=str, default="Derek Sorensen",
                    help="value for the Authors line of the generated copyright header")
    ap.add_argument("--self-test", action="store_true",
                    help="check the generator against known-answer cases and exit")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    p = args.p
    f = [c % p for c in map(int, args.f.split(","))]
    cert = build_certificate(p, f)
    d = cert["degree"]
    xpd_steps = cert["_trace_steps"]
    coprimes = cert["_coprimes"]
    condA, condB = cert["condA_trace_ok"], cert["condB_coprime_ok"]

    irreducible = cert["IRREDUCIBLE"]
    summary = {k: v for k, v in cert.items() if not k.startswith("_")}
    print(json.dumps(summary, indent=2))

    if args.out:
        with open(args.out, "w") as fh:
            json.dump({"summary": summary,
                       "condA": {"steps": xpd_steps},
                       "condB": [{"m": c["m"], "steps": c["steps"]} for c in coprimes]}, fh)
        print(f"full certificate written to {args.out}", file=sys.stderr)

    if args.lean:
        ns = args.namespace
        is_prime_degree = cert["prime_factors"] == [d]
        # At prime degree there is exactly one coprimality certificate, at exponent `p^1`, and it
        # keeps the historical `frobSteps`/`rp`/`w`/`u`/`v` names so existing generated modules
        # regenerate unchanged. At composite degree the blocks are suffixed by `m = d / l`.
        cop_lines: list[str] = []
        for ell, c in zip(cert["prime_factors"], coprimes):
            m = c["m"]
            if is_prime_degree:
                names = ("frobSteps", "rp", "w", "u", "v")
                exp = "p"
            else:
                names = (f"cop{m}Steps", f"cop{m}Rp", f"cop{m}W", f"cop{m}U", f"cop{m}V")
                exp = f"p^{m}"
            sname, rname, wname, uname, vname = names
            cop_lines += [
                f"/-! ### Coprimality with `X^({exp}) - X`, for the prime factor `{ell}` of "
                f"`d = {d}`. -/",
                "",
                f"/-- Square-and-multiply chain for `X^({exp}) mod f` "
                f"({len(c['steps'])} steps). -/",
                f"def {sname} : List Step := {steps_to_lean(c['steps'])}",
                "",
                f"/-- The residue `X^({exp}) mod f`. -/",
                f"def {rname} : List ℕ := "
                f"{poly_to_lean(c['rp'], len(rname) + 20)}",
                "",
                f"/-- `{wname} = (X^({exp}) mod f) - X`, the reduced form of `X^({exp}) - X`. -/",
                f"def {wname} : List ℕ := "
                f"{poly_to_lean(c['w'], len(wname) + 20)}",
                "",
                f"/-- Bézout coefficient: `{uname}·f + {vname}·{wname} = 1`. -/",
                f"def {uname} : List ℕ := "
                f"{poly_to_lean(c['u'], len(uname) + 20)}",
                "",
                f"/-- Bézout coefficient: `{uname}·f + {vname}·{wname} = 1`. -/",
                f"def {vname} : List ℕ := "
                f"{poly_to_lean(c['v'], len(vname) + 20)}",
                "",
            ]
        if is_prime_degree:
            # Preserve the original layout exactly: no per-factor section heading, and the
            # coprimality chain is introduced with its historical docstring wording.
            cop_lines = [
                f"/-- Square-and-multiply chain for `X^p mod f` "
                f"({len(coprimes[0]['steps'])} steps). -/",
                f"def frobSteps : List Step := {steps_to_lean(coprimes[0]['steps'])}",
                "",
                "/-- The residue `X^p mod f`. -/",
                f"def rp : List ℕ := {poly_to_lean(coprimes[0]['rp'], 22)}",
                "",
                "/-- `w = (X^p mod f) - X`, the reduced form of `X^p - X`. -/",
                f"def w : List ℕ := {poly_to_lean(coprimes[0]['w'], 21)}",
                "",
                "/-- Bézout coefficient: `u·f + v·w = 1`. -/",
                f"def u : List ℕ := {poly_to_lean(coprimes[0]['u'], 21)}",
                "",
                "/-- Bézout coefficient: `u·f + v·w = 1`. -/",
                f"def v : List ℕ := {poly_to_lean(coprimes[0]['v'], 21)}",
                "",
            ]
        lines = [
            "/-",
            "Copyright (c) 2026 CompPoly Contributors. All rights reserved.",
            "Released under Apache 2.0 license as described in the file LICENSE.",
            f"Authors: {args.authors}",
            "-/",
            "module",
            "",
            "public import CompPoly.Data.Polynomial.RabinCertificate",
            "",
            "/-!",
            f"# Rabin certificate data for `p = {p}`",
            "",
            *textwrap.wrap(f"The modulus `f` has little-endian coefficients `{f}`.",
                           width=98, break_long_words=False, break_on_hyphens=False),
            "",
            *([] if is_prime_degree else [
                f"`d = {d}` is composite, so Rabin's coprimality condition needs one certificate "
                f"per",
                f"prime factor of `d` ({', '.join(map(str, cert['prime_factors']))}), at exponents "
                f"{', '.join('p^' + str(c['m']) for c in coprimes)} respectively. Checking only "
                "the",
                "linear-factor case would admit a product of equal-degree factors.",
                "",
            ]),
            "GENERATED. Do not edit by hand; regenerate with:",
            "",
            "```sh",
            *_wrap_command(p, args.f, args.namespace, args.authors),
            "```",
            "",
            "Nothing here is trusted — the kernel re-checks every step through",
            "`CompPoly.RabinCert.runChain`, so incorrect data fails to compile rather than",
            "producing a false theorem.",
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
            *cop_lines,
            f"end {ns}",
            "",
        ]
        with open(args.lean, "w") as fh:
            fh.write("\n".join(lines))
        print(f"Lean data written to {args.lean}", file=sys.stderr)
    return 0 if irreducible else 1


if __name__ == "__main__":
    raise SystemExit(main())
