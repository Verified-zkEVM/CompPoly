# Fields for ZK Protocols

This directory contains formally verified field infrastructure used in zero-knowledge proof systems and elliptic-curve cryptography, including scalar prime fields and binary-field constructions.

## Modules

| Module | Description |
|--------|-------------|
| **Basic.lean** | `NonBinaryField` type class (char ≠ 2), polynomial composition lemmas (`coeffs_of_comp_minus_x`, `comp_x_square_coeff`). |
| **PrattCertificate.lean** | Lucas test for primality and Pratt certificate infrastructure (`PrattCertificate`, `PrattCertificate'`) for proving concrete primality goals. |
| **BabyBear.lean** | Facade for BabyBear modules, re-exporting the canonical field and fast native-word implementation. |
| **BabyBear/Basic.lean** | \(2^{31} - 2^{27} + 1\) — Risc Zero. |
| **BabyBear/Fast.lean** | BabyBear-namespaced API over the shared fast-field implementation (`Montgomery/Native32Field.lean`): thin wrappers forwarding the native `UInt32` Montgomery-residue operations and their `BabyBear.Field` equivalence (`@[simp]`) lemmas. |
| **BLS12_377.lean** | Facade for the BLS12-377 modules, re-exporting the canonical field and the fast eight-limb implementation. |
| **BLS12_377/Basic.lean** | Scalar field of BLS12-377 (253-bit, 2-adicity 47) — Zexe. |
| **BLS12_377/Fast.lean** | Eight-limb Montgomery instantiation of the BLS12-377 scalar field (`Mont64x8Field` and `GcdData` constants, `ScalarField`, `ringEquiv`). |
| **BLS12_381.lean** | Facade for the BLS12-381 modules, re-exporting the canonical field and the fast eight-limb implementation. |
| **BLS12_381/Basic.lean** | Scalar field of BLS12-381 (255-bit, 2-adicity 32). |
| **BLS12_381/Fast.lean** | Eight-limb Montgomery instantiation of the BLS12-381 scalar field (`Mont64x8Field` and `GcdData` constants, `ScalarField`, `ringEquiv`). |
| **BN254.lean** | Facade for the BN254 modules, re-exporting the canonical field and the fast eight-limb implementation. |
| **BN254/Basic.lean** | Scalar field of BN254 (254-bit, 2-adicity 28). |
| **BN254/Fast.lean** | Eight-limb Montgomery instantiation of the BN254 scalar field (`Mont64x8Field` and `GcdData` constants, `ScalarField`, `ringEquiv`). |
| **Extension.lean** | Facade for the field-extension stack (arbitrary monic modulus; binomial as a special case). |
| **Extension/Binomial.lean** | Irreducibility of `X^d - W` over a finite field: Rabin's test collapsed to two base-field exponentiations (`irreducible_X_pow_four_sub_C_iff`). |
| **Extension/Defs.lean** | `ExtensionParams` (degree, lower coefficients of the monic modulus, base cardinality), `BinomialParams` and its `toExtensionParams`, and the carrier `Ext P = Vector F d` with its ring operations — including the `red` reduction table and the `@[csimp]`-registered `mulTbl`. |
| **Extension/Bridge.lean** | `toQuot : Ext P → AdjoinRoot P.poly`, its ring-hom and injectivity proofs, and `CommRing (Ext P)`. |
| **Extension/Field.lean** | Bijectivity (`ringEquivQuot`), cardinality, Fermat inversion, and `Field (Ext P)`. |
| **BabyBear/Ext4.lean** | \(\mathrm{BabyBear}[X]/(X^4 - 11)\). |
| **KoalaBear/Ext4.lean** | \(\mathrm{KoalaBear}[X]/(X^4 - 3)\). |
| **KoalaBear/Ext5.lean** | \(\mathrm{KoalaBear}[X]/(X^5 + X^2 - 1)\) — first non-binomial modulus; no degree-5 binomial exists since \(\gcd(5, p-1) = 1\). |
| **KoalaBear/Ext5/QuinticCertData.lean** | Generated Rabin certificate data for the quintic. Regenerate with `scripts/gen_rabin_certificate.py`; do not hand-edit. |
| **KoalaBear/Ext5/QuinticIrreducible.lean** | Kernel-checked irreducibility of \(X^5 + X^2 - 1\) via Rabin's test at prime degree. |
| **KoalaBear/Ext6.lean** | \(\mathrm{KoalaBear}[X]/(X^6 + X^3 + 1)\) — \(\Phi_9\), a \(2^{186}\)-element field. No degree-6 binomial exists since \(3 \nmid p-1\) makes every element a cube. |
| **KoalaBear/Ext6/SexticCertData.lean** | Generated Rabin certificate data for the sextic, including one coprimality certificate per prime factor of 6. Do not hand-edit. |
| **KoalaBear/Ext6/SexticIrreducible.lean** | Kernel-checked irreducibility of \(X^6 + X^3 + 1\) via Rabin's test at composite degree. |
| **KoalaBear/Ext6/GaloisField.lean** | Opt-in bridge identifying `Ext6` with Mathlib's abstract `GaloisField KoalaBear.fieldSize 6` (ArkLib's `KoalaSextic` parameter point). Separate module so the GaloisField import is not forced on `Ext6` users. |
| **Goldilocks.lean** | Facade for the \(2^{64} - 2^{32} + 1\) Plonky2/3 field, re-exporting the canonical `ZMod` model and fast native-word implementation. |
| **Goldilocks/Basic.lean** | Canonical \(2^{64} - 2^{32} + 1\) field model and primality proof. |
| **Goldilocks/Fast.lean** | Verified `UInt64` implementation of Goldilocks arithmetic. A single-word 64-bit prime fits neither Montgomery carrier — `Mont32Field` requires modulus < 2^31 and `Mont64x8Field` is an eight-limb layout — so this is a bespoke implementation resting on \(2^{64} \equiv 2^{32} - 1\). |
| **Goldilocks/FastDefs.lean** | Zero-import runtime word kernels behind `Goldilocks/Fast.lean`, kept importless so `precompileModules` lanes can compile them. |
| **Hachi.lean** | \(2^{32} - 99\) — 32-bit prime field. **Name provisional.** Included as a 32-bit example rather than a production target: it exercises a base field with no Montgomery fast path (`Mont32Field` requires modulus < 2^31) and two-adicity 2, so no radix-2 NTT domain exists for it. |
| **Hachi/Ext4.lean** | \(\mathrm{Hachi}[X]/(X^4 - 2)\). |
| **KoalaBear.lean** | Facade for KoalaBear modules, re-exporting the canonical field and fast native-word implementation. |
| **KoalaBear/Basic.lean** | \(2^{31} - 2^{24} + 1\) — lean Ethereum spec. |
| **KoalaBear/Fast.lean** | KoalaBear-namespaced API over the shared fast-field implementation (`Montgomery/Native32Field.lean`): thin wrappers forwarding the native `UInt32` Montgomery-residue operations and their `KoalaBear.Field` equivalence (`@[simp]`) lemmas. |
| **Mersenne31.lean** | Facade for the \(2^{31} - 1\) Circle STARK field, re-exporting the canonical `ZMod` model and fast native-word implementation. |
| **Mersenne31/Basic.lean** | Canonical \(2^{31} - 1\) field model and primality proof. |
| **Mersenne31/Fast.lean** | Verified `UInt32` implementation of Mersenne31 arithmetic. |
| **Mersenne.lean** | Deprecated compatibility re-export of `Mersenne31.lean`; retained so existing imports continue to work. |
| **Montgomery/Basic.lean** | Radix-generic Montgomery reduction, field-agnostic number theory shared by the fast prime fields. |
| **Montgomery/Native32.lean** | Raw `UInt32`/`UInt64` Montgomery reduction over explicit word constants, including bounds and correctness. |
| **Montgomery/Native32Field.lean** | Per-field parameters, the shared `FastField` carrier, arithmetic, instances, and canonical-field bridge. |
| **Montgomery/Native64x8Defs.lean** | Zero-import runtime definitions of the eight-limb Montgomery arithmetic, for `precompileModules` consumers. |
| **Montgomery/Native64x8.lean** | Word-level specifications and add/sub/negate correctness for the eight-limb arithmetic. |
| **Montgomery/Native64x8Mul.lean** | Correctness of the eight-limb CIOS Montgomery multiplication. |
| **Montgomery/Native64x8Field.lean** | The `Mont64x8Field` class, `FastField` carrier, arithmetic, instances, and canonical-field bridge for moduli below `2^255`. |
| **Montgomery/Native64x8InvDefs.lean** | Mathlib-free binary-GCD inversion runtime ([eprint 2020/972](https://eprint.iacr.org/2020/972)): the `GcdData` schedule, the candidate, and the checked `invGcdRaw`. |
| **Montgomery/Native64x8Inv.lean** | Correctness of the checked inversion (`invGcdRaw`, wrapper `FastField.invGcd`), the divstep coefficient bounds, and the candidate's mac-width safety. |
| **Secp256k1.lean** | Base and scalar fields for the Secp256k1 curve (used in Bitcoin/Ethereum). |

## Binary-field modules

The `Binary/` subtree provides characteristic-2 field infrastructure used by GHASH and additive-NTT workflows:

- `Binary/BF128Ghash/*` — GF(2^128) model, implementation, and certificates.
- `Binary/AdditiveNTT/*` — additive-NTT domain/algorithm/correctness stack.
- `Binary/Tower/*` — abstract/concrete binary tower-field constructions and supporting lemmas.
- `Binary/Tower/Fast.lean` — packed machine-word tower arithmetic with a GF(2^8) table base, proven against the concrete tower; `Field` instances up to GF(2^128).
- `Binary/Tower/FastDefs.lean` — zero-import runtime definitions of the packed tower arithmetic, for `precompileModules` consumers.

## Field extensions

`Extension/` provides computable `F[X]/f` arithmetic for an arbitrary monic `f` in odd
characteristic, with the `Field` structure proved against `AdjoinRoot f`, plus
`Algebra F (Ext P)`, a base embedding `ofBase`, and the adjoined root `gen`. Binomial moduli
`X^d - W` are the special case entered through `BinomialParams.toExtensionParams`, and get
`gen ^ d = ofBase W`.

Irreducibility of the defining polynomial comes from Rabin's test. For a binomial it collapses to
two exponentiations in the base field — no generated certificates. For a general modulus it uses
kernel-checked certificates emitted by `scripts/gen_rabin_certificate.py`, with one coprimality
certificate per prime factor of the degree. Neither path uses `native_decide`. See
[`../../docs/wiki/field-extensions.md`](../../docs/wiki/field-extensions.md).

The characteristic-2 `Binary/Tower/` stack is a separate, independent development.

## Primality proofs

Primality is proved via Pratt certificates (Lucas witnesses). Some field definitions (e.g. BN254, BLS12_377) use explicit `PrattCertificate'` proofs, while others construct certificate-driven primality proofs in a similar style.

## References

- [Kestrel crypto primes (ACL2)](https://github.com/acl2/acl2/tree/master/books/kestrel/crypto/primes)
- [SEC 2.4.1 — Secp256k1](http://www.secg.org/sec2-v2.pdf)
- [BCGMMW18 — Zexe (BLS12-377)](https://eprint.iacr.org/2018/962)
- [Rabin80 — Probabilistic Algorithms in Finite Fields](https://doi.org/10.1137/0209024)
- [Lidl & Niederreiter — Finite Fields, 2nd ed., Theorem 3.75](https://doi.org/10.1017/CBO9780511525926)
