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
| **BLS12_377.lean** | Scalar field of BLS12-377 (253-bit, 2-adicity 47) — Zexe. |
| **BLS12_381.lean** | Scalar field of BLS12-381 (253-bit, 2-adicity 47). |
| **BN254.lean** | Scalar field of BN254 curve. |
| **Extension.lean** | Facade for the binomial field-extension stack. |
| **Extension/Binomial.lean** | Irreducibility of `X^d - W` over a finite field: Rabin's test collapsed to two base-field exponentiations (`irreducible_X_pow_four_sub_C_iff`). |
| **Extension/Defs.lean** | `BinomialParams` (degree, `W`, base cardinality) and the carrier `Ext P = Vector F d` with its ring operations. |
| **Extension/Bridge.lean** | `toQuot : Ext P → AdjoinRoot P.poly`, its ring-hom and injectivity proofs, and `CommRing (Ext P)`. |
| **Extension/Field.lean** | Bijectivity (`ringEquivQuot`), cardinality, Fermat inversion, and `Field (Ext P)`. |
| **BabyBear/Ext4.lean** | \(\mathrm{BabyBear}[X]/(X^4 - 11)\). |
| **KoalaBear/Ext4.lean** | \(\mathrm{KoalaBear}[X]/(X^4 - 3)\). |
| **Hachi.lean** | \(2^{32} - 99\) — 32-bit prime field. **Name provisional.** Included as a 32-bit example rather than a production target: it exercises a base field with no Montgomery fast path (`Mont32Field` requires modulus < 2^31) and two-adicity 2, so no radix-2 NTT domain exists for it. |
| **Hachi/Ext4.lean** | \(\mathrm{Hachi}[X]/(X^4 - 2)\). |
| **Goldilocks.lean** | \(2^{64} - 2^{32} + 1\) — Plonky2/3. |
| **KoalaBear.lean** | Facade for KoalaBear modules, re-exporting the canonical field and fast native-word implementation. |
| **KoalaBear/Basic.lean** | \(2^{31} - 2^{24} + 1\) — lean Ethereum spec. |
| **KoalaBear/Fast.lean** | KoalaBear-namespaced API over the shared fast-field implementation (`Montgomery/Native32Field.lean`): thin wrappers forwarding the native `UInt32` Montgomery-residue operations and their `KoalaBear.Field` equivalence (`@[simp]`) lemmas. |
| **Mersenne.lean** | \(2^{31} - 1\) — Circle STARKs. |
| **Montgomery/Basic.lean** | Radix-generic Montgomery reduction, field-agnostic number theory shared by the fast prime fields. |
| **Montgomery/Native32.lean** | Raw `UInt32`/`UInt64` Montgomery reduction over explicit word constants, including bounds and correctness. |
| **Montgomery/Native32Field.lean** | Per-field parameters, the shared `FastField` carrier, arithmetic, instances, and canonical-field bridge. |
| **Secp256k1.lean** | Base and scalar fields for the Secp256k1 curve (used in Bitcoin/Ethereum). |

## Binary-field modules

The `Binary/` subtree provides characteristic-2 field infrastructure used by GHASH and additive-NTT workflows:

- `Binary/BF128Ghash/*` — GF(2^128) model, implementation, and certificates.
- `Binary/AdditiveNTT/*` — additive-NTT domain/algorithm/correctness stack.
- `Binary/Tower/*` — abstract/concrete binary tower-field constructions and supporting lemmas.

## Field extensions

`Extension/` provides computable `F[X]/(X^d - W)` arithmetic in odd characteristic, with the
`Field` structure proved by transport along a ring equivalence to `AdjoinRoot (X^d - W)`, plus
`Algebra F (Ext P)`, a base embedding `ofBase`, and the adjoined root `gen` with
`gen ^ d = ofBase W`.
Irreducibility of the defining polynomial comes from Rabin's test, which for a binomial
collapses to two exponentiations in the base field — no generated certificates and no
`native_decide`. See [`../../docs/wiki/field-extensions.md`](../../docs/wiki/field-extensions.md).

The characteristic-2 `Binary/Tower/` stack is a separate, independent development.

## Primality proofs

Primality is proved via Pratt certificates (Lucas witnesses). Some field definitions (e.g. BN254, BLS12_377) use explicit `PrattCertificate'` proofs, while others construct certificate-driven primality proofs in a similar style.

## References

- [Kestrel crypto primes (ACL2)](https://github.com/acl2/acl2/tree/master/books/kestrel/crypto/primes)
- [SEC 2.4.1 — Secp256k1](http://www.secg.org/sec2-v2.pdf)
- [BCGMMW18 — Zexe (BLS12-377)](https://eprint.iacr.org/2018/962)
- [Rabin80 — Probabilistic Algorithms in Finite Fields](https://doi.org/10.1137/0209024)
- [Lidl & Niederreiter — Finite Fields, 2nd ed., Theorem 3.75](https://doi.org/10.1017/CBO9780511525926)
