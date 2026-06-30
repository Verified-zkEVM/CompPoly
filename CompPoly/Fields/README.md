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
| **Goldilocks.lean** | \(2^{64} - 2^{32} + 1\) — Plonky2/3. |
| **KoalaBear.lean** | Facade for KoalaBear modules, re-exporting the canonical field and fast native-word implementation. |
| **KoalaBear/Basic.lean** | \(2^{31} - 2^{24} + 1\) — lean Ethereum spec. |
| **KoalaBear/Fast.lean** | KoalaBear-namespaced API over the shared fast-field implementation (`Montgomery/Native32Field.lean`): thin wrappers forwarding the native `UInt32` Montgomery-residue operations and their `KoalaBear.Field` equivalence (`@[simp]`) lemmas. |
| **Mersenne.lean** | \(2^{31} - 1\) — Circle STARKs. |
| **Montgomery/Basic.lean** | Radix-generic Montgomery reduction, field-agnostic number theory shared by the fast prime fields. |
| **Montgomery/Native32.lean** | `UInt32 × UInt64`, radix `R = 2^32` word-level Montgomery bridge over the generic core. |
| **Montgomery/Native32Field.lean** | Shared 32-bit-word fast-field implementation over the word bridge: the `Mont32Field` per-field data class, the `FastField` carrier, every field operation, the algebraic instances, and the `toField`/`ofField` correctness bridge — written once and instantiated by both BabyBear and KoalaBear. |
| **Secp256k1.lean** | Base and scalar fields for the Secp256k1 curve (used in Bitcoin/Ethereum). |

## Binary-field modules

The `Binary/` subtree provides characteristic-2 field infrastructure used by GHASH and additive-NTT workflows:

- `Binary/BF128Ghash/*` — GF(2^128) model, implementation, and certificates.
- `Binary/AdditiveNTT/*` — additive-NTT domain/algorithm/correctness stack.
- `Binary/Tower/*` — abstract/concrete binary tower-field constructions and supporting lemmas.

## Primality proofs

Primality is proved via Pratt certificates (Lucas witnesses). Some field definitions (e.g. BN254, BLS12_377) use explicit `PrattCertificate'` proofs, while others construct certificate-driven primality proofs in a similar style.

## References

- [Kestrel crypto primes (ACL2)](https://github.com/acl2/acl2/tree/master/books/kestrel/crypto/primes)
- [SEC 2.4.1 — Secp256k1](http://www.secg.org/sec2-v2.pdf)
- [BCGMMW18 — Zexe (BLS12-377)](https://eprint.iacr.org/2018/962)
