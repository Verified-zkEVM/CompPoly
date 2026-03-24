# Fields for ZK Protocols

This directory contains formally verified field infrastructure used in zero-knowledge proof systems and elliptic-curve cryptography, including scalar prime fields and binary-field constructions.

## Modules

| Module | Description |
|--------|-------------|
| **Basic.lean** | `NonBinaryField` type class (char ≠ 2), polynomial composition lemmas (`coeffs_of_comp_minus_x`, `comp_x_square_coeff`). |
| **PrattCertificate.lean** | Lucas test for primality and Pratt certificate infrastructure (`PrattCertificate`, `PrattCertificate'`) for proving concrete primality goals. |
| **BabyBear.lean** | \(2^{31} - 2^{27} + 1\) — Risc Zero. |
| **BLS12_377.lean** | Scalar field of BLS12-377 (253-bit, 2-adicity 47) — Zexe. |
| **BLS12_381.lean** | Scalar field of BLS12-381 (253-bit, 2-adicity 47). |
| **BN254.lean** | Scalar field of BN254 curve. |
| **Goldilocks.lean** | \(2^{64} - 2^{32} + 1\) — Plonky2/3. |
| **KoalaBear.lean** | \(2^{31} - 2^{24} + 1\) — lean Ethereum spec; includes `NonBinaryField` instance and roots-of-unity tables. |
| **Mersenne.lean** | \(2^{31} - 1\) — Circle STARKs. |
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
