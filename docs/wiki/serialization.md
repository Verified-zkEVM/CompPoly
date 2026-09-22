# Serialization

How CompPoly turns field elements and polynomials into bytes, and what a consumer such as
ArkLib's Fiat-Shamir layer can rely on. The class layer is in `CompPoly/Data/Classes/`, the
encoder in `CompPoly/Data/Bytes/`, and the per-field instances sit beside each carrier.

## The contract

A protocol absorbs messages into a duplex sponge as fixed-size vectors of units and squeezes
challenges back out. That fixes the shape of everything here:

- **Fixed width.** Every element of a type encodes to the same number of bytes.
- **Injective.** Distinct elements have distinct encodings, and the proof is an instance.
- **Value, not carrier.** The bytes depend only on the abstract field element. Two carriers of
  the same field, say `ZMod p` and a Montgomery word, encode equal elements identically.
- **Little-endian canonical integer.** The layout arkworks and plonky3 use.

## Classes

The protocol-facing classes are ArkLib's, ported verbatim so ArkLib can import them from here:

| Class | File | Meaning |
|---|---|---|
| `Serialize α β`, `Serialize.IsInjective` | `CompPoly/Data/Classes/Serialize.lean` | `α → β`, and its injectivity as a `Prop` class |
| `Deserialize α β` | same | total decoder `β → α` |
| `DeserializeOption α β`, `Serde α β` | same | partial decoder, and the pair |
| `HasSize α β` | `CompPoly/Data/Classes/HasSize.lean` | an embedding `α ↪ Vector β size` |

`Deserialize.CloseToUniform`, the statistical-distance class, stays in ArkLib because it needs
`PMF`; CompPoly proves the counting fact behind it in `Nat` terms.

Two classes are CompPoly's own:

- **`CanonicalNat F`** (`CompPoly/Data/Classes/CanonicalNat.lean`): `bound`, `toNat`, and a
  total `ofNat` that reduces modulo `bound`, with laws making `toNat` a bijection onto
  `Fin bound`. So `bound` is the cardinality and `ofNat n` is the element with canonical natural
  `n % bound`. For a prime field the canonical natural is the residue; for a binary field the
  bit pattern of the declared basis; for an extension the base-`q` expansion of its coefficients.
- **`ByteCodec F`** (`CompPoly/Data/Bytes/Codec.lean`): `width`, `toBytes : F → Vector UInt8
  width`, and `ofBytes?` with the one law `ofBytes? (toBytes x) = some x`. From it, `HasSize`,
  `Serialize`, `Serialize.IsInjective`, `DeserializeOption`, and `Serde` are derived once, for
  both `ByteArray` and `Vector UInt8 width`.

The vector instances are stated at `Vector UInt8 (ByteCodec.width F)`. Instance search does not
unfold `width` to a numeral, so ask for `Vector UInt8 (ByteCodec.width BabyBear.Field)` rather
than `Vector UInt8 4`; a protocol that fixes message sizes should define them in terms of
`ByteCodec.width`. In proofs and `#guard`s the numeral is available by `decide` or `rfl`.

## Deriving bytes from canonical naturals

`ByteCodec.ofCanonicalNat F` (`CompPoly/Data/Bytes/CanonicalNat.lean`) is the codec of a scalar
field: `bytesFor bound` little-endian bytes of `toNat`, decoded by `ofNat?`, which fails on a
string whose integer is at or above the bound. It is a definition, not an instance, because a
composite type may want a different codec while still having a canonical natural: an
extension field concatenates the codecs of its coefficients, as arkworks and plonky3 do, which
is not the little-endian expansion of its canonical natural.

`bytesFor bound = (Nat.log2 (bound - 1) + 8) / 8` is the least width holding every natural
below `bound`, with one byte for `bound ≤ 256`. It is `Nat.log2`-based so the kernel evaluates
it on numerals: `ByteCodec.width BabyBear.Field = 4` is `by decide`.

| Field | Width |
|---|---|
| BabyBear, KoalaBear, Mersenne31 | 4 |
| Goldilocks, `BF64` | 8 |
| `BF128` | 16 |
| BN254, BLS12-377, BLS12-381, Pasta, secp256k1 scalar fields | 32 |
| `Ext P` | `P.d` times the base width |

## Decoding

Two decoders, both derived from `ofNat`:

- **Exact width, may fail.** `ofBytes?` and `ofByteArray?`. A string of the right width whose
  integer is not below the bound is rejected. This is `DeserializeOption`, the decoder for a
  transcript parser or a fixture loader. Nothing here silently truncates.
- **Reduce modulo the order, total.** `CanonicalNat.ofBytesModOrder` reads any number of bytes
  as a little-endian integer and applies `ofNat`. This is `Deserialize F (Vector UInt8 n)` for
  every `n`, the decoder for a challenge squeezed from a byte sponge. Reading back an exact-width
  encoding recovers the element; reading more bytes than the width makes the result close to
  uniform, with statistical distance at most `bound / 256 ^ n`. spongefish squeezes the width
  plus sixteen bytes.

## Fast carriers must agree with the spec

A fast carrier of a prime field stores a Montgomery residue or a raw word. Its `CanonicalNat`
instance reduces on the way out (`toField`) and converts on the way in (`ofField`), and it owes
the lemma that its `toNat` agrees with the `ZMod` instance under `ofField`. That lemma is what
makes the bytes carrier-independent, and it doubles as the correctness statement of the fast
instance. Dumping the stored Montgomery word would be faster and wrong.

## Binary fields

A binary field element is a bit pattern relative to a basis, and the basis is part of the type.
`AesField` and level three of the binary tower both have 256 elements and different bases;
`ConcreteBF128Ghash` and `FastBT128` likewise at 128 bits. Each instance encodes the bit pattern
of its own declared basis, little-endian, and documents the modulus polynomial. There is no
cross-presentation conversion in the serialization layer; the explicit ring homomorphisms such
as `AesField.toGhash` remain the only sanctioned path. GCM's big-endian, bit-reflected wire
format is out of scope here and would be a separately named codec.

## Polynomials

Variable-length types get two encodings that agree:

- **Fixed width** for protocol messages: `↥(degreeLT n)` as `n` coefficients, zero-padded,
  through `degreeLTCoeffs`; `CMlPolynomial R n` as its `2 ^ n` coefficients; `Ext P` as `P.d`
  coefficients. Unconditionally injective.
- **Self-delimiting** for fixtures and hashing: a `u64` little-endian length prefix, then the
  coefficients. Injective because the representation is canonical (no trailing zeros, sorted
  keys with no zero coefficients), stated under `size < 2 ^ 64`. The fixed encoding at
  `n = size` is the suffix of this one.

`CMvPolynomial` gets only the self-delimiting form: term count, then per term `n` exponents and
one coefficient, all `u64`-framed. `CBivariate` nests the univariate encoding.

## Adding an instance

1. Give the type `CanonicalNat` if it is a scalar: `bound`, `toNat`, `ofNat`, four laws. For a
   fast carrier, implement `toNat` through `toField` and prove agreement with the `ZMod`
   instance.
2. Give it `ByteCodec`: `ByteCodec.ofCanonicalNat _` for a scalar, concatenation for a
   composite.
3. Everything ArkLib consumes is now derived. Add a `#guard` round trip and one known vector to
   the mirrored test module under `tests/CompPolyTests/`.
