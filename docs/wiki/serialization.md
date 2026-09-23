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
  bit pattern of the declared basis. Two constructors cover the concrete cases:
  `CanonicalNat.ofToField` builds the structure of a fast carrier from its own `toNat` and the
  conversion from `ZMod p`, taking the carrier-agreement law as a hypothesis;
  `CanonicalNat.ofBitVec` builds it from a bit-pattern presentation.
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
| `AesField`, tower level 3 | 1 |
| `Ext P` | `P.d` times the base width |

For a bit-pattern type the width is `(k + 7) / 8` by `bytesFor_two_pow`, so a binary field's
width lemma is a small numeral computation rather than a kernel evaluation of `2 ^ k`.

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
  plus sixteen bytes. `CompPoly/Data/Bytes/Bias.lean` proves this by counting:
  `card_fiber_ofBytesModOrder` gives the exact number of `n`-byte strings landing on each
  element (`256 ^ n / bound` or one more), and `tv_ofBytesModOrder_le` the total-variation
  bound over `ℚ`, with no probability theory. ArkLib's `Deserialize.CloseToUniform` is derived
  from it.

## Fast carriers must agree with the spec

A fast carrier of a prime field stores a Montgomery residue or a raw word. Its `CanonicalNat`
instance reduces on the way out (`toField`) and converts on the way in (`ofField`), and it owes
the lemma that its `toNat` agrees with the `ZMod` instance under `ofField`. That lemma is what
makes the bytes carrier-independent, and it doubles as the correctness statement of the fast
instance. Dumping the stored Montgomery word would be faster and wrong.

| Carrier | Instance module | Agreement lemma |
|---|---|---|
| `Native32.FastField` (BabyBear, KoalaBear) | `CompPoly/Fields/Montgomery/Native32Bytes.lean` | `FastField.toBytes_ofField` |
| `Native64x8.FastField` (BN254, BLS12-377/381, Pasta) | `CompPoly/Fields/Montgomery/Native64x8Bytes.lean` | `FastField.toBytes_ofField` |
| `Goldilocks.Fast.Field` | `CompPoly/Fields/Goldilocks/Bytes.lean` | `toBytes_ofField` |
| `Mersenne31.Fast.Field` | `CompPoly/Fields/Mersenne31/Bytes.lean` | `toBytes_ofField` |
| `FastBT128` against `ConcreteBTField 7` | `CompPoly/Fields/Binary/Tower/Bytes.lean` | `toByteArray_toConcrete` |

Every `ZMod p` gets its instances from `CompPoly/Data/Bytes/CanonicalNat.lean` at once, so the
spec fields need no per-field module.

## Binary fields

A binary field element is a bit pattern relative to a basis, and the basis is part of the type.
`AesField` and level three of the binary tower both have 256 elements and different bases;
`ConcreteBF128Ghash` and `FastBT128` likewise at 128 bits. Each instance encodes the bit pattern
of its own declared basis, little-endian, and documents the modulus polynomial
(`CompPoly/Fields/Binary/BF64/Bytes.lean`, `CompPoly/Fields/Binary/BF128Ghash/Bytes.lean`,
`CompPoly/Fields/Binary/Aes/Bytes.lean`, `CompPoly/Fields/Binary/Tower/Bytes.lean`). There is
no cross-presentation conversion in the serialization layer; the explicit ring homomorphisms
such as `AesField.toGhash` remain the only sanctioned path. GCM's big-endian, bit-reflected
wire format is out of scope here and would be a separately named codec. For a bit-pattern type
the bound is `2 ^ (8 * width)`, so exact-width decoding never fails and exact-width squeezing is
exactly uniform.

## Vectors and extensions

`Vector F n` encodes as the concatenation of its entries' encodings, `n * width F` bytes
(`CompPoly/Data/Bytes/Vector.lean`), and decodes entry by entry, failing if any entry fails.
`Ext P` is its coefficient vector, so it encodes as `P.d * width F` bytes
(`CompPoly/Fields/Extension/Bytes.lean`), the arkworks and plonky3 layout. This is not the
little-endian expansion of the element's base-`q` canonical natural, which is why `Ext` has a
`ByteCodec` but no `CanonicalNat`. Challenges in `Ext P` are read coefficient by coefficient
from `P.d * k` bytes, and a vector of challenges likewise from `n * k` bytes; these instances
are stated at the product `n * k`, so a protocol should write its challenge sizes as products.

## Self-delimiting codecs

A variable-length type cannot have a `ByteCodec`. What it has instead is `DelimitedCodec α`
(`CompPoly/Data/Bytes/Delimited.lean`): `encode : α → List UInt8` and
`decode? : List UInt8 → Option (α × List UInt8)`, a decoder that reads exactly one encoding off
the front of a stream and returns the rest, with the law
`decode? (encode x ++ rest) = some (x, rest)` for every `Valid x`. `Valid` marks what the
format can represent: everything for a fixed-width codec (`DelimitedCodec.ofByteCodec`, so
every `ByteCodec` is a delimited codec too), and for the framed formats below, whatever fits
in a `u64`.

Lengths, counts, and exponents are `u64` little-endian words, the arkworks layout. So a natural
is valid below `2 ^ 64`, and a list is valid when its length is and its entries are. The class
derives `Serialize`, `DeserializeOption`, and `Serde` on `ByteArray` (a `ByteArray` must hold
exactly one encoding; leftover bytes are refused), and `Serialize.IsInjective` for `Total`
codecs, where everything is valid. Otherwise injectivity is `encode_inj`, which takes the two
validity hypotheses. Composite codecs exist for lists (count, then entries), pairs (first, then
second), and fixed-length vectors (entries, no count; a definition, `DelimitedCodec.vector`,
rather than an instance, so a vector of fixed-width elements keeps its `ByteCodec`).

## Polynomials

| Type | Codec | Layout | Module |
|---|---|---|---|
| `↥(degreeLT n)` | `ByteCodec`, `n * width R` | the `n` coefficients, zero-padded; decoding trims | `CompPoly/Univariate/Bytes.lean` |
| `CPolynomial R` | `DelimitedCodec` | `u64` count, then the coefficients | `CompPoly/Univariate/Bytes.lean` |
| `CMlPolynomial R n`, `CMlPolynomialEval R n` | `ByteCodec`, `2 ^ n * width R` | the vector codec, little-endian index order | `CompPoly/Multilinear/Bytes.lean` |
| `CMvPolynomial n R` | `DelimitedCodec` | `u64` term count, then terms in key order: `n` exponents as `u64`, then the coefficient | `CompPoly/Multivariate/Bytes.lean` |
| `CBivariate R` | `DelimitedCodec` | the univariate codec at coefficient type `CPolynomial R` | `CompPoly/Bivariate/Bytes.lean` |

The fixed-width univariate codec is the message shape of a sumcheck round polynomial or a FRI
fold; it is unconditionally injective. The self-delimiting one is for fixtures and hashing and
nests, which is how the bivariate codec is obtained for free. Both are injective because the
representation is canonical: no trailing zeros, sorted keys with no zero coefficients. They
agree where they overlap: `encode_eq_encodeU64_append_toBytes` says the self-delimiting
encoding is the count followed by the fixed-width encoding at `n = size`. A univariate
polynomial over a fixed-width coefficient type is `Valid` exactly when its size is below
`2 ^ 64` (`valid_iff_size_lt`); a multivariate one additionally needs every exponent below
`2 ^ 64`. Decoding a multivariate polynomial rebuilds the map and drops zero coefficients, so
it lands on the canonical polynomial whatever order the stream listed the terms in.

There is no fixed-width multivariate codec. Genuinely multivariate protocol messages are
multilinear, and those have the dense codec.

## Adding an instance

1. Give the type `CanonicalNat` if it is a scalar: `bound`, `toNat`, `ofNat`, four laws. For a
   fast carrier, implement `toNat` through `toField` and prove agreement with the `ZMod`
   instance.
2. Give it `ByteCodec`: `ByteCodec.ofCanonicalNat _` for a scalar, concatenation for a
   composite.
3. Everything ArkLib consumes is now derived. Add a `#guard` round trip and one known vector to
   the mirrored test module under `tests/CompPolyTests/`.

For a variable-length type, give it `DelimitedCodec` instead, built from the list, pair, and
vector codecs, with `Valid` stating what fits in the framing, and prove the one law from the
laws of the parts.
