# Field Extensions

`CompPoly/Fields/Extension/` is the computable field-extension framework for odd
characteristic. It models `F[X] / f` for an **arbitrary monic modulus** `f` as a dense
coefficient vector and proves it equal to `AdjoinRoot f`, so Mathlib field theory applies to
it. The parameters are `ExtensionParams` (the modulus stored by its lower coefficients);
binomials `X^d - W` keep the ergonomic front-end `BinomialParams`, mapped in by
`BinomialParams.toExtensionParams`.

This page owns extension-field architecture. The characteristic-2 stack is a separate,
independent development — see [`binary-fields-and-ntt.md`](binary-fields-and-ntt.md).

## Binomials When Possible, General Moduli When Not

Most extension fields used in practice by a STARK or zkVM are binomial extensions: a
degree-2 to degree-8 extension of a 31- or 32-bit prime, defined by `X^d - W`. When a
binomial is available, prefer it — it buys two things:

- **Cheap irreducibility.** Rabin's test collapses to two exponentiations in the *base*
  field (see below).
- **Cheap multiplication.** `X^d = W` means the high half of the schoolbook product folds
  back with a single scalar multiply, with no polynomial remainder step.

But a binomial is not always available. A degree-`d` binomial extension of `F_q` requires
`d ∣ q - 1`; when `gcd(d, q - 1) = 1` the map `x ↦ x^d` is a bijection and **every** `X^d - W`
has a root. KoalaBear at degree 5 is exactly this case (`p - 1 = 2^24 · 127`), which is why
[`KoalaBear/Ext5.lean`](../../CompPoly/Fields/KoalaBear/Ext5.lean) adjoins a root of the
non-binomial quintic `X^5 + X^2 - 1` instead. The general-modulus framework and the
certificate-based irreducibility pipeline below exist to make such extensions routine.

## Layering

| Layer | File | Owns |
|---|---|---|
| Rabin's test, general | [`../../CompPoly/Data/Polynomial/Rabin.lean`](../../CompPoly/Data/Polynomial/Rabin.lean) | `irreducible_of_rabin`, `irreducible_iff_rabin` for any degree over any finite field |
| Factor-degree bound | [`../../CompPoly/ToMathlib/Polynomial/Irreducible.lean`](../../CompPoly/ToMathlib/Polynomial/Irreducible.lean) | `exists_factor_natDegree_le_of_reducible` |
| Binomial criterion | [`../../CompPoly/Fields/Extension/Binomial.lean`](../../CompPoly/Fields/Extension/Binomial.lean) | the collapse to base-field exponentiations; `irreducible_X_pow_four_sub_C_iff` |
| Rabin certificates | [`../../CompPoly/Data/Polynomial/RabinCertificate.lean`](../../CompPoly/Data/Polynomial/RabinCertificate.lean) | kernel-checked chains for non-binomial moduli; `runChain_sound`, `irreducible_of_rabin_prime_degree` |
| Carrier and ring ops | [`../../CompPoly/Fields/Extension/Defs.lean`](../../CompPoly/Fields/Extension/Defs.lean) | `ExtensionParams`, `BinomialParams` (+ `toExtensionParams`), `Ext P`, `Ext.shiftReduce`, `Ext.monomialMod`, `Ext.mul` |
| Bridge and `CommRing` | [`../../CompPoly/Fields/Extension/Bridge.lean`](../../CompPoly/Fields/Extension/Bridge.lean) | `toQuot`, `toQuot_shiftReduce`, `toQuot_mul`, `instCommRing` |
| Bijectivity and `Field` | [`../../CompPoly/Fields/Extension/Field.lean`](../../CompPoly/Fields/Extension/Field.lean) | `ringEquivQuot`, `card_ext`, `inv`, `instField` |

`Data/Polynomial/Rabin.lean` generalizes the degree-128/GF(2) specialization
`irreducible_of_rabin_128_passed_over_GF2` in `Fields/Binary/BF128Ghash/Basic.lean`, but does not
yet replace it — `Binary/` is deliberately untouched, so there are currently **two** Rabin
soundness proofs in the repo. Rebasing the GHASH one onto `irreducible_of_rabin` is a named
follow-up; until then, a fix to the argument needs applying in both places.

Concrete instances live next to their base field:
[`KoalaBear/Ext4.lean`](../../CompPoly/Fields/KoalaBear/Ext4.lean) (`X^4 - 3`),
[`BabyBear/Ext4.lean`](../../CompPoly/Fields/BabyBear/Ext4.lean) (`X^4 - 11`),
[`Hachi/Ext4.lean`](../../CompPoly/Fields/Hachi/Ext4.lean) (`X^4 - 2`), and the non-binomial
[`KoalaBear/Ext5.lean`](../../CompPoly/Fields/KoalaBear/Ext5.lean) (`X^5 + X^2 - 1`, with its
irreducibility proof in
[`KoalaBear/Ext5/QuinticIrreducible.lean`](../../CompPoly/Fields/KoalaBear/Ext5/QuinticIrreducible.lean)
and generated certificate data in
[`KoalaBear/Ext5/QuinticCertData.lean`](../../CompPoly/Fields/KoalaBear/Ext5/QuinticCertData.lean)).

## What The Interface Provides

Concretely, for `P : ExtensionParams F`:

| Surface | Declarations |
|---|---|
| Ring / field | `CommRing (Ext P)`, `Field (Ext P)` (the latter given `[Fact (Irreducible P.poly)]`) |
| Base field | `Ext.ofBase : F → Ext P`, `Ext.ofBaseRingHom`, `Algebra F (Ext P)` (hence `Module F (Ext P)` via `Algebra.toModule`) |
| Adjoined root | `Ext.gen`, `Ext.gen_pow_d : gen ^ d = monomialMod d`, `Ext.aeval_gen_poly : aeval gen P.poly = 0`; for a binomial, `Ext.gen_pow_d_binomial : gen ^ d = ofBase W` |
| Specification | `Ext.toQuot`, `Ext.ringEquivQuot : Ext P ≃+* AdjoinRoot P.poly` |
| Cardinality | `Fintype (Ext P)`, `Ext.card_ext : Fintype.card (Ext P) = q ^ d` |
| Coefficients | `Ext.coeff`, `Ext.ofFn`, `Ext.equivFn : Ext P ≃ (Fin d → F)` |

With the `Algebra` instance in place, ordinary Mathlib machinery — `aeval`, scalar towers,
`Subalgebra`, `Module` — applies directly.

**Still missing**, and the natural next step: tower support. There is no `AlgebraTower` instance
(`CompPoly/Data/RingTheory/AlgebraTower.lean`), so `F ⊂ Ext F 2 ⊂ Ext F 4` does not compose and
the Mersenne31 CM31/QM31 Circle-STARK stack is out of reach.

## Irreducibility: Rabin, Collapsed

Rabin's test says a degree-`d` polynomial `f` over `F_q` is irreducible exactly when
`f ∣ X^(q^d) - X` and `f` is coprime to `X^(q^(d/l)) - X` for every prime `l ∣ d`.

For a binomial, `X^d = W` gives `X^(q^j) ≡ W^((q^j - 1)/d) * X (mod X^d - W)` whenever
`d ∣ q^j - 1`. Both conditions therefore become conditions on `W` alone:

> `X^d - W` is irreducible over `F_q` **iff** `W^((q^d - 1)/d) = 1` and
> `W^((q^(d/l) - 1)/d) ≠ 1` for every prime `l ∣ d`.

For `d = 4` that is two exponentiations, discharged by `reduce_mod_char`, which does modular
repeated squaring during elaboration.

Nothing here uses `native_decide`, per the TCB policy in [`AGENTS.md`](../../AGENTS.md).

## Irreducibility: Rabin, Certified (Non-Binomial Moduli)

For a non-binomial modulus nothing collapses, and the Rabin conditions are genuine
`F[X]` statements: `f ∣ X^(q^d) - X` needs `X^(q^d) mod f`, about `d · log₂ q` modular
squarings. [`Data/Polynomial/RabinCertificate.lean`](../../CompPoly/Data/Polynomial/RabinCertificate.lean)
handles this with kernel-checked certificates:

- Polynomials are little-endian `ℕ`-coefficient lists with schoolbook arithmetic by
  structural recursion, so checks reduce in the kernel via GMP-accelerated `Nat` ops.
- A whole square-and-multiply chain is **one list literal** verified by a single kernel
  reduction of `runChain`; `runChain_sound` lifts it to `X^N % f = r % f`.
- The trace condition is a chain ending at `X`; coprimality is a chain plus a Bézout
  identity `u·f + v·w = 1` on the reduced residue — no Euclidean gcd chain.
- `irreducible_of_rabin_prime_degree` packages the test when `d` is prime (one trace, one
  coprimality check).

Certificate data is emitted by the untrusted generator
[`scripts/gen_rabin_certificate.py`](../../scripts/gen_rabin_certificate.py)
(`--lean`/`--namespace` produce a complete data module); the kernel re-checks every step.
The KoalaBear quintic instance costs ~290 generated lines and compiles in about two
seconds — contrast the roughly 2100 lines of per-step `BitVec` certificates the same test
costs the GHASH polynomial (`Fields/Binary/BF128Ghash/XPowTwoPow{Mod,Gcd}Certificate.lean`),
which predates this framework.

### Adding a new binomial extension

1. Pick `W`. For `d = 4` over `q ≡ 1 mod 4`, any non-square works; prefer the smallest, so
   that multiplying by `W` is cheap.
2. Write the `BinomialParams`, supplying `card_eq := ZMod.card _`.
3. Prove irreducibility with `irreducible_X_pow_four_sub_C_of_card`. The two exponentiation
   goals need the type presented as `ZMod <numeral>`, because `reduce_mod_char` reads the
   modulus syntactically and `fieldSize` is an expression like `2 ^ 31 - 2 ^ 24 + 1`. Use a
   `show` — see any of the three `Ext4.lean` files.
4. Register `instance : Fact (Irreducible ...)`, define the `abbrev` as
   `Ext ...Params.toExtensionParams`, and route the `Fact` through `toExtensionParams_poly` — see
   `KoalaBear/Ext4.lean`.

That is about 60 lines.

### Adding a new non-binomial extension

1. Pick a monic irreducible `f` (confirm with `scripts/gen_rabin_certificate.py`, which
   exits nonzero if `f` is reducible).
2. Generate the certificate module:
   `python3 scripts/gen_rabin_certificate.py --p <p> --f <coeffs> --lean <path> --namespace <NS>`.
3. Write the irreducibility wrapper: `toPoly p fL = f`, `natDegree`, `f ≠ 0`, then the
   chain/Bézout `rfl` checks and the assembly through `irreducible_of_rabin_prime_degree`
   (for prime `d`) — see `KoalaBear/Ext5/QuinticIrreducible.lean` for the idiom.
4. Write the `ExtensionParams` (lower coefficients of `f`, little-endian) and prove
   `...Params.poly = f`; register the `Fact` and define the `abbrev` — see
   `KoalaBear/Ext5.lean` (supporting cert/proof files under `KoalaBear/Ext5/`).

That is the generated data plus about 200 hand-written lines.

## Representation And Computability

`Ext P` is `Vector F P.d`: dense, little-endian, length exactly `d`. There is no degree-bound
invariant to maintain — the bound is *structural*, a consequence of the length, not a proposition
carried alongside the data. As a result this subtree is **independent of the `CPolynomial`
stack**: nothing under `CompPoly/Fields/Extension/` imports `CompPoly/Univariate/`.

The one place a degree bound is needed on the *polynomial* side — showing that the representative
`Ext.toQuot` picks is the canonical degree-`< d` one — is proved directly in
[`Extension/Bridge.lean`](../../CompPoly/Fields/Extension/Bridge.lean) as `degree_repr_lt`, from
`Polynomial.degree_sum_le` and `Polynomial.degree_C_mul_X_pow_le`. If you want the
`CPolynomial`-side theory instead (`degreeLT`, `degreeLTEquiv` in
[`Univariate/Linear.lean`](../../CompPoly/Univariate/Linear.lean) and
[`Univariate/ToPoly/Degree.lean`](../../CompPoly/Univariate/ToPoly/Degree.lean)), it exists but is
**not** wired to this framework; connecting them would be new work.

`ExtensionParams` carries `d`, the modulus's lower coefficients, and the base-field cardinality
`q` as a *type index*, so two different extensions of the same base field are different types
whose instances cannot be confused. `q` is data rather than `Fintype.card F` because Fermat
inversion evaluates the exponent at runtime, and `Fintype.card (ZMod p)` would enumerate all
of `Fin p`. `BinomialParams` is the ergonomic front-end for `X^d - W`, mapped in by
`BinomialParams.toExtensionParams` (lower coefficients `(-W, 0, …, 0)`), with `toExtensionParams_poly`
identifying the two spellings of the defining polynomial.

**The instances are assembled field-by-field, not by `Function.Injective.commRing` /
`.field`.** Those transports take `toQuot` as data, which forces the resulting instance
`noncomputable`. That is not merely cosmetic: `Monoid.toNatPow` then outranks `Ext.instPow`, and
compiled `x ^ n` fails to build. This was observed, not hypothesized. If you add structure to
`Ext P`, keep it computable and keep a `#guard` in
[`tests/CompPolyTests/Fields/Extension/Arithmetic.lean`](../../tests/CompPolyTests/Fields/Extension/Arithmetic.lean)
that exercises the operation, since only compiled evaluation catches this class of regression.

The load-bearing correctness lemma is `Ext.toQuot_shiftReduce`: `shiftReduce` is "multiply by
`X`, reduce mod `f`", and `toQuot (shiftReduce e) = rt * toQuot e` is the one place the
defining relation `rt_relation` is consumed. `monomialMod k = shiftReduce^[k] 1` is then
`X^k mod f` by a one-line induction, and `toQuot_mul` — `Ext.mul` expands product monomials
through `monomialMod` — follows with no wrap-around case analysis at all.

## Performance: Measured, And Not Yet Competitive

The framework is correctness-complete, and its *design* is ready for fast arithmetic — `Ext P`
is generic over the base-field carrier precisely so a Montgomery representation can be dropped
in. The current instantiation over `ZMod`, however, is **not** fast. Measured with
`lake exe CompPolyBench --small` on a developer laptop:

| Group | Operation | Average |
|---|---|---|
| `fields-extension-koalabear-ext4-mul` | `mul` | ~73 us |
| `fields-extension-koalabear-ext4-inv` | `inv` | ~13 ms |

For scale, a hand-written Rust degree-4 BabyBear multiply is a few nanoseconds. Do not quote
this framework as performance-ready until the items below are done. (Before the
general-modulus rewrite the binomial fold measured ~13.4 us / ~1.7 ms; the ~5x regression is
the cost of `monomialMod` below and is the first thing the planned rewrite recovers.)

The three causes, in order of size:

1. **`Ext.mul` recomputes the reduction per term, and separately allocates.** Two distinct
   problems, and a rewrite must fix both.

   *Asymptotics.* The definition expands each product monomial through
   `monomialMod (i + j) = shiftReduce^[i+j] 1`, recomputed for every `(m, i, j)` — that is what
   keeps the correctness proof one additive lemma, and what makes the compiled code roughly
   O(d⁴)–O(d⁵). The fast shape is O(d²): schoolbook convolution to length `2d - 1`, then fold
   the high half through a **precomputed** table `X^d … X^(2d-2) mod f` (the `monomialMod`
   values, computed once per `P` rather than per multiplication).

   *Allocation.* Because `P` is a runtime parameter nothing monomorphises: `Finset.univ` is
   rebuilt and `Fin` values boxed on every call. `@[specialize]` recovers only about 6%.

   The fix is an `Array`-loop implementation proved equal to the current sum-based definition —
   either as a separate backend behind an agreement lemma, following the `MulContext` idiom in
   [`Univariate/Context.lean`](../../CompPoly/Univariate/Context.lean), or via `@[csimp]` so the
   compiled code is swapped while every existing proof keeps referring to `Ext.mul`. Keep the
   current `monomialMod` expansion as the *spec*: it is what `toQuot_mul` is proved against,
   and reducing everything to `toQuot_shiftReduce` is why that proof is short.
2. **The base field is `ZMod p`**, i.e. boxed `Nat` arithmetic. Instantiating over
   `KoalaBear.Fast.Field` (`UInt32` Montgomery,
   [`Montgomery/Native32Field.lean`](../../CompPoly/Fields/Montgomery/Native32Field.lean))
   needs only `Fintype` for that carrier plus irreducibility transported along
   `Montgomery.Native32.ringEquiv` with `Polynomial.mapEquiv`. No change to the framework.
3. **Inversion is Fermat** (`x ^ (q^d - 2)`), about `d · log q` extension multiplications — the
   ~130x ratio to `mul` above. A norm-based inverse would be roughly an order of magnitude
   faster: when `d ∣ q - 1` the Frobenius map is a coordinate-wise scaling by powers of
   `W^((q-1)/d)`, so `N(x) = ∏_j φ^j(x)` lands in the base field and
   `x⁻¹ = (∏_{j≥1} φ^j(x)) · N(x)⁻¹`.

None of these is hidden behind an abstraction that makes replacing it awkward, and each is
guarded by the `#guard` regressions in
[`tests/CompPolyTests/Fields/Extension/Arithmetic.lean`](../../tests/CompPolyTests/Fields/Extension/Arithmetic.lean).

## Base Field Caveats

`Hachi` (`2^32 - 99`) has no `FastField` Montgomery path: `Mont32Field` requires
`modulus < 2^31`, since radix-`2^32` reduction needs `x + m * p < 2^64`. It also has two-adicity
2, so it admits no radix-2 NTT domain. The extension layer is generic over the base-field
carrier, so a future 64-bit Montgomery layer would be picked up unchanged.
