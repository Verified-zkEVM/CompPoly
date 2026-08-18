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
has a root. Over KoalaBear, `p - 1 = 2^24 · 127`, so the only binomial degrees available are the
powers of two (up to `2^24`) and multiples of 127:

| `d` | bits | binomial? |
|---|---|---|
| 4 | 124 | yes, `X^4 - 3` — but under `2^128` |
| 5 | 155 | **no**: `5 ∤ p - 1`, so `x ↦ x^5` is a bijection |
| 6 | 186 | **no**, and more strongly: `3 ∤ p - 1`, so every `W` is a cube `V^3` and `X^6 - W = (X^2 - V)(X^4 + V X^2 + V^2)` factors for *every* `W` |
| 8 | 248 | yes, but wider than needed |

Hence [`KoalaBear/Ext5.lean`](../../CompPoly/Fields/KoalaBear/Ext5.lean) adjoins a root of the
non-binomial quintic `X^5 + X^2 - 1`, and
[`KoalaBear/Ext6.lean`](../../CompPoly/Fields/KoalaBear/Ext6.lean) a root of the sextic
`X^6 + X^3 + 1 = Φ₉`. The general-modulus framework and the certificate-based irreducibility
pipeline below exist to make such extensions routine.

Degree 6 is the smallest KoalaBear extension that is both comfortably above `2^128` and of
*composite* degree, so — unlike the prime-degree quintic — it has proper subfields, which is what
makes a cheap Frobenius and a norm-based inverse possible. See "Choosing a general modulus".

## Layering

| Layer | File | Owns |
|---|---|---|
| Rabin's test, general | [`../../CompPoly/Data/Polynomial/Rabin.lean`](../../CompPoly/Data/Polynomial/Rabin.lean) | `irreducible_of_rabin`, `irreducible_iff_rabin` for any degree over any finite field |
| Factor-degree bound | [`../../CompPoly/ToMathlib/Polynomial/Irreducible.lean`](../../CompPoly/ToMathlib/Polynomial/Irreducible.lean) | `exists_factor_natDegree_le_of_reducible` |
| Binomial criterion | [`../../CompPoly/Fields/Extension/Binomial.lean`](../../CompPoly/Fields/Extension/Binomial.lean) | the collapse to base-field exponentiations; `irreducible_X_pow_four_sub_C_iff` |
| Rabin certificates | [`../../CompPoly/Data/Polynomial/RabinCertificate.lean`](../../CompPoly/Data/Polynomial/RabinCertificate.lean) | kernel-checked chains for non-binomial moduli; `runChain_sound`, `irreducible_of_rabin_prime_degree`, `irreducible_of_rabin_two_prime_factors`, `irreducible_of_rabin_degree_six`, and the `_of_card` forms concrete callers use |
| Carrier and ring ops | [`../../CompPoly/Fields/Extension/Defs.lean`](../../CompPoly/Fields/Extension/Defs.lean) | `ExtensionParams`, `BinomialParams` (+ `toExtensionParams`), `Ext P`, `Ext.shiftReduce`, `Ext.monomialMod`, `Ext.mul` (spec), `Ext.red` + `Ext.mulTbl` (compiled, via `@[csimp]`) |
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
[`KoalaBear/Ext5/QuinticCertData.lean`](../../CompPoly/Fields/KoalaBear/Ext5/QuinticCertData.lean))
and [`KoalaBear/Ext6.lean`](../../CompPoly/Fields/KoalaBear/Ext6.lean) (`X^6 + X^3 + 1`, the first
*composite*-degree general modulus, with
[`Ext6/SexticIrreducible.lean`](../../CompPoly/Fields/KoalaBear/Ext6/SexticIrreducible.lean) and
[`Ext6/SexticCertData.lean`](../../CompPoly/Fields/KoalaBear/Ext6/SexticCertData.lean)).

[`Ext6/GaloisField.lean`](../../CompPoly/Fields/KoalaBear/Ext6/GaloisField.lean) is a separate
opt-in module identifying `Ext6` with Mathlib's abstract `GaloisField KoalaBear.fieldSize 6`, so
the computable arithmetic here can serve developments phrased over that (ArkLib's `KoalaSextic`,
for the Proximity Prize parameter point of [ABF26], ePrint 2026/680). `GaloisField` commits to no
modulus, so the identification follows from `card_ext6` alone and is independent of the choice of
`Φ₉` — but it is noncanonical, so it pins down nothing about where `ext6Gen` lands.

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

**Composite degree needs one coprimality check per prime factor**, and the prime-degree collapse
is *unsound* there rather than merely weak. `Polynomial.irreducible_of_rabin` already quantifies
over `d.primeFactors`; the packaged forms are:

| `d` | Wrapper | Checks |
|---|---|---|
| prime | `irreducible_of_rabin_prime_degree` | `f ∣ X^(q^d) - X`, `IsCoprime f (X^q - X)` |
| `6` | `irreducible_of_rabin_degree_six` | plus `IsCoprime f (X^(q^3) - X)` and `IsCoprime f (X^(q^2) - X)` |
| two prime factors | `irreducible_of_rabin_two_prime_factors` | as above, `Nat.primeFactors d = {ℓ₁, ℓ₂}` supplied by the caller |

Each of the first two also has an `_of_card` form (`irreducible_of_rabin_prime_degree_of_card`,
`irreducible_of_rabin_degree_six_of_card`) taking the field size as a numeral `q` with
`hcard : Fintype.card F = q`, supplied as `ZMod.card _`. Concrete extensions use those: their
generated certificates are already stated in terms of `fieldSize`, so the conditions apply
directly instead of needing a `rw [hcard]` cast per condition. This mirrors
`irreducible_X_pow_four_sub_C_of_card` on the binomial side. The two forms are inter-derivable —
instantiating at `q := Fintype.card F` with `rfl` recovers the plain one — and
`tests/CompPolyTests/Data/Polynomial/RabinCertificate.lean` pins that round trip.

Concretely, over KoalaBear `(X^3 + X + 4)(X^3 + X - 4)` divides `X^(p^6) - X` and is coprime to
`X^p - X`, so it satisfies the prime-degree conditions verbatim while being visibly reducible;
only the `q^3` check rejects it. `Nat.primeFactors 6 = {2, 3}` cannot be closed by `decide`
(`Nat.primeFactorsList` is well-founded recursive and does not reduce in the kernel), so it is
proved via `Nat.primeFactors_mul`, mirroring `primeFactors_four` in `Extension/Binomial.lean`.

The generator loops over the prime factors too, and the same trap applied to it: before that fix
it reported the product above as irreducible and exited `0`. Its `--self-test` flag now checks it
against known-answer cases including that polynomial.

Certificate data is emitted by the untrusted generator
[`scripts/gen_rabin_certificate.py`](../../scripts/gen_rabin_certificate.py)
(`--lean`/`--namespace` produce a complete data module); the kernel re-checks every step.
The KoalaBear quintic instance costs ~290 generated lines and compiles in about two
seconds — contrast the roughly 2100 lines of per-step `BitVec` certificates the same test
costs the GHASH polynomial (`Fields/Binary/BF128Ghash/XPowTwoPow{Mod,Gcd}Certificate.lean`),
which predates this framework.

### Choosing a general modulus

Since every irreducible `f` of degree `d` gives the same field up to isomorphism, the choice is
purely about arithmetic cost, and it is decided by two tables: the reduction table
`X^d … X^(2d-2) mod f` that `Ext.red` holds, and the Frobenius matrix. Entries of `±1` cost an
add or a negation; anything else costs a base-field multiplication. Measured over the irreducible
sextics of KoalaBear:

| modulus | red-table nonzeros | needing a multiply | Frobenius nonzeros | needing a multiply |
|---|---|---|---|---|
| `X^6 + X^3 + 1` (`Φ₉`) | 8 | **0** | 8 | **0** |
| `X^6 - X^3 + 1` (`Φ₁₈`) | 8 | 0 | 8 | 0 |
| `X^6 - 2X^3 - 2` | 10 | 10 | 11 | 9 |
| `X^6 + 4X - 3` | 10 | 10 | 31 | 30 |
| `X^6 + 3X^2 - 3` | 11 | 11 | 16 | 15 |
| `X^6 + X^4 + 3` | 13 | 9 | 16 | 15 |

So prefer, in order: a cyclotomic `Φₙ` when one has the right degree; then a sparse trinomial with
`±1` coefficients; then anything sparse. Two further points, both visible above:

- A modulus of the form `g(X^k)` puts a subfield at `F_p(θ^k)` with a sparse coordinate
  description, i.e. it *is* a tower in disguise. `Φ₉ = g(X^3)` with `g = Y^2 + Y + 1` gives
  `F_p ⊂ F_p² ⊂ F_p⁶`, so the tower's arithmetic is available without any tower machinery. The
  mirror orientation `h(X^2)` with `h` cubic is `X^6 + X^4 + 3` — the same idea, measurably worse.
- Prefer all-nonnegative coefficients when there is a choice: the certificate encoding then needs
  no `p - 1` literal, and no `cast_p_sub_one`-style lemma. Compare `sexticL = [1,0,0,1,0,0,1]`
  against `quinticL = [2130706432, 0, 1, 0, 0, 1]`.

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
   chain/Bézout `rfl` checks and the assembly through
   `irreducible_of_rabin_prime_degree_of_card` (prime `d`, see
   `KoalaBear/Ext5/QuinticIrreducible.lean`) or `irreducible_of_rabin_degree_six_of_card`
   (composite `d`, see `KoalaBear/Ext6/SexticIrreducible.lean`), passing
   `hcard : Fintype.card Field = fieldSize := ZMod.card _`. At a composite `d` with no `_of_card`
   form yet, use `irreducible_of_rabin_two_prime_factors` and cast each condition with
   `rw [hcard]`. At composite `d` there is one chain plus Bézout block per prime factor, named
   `cop<m>Steps`/`cop<m>Rp`/… for `m = d / ℓ`.
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
| `fields-extension-koalabear-ext4-mul` | `mul` | ~25 us |
| `fields-extension-koalabear-ext4-inv` | `inv` | ~3.5 ms |
| `fields-extension-koalabear-ext5-mul` | `mul` | ~41 us |
| `fields-extension-koalabear-ext5-inv` | `inv` | ~7.6 ms |
| `fields-extension-koalabear-ext6-mul` | `mul` | ~64 us |
| `fields-extension-koalabear-ext6-inv` | `inv` | ~15 ms |

For scale, a hand-written Rust degree-4 BabyBear multiply is a few nanoseconds. Do not quote
this framework as performance-ready until the items below are done.

Those numbers are with the reduction table in place. The same benchmarks with `@[csimp]` removed
from `mul_eq_mulTbl`, i.e. running the specification directly, on the same machine:

| Operation | Spec (`mul`) | Table (`mulTbl`) | Speedup |
|---|---|---|---|
| Ext4 `mul` | 78.1 us | 25.4 us | 3.1x |
| Ext4 `inv` | 14.0 ms | 3.5 ms | 4.0x |
| Ext5 `mul` | 195.6 us | 40.6 us | 4.8x |
| Ext6 `mul` | 429.8 us | 63.8 us | 6.7x |
| Ext6 `inv` | 119.6 ms | 15.1 ms | 7.9x |

The speedup growing with `d` is the point: it is the `O(d^5) → O(d^3)` change becoming visible.
The 78 us spec figure also reproduces the ~73 us recorded before the table existed, which is what
makes this an honest A/B rather than a change of measurement conditions.

The remaining causes, in order of size:

1. **`Ext.mul` allocates, and its asymptotics are still not optimal.**

   *Asymptotics.* `mul` — the specification — expands each product monomial through
   `monomialMod (i + j) = shiftReduce^[i+j] 1`, recomputed for every `(m, i, j)`. That is what
   keeps the correctness proof one additive lemma, and what made the compiled code roughly
   O(d⁵). `Ext.red` now holds `X^0 … X^(2d-2) mod f`, and `Ext.mulTbl` consults it instead;
   `mul_eq_mulTbl` is registered `@[csimp]`, so compilation is swapped while every proof still
   refers to `Ext.mul`. That is O(d³). The remaining step to O(d²) is a schoolbook convolution
   to length `2d - 1` folded through `red`, rather than the current triple sum, plus hoisting
   `red` out of `mulTbl` so it is computed once per `P` rather than once per multiplication.

   *Allocation.* Because `P` is a runtime parameter nothing monomorphises: `Finset.univ` is
   rebuilt and `Fin` values boxed on every call. `@[specialize]` recovers only about 6%. The fix
   is an `Array`-loop backend, following the `MulContext` idiom in
   [`Univariate/Context.lean`](../../CompPoly/Univariate/Context.lean).

   Keep the `monomialMod` expansion as the *spec* whatever replaces `mulTbl`: it is what
   `toQuot_mul` is proved against, and reducing everything to `toQuot_shiftReduce` is why that
   proof is short.
2. **The base field is `ZMod p`**, i.e. boxed `Nat` arithmetic. Instantiating over
   `KoalaBear.Fast.Field` (`UInt32` Montgomery,
   [`Montgomery/Native32Field.lean`](../../CompPoly/Fields/Montgomery/Native32Field.lean))
   needs only `Fintype` for that carrier plus irreducibility transported along
   `Montgomery.Native32.ringEquiv` with `Polynomial.mapEquiv`. No change to the framework.
3. **Inversion is Fermat** (`x ^ (q^d - 2)`), about `d · log q` extension multiplications — the
   ~140x ratio to `mul` above, and it is the reason the `#guard` regressions dominate the test
   module's build time. A norm-based inverse (Itoh–Tsujii) would be roughly two orders of
   magnitude faster: `N(x) = ∏_j φ^j(x)` lands in the base field, so
   `x⁻¹ = (∏_{j≥1} φ^j(x)) · N(x)⁻¹` costs `d - 1` Frobenius applications, `d - 1` extension
   multiplications, and one base-field inverse.

   The cost hinges on Frobenius being sparse, which is exactly what the modulus choice above
   buys. For a binomial with `d ∣ q - 1` it is a coordinate-wise scaling by powers of
   `W^((q-1)/d)`; for `Ext6` it is `θ ↦ θ^2` with all-`±1` entries, since `p ≡ 2 mod 9`. Neither
   `Ext.frobenius` nor `Ext.norm` exists yet.

None of these is hidden behind an abstraction that makes replacing it awkward, and each is
guarded by the `#guard` regressions in
[`tests/CompPolyTests/Fields/Extension/Arithmetic.lean`](../../tests/CompPolyTests/Fields/Extension/Arithmetic.lean).

## Base Field Caveats

`Hachi` (`2^32 - 99`) has no `FastField` Montgomery path: `Mont32Field` requires
`modulus < 2^31`, since radix-`2^32` reduction needs `x + m * p < 2^64`. It also has two-adicity
2, so it admits no radix-2 NTT domain. The extension layer is generic over the base-field
carrier, so a future 64-bit Montgomery layer would be picked up unchanged.
