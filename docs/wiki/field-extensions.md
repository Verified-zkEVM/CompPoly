# Field Extensions

`CompPoly/Fields/Extension/` is the computable field-extension framework for odd
characteristic. It models `F[X] / (X^d - W)` as a dense coefficient vector and proves
it equal to `AdjoinRoot (X^d - W)`, so Mathlib field theory applies to it.

This page owns extension-field architecture. The characteristic-2 stack is a separate,
independent development — see [`binary-fields-and-ntt.md`](binary-fields-and-ntt.md).

## Why Binomials

Every extension field used in practice by a STARK or zkVM is a binomial extension: a
degree-2 to degree-8 extension of a 31- or 32-bit prime, defined by `X^d - W`. Restricting
to binomials buys two things that matter a great deal:

- **Cheap irreducibility.** Rabin's test collapses to two exponentiations in the *base*
  field (see below).
- **Cheap multiplication.** `X^d = W` means the high half of the schoolbook product folds
  back with a single scalar multiply, with no polynomial remainder step.

## Layering

| Layer | File | Owns |
|---|---|---|
| Rabin's test, general | [`../../CompPoly/Data/Polynomial/Rabin.lean`](../../CompPoly/Data/Polynomial/Rabin.lean) | `irreducible_of_rabin`, `irreducible_iff_rabin` for any degree over any finite field |
| Factor-degree bound | [`../../CompPoly/ToMathlib/Polynomial/Irreducible.lean`](../../CompPoly/ToMathlib/Polynomial/Irreducible.lean) | `exists_factor_natDegree_le_of_reducible` |
| Binomial criterion | [`../../CompPoly/Fields/Extension/Binomial.lean`](../../CompPoly/Fields/Extension/Binomial.lean) | the collapse to base-field exponentiations; `irreducible_X_pow_four_sub_C_iff` |
| Carrier and ring ops | [`../../CompPoly/Fields/Extension/Defs.lean`](../../CompPoly/Fields/Extension/Defs.lean) | `BinomialParams`, `Ext P`, `Ext.mul` |
| Bridge and `CommRing` | [`../../CompPoly/Fields/Extension/Bridge.lean`](../../CompPoly/Fields/Extension/Bridge.lean) | `toQuot`, `toQuot_mul`, `instCommRing` |
| Bijectivity and `Field` | [`../../CompPoly/Fields/Extension/Field.lean`](../../CompPoly/Fields/Extension/Field.lean) | `ringEquivQuot`, `card_ext`, `inv`, `instField` |

`Data/Polynomial/Rabin.lean` generalizes the degree-128/GF(2) specialization
`irreducible_of_rabin_128_passed_over_GF2` in `Fields/Binary/BF128Ghash/Basic.lean`, but does not
yet replace it — `Binary/` is deliberately untouched, so there are currently **two** Rabin
soundness proofs in the repo. Rebasing the GHASH one onto `irreducible_of_rabin` is a named
follow-up; until then, a fix to the argument needs applying in both places.

Concrete instances live next to their base field:
[`KoalaBear/Ext4.lean`](../../CompPoly/Fields/KoalaBear/Ext4.lean) (`X^4 - 3`),
[`BabyBear/Ext4.lean`](../../CompPoly/Fields/BabyBear/Ext4.lean) (`X^4 - 11`), and
[`Hachi/Ext4.lean`](../../CompPoly/Fields/Hachi/Ext4.lean) (`X^4 - 2`).

## What The Interface Provides

Concretely, for `P : BinomialParams F`:

| Surface | Declarations |
|---|---|
| Ring / field | `CommRing (Ext P)`, `Field (Ext P)` (the latter given `[Fact (Irreducible P.poly)]`) |
| Base field | `Ext.ofBase : F → Ext P`, `Ext.ofBaseRingHom`, `Algebra F (Ext P)` (hence `Module F (Ext P)` via `Algebra.toModule`) |
| Adjoined root | `Ext.gen`, `Ext.gen_pow_d : gen ^ d = ofBase W`, `Ext.aeval_gen_poly : aeval gen P.poly = 0` |
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
repeated squaring during elaboration. Contrast the roughly 2100 lines of generated `BitVec`
step certificates that the same test needs for the non-binomial GHASH polynomial
(`Fields/Binary/BF128Ghash/XPowTwoPow{Mod,Gcd}Certificate.lean`).

Nothing here uses `native_decide`, per the TCB policy in [`AGENTS.md`](../../AGENTS.md).

### Adding a new extension

1. Pick `W`. For `d = 4` over `q ≡ 1 mod 4`, any non-square works; prefer the smallest, so
   that multiplying by `W` is cheap.
2. Write the `BinomialParams`, supplying `card_eq := ZMod.card _`.
3. Prove irreducibility with `irreducible_X_pow_four_sub_C_of_card`. The two exponentiation
   goals need the type presented as `ZMod <numeral>`, because `reduce_mod_char` reads the
   modulus syntactically and `fieldSize` is an expression like `2 ^ 31 - 2 ^ 24 + 1`. Use a
   `show` — see any of the three `Ext4.lean` files.
4. Register `instance : Fact (Irreducible ...)` and define the `abbrev`.

That is about 60 lines.

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

`BinomialParams` carries `d`, `W`, and the base-field cardinality `q` as a *type index*, so
two different extensions of the same base field are different types whose instances cannot be
confused. `q` is data rather than `Fintype.card F` because Fermat inversion evaluates the
exponent at runtime, and `Fintype.card (ZMod p)` would enumerate all of `Fin p`.

**The instances are assembled field-by-field, not by `Function.Injective.commRing` /
`.field`.** Those transports take `toQuot` as data, which forces the resulting instance
`noncomputable`. That is not merely cosmetic: `Monoid.toNatPow` then outranks `Ext.instPow`, and
compiled `x ^ n` fails to build. This was observed, not hypothesized. If you add structure to
`Ext P`, keep it computable and keep a `#guard` in
[`tests/CompPolyTests/Fields/Extension/Arithmetic.lean`](../../tests/CompPolyTests/Fields/Extension/Arithmetic.lean)
that exercises the operation, since only compiled evaluation catches this class of regression.

The load-bearing correctness lemma is `Ext.toQuot_mul`: `root ^ d = W` is exactly the
wrap-around factor in `Ext.mul`, so the double sum defining the product regroups into the
product of sums.

## Performance: Measured, And Not Yet Competitive

The framework is correctness-complete, and its *design* is ready for fast arithmetic — `Ext P`
is generic over the base-field carrier precisely so a Montgomery representation can be dropped
in. The current instantiation over `ZMod`, however, is **not** fast. Measured with
`lake exe CompPolyBench --small` on a developer laptop:

| Group | Operation | Average |
|---|---|---|
| `fields-extension-koalabear-ext4-mul` | `mul` | ~13.4 us |
| `fields-extension-koalabear-ext4-inv` | `inv` | ~1.7 ms |

For scale, a hand-written Rust degree-4 BabyBear multiply is a few nanoseconds. Do not quote
this framework as performance-ready until the items below are done.

The three causes, in order of size:

1. **`Ext.mul` is O(d³), and separately allocates.** Two distinct problems, and a rewrite must
   fix both.

   *Asymptotics.* The definition is `ofFn` over `d` output coefficients, each a `d × d` double
   sum with `if`-tests — so `d³` term visits, nearly all of them contributing zero. Schoolbook
   binomial reduction is **O(d²)**: for each output index, one sum of `d` products with the
   partner index computed rather than searched. At `d = 4` that is 64 visits versus 16. A
   rewrite that only swaps in faster containers while keeping the triple sum leaves a factor of
   `d` on the table, so specify the target as **O(d²) *and* allocation-free**.

   *Allocation.* Because `P` is a runtime parameter nothing monomorphises: `Finset.univ` is
   rebuilt and `Fin` values boxed on every call. `@[specialize]` recovers only about 6%.

   The fix is an `Array`-loop implementation proved equal to the current sum-based definition —
   either as a separate backend behind an agreement lemma, following the `MulContext` idiom in
   [`Univariate/Context.lean`](../../CompPoly/Univariate/Context.lean), or via `@[csimp]` so the
   compiled code is swapped while every existing proof keeps referring to `Ext.mul`. Keep the
   current O(d³) double sum as the *spec*: it is what `toQuot_mul` is proved against, and its
   symmetry in `(i, j)` is why that proof is short.
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
