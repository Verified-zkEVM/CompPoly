# Representations And Bridges

CompPoly has several distinct polynomial representations. Picking the right one is
usually the first architectural decision in a change.

## At A Glance

| Surface | Main type(s) | Best for | Main entrypoints |
|---|---|---|---|
| Univariate | `CPolynomial.Raw R`, `CPolynomial R`, `QuotientCPolynomial R` | Canonical coefficient-sequence arithmetic, quotient reasoning, interpolation | `CompPoly/Univariate/README.md`, `CompPoly/Univariate/Basic.lean`, `CompPoly/Univariate/ToPoly.lean` |
| Multivariate | `CMvPolynomial n R` | Sparse computable multivariate operations and `MvPolynomial` interop | `CompPoly/Multivariate/CMvPolynomial.lean`, `CompPoly/Multivariate/Operations.lean`, `CompPoly/Multivariate/MvPolyEquiv.lean` |
| Multilinear | `CMlPolynomial R n`, `CMlPolynomialEval R n` | Boolean-hypercube evaluation form, basis conversion, multilinear extensions | `CompPoly/Multilinear/Basic.lean`, `CompPoly/Multilinear/Equiv.lean` |
| Field extensions | `Extension.Ext P` | Computable `F[X]/f` arithmetic for challenge fields, `f` an arbitrary monic modulus | `CompPoly/Fields/Extension.lean`, `docs/wiki/field-extensions.md` |
| Bivariate | `CBivariate R` | Specialized two-variable APIs and `R[X][Y]` transport | `CompPoly/Bivariate/README.md`, `CompPoly/Bivariate/Basic.lean`, `CompPoly/Bivariate/ToPoly.lean`, `CompPoly/ToMathlib/Polynomial/BivariateDegree.lean`, `CompPoly/ToMathlib/Polynomial/BivariateWeightedDegree.lean`, `CompPoly/ToMathlib/Polynomial/BivariateMultiplicity.lean` |
| Dense matrices | `DenseMatrix F` | Row-major matrices over a field: Gauss-Jordan reduction and homogeneous kernels | `CompPoly/LinearAlgebra/README.md`, `CompPoly/LinearAlgebra/Dense/Basic.lean` |
| Polynomial matrices | `PolynomialMatrix F`, `PolynomialRow F` | Rows of univariate polynomials, shifted degrees, and shifted row reduction | `CompPoly/LinearAlgebra/README.md`, `CompPoly/LinearAlgebra/PolynomialMatrix/Basic.lean` |

## Univariate Family

The univariate stack distinguishes between three closely related views:

- `CPolynomial.Raw R` is the array-backed representation where trailing zeros are
  allowed.
- `CPolynomial R` is the canonical trimmed representation.
- `QuotientCPolynomial R` is the quotient model that packages coefficient-wise
  equivalence on raw arrays.

Use `Raw` when implementation detail matters, `CPolynomial` for normal user-facing
 work, and `QuotientCPolynomial` when quotient reasoning is the cleanest proof
 boundary.

The main bridge to Mathlib lives in:

- [`../../CompPoly/Univariate/ToPoly/Core.lean`](../../CompPoly/Univariate/ToPoly/Core.lean)
- [`../../CompPoly/Univariate/ToPoly/Equiv.lean`](../../CompPoly/Univariate/ToPoly/Equiv.lean)
- [`../../CompPoly/Univariate/ToPoly/Degree.lean`](../../CompPoly/Univariate/ToPoly/Degree.lean)
- [`../../CompPoly/Univariate/ToPoly/RingHom.lean`](../../CompPoly/Univariate/ToPoly/RingHom.lean)
  for `CPolynomial.C`/`eval₂`/coefficient-map bundled as `RingHom`s and the
  `ringHom_ext` extensionality principle.

For interpolation work, also read:

- [`../../CompPoly/Univariate/Lagrange.lean`](../../CompPoly/Univariate/Lagrange.lean)
  for the baseline interpolation surface and correctness statements.
- [`../../CompPoly/Univariate/Barycentric.lean`](../../CompPoly/Univariate/Barycentric.lean)
  for repeated-query barycentric evaluation over a fixed node set with precomputed
  barycentric weights.

For root-of-unity NTT work:

- [`../../CompPoly/Univariate/NTT/Domain.lean`](../../CompPoly/Univariate/NTT/Domain.lean)
  contains the shared domain type, fitting-domain helpers, and natural-order input
  loaders.
- [`../../CompPoly/Univariate/NTT/Evaluation.lean`](../../CompPoly/Univariate/NTT/Evaluation.lean)
  and [`../../CompPoly/Univariate/NTT/Interpolation.lean`](../../CompPoly/Univariate/NTT/Interpolation.lean)
  state the bridge theorems connecting forward/inverse NTTs to evaluation and
  Lagrange interpolation.
- [`../../CompPoly/Univariate/NTT/FastMul.lean`](../../CompPoly/Univariate/NTT/FastMul.lean)
  exposes the shared specification and baseline multiplication surface.
- [`../../CompPoly/Univariate/NTTFast/Plan.lean`](../../CompPoly/Univariate/NTTFast/Plan.lean)
  is the optimized planned implementation surface. The `NTTFast/Evaluation.lean`
  and `NTTFast/Interpolation.lean` bridge files prove the planned transforms agree
  with the shared `NTT` evaluation and interpolation specifications.

## Multivariate Family

`CMvPolynomial n R` is the sparse computable multivariate surface highlighted in the
root README. It is the right place for:

- computable monomial-based operations,
- evaluation and substitution APIs,
- variable renaming and restriction,
- support and degree queries,
- transport to Mathlib `MvPolynomial (Fin n) R`.

The main split is:

- [`../../CompPoly/Multivariate/CMvPolynomial.lean`](../../CompPoly/Multivariate/CMvPolynomial.lean)
  for core type-level definitions,
- [`../../CompPoly/Multivariate/Operations.lean`](../../CompPoly/Multivariate/Operations.lean)
  for the higher-level operation surface,
- [`../../CompPoly/Multivariate/MvPolyEquiv/`](../../CompPoly/Multivariate/MvPolyEquiv/)
  for ring instances and bridge lemmas.

## Multilinear Family

The multilinear stack is easy to miss if you only read the old top-level summary.
It already has two distinct computable forms:

- `CMlPolynomial R n` for monomial-basis coefficients,
- `CMlPolynomialEval R n` for evaluation values on `{0,1}^n`.

These are both represented as vectors of length `2 ^ n`, with little-endian indexing.
That design is described directly in
[`../../CompPoly/Multilinear/Basic.lean`](../../CompPoly/Multilinear/Basic.lean).

Use this area for:

- Boolean-hypercube evaluation form,
- zeta / Mobius style basis transforms,
- multilinear-extension equivalences,
- fast multilinear pathways that do not fit the sparse `CMvPolynomial` API.

`CMlPolynomial.evalWithProducts` supports coefficient evaluation through a separate
product accumulator. It returns a value in the coefficient type after reducing the
accumulated products with an additive homomorphism. Its correctness theorem requires
that reducing each constructed product gives the ordinary product of its factors.
The little-endian monomial order is the same as for `CMlPolynomial.eval`.

The underlying `Vector.accumulateProducts` in
[`../../CompPoly/Data/Vector/Basic.lean`](../../CompPoly/Data/Vector/Basic.lean)
accepts equal-length vectors and an arbitrary initial accumulator, and returns the
accumulator before reduction. `Vector.reduce_accumulateProducts` accounts for that
initial value as well as the dot product. Ordinary multiplication with identity
reduction is the eager fallback; a specialized accumulator must supply its own
additive reduction and product equation. No field-specific backend is selected by
this generic interface.

## Bivariate Family

`CBivariate R` is the specialized `CPolynomial (CPolynomial R)` layer. Use it when
the problem is truly two-variable and a dedicated API is clearer than treating the
code as generic multivariate syntax.

The key files are:

- [`../../CompPoly/Bivariate/Basic.lean`](../../CompPoly/Bivariate/Basic.lean)
- [`../../CompPoly/Bivariate/ToPoly.lean`](../../CompPoly/Bivariate/ToPoly.lean)
- [`../../CompPoly/ToMathlib/Polynomial/BivariateDegree.lean`](../../CompPoly/ToMathlib/Polynomial/BivariateDegree.lean)
- [`../../CompPoly/ToMathlib/Polynomial/BivariateWeightedDegree.lean`](../../CompPoly/ToMathlib/Polynomial/BivariateWeightedDegree.lean)
- [`../../CompPoly/ToMathlib/Polynomial/BivariateMultiplicity.lean`](../../CompPoly/ToMathlib/Polynomial/BivariateMultiplicity.lean)
- [`../../CompPoly/Bivariate/README.md`](../../CompPoly/Bivariate/README.md)

## Bridge Layers

When the task is "prove the computable thing agrees with Mathlib", start in the
bridge layer rather than the implementation file:

- Univariate bridge: `Univariate/ToPoly/*`
- Multivariate bridge: `Multivariate/MvPolyEquiv/*`
- Bivariate bridge: `Bivariate/ToPoly.lean` plus `ToMathlib/Polynomial/BivariateDegree.lean`, `ToMathlib/Polynomial/BivariateWeightedDegree.lean`, and `ToMathlib/Polynomial/BivariateMultiplicity.lean`
- Multilinear bridge: `Multilinear/Equiv.lean`
- Supporting upstream-facing lemmas: `ToMathlib/*`

The local `ToMathlib` subtree is especially useful when a proof needs a helper lemma
that conceptually belongs between CompPoly and Mathlib rather than inside one
specific polynomial representation.

## Proof API: Simp And Grind Sets

The bridge lemmas come in two kinds, and only one belongs in the default simp set.

- **Push lemmas** move `toPoly` inward: `toPoly_add`, `toPoly_sub`, `toPoly_neg`,
  `toPoly_mul`, `toPoly_pow`, `toPoly_zero`, `toPoly_one`, `toPoly_sum`, `toPoly_prod`,
  `toPoly_smul`, `C_toPoly`, `X_toPoly`, `monomial_toPoly` and `derivative_toPoly`, plus
  `toPoly_inj` and `toPoly_eq_zero_iff`. They are `@[simp, grind =]`: a push never introduces
  a `toPoly` that was not already in the goal.
- **Lift lemmas** rewrite a `CPolynomial` operation into a Mathlib one: `eval_toPoly`,
  `coeff_toPoly`, `degree_toPoly`, `natDegree_toPoly` and `leadingCoeff_toPoly`. They are
  **not** simp. As simp lemmas they would turn every `CPolynomial.eval` in the library into a
  `Polynomial.eval`. Name them when a proof crosses to Mathlib on purpose.

Evaluation has its own `CPolynomial`-level set, `@[simp, grind =]`: `eval_zero`, `eval_one`,
`eval_C`, `eval_X`, `eval_add`, `eval_neg`, `eval_sub`, `eval_mul`, `eval_pow` and
`eval_monomial`. `evalHom` bundles evaluation as a `RingHom`, and `eval_sum`/`eval_prod`
follow from it. This matches the multivariate set in
[`../../CompPoly/Multivariate/Eval.lean`](../../CompPoly/Multivariate/Eval.lean).

The other families follow the same rule:

- **Bivariate:** `CBivariate.toPoly_{add,mul,zero,one,monomial}`, `CC_toPoly`, `X_toPoly`,
  `Y_toPoly`, `monomialXY_toPoly` and the `ofPoly`/`toPoly` round trips are `@[simp, grind =]`.
  So are the `bivariateEquiv_*` lemmas into `CMvPolynomial 2 R`.
- **Multivariate:** `CMvPolynomial.eval_*` and the `fromCMvPolynomial` round trips, in
  `Multivariate/Eval.lean` and `Multivariate/MvPolyEquiv/`.
- **Multilinear:** `eval_zero`, `eval_add` and `eval_smul` for both `CMlPolynomial` and
  `CMlPolynomialEval` are `@[simp]`.

What that buys, all checked in
[`../../tests/CompPolyTests/Univariate/Ergonomics.lean`](../../tests/CompPolyTests/Univariate/Ergonomics.lean):

```lean
example : (p * q + C a).toPoly = p.toPoly * q.toPoly + Polynomial.C a := by simp  -- or grind
example : (p * q + 1).eval x = p.eval x * q.eval x + 1 := by simp                -- or grind
example : C (1 : R) * p = p := toPoly_inj.mp (by simp)
example : derivative (p * q) = derivative p * q + p * derivative q :=
  toPoly_inj.mp (by simp [Polynomial.derivative_mul])
```

`toPoly_inj.mp (by simp [...])` is the general transfer pattern for an equation between
`CPolynomial`s. It moves the goal to Mathlib, pushes `toPoly` through, and closes it with the
Mathlib lemma you name.

### The `toPoly` Coercion

`toPoly` is also the coercion `CPolynomial R → Polynomial R` (`@[coe]`, with a `Coe`
instance), so `↑p` and `p.toPoly` are the same term. The push lemmas carry `norm_cast`, and
`toPoly_eval`, `toPoly_coeff`, `toPoly_degree`, `toPoly_natDegree` and `toPoly_leadingCoeff`
restate the lift lemmas with the cast on the left, as `norm_cast` wants. A Mathlib theorem
about `↑p` then transfers in one line:

```lean
example (hp : p ≠ 0) (hq : q ≠ 0) : (p * q).natDegree = p.natDegree + q.natDegree := by
  exact_mod_cast Polynomial.natDegree_mul (p := (p : Polynomial R)) (q := q)
    (by exact_mod_cast hp) (by exact_mod_cast hq)
example : (p * q).leadingCoeff = p.leadingCoeff * q.leadingCoeff := by
  exact_mod_cast Polynomial.leadingCoeff_mul (p : Polynomial R) q
```

Two limits:

- The cast-oriented lemmas are `norm_cast` only, **not** `@[simp]`. With both orientations
  in the simp set, `simp [eval_toPoly]` loops, and the library uses that call in many places.
- `C_toPoly` and `derivative_toPoly` cannot be `norm_cast` lemmas. `Polynomial.C` and
  `derivative` are bundled maps applied through a coercion to functions, and `norm_cast`
  rejects a right-hand side that starts with a coercion. A statement
  mentioning `C` or `X` takes one more step: rewrite the query into Mathlib's
  (`rw [← toPoly_coeff]`), `push_cast`, then `exact_mod_cast` the Mathlib lemma.

Known friction when porting a Mathlib proof:

- Inside `namespace CPolynomial`, `X`, `C`, `degree` and `eval_*` resolve to the
  `CPolynomial` versions. Qualify the Mathlib side (`Polynomial.eval_X`), or `open` with
  `hiding`.
- `CPolynomial.toPoly`, `Raw.coeff` and `Raw.toPoly` are not exposed by a plain `public
  import`. A proof that must see through them with `change`, `unfold` or `rfl` needs `import
  all` of `ToPoly/Core.lean` or `Raw/Core.lean`. See [`module-system.md`](module-system.md).
- Multivariate lives in `CPoly.CMvPolynomial` and univariate in `CompPoly.CPolynomial`.
- `CMlPolynomial R n` and `CMlPolynomialEval R n` are `def`s for `Vector R (2 ^ n)`, so
  `p + q` and `0` elaborate with core's `Vector` instances rather than the ones declared in
  `Multilinear/Basic.lean`. Pointwise proofs go through `Vector.getElem_add` and
  `Vector.getElem_zero`, not `Vector.zipWith`.

## Choosing A Surface

- If you need canonical coefficient arrays and interpolation, start with
  `CPolynomial`; for repeated interpolation queries over a fixed domain, also
  inspect `Univariate/Barycentric.lean`.
- If you need sparse multivariate monomials or `MvPolynomial` equivalence, start
  with `CMvPolynomial`.
- If you need Boolean-cube evaluation data or multilinear transforms, start with
  `CMlPolynomial` or `CMlPolynomialEval`.
- If the API is naturally two-variable and you want `X` / `Y`-specific operations,
  start with `CBivariate`.
- If you need to solve a linear system or reduce a matrix rather than manipulate a
  polynomial, start with `DenseMatrix` or `PolynomialMatrix`. These are `Array`-backed
  and carry no shape invariant in the type; there is no bridge to Mathlib's `Matrix`.

## Matrix Surfaces

`CompPoly/LinearAlgebra/` is the one family here with no Mathlib bridge layer, by
design: it exists to run, and its correctness statements are phrased against
row-span and pivot-shape predicates defined locally (`RowSpan`, `PivotColumnsShaped`)
rather than transported to `Matrix`. Both layers ship a direct definition and a
faster variant proved equal to it — `rrefInPlace_eq` for dense matrices,
`muldersStorjohannReduceFast_eq` for polynomial ones — so proofs go against the
direct version and executable code calls the fast one. See
[`../../CompPoly/LinearAlgebra/README.md`](../../CompPoly/LinearAlgebra/README.md).

## Coding Theory

Reed-Solomon codewords are not a separate representation — they are arrays of field
elements produced by evaluating a `CPolynomial` on a domain — but the decoders are a
substantial surface spanning `Univariate/ReedSolomon/`, `Bivariate/GuruswamiSudan/`,
`Univariate/Roots/`, and `LinearAlgebra/`. They are documented together in
[`coding-theory.md`](coding-theory.md).

## Field Extensions

`CompPoly.Extension.Ext P` is a *fixed-length* dense representation, unlike the
polynomial surfaces above: `Vector F P.d`, where `P : ExtensionParams F` carries the
degree `d`, the lower coefficients of the monic modulus `f`, and the base-field
cardinality `q` as a type index. Binomials `X^d - W` are the ergonomic special case,
entered through `BinomialParams.toExtensionParams`.

The bridge is
[`../../CompPoly/Fields/Extension/Bridge.lean`](../../CompPoly/Fields/Extension/Bridge.lean),
which maps into `AdjoinRoot P.poly` and proves the map bijective, and
[`../../CompPoly/Fields/Extension/Field.lean`](../../CompPoly/Fields/Extension/Field.lean),
which yields `Ext P ≃+* AdjoinRoot P.poly`.

Because the representation has a fixed length, the degree bound is structural and no
degree-bound invariant is carried; this subtree is independent of the `CPolynomial` stack
and imports none of `CompPoly/Univariate/`. See
[`field-extensions.md`](field-extensions.md) for the full architecture, including why the
ring and field instances must be built by hand rather than transported.
