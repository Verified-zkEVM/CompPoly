# Linear Algebra

Executable matrices for [CompPoly](../../README.md), in two independent flavours:
dense matrices over a field, and row-oriented matrices whose entries are
univariate polynomials. Both exist to serve the Guruswami-Sudan interpolation
backends (see [`../../docs/wiki/coding-theory.md`](../../docs/wiki/coding-theory.md)),
but neither depends on the decoder and both are usable on their own.

`TensorProduct/Basis.lean` contains generic tensor basis theory with explicit
scalar actions, independently of the executable matrix layers.

## Types

| Type | Description |
|------|-------------|
| `DenseMatrix F` | Dense row-major storage: a flat `Array F` plus `rows` and `cols`. `WellFormed` asserts `data.size = rows * cols`. |
| `RrefResult F` | The output of row reduction: the reduced matrix together with its pivot columns. |
| `PolynomialRow F` | A row of univariate polynomials, `Array (CPolynomial F)`. |
| `PolynomialMatrix F` | An array of `PolynomialRow`s, with no shape invariant baked in. |

## Dense matrices (`Dense/`)

| Module | Description |
|--------|-------------|
| **Basic.lean** | `DenseMatrix`, `WellFormed`, `index`/`get`/`set`, and the homogeneous-system predicates. |
| **RowOps.lean** | Executable row operations (`swapRows`, `scaleRow`, `addScaledRow`, `findPivotRow`, `normalizeAndEliminate`) and Gauss-Jordan reduction `rref`, returning an `RrefResult`. |
| **RowOpsCorrectness.lean** | Proof layer for the individual row operations. |
| **RrefSemantics.lean** | Semantic preservation and reflection lemmas for row reduction — what `rref` preserves about the solution set. |
| **RrefShape.lean** | The shape invariants: `PivotColumnsShaped`, `PivotColumnsStrict`, `ProcessedColumnsZeroBelow`. |
| **Kernel.lean** | Homogeneous-kernel extraction from a reduced matrix: `freeColumns`, `basisVectorForFreeColumn`, `homogeneousKernelBasis`, `homogeneousWitness`. |
| **KernelCorrectness.lean** | `homogeneousWitness_eq_none_iff` and `homogeneousWitness_exists_of_rows_lt_cols` — a wide homogeneous system always has a nonzero solution. |
| **KernelInPlace.lean** | Allocation-efficient variant: `rrefInPlace`, `homogeneousKernelBasisInPlace`, `homogeneousWitnessInPlace`. |
| **KernelInPlaceCorrectness.lean** | `rrefInPlace_eq` and `homogeneousWitnessInPlace_eq`, proving the fast path returns exactly what the direct path does. |

### Why the in-place variant exists

`RowOps.lean` threads a whole `DenseMatrix` through every operation. Because
`scaleRow` / `addScaledRow` / `swapRows` read through `M.get` while the structure
`M` is still live, the backing array is multiply-referenced at the first write, so
`Array.setIfInBounds` copies the entire array on every call. Gauss-Jordan does
`Θ(rows)` row operations per pivot over `Θ(min rows cols)` pivots, which turns an
`O(n³)` algorithm into `O(n⁴)` work plus `Θ(n⁴)` words of short-lived allocation.

`KernelInPlace.lean` performs the same arithmetic in the same order, threading a
bare `Array F` with the dimensions passed separately. The array stays uniquely
referenced as it flows between operations, so writes mutate in place after at most
one fork from a shared input. The results are bit-for-bit identical, which is
exactly what `rrefInPlace_eq` says — so use the in-place path in executable code
and reason with `rref`.

## Polynomial matrices (`PolynomialMatrix/`)

| Module | Description |
|--------|-------------|
| **Basic.lean** | `PolynomialRow`, `PolynomialMatrix`, and row-level accessors. |
| **Degree.lean** | Degree helpers for polynomial rows. |
| **Shifted.lean** | Shifted degrees: the degree of a row measured against a per-column shift vector. |
| **RowSpan.lean** | `rowLinearCombination`, `RowSpan`, `RowSpanEq`, and `matrix_row_mem_rowSpan` — the invariant reduction must preserve. |
| **ShiftedReduction.lean** | The shifted row-reduction context. |
| **MuldersStorjohann.lean** | The reducer: `shiftedLeadingConflict?`, `cancelShiftedLeadingTerm`, `muldersStorjohannStep`, `muldersStorjohannReduceWithFuel`, and `muldersStorjohannReduce` with its termination measure `muldersStorjohannFuel`. Also the fast variants. |
| **MuldersStorjohannCorrectness.lean** | Umbrella for the correctness contract; the argument itself is split across `MuldersStorjohannCorrectness/`. |

### The correctness subtree

`MuldersStorjohannCorrectness/` splits the proof by concern: `Conflict`,
`Leading`, `RowOps`, `MatrixRows`, `Combinations`, `Reduction`, `Measure`,
`Minimal`, and `Fast`. The results worth knowing:

- `muldersStorjohannStep_rowSpan_subset` / `_superset` (`Reduction.lean`) — each
  step preserves the row span, so the reduced matrix generates the same module.
- `muldersStorjohannReduce_least_row_minimal` (`Minimal.lean`) — the output is
  shift-minimal, which is what the Lee-O'Sullivan interpolation backend consumes.
- `Measure.lean` — the decreasing measure justifying the fuel bound.

### Direct versus fast

The direct loop recomputes every row's shifted leading position for each scanned
row pair and cancels leading terms through a generic monomial-times-row multiply.
The fast variants compute each row's leading position once per scan and use the
fused `rowSubScaledShift` update.

`MuldersStorjohannCorrectness/Fast.lean` proves them extensionally equal —
`muldersStorjohannStepFast_eq`, `muldersStorjohannReduceWithFuelFast_eq`,
`muldersStorjohannReduceFast_eq` — so every correctness result stated for the
direct definitions transfers to the fast ones. Write proofs against the direct
version; call the fast one.

## Tensor product bases (`TensorProduct/`)

`TensorProduct/Basis.lean` provides `Module.Basis.baseChangeRight`: a basis of
`Left ⊗[K] Right` over `Right` with basis vectors `b i ⊗ₜ[K] 1` and scalars acting
on the right factor. Its construction uses Mathlib's
`Algebra.TensorProduct.commRight.toLinearEquiv`. The coordinate formula is
`baseChangeRight_repr_tmul`; the basis vectors are exposed by
`baseChangeRight_apply`. Standard `Basis.sum_repr` and `Basis.repr_sum_self`
give reconstruction and coordinate recovery.

Mathlib provides direct tensor instances for `Algebra`, `Module`, `DistribMulAction`
and `SMul`, using the left factor. For a right view on equal factors, select all
four locally:

```lean
letI rightAlgebra : Algebra L (L ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
letI : Module L (L ⊗[K] L) := rightAlgebra.toModule
letI : DistribMulAction L (L ⊗[K] L) := rightAlgebra.toModule.toDistribMulAction
letI : SMul L (L ⊗[K] L) := rightAlgebra.toSMul
let bRight := b.baseChangeRight (Right := L)
```

The module selection allows right-basis projections such as `bRight.repr`.
The `SMul` selection makes `c • z` act on the right factor, and `DistribMulAction`
ensures that ordinary laws such as `smul_add` and `mul_smul` use that same action.
Selecting the algebra alone does not override those direct defaults. No alternative
global instance is installed by this module or its binary-tower re-export.

This recipe chooses one meaning for scalar notation in its scope. Both coordinate
functions can coexist after their respective module choices have been fixed;
the recipe does not provide two simultaneous meanings for `•` on the same carrier.

## Matrix conventions

- Both layers are `Array`-backed and index with plain `Nat`, with out-of-bounds
  reads returning a default rather than requiring a proof at the call site. Shape
  facts are separate propositions (`WellFormed`, the `RrefShape` predicates), not
  invariants carried in the type.
- Nothing here depends on `CompPoly/Multivariate/` or on Mathlib's `Matrix`; there
  is no bridge to `Matrix` yet, and adding one would be new work.
