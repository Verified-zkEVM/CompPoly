# CompPoly tests

This directory contains Lean test modules for regression and behavioral checks.

## Structure

Tests mostly mirror the `CompPoly/` hierarchy under the `CompPolyTests` namespace.
For example:

- library module: `CompPoly/Univariate/Raw.lean`
- test module: `tests/CompPolyTests/Univariate/Raw.lean`

Some tests are cross-cutting rather than one-to-one mirrors (for example, `CompPolyTests/BF128GhashPrelude.lean`).

## Running tests

Build all tests:

```bash
lake test
```

Build a single test module:

```bash
lake build CompPolyTests.Univariate.Raw
```