# CompPoly tests

This directory contains Lean test modules for regression and behavioral checks.

## Structure

Tests mirror the `CompPoly/` hierarchy under the `CompPolyTests` namespace.
For example:

- library module: `CompPoly/Univariate/Raw.lean`
- test module: `tests/CompPolyTests/Univariate/Raw.lean`

## Running tests

Build all tests:

```bash
lake build CompPolyTests
```

Build a single test module:

```bash
lake build CompPolyTests.Univariate.Raw
```