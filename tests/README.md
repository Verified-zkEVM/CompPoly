# CompPoly tests

This directory contains Lean test modules for regression and behavioral checks.

## Structure

Tests mostly mirror the `CompPoly/` hierarchy under the `CompPolyTests` namespace.
For example:

- library module: `CompPoly/Univariate/Raw.lean`
- test module: `tests/CompPolyTests/Univariate/Raw.lean`

Some tests are cross-cutting rather than one-to-one mirrors, and some mirror a
whole subtree rather than a single module (for example,
`tests/CompPolyTests/Fields/Binary/BF128Ghash/`).

## Running tests

Build all tests:

```bash
lake test
```

Build a single test module:

```bash
lake build CompPolyTests.Univariate.Raw
```

## Native startup and field arithmetic

`lake test` checks the Lean test modules. The separate `CompPolyNativeSmoke` executable checks
linked module initialization and BF64/Ext3 arithmetic. On Linux with GNU `timeout`, run from the
repository root:

```bash
lake build --wfail CompPolyNativeSmoke && (
  set -euo pipefail
  ulimit -v 4194304
  ulimit -c 0
  LEAN_NUM_THREADS=1 timeout --kill-after=5s 30s .lake/build/bin/CompPolyNativeSmoke
)
```

The build runs normally. Execution has a 4 GiB address-space limit, a 30-second deadline, and a
five-second termination grace period. These limits cover initialization before `main`, where
accidental full-field enumeration could otherwise exhaust memory. Arithmetic mismatches, startup
failures, resource exhaustion, and timeout all fail the command.

The executable checks a wrapping BF64 product, an Ext3 reference product, addition, and inversion
including zero. It prints a success message only after every check passes. This is native
implementation evidence, not a proof of the compiler or a performance benchmark. Other platforms
can build the target; running it requires equivalent platform-specific resource limits.
