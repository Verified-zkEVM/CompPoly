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
linked module initialization, BF64/Ext3 arithmetic, and canonical binary-tower powers. On Linux
with GNU `timeout`, run from the repository root:

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

The tower checks pass the field dictionary to a generic helper with inlining and specialization
disabled. They cover large natural and negative integer exponents, zero bases and exponents,
and a high bit at level 7. `CompPolyTests/Fields/Binary/Tower/Powers.lean` additionally checks symbolic
operation projections and agreement with the named raw binary-power routine. These checks
establish operation and execution behavior, not compiler correctness or a performance ranking.

The packed accumulation checks compare complete 128-bit output words against concrete tower
operations. They exercise arbitrary initial accumulators, empty and cancelling sums, both limbs,
the highest bit, and the generic coefficient-evaluation entry point. A same-width BF64/tower
counterexample checks that the two field presentations remain distinct. The corresponding
`CompPolyTests/Fields/Binary/Tower/ProductAccumulation.lean` regression also checks the universal
refinement statements and coefficient ordering.
