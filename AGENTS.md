# CompPoly — Agent & Contributor Guidelines

## Trusted Code Base (TCB) Policy

**`native_decide` is forbidden.** The project must not depend on `Lean.ofReduceBool`.
All proofs must be kernel-safe — verifiable by Lean's type-checker alone, without
trusting the compiler.

- Use `decide` for decidable propositions (kernel-evaluated).
- For expensive kernel computations (e.g., BitVec arithmetic), use `Nat`-based
  structural recursion instead of `Finset.fold` over `BitVec` — see the `clMulNat`
  pattern in `CompPoly/Fields/Binary/BF128Ghash/Prelude.lean`.
- If `decide` is too slow, restructure the proposition (e.g., batch multiple checks
  into a single conjunction) rather than reaching for `native_decide`.

## Performance Guidelines

### Typeclass instances

- **Never** put `@[simp]` on `instance` declarations. Instances are found by
  typeclass synthesis, not `simp`. Marking them `@[simp]` registers equation lemmas
  that cause `simp` to unfold typeclass internals, ballooning unification work.
- Prefer explicit instance constructions (e.g., `Field.isDomain`) over
  `inferInstance` when the synthesis path is long or ambiguous.

### Tactics

- Prefer `simp only [...]` over bare `simp` — bare `simp` pulls in the full simp set.
- Avoid `grind` when a simpler tactic suffices (`omega`, `ring`, `simp only`, `exact`).
  `grind` generates large proof terms via saturation-based reasoning.
- Use `decide` sparingly on large types — each `decide` must be kernel-evaluated.

### Certificate / computational proofs

- For proofs that reduce large arithmetic in the kernel (e.g., modular squaring
  certificates over finite fields), define kernel-efficient checkers using `Nat`
  primitives (`Nat.testBit`, `Nat.xor`, `Nat.shiftLeft`) with structural recursion.
- Prove equivalence to the mathematically clean definition once, then use the fast
  checker in all certificate lemmas.
- Specialize operations where possible (e.g., if a polynomial has few nonzero
  coefficients, hardcode the multiplication instead of iterating over all bits).

### Imports

- Avoid umbrella imports like `import Mathlib.Tactic`. Import only the specific
  modules you need (e.g., `Mathlib.Tactic.Ring`, `Mathlib.Tactic.Omega`).
