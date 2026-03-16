# Typeclass Minimization

This page records the repo's expectation that new Lean declarations carry the
weakest typeclass assumptions that actually match the code.

## Core Rule

- For every new `def`, `instance`, `lemma`, or `theorem`, spell out the minimal
  typeclass assumptions needed by that declaration.
- Avoid blanket section-level declarations such as
  `variable {R : Type*} [Ring R] [BEq R] [LawfulBEq R]` unless every
  declaration in scope genuinely needs all of them.
- Keep definitions as weak as possible even if some later proofs need stronger
  assumptions.
- If one theorem in a group needs stronger assumptions than nearby definitions,
  strengthen only that theorem instead of the whole section.

## Preferred Style

Avoid:

```lean
variable {R : Type*} [Ring R] [BEq R] [LawfulBEq R]

def coeff (p : Foo R) : R := ...
def X : Foo R := ...
theorem support_spec (p : Foo R) : ... := ...
```

Prefer:

```lean
def coeff {R : Type*} [Zero R] (p : Foo R) : R := ...

def X {R : Type*} [Zero R] [One R] : Foo R := ...

theorem support_spec {R : Type*} [Zero R] [BEq R] (p : Foo R) : ... := ...
```

## How To Choose The Weakest Assumptions

- Use `Zero` for coefficient lookup, support, degree, trimming, and other
  zero-sensitive queries.
- Use `Zero` and `One` for constants and variables.
- Use `Add` or `Semiring` only when addition or multiplication is actually used.
- Use `NegZeroClass` for coefficientwise negation facts when the only extra fact
  needed is `-0 = 0`.
- Use `Ring` only when the declaration genuinely uses subtraction or additive
  inverses in an essential way.
- Add `DecidableEq`, `BEq`, or `LawfulBEq` only when the declaration actually
  branches on equality, trims through `BEq`, or uses lemmas that require those
  structures.

## Recent Refactor Examples

These examples come directly from the recent typeclass-tightening refactor.

- `CompPoly/Univariate/Quotient.lean` now defines the quotient carrier at
  `Zero` level because coefficientwise equivalence only needs zero-padding:

```lean
def QuotientCPolynomial (R : Type*) [Zero R] :=
  Quotient (@Raw.instSetoidCPolynomial R _)
```

- `CompPoly/Bivariate/ToPoly.lean` now states bridge lemmas like
  `evalEval_toPoly` at `Semiring` level because the proof uses only additive and
  multiplicative structure:

```lean
theorem evalEval_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Semiring R]
    (x y : R) (f : CBivariate R) :
    @CBivariate.evalEval R _ _ _ _ x y f = (toPoly f).evalEval x y := by
  ...
```

- `CompPoly/Univariate/Raw/Proofs.lean` now keeps `neg_coeff` at
  `NegZeroClass` rather than `Ring` because coefficientwise negation only needs
  `-0 = 0`:

```lean
lemma neg_coeff {R : Type*} [NegZeroClass R] (p : CPolynomial.Raw R) (i : ℕ) :
    p.neg.coeff i = - p.coeff i := by
  ...
```

- `CompPoly/Univariate/Raw/Division.lean` no longer carries a blanket `Ring`
  assumption at section scope because every definition already has its own
  `[Field R]` requirement:

```lean
section Division

variable [BEq R]

def divModByMonicAux [Field R] ...
```

## Review Checklist

Before finishing a change, check:

- Could this declaration drop from `Ring` to `Semiring`?
- Could it drop from `Semiring` to `Zero`, `One`, `Add`, or `Mul`?
- Is `NegZeroClass` enough instead of `Ring`?
- Is a section-level `variable [...]` forcing stronger assumptions onto nearby
  declarations that do not need them?
- If a stronger theorem is unavoidable, can the stronger assumptions be made
  local to that theorem?
