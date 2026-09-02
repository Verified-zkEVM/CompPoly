# Lean Module System

Every `.lean` file in this repo — `CompPoly.lean`, `CompPoly/**`, `tests/**`, and
`bench/**` — uses the Lean 4 module system. `lakefile.lean` is the only exception.

The reference for the module system is [here](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/).

## File Header Shape

New library modules should use the narrowest import and exposure modifiers that
their public API requires:

```lean
/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
module

import Mathlib.Tactic.Ring
public import CompPoly.Data.Array.Lemmas

/-!
# Module docstring
-/

public section
```

- `module` goes on the line after the copyright header, before the imports.
- Use plain `import` for proof and implementation dependencies. Use `public import`
  only when the current module deliberately re-exports the imported API or a public
  declaration requires it.
- Use `public section` for exported declarations. Keep definition bodies opaque by
  default, and put `@[expose]` on individual definitions only when downstream
  definitional reduction is an intentional part of their interface.

## Internal Definition Access

Proof and correctness modules in this package may need to unfold an implementation
without exposing it to every downstream importer. Import the private scope alongside
the public API in that case:

```lean
module

import all CompPoly.Univariate.Raw.Ops
public import CompPoly.Univariate.Raw.Ops

public section
```

The plain `import all` is an explicit same-package implementation dependency; the
separate `public import` preserves the intended re-export. Prefer a characterization
lemma when ordinary downstream code only needs a behavioral fact. The
`CompPoly.Univariate.Raw` modules are the first migrated example of this pattern.

Definitions implemented with a `where` recursion may require targeted `@[expose]`
when a separate correctness module refers to the generated `.go` declaration by
name. Do not restore file-wide exposure for this case.

## Test Files And `meta`

`#guard` and `#eval` run compiled code *during elaboration*, so any module whose
definitions they evaluate must be imported as `meta`. Test files that contain
`#guard`/`#eval` therefore use:

```lean
module

public meta import CompPoly.Fields.KoalaBear.Fast

public meta section
```

Immediately post-migration, this may be `@[expose]`d.

A file may need both forms. `tests/CompPolyTests/Fields/Extension/Arithmetic.lean`
mixes `#guard`s (which need the `meta` imports) with `example : Algebra .. :=
inferInstance` declarations (which are ordinary declarations and need a plain
`public import` of the same module). Repeating the import with a different modifier
is legal and is the intended fix.

The `pratt` tactic in [`../../CompPoly/Fields/PrattCertificate.lean`](../../CompPoly/Fields/PrattCertificate.lean)
is currently the one place in the library proper with `meta` code. Meta definitions may only
call other `meta` definitions from the same module, so the whole elaboration
pipeline (`powMod`, `factor`, `computePrattCertificate`, `verifyCertificate`, ...)
is `meta def`. Theorems that end up inside generated proof terms via `q(...)` must
stay ordinary declarations.

## Fix Patterns For Migration Fallout

When a proof breaks after modulization, it is almost always one of these:

| Symptom | Cause | Fix |
|---|---|---|
| `rfl`/`simp [Foo]` fails, "Expected a definition with an exposed body" | Unfolding a library definition whose body is not exposed (`Vector.ofFn`, `Array.rightpad`, `AddMonoidAlgebra.mul'`) | Use a characterisation lemma (`Array.size_rightpad`, `List.rightpad_toArray`, `AddMonoidAlgebra.mul_def`) or `ext`/`cases` first |
| `Unknown identifier X` plus a "would need to be public" note | `private` declaration used from an exposed body or another module | Remove `private` |
| `tactic execution is stuck, goal contains metavariables` | Notation or `cast (by exact h) x` whose type is opaque | Type-ascribe the term, or pass the proof term directly instead of `by exact` |
| `Unknown constant Std....Internal....` | Internal lemmas are no longer re-exported transitively | Import the specific internal module, e.g. `Std.Data.DTreeMap.Internal.Lemmas` |
| `rw`/`erw` "did not find an occurrence" on a pattern that is visibly present | Over-specialised rewrite (`lemma (p := p + q)`) no longer matches syntactically | Use the unspecialised `simp only [lemma]` |
| Duplicate declaration after removing `private` | Two modules had identically named `private` helpers | Keep one and delete the duplicate |

## Regenerating `CompPoly.lean`

[`../../scripts/update-lib.sh`](../../scripts/update-lib.sh) emits a modulized root
file (`module`, blank line, one `public import` per tracked source file). See
[`generated-files.md`](generated-files.md).
