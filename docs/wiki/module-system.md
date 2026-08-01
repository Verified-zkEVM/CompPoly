# Lean Module System

Every `.lean` file in this repo — `CompPoly.lean`, `CompPoly/**`, `tests/**`, and
`bench/**` — uses the Lean 4 module system. `lakefile.lean` is the only exception.

## File Header Shape

Library and bench files look like this:

```lean
/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
module

public import Mathlib.Algebra.Ring.Defs
public import CompPoly.Data.Array.Lemmas

/-!
# Module docstring
-/

@[expose] public section
```

- `module` goes on the line after the copyright header, before the imports.
- Imports are `public import`, so downstream modules keep seeing them.
- `@[expose] public section` goes after the module docstring and stays open for the
  rest of the file, so definition bodies remain available to `rfl`, `decide`, `simp`,
  and kernel reduction downstream.

This is exactly what lean4's `script/Modulize.lean` produces; the whole tree was
converted with it against the toolchain pinned in `lean-toolchain`.

## Test Files And `meta`

`#guard` and `#eval` run compiled code *during elaboration*, so any module whose
definitions they evaluate must be imported as `meta`. Test files that contain
`#guard`/`#eval` therefore use:

```lean
module

public meta import CompPoly.Fields.KoalaBear.Fast

public meta section
```

A file may need both forms. `tests/CompPolyTests/Fields/Extension/Arithmetic.lean`
mixes `#guard`s (which need the `meta` imports) with `example : Algebra .. :=
inferInstance` declarations (which are ordinary declarations and need a plain
`public import` of the same module). Repeating the import with a different modifier
is legal and is the intended fix.

The `pratt` tactic in [`../../CompPoly/Fields/PrattCertificate.lean`](../../CompPoly/Fields/PrattCertificate.lean)
is the one place in the library proper with `meta` code. Meta definitions may only
call other `meta` definitions from the same module, so the whole elaboration
pipeline (`powMod`, `factor`, `computePrattCertificate`, `verifyCertificate`, ...)
is `meta def`. Theorems that end up inside generated proof terms via `q(...)` must
stay ordinary declarations.

## `private` Now Means Module-Private

Under the module system `private` is real privacy: the declaration is invisible
outside its own module, and a `@[simp] private theorem` is *not* in the simp set of
importing modules. Two consequences show up repeatedly:

- A `private` helper referenced by an exposed public definition fails with
  "unknown identifier ... would need to be public to access here". Drop `private`.
- `@[simp] private theorem` used by proofs in other modules silently stops firing.
  Drop `private` there too.

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
