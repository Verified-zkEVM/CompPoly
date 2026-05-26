# `perf/bivariate-topoly-skip-trim` — change report

## Goal

Optimize `CBivariate.evalY` so it does one trim at the end of the Horner fold
instead of paying a trim on every Y-coefficient. This follows the same
"defer the trim" pattern as the recent perf commits on `Raw.mul`, `Raw.powBySq`,
`divX`, `div`/`mod` wrappers, and the Lagrange basis/interpolation.

`evalY a f` computes `f` viewed as `R[X][Y]` evaluated at `Y = a`, returning
`R[X]`. The old implementation reused `CPolynomial.eval`, which goes through
`CPolynomial.mul`/`CPolynomial.add` — each of which trims its result. For a
bivariate of Y-degree `d`, that is roughly `2d` trims of the (growing) running
coefficient array. The new implementation folds with `Raw.smulRight` and
`Raw.addRaw` (neither trims) and trims exactly once at the end.

The branch name (`perf/bivariate-topoly-skip-trim`) matches the convention of
prior trim-deferral PRs.

## Summary of files touched

| File | Nature |
| --- | --- |
| `CompPoly/Univariate/Raw/Ops.lean` | New raw op `smulRight` |
| `CompPoly/Univariate/ToPoly/Core.lean` | New correctness lemma `toPoly_smulRight` |
| `CompPoly/Bivariate/Basic.lean` | New `evalY` definition; `evalEval` rewired; two theorems moved out |
| `CompPoly/Bivariate/ToPoly.lean` | New helper `toPoly_foldr_evalY_eq_sum`; `evalY_toPoly` rewritten; relocated correctness theorems |

## 1. `CompPoly/Univariate/Raw/Ops.lean` — `smulRight`

```lean
def smulRight [Mul R] (r : R) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  .mk (Array.map (fun a => a * r) p)
```

### Why a new op (instead of reusing `smul`)?

`smul r p` multiplies coefficients on the left (`r * a`); `smulRight r p`
multiplies on the right (`a * r`). The new `evalY` Horner step needs
right-multiplication by `Polynomial.C a`, which under `toPoly` corresponds to
`p.toPoly * Polynomial.C r`, not `Polynomial.C r * p.toPoly`.

For commutative semirings the two coincide, but `CPolynomial.Raw` is parametric
over `Semiring R` (non-commutative). Reusing `smul` would silently bake in a
commutativity assumption and break for the binary-field / non-commutative
clients. Hence a parallel `smulRight` with the symmetric correctness lemma.

The op is marked `@[inline, specialize]` to match `smul` and the other raw
arithmetic primitives.

## 2. `CompPoly/Univariate/ToPoly/Core.lean` — `toPoly_smulRight`

```lean
theorem toPoly_smulRight {p : CPolynomial.Raw Q} {r : Q} :
    (smulRight r p).toPoly = p.toPoly * Polynomial.C r
```

Proven coefficient-wise via `Polynomial.coeff_mul_C` and `Array.getElem?_map`.
Tagged `@[grind =]` to match the surrounding `toPoly_*` lemmas. This is the
correctness anchor that lets the new `evalY` proof relate the raw fold to a
`Polynomial.eval`.

## 3. `CompPoly/Bivariate/Basic.lean`

### New `evalY`

```lean
def evalY [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (a : R) (f : CBivariate R) : CPolynomial R :=
  ⟨(f.val.foldr
      (fun (c : CPolynomial R) (acc : CPolynomial.Raw R) =>
        (acc.smulRight a).addRaw c.val)
      (CPolynomial.Raw.mk #[])).trim,
   CPolynomial.Raw.Trim.isCanonical_trim _⟩
```

The fold is a textbook right-Horner over the Y-coefficients
(`((⋯ * Y + cₙ₋₁) * Y + cₙ₋₂) * Y + … + c₀`). Critically:

- accumulator type is `CPolynomial.Raw R`, not `CPolynomial R` — so each step
  is `smulRight` + `addRaw`, both untrimmed;
- the single `.trim` at the outside, plus `Raw.Trim.isCanonical_trim _`,
  reconstructs a canonical `CPolynomial R` once at the end.

### `evalEval` retargeted

```lean
def evalEval … (x y : R) (f : CBivariate R) : R :=
  CPolynomial.eval x (evalY y f)
```

Previously this inlined `f.val.eval (CPolynomial.C y)`. Routing through the new
`evalY` inherits the same optimization for free, and the rewritten
`evalEval_toPoly` proof becomes a two-line `rw` chain.

### Why the equality theorems were moved out

`eval_y_horner_eq_eval_y` (Horner agrees with the new sum-of-powers `evalY`) and
the dependent `eval_eval_horner_y_then_x_eq_eval_eval` used to live in
`Basic.lean`. With the old definition they were one-liners because both sides
were literally `f.val.eval (CPolynomial.C a)` — `simpa` finished them.

With the new `evalY`, the two sides are syntactically very different and the
honest proof needs `toPoly`-injectivity plus `toPoly_eq_map`. None of that
machinery is in scope in `Basic.lean` (it only imports `Univariate.Basic`).

Two options were considered:

- **(A) Move both theorems into `Bivariate/ToPoly.lean`** where `CPolynomial.toPoly`,
  `toImpl_toPoly_of_canonical`, `toPoly_eq_map`, etc. are available.
- **(B) Prove `eval_y_horner_eq_eval_y` directly in `Basic.lean`** by induction
  on `f.val`, reproving the trim-deferral lemma inline (a few dozen lines).

(A) was chosen: the theorems' natural home is alongside `evalY_toPoly`, they reuse
existing lemmas instead of re-deriving them, and the optimization itself doesn't
leak any new dependency into `Basic.lean`. A comment in `Basic.lean` points
readers to where the correctness theorem now lives.

## 4. `CompPoly/Bivariate/ToPoly.lean`

### Replaced helper: `toPoly_foldr_evalY_eq_sum`

The old helper `toPoly_foldl_zipIdx_eq_sum` bridged the foldl-over-`zipIdx` form
used by the old `evalY` and `evalEval` proofs. With the new definition the
bridge needs to be over `foldr` of the raw Horner step:

```lean
private theorem toPoly_foldr_evalY_eq_sum (l : List (CPolynomial R)) (y : R) :
    (l.foldr (fun c acc => (acc.smulRight y).addRaw c.val) ⟨#[⟩⟩).toPoly =
    ∑ i ∈ Finset.range l.length, (l[i]?.getD 0).toPoly * Polynomial.C y ^ i
```

The cons case unfolds one Horner step, applies `toPoly_addRaw` and the new
`toPoly_smulRight`, then matches the sum via `List.length_cons` (to expose
`tail.length + 1`) and `Finset.sum_range_succ'`. `List.length_cons` is the
critical lemma — without it, `Finset.sum_range_succ'` cannot pattern-match the
`(head :: tail).length`. The closing simp set folds `pow_succ`, `← mul_assoc`,
and `← Finset.sum_mul` to reach the LHS up to the trivial
`head.val.toPoly = head.toPoly` defeq, finishing with `rfl`.

### `evalY_toPoly` rewritten

The new proof first peels off the outer `Raw.toPoly_trim` and switches
`Array.foldr` to `List.foldr` (via `Array.foldr_toList`), then applies the new
helper. The remaining work — collapsing `f.val.toList` indices back to array
indices and identifying the sum with `(toPoly f).eval (C a)` — is the same
shape as the old proof of the foldl variant; only the simp lemmas for indexing
differ.

### Reordering inside `ImplementationCorrectness`

Source order matters: `evalEval_toPoly` now rewrites with `evalY_toPoly`, so
`evalY_toPoly` must be defined first. The original file had `evalY_toPoly` near
the bottom (line ~660). It and the two newly-imported theorems
(`eval_y_horner_eq_eval_y`, `eval_eval_horner_y_then_x_eq_eval_eval`) were
moved to sit immediately after the helper and before `evalEval_toPoly`. This
keeps all `evalY`-related correctness adjacent and removes the forward
reference.

### `eval_y_horner_eq_eval_y` proof

```lean
have h_inj : Function.Injective (CPolynomial.toPoly (R := R)) := by
  intro p₁ p₂ h
  apply Subtype.ext
  rw [← CPolynomial.toImpl_toPoly_of_canonical p₁, h,
      CPolynomial.toImpl_toPoly_of_canonical p₂]
apply h_inj
…
rw [CPolynomial.eval_horner_eq_eval, CPolynomial.eval_toPoly, toPoly_eq_map,
    Polynomial.eval_map]
have hC : (↑(CPolynomial.ringEquiv (R := R)) : CPolynomial R →+* Polynomial R)
              (CPolynomial.C a) = (Polynomial.C a : Polynomial R) :=
  CPolynomial.C_toPoly a
rw [← hC, Polynomial.eval₂_at_apply]
rfl
```

Strategy:

1. `toPoly` is injective on canonical polynomials. The witness is
   `toImpl_toPoly_of_canonical : p.toPoly.toImpl = ↑p`, used inline because
   it isn't quite a `Function.LeftInverse` (the subtype coercion gets in the
   way of the standard `Function.LeftInverse.injective` plumbing).
2. After injectivity, reduce both sides to `Polynomial`. LHS becomes
   `((CPolynomial.toPoly p).eval (C a)).toPoly`; RHS becomes
   `(toPoly p).eval (Polynomial.C a)`.
3. Expand `toPoly p = (CPolynomial.toPoly p).map ringEquiv` (`toPoly_eq_map`)
   and apply `Polynomial.eval_map` to turn `(P.map f).eval x` into
   `P.eval₂ f x`.
4. The shape `eval₂ f (f r)` matches `Polynomial.eval₂_at_apply`, which folds
   the eval into `f (P.eval r)` — i.e. `CPolynomial.toPoly` of the original
   eval. This matches the LHS exactly, modulo the `ringEquiv` = `toPoly`
   defeq finished by `rfl`.

### One subtle elaboration trap

`Polynomial.eval_map` introduces `eval₂` with first argument
`↑CPolynomial.ringEquiv` (the `RingEquiv → RingHom` coercion). An obvious
`hC` of the form

```lean
hC : Polynomial.C a = CPolynomial.ringEquiv.toRingHom (CPolynomial.C a)
```

does NOT match: even though `↑ringEquiv` and `ringEquiv.toRingHom` are
definitionally equal, `rw` matches syntactically and the higher-order
unification on `eval₂ ?f (?f ?r)` fails. The proof therefore states `hC` with
the explicit `(↑(CPolynomial.ringEquiv) : CPolynomial R →+* Polynomial R)`
coercion so the form on both sides is the same. After this `rw [← hC]`
introduces the `?f ?r` pattern unambiguously, and `Polynomial.eval₂_at_apply`
fires.

### `evalEval_toPoly` proof

```lean
show CPolynomial.eval x (evalY y f) = (toPoly f).evalEval x y
rw [CPolynomial.eval_toPoly, evalY_toPoly]
```

Once `evalEval` is `eval x (evalY y f)`, the two rewrites unfold to exactly
`Polynomial.evalEval`, so no terminal `rfl` is needed (and a trailing `rfl`
errors with "no goals" because `rw` closes the goal definitionally — this had
been left in by mistake during the in-progress edits).

## What was *not* done

- `evalX`, `evalEvalHornerXThenY`, `swap`, etc. were not retouched. They
  follow different evaluation patterns and the trim-deferral pattern that
  fits `evalY` doesn't apply directly.
- The Horner agreement proof was not generalized to a single shared
  `toPoly_*` lemma over arbitrary fold steps. The only consumer is `evalY`,
  and a generic helper would have a larger signature than the single use
  justifies.

## Verification

`lake build` and `lake test` both pass on the resulting tree.
