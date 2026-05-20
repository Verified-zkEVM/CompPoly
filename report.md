# Branch report: `perf/divmod-skip-trim`

## Scope

Branched from `upstream/master` at `1fc573f` (PR #224, "defer trimming to end
of `Raw.mul` convolution fold"). It extends the same "trim exactly once, at
the end" discipline from `Raw.mul` and `CPolynomial.divX` to every
`CPolynomial`-level division wrapper.

Commits unique to this branch (excluding the `upstream/master` merge):

| Commit    | Subject                                                       | Status     |
|-----------|---------------------------------------------------------------|------------|
| `c708392` | perf(univariate): defer trimming to end of `Raw.mul` fold     | committed (same content already landed via PR #224) |
| `253796d` | perf(univariate): remove trim from `divX` definition          | committed  |
| *(WIP)*   | perf(univariate): skip post-trim in `div`/`mod` wrappers      | uncommitted, in `Basic.lean` + `Raw/Proofs.lean` |

The merge commit `39bab40` pulls upstream into the branch; it carries no
content of its own.

## What changed and why

### 1. `divX` — no post-extract trim (`253796d`, `Basic.lean`)

Old definition: `⟨q.trim, Trim.isCanonical_trim q⟩` where
`q = p.val.extract 1 p.val.size`.

New definition: returns the extracted array directly and discharges
`IsCanonical` inline.

**Why it's safe.** `p` is canonical, so its last entry is nonzero.
`Array.extract 1 size` only strips from the front, so the last entry
survives unchanged. The canonicity obligation reduces to
`(p.val.extract 1 p.val.size).getLast _ = p.val.getLast _`, which
`Array.getElem_extract` discharges.

Side effects:
- `[BEq R] [LawfulBEq R]` constraints drop from `divX`, `coeff_divX`,
  and `divX_size_lt` (no `trim` means no `BEq`).
- `coeff_divX` and `divX_size_lt` collapse to direct lemmas about
  `extract` instead of routing through `Trim.coeff_eq_coeff` /
  `Trim.size_le_size`.

### 2. `div`/`mod` family — no post-trim in wrappers (uncommitted, `Basic.lean` + `Raw/Proofs.lean`)

All six division-family wrappers in `CPolynomial` previously wrapped each
`Raw.*` call in `(...).trim` and proved canonicity with
`Trim.isCanonical_trim`. The uncommitted change replaces those with raw
calls plus `Trim.isCanonical_of_trim_eq <canonical-proof>`:

| Wrapper                     | Why no trim is needed                                                                                |
|-----------------------------|------------------------------------------------------------------------------------------------------|
| `divByMonic`                | `divModByMonicAux.go` accumulates the quotient via `Raw.add` (already trims); base case returns `0`. |
| `modByMonic`                | Each recursive step feeds the next call `(p - q').trim`; base case returns its (canonical) input.    |
| `modByMonicRemainderOnly`   | `subScaledShift` ends with `.trim`, so every intermediate remainder is canonical.                    |
| `modByMonicByReversal`      | The reversal branch ends in `Raw.sub` (trims via `Raw.add`); fallback delegates to the above.        |
| `div`                       | Delegates to `divByMonic`.                                                                           |
| `mod`                       | Calls `modByMonic` on `C (q.leadingCoeff)⁻¹ * p`, whose `Raw.mul` step trims.                        |

The reasoning above is captured in seven new lemmas in
`CompPoly/Univariate/Raw/Proofs.lean`:

- `add_is_trimmed`, `sub_is_trimmed` — bridge lemmas (analogues of the
  existing `mul_is_trimmed`).
- `subScaledShift_is_trimmed` — the leaf operation used by both
  remainder algorithms.
- `divModByMonicAux_go_fst_canonical` / `divModByMonicAux_go_snd_canonical`
  — induction on the recursion depth: quotient is *always* canonical;
  remainder is canonical when the input is.
- `modByMonicRemainderOnly_go_canonical` — same induction for the
  remainder-only variant.
- Public wrappers `divByMonic_canonical`, `modByMonic_canonical`,
  `modByMonicRemainderOnly_canonical`, `modByMonicByReversal_canonical`,
  `div_canonical`, `mod_canonical`.

The `modByMonic`/`mod` family requires `p.trim = p` as a hypothesis,
which is supplied at the wrapper boundary via
`Trim.trim_eq_of_isCanonical p.property` (the `CPolynomial` invariant).
`divByMonic`/`div` need no such hypothesis: the quotient is canonical
unconditionally.

## Why this is worth doing

The merged `Raw.mul` work (PR #224) was the headline win — it cut O(n)
extra `trim` scans down to a single end-of-fold trim. The follow-ups on
this branch are smaller but in the same spirit: every place where a
canonical-by-construction `Raw` result was getting re-trimmed at the
`CPolynomial` boundary is one extra O(size) scan and one extra
canonicity-by-`trim` proof that adds nothing. Removing them:

- skips a redundant array scan per `div`/`mod`/`divX` call, and
- avoids producing `Trim.isCanonical_trim` proof terms when a structural
  argument suffices.

The bottleneck in `divByMonic` is still the recursion itself
(`O(deg p · deg q)`); this change does not touch that.

## Files touched

- `CompPoly/Univariate/Basic.lean` — `divX` (committed) and the six
  division wrappers (uncommitted).
- `CompPoly/Univariate/Raw/Proofs.lean` — seven new canonicity lemmas
  (uncommitted).

No public API signatures change; only the canonicity-proof obligations
inside the `Subtype` constructors and a relaxation of typeclass
constraints on `divX`/`coeff_divX`/`divX_size_lt`.

## Validation status

Per `CLAUDE.md`, the standard validation gates for this kind of change
are `lake build`, `lake test`, and `scripts/lint-style.sh`. The
committed `divX` change (`253796d`) was made against a clean build; the
uncommitted `div`/`mod` work has not yet been re-validated end-to-end on
this report's writing.
