# Build Cache

Two independent caches keep you from compiling code someone else already compiled.
They cover different packages and are fetched by different commands.

| What | Covers | How you get it |
| --- | --- | --- |
| Mathlib's cache | `mathlib` and its own dependencies | `lake exe cache get` |
| CompPoly release archive | `CompPoly` itself | automatic for consumers; see below for contributors |

Neither is required — both only ever save time. If a fetch fails, Lake logs a warning
and builds from source.

## Consuming CompPoly

Nothing to run. A project that requires CompPoly at a release tag gets the prebuilt
library from a plain build:

```bash
lake exe cache get   # Mathlib's oleans
lake build           # downloads CompPoly's oleans instead of compiling them
```

This works because [`../../lakefile.lean`](../../lakefile.lean) sets
`preferReleaseBuild := true`, so Lake fetches
`CompPoly-oleans.tar.gz` from the matching GitHub release and unpacks it into the
build directory. One archive serves every platform: the library sets
`platformIndependent := true`, so its module traces exclude platform-dependent
elements and Linux-built oleans validate on macOS and Windows.

**This only applies to release tags.** Lake resolves the archive URL from a git tag
reachable at the revision you pinned, so a dependency pinned to an arbitrary `main`
commit has no tag, logs `no release tag found for revision`, and compiles from source.
Pin a release tag to get the cache.

## Working on CompPoly itself

Lake deliberately skips this mechanism for the root package — it assumes the package
you are editing should be built from your sources — so a contributor does not get the
archive from `lake build`. On a cold clone:

```bash
lake exe cache get   # Mathlib's oleans; the expensive half
lake build
```

That compiles CompPoly's own modules, currently a few minutes. To start from a release
tag's prebuilt artifacts instead, fetch the archive explicitly with an empty build
directory:

```bash
git checkout v4.32.0
gh release download v4.32.0 --pattern CompPoly-oleans.tar.gz
lake unpack CompPoly-oleans.tar.gz
```

## Publishing the archive

[`../../.github/workflows/lean_release_tag.yml`](../../.github/workflows/lean_release_tag.yml)
does this. On a push to `main` that changes
[`../../lean-toolchain`](../../lean-toolchain), `lean-release-tag` creates the tag and
release, then the `publish-oleans` job checks out that tag, fetches Mathlib's oleans,
builds the library, and runs `lake upload <tag>`.

The build step is `rm -rf .lake/build && lake build CompPoly`, and the narrow target
matters. `lake upload` packs the *whole* build directory, so a full `lake build` would
also ship the benchmark executable's Linux-only `bin/` and `.o` output — bloating the
asset and contradicting the platform-independence claim above.

To attach an asset to a release that predates this workflow, or to replace one, use
**Actions → Add Lean release tag → Run workflow** and give it the tag.
`lake upload` passes `--clobber`, so re-running replaces the existing asset.

## Reproducing an archive locally

```bash
lake exe cache get
rm -rf .lake/build && lake build CompPoly
lake pack                       # writes .lake/CompPoly-oleans.tar.gz
tar tzf .lake/CompPoly-oleans.tar.gz | head
```

`lake pack` only packs what is already built; it never builds anything.

## What this does not cover

CI's own per-commit build reuse is a separate mechanism — two GitHub Actions caches,
one for `.lake/packages` and one for `.lake/build`, with `lean-action` supplying
Mathlib's oleans via `lake exe cache get`. See
[`quickstart.md`](quickstart.md#ci-mapping). The release archive is cut once per
release tag and plays no part in it.
