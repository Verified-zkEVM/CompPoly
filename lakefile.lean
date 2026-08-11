import Lake

open System Lake DSL

package CompPoly where
  version := v!"0.1.0"
  testDriver := "CompPolyTests"
  -- Downstream users fetch prebuilt artifacts from our GitHub releases instead of
  -- compiling CompPoly from source. Lake only does this for a package consumed as a
  -- dependency; it skips the root package, so this does not affect building CompPoly
  -- itself. See `docs/wiki/build-cache.md`.
  preferReleaseBuild := true
  -- Set explicitly rather than left to Lake's `remoteUrl?` fallback. `gh` accepts a
  -- URL here, so this serves both the download URL and `lake upload`'s `-R`.
  releaseRepo := "https://github.com/Verified-zkEVM/CompPoly"
  -- Overrides Lake's default `CompPoly-{platform}.tar.gz`: one archive serves every
  -- platform, because the archive holds only the platform-independent library
  -- artifacts (see `platformIndependent` on `lean_lib CompPoly` below).
  buildArchive := "CompPoly-oleans.tar.gz"
  -- A CompPoly release only supports the toolchain it was built with, so let Lake
  -- prioritize it when resolving toolchains for downstream projects.
  fixedToolchain := true

require "leanprover-community" / mathlib @ git "v4.32.0"

@[default_target]
lean_lib CompPoly where
  -- Release archives are built on Linux CI and consumed on every platform. This drops
  -- platform-dependent elements from module traces so those oleans validate on macOS
  -- and Windows too. Declared on the library rather than the package so it does not
  -- also claim platform independence for `lean_exe CompPolyBench`, whose native output
  -- genuinely is platform-specific. Mathlib uses the same mechanism.
  platformIndependent := true

lean_lib CompPolyTests where
  srcDir := "tests"

lean_lib CompPolyBenchLib where
  srcDir := "bench"
  globs := #[Glob.submodules `CompPolyBench]

lean_exe CompPolyBench where
  srcDir := "bench"

/-- Kernel-level axiom / `sorry` accounting with a committed regression baseline
(`scripts/axiom_baseline.json`). Runtime-imports the built CompPoly oleans, so run it
after `lake build`. See `scripts/AxiomSweep.lean`. -/
lean_exe axiomsweep where
  srcDir := "scripts"
  root := `AxiomSweep
  supportInterpreter := true
