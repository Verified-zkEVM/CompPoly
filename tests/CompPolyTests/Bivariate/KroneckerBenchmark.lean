/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/

import CompPolyTests.Bivariate.KroneckerCommon

/-!
  # Bivariate Multiplication Benchmark

  Manual benchmark comparing four strategies for bivariate multiplication over the
  KoalaBear field:

  1. **normal** — the schoolbook `CBivariate` product `p * q`;
  2. **kron** — Kronecker substitution with schoolbook univariate multiplication;
  3. **kron+NTT** — Kronecker with the classic NTT (`NTT.FastMul.withFallback`);
  4. **kron+FastNTT** — Kronecker with the recursive NTT (`NTTFast.withFallback`).

  All four results are checked for agreement at every size. Operands are square
  (`degX = degY = n`) and the Kronecker stride is `D = 2 * n`, which always satisfies
  `natDegreeX (p * q) < D`, so unpacking is faithful. Shared data (`mkBiv`,
  `bestDomainForLength?`, `kronWith`) lives in `KroneckerCommon.lean`; the agreement
  check lives in `Kronecker.lean`.

  Not part of the aggregate `CompPolyTests` build; run manually, e.g.
  `lake build CompPolyTests.Bivariate.KroneckerBenchmark`.
-/

namespace CompPoly
namespace CBivariate
namespace Benchmark

open CBivariate.TestCommon

/-- Sweep of square sizes (`degX = degY = n`).

Kept modest because `#eval` runs in the interpreter; for larger sizes compile a native
executable (see the note at the bottom of this file). The NTT crossover on the packed
univariate operand (size `2 * n^2`) is already visible by `n = 16`–`32`. -/
def benchSizes : Array Nat := #[4, 8, 12, 16, 24, 32]

/-- Render an average millisecond count. -/
def avgMsString (totalMs reps : Nat) : String :=
  s!"{(Float.ofNat totalMs) / (Float.ofNat reps)}"

/-- Number of repetitions to use for a given square size. -/
def repeatsFor (n : Nat) : Nat :=
  if n ≤ 8 then 10
  else if n ≤ 16 then 4
  else 1

/-- Time repeated calls to a thunk and return the final result. -/
def timeRepeated {α : Type} (reps : Nat) (f : Unit → α) : IO (Nat × α) := do
  let actualReps := max reps 1
  let start ← IO.monoMsNow
  let mut last := f ()
  for _ in [1:actualReps] do
    last := f ()
  let stop ← IO.monoMsNow
  pure (stop - start, last)

#eval show IO Unit from do
  IO.println s!"sizes tested = {benchSizes.size}  (degX = degY = n, stride D = 2n)"
  IO.println "n | reps | normal ms | kron ms | kron+NTT ms | kron+FastNTT ms"
  IO.println "------------------------------------------------------------------"
  for i in [0:benchSizes.size] do
    let n := benchSizes[i]!
    let reps := repeatsFor n
    let D := 2 * n
    let p := mkBiv n n (41 + 13 * i)
    let q := mkBiv n n (73 + 17 * i)
    let (normalMs, normalRes) ← timeRepeated reps (fun _ ↦ p * q)
    let (kronMs, kronRes) ← timeRepeated reps (fun _ ↦ kronWith (· * ·) D p q)
    let (nttMs, nttRes) ←
      timeRepeated reps (fun _ ↦ kronWith (CPolynomial.NTT.FastMul.withFallback
        bestDomainForLength?) D p q)
    let (fastMs, fastRes) ←
      timeRepeated reps (fun _ ↦ kronWith (CPolynomial.NTTFast.withFallback
        bestDomainForLength?) D p q)
    unless (kronRes == normalRes) && (nttRes == normalRes) && (fastRes == normalRes) do
      throw <| IO.userError s!"benchmark mismatch at n = {n}"
    let row :=
      s!"{n} | {reps} | {avgMsString normalMs reps} | {avgMsString kronMs reps} | " ++
      s!"{avgMsString nttMs reps} | {avgMsString fastMs reps}"
    IO.println row

end Benchmark
end CBivariate
end CompPoly

/-
  ## Running larger sizes

  `#eval` runs in the interpreter, which dominates the absolute timings (the relative
  comparison and crossover are still meaningful). For larger operands, compile natively:
  turn the `#eval` body into `def main : IO Unit` and add a `lean_exe` target to the
  lakefile, or run with `lake env lean --run` on a standalone copy. Native execution is
  typically two to three orders of magnitude faster, pushing the practical sweep well past
  `n = 32`.
-/
