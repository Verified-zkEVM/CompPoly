/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Univariate.Common
public import CompPoly.Univariate.NTTFast.FastMul
public import CompPoly.Univariate.NTTFast.Plan

/-!
# Schoolbook / NTT crossover

Where NTT-based multiplication starts to beat the schoolbook product. A sweep
of operand sizes, schoolbook against the planned NTT pipeline, over KoalaBear's
native-word representation.

This replaces `tests/CompPolyTests/Univariate/NTT/Benchmark.lean`, which held
the only crossover logic in the repo, ran nothing under `lake test`, was
imported by nothing, and printed its results through `#eval`.
`BENCHMARKING.md` recorded it as "the specification for a future crossover
metric"; this is that metric, so the file goes.

One group per operand size, because `workUnits` — the operand coefficient
count — must agree across a group, and the whole point of the sweep is that it
does not agree across sizes. The domain for each size is the smallest that
holds the convolution length `2k - 1`, and the plan is built outside the timed
closure, as a caller would.
-/

public section

open CompPoly

namespace CompPolyBench

/-- Time schoolbook against planned NTT multiplication at one operand size. -/
private def runCrossoverGroup (coeffs logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity)
    (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (lhsValues, gen) := (koalaBearArray coeffs false).run gen
  let (rhsValues, gen) := (koalaBearArray coeffs false).run gen
  let lhs := cpolyOfArray (koalaBearFastArray lhsValues)
  let rhs := cpolyOfArray (koalaBearFastArray rhsValues)
  let pairs := #[(lhs, rhs), (rhs, lhs)]
  let pair (i : Nat) : CPolynomial KoalaBear.Fast.Field × CPolynomial KoalaBear.Fast.Field :=
    pairs.getD (i % 2) (lhs, rhs)
  let domain := CPolynomial.NTT.KoalaBear.fastDomainOfLogN logN hlogN
  let plan := CPolynomial.NTTFast.Plan.ofDomain domain
  let checksum := checksumCPolynomial checksumKoalaBearFast
  let shape := s!"degree<{coeffs} dense lhs/rhs, two orderings"
  let schoolbook ← runTimedSpec
    { name := s!"univariate-mul-crossover-schoolbook", representation := "CPolynomial",
      method := "mul", field := "KoalaBear.Fast.Field", inputShape := shape,
      digestIterations := digestPeriod 2, workUnits := coeffs }
    preset (fun i ↦ let (p, q) := pair i; p * q) checksum
  let planned ← runTimedSpec
    { name := s!"univariate-mul-crossover-ntt", representation := "CPolynomial",
      method := "NTTFast.Plan.fastMulImpl", field := "KoalaBear.Fast.Field",
      inputShape := shape, digestIterations := digestPeriod 2, workUnits := coeffs }
    preset (fun i ↦ let (p, q) := pair i; CPolynomial.NTTFast.Plan.fastMulImpl plan p q)
      checksum
  pure ({ groupKey := s!"univariate-mul-crossover-{coeffs}",
          title := s!"Schoolbook against NTT multiplication, degree<{coeffs}",
          records := #[schoolbook, planned] }, gen)

/-- Registry entries for the crossover sweep. -/
def crossoverTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"univariate-mul-crossover-4", "Schoolbook against NTT multiplication, degree<4"⟩
    (runCrossoverGroup 4 3 (by decide)),
  BenchTask.fromGroupRunner
    ⟨"univariate-mul-crossover-8", "Schoolbook against NTT multiplication, degree<8"⟩
    (runCrossoverGroup 8 4 (by decide)),
  BenchTask.fromGroupRunner
    ⟨"univariate-mul-crossover-16", "Schoolbook against NTT multiplication, degree<16"⟩
    (runCrossoverGroup 16 5 (by decide)),
  BenchTask.fromGroupRunner
    ⟨"univariate-mul-crossover-32", "Schoolbook against NTT multiplication, degree<32"⟩
    (runCrossoverGroup 32 6 (by decide)),
  BenchTask.fromGroupRunner
    ⟨"univariate-mul-crossover-64", "Schoolbook against NTT multiplication, degree<64"⟩
    (runCrossoverGroup 64 7 (by decide)),
  BenchTask.fromGroupRunner
    ⟨"univariate-mul-crossover-128", "Schoolbook against NTT multiplication, degree<128"⟩
    (runCrossoverGroup 128 8 (by decide)),
  BenchTask.fromGroupRunner
    ⟨"univariate-mul-crossover-256", "Schoolbook against NTT multiplication, degree<256"⟩
    (runCrossoverGroup 256 9 (by decide)),
  BenchTask.fromGroupRunner
    ⟨"univariate-mul-crossover-512", "Schoolbook against NTT multiplication, degree<512"⟩
    (runCrossoverGroup 512 10 (by decide)),
  BenchTask.fromGroupRunner
    ⟨"univariate-mul-crossover-1024", "Schoolbook against NTT multiplication, degree<1024"⟩
    (runCrossoverGroup 1024 11 (by decide))
]

end CompPolyBench
