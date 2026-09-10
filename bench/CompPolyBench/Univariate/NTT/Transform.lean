/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Univariate.Common
public import CompPoly.Univariate.NTT.Forward
public import CompPoly.Univariate.NTT.Inverse
public import CompPoly.Univariate.NTTFast.Plan

/-!
# Multiplicative NTT benchmarks

The forward and inverse transforms on their own, swept over size, rather than
buried inside a multiplication. `BENCHMARKING.md` §13 names the multiplicative
NTT as one of the operations to measure against Plonky3, and until now the only
way to see it here was as one term of `univariate-mul-*`.

Two implementations per direction, cross-checked by the group digest:

* the reference radix-2 transform, `NTT.Forward.forwardImpl` and
  `NTT.Inverse.inverseImpl`;
* the planned radix-4 transform, `NTTFast.Plan.forwardImpl` and
  `NTTFast.Plan.inverseImpl`, over a `Plan` built outside the timed closure.

Every body reads its input from a two-entry pool indexed by the iteration
counter. That is not decoration. The first version of this file precomputed
`spectrum` with the very expression the forward reference row then timed, and
the compiler recognised the two as the same: the row reported 6 ns for a
`2 ^ 12` transform and 1.6 million iterations per sample, at every size
identically. A body that varies with `i` can be neither shared with a value
computed outside the loop nor hoisted out of it.

`workUnits` is `n / 2 * log n`, the radix-2 butterfly count. It is a property
of the *problem*, not of the implementation: giving the radix-4 row its own
smaller count would divide away exactly the algorithmic advantage the group
exists to show.

## Bit reversal, and where it is allowed to appear

`Plan.forwardImpl` returns its output bit-reversed relative to the reference
(`NTTFast/Correctness/Pipeline.lean:29`), and `Plan.inverseImpl` expects its
input that way. Neither permutation may enter the timed region: an
`Array.ofFn` of size `n` inside the body would make the fast row look slower,
a failure in the direction that reads as an honest result.

So the forward group puts the permutation in the planned row's **checksum**,
which `runTimedSpec` uses only in the untimed pass, and gives that row an
explicit `sink` so the default does not drag the permuting checksum into the
measurement. The inverse group instead permutes the planned row's **input**
once, before timing.

The permutation is defined here rather than imported from
`NTT.Transform.bitRevPermute`, because the reference forward transform is
built from that same function: importing it would let a single wrong
`bitRevNat` produce two compensating errors and a group that agrees on a wrong
digest.
-/

public section

open CompPoly

namespace CompPolyBench

/-- Bit-reverse an index of `bits` bits. A local definition on purpose; see above. -/
private def benchBitRev : Nat → Nat → Nat
  | 0, _ => 0
  | bits + 1, i => ((i &&& 1) <<< bits) ||| benchBitRev bits (i >>> 1)

/-- Apply the bit-reversal permutation to an array of length `2 ^ bits`. -/
private def benchBitRevPermute {F : Type} (bits : Nat) (zero : F) (a : Array F) : Array F :=
  Array.ofFn (n := 2 ^ bits) fun i ↦ a.getD (benchBitRev bits i.1) zero

/-- Radix-2 butterflies in a transform of size `2 ^ logN`. -/
private def butterflyCount (logN : Nat) : Nat := 2 ^ logN / 2 * logN

/-- Largest size at which the reference transform still earns a row.

The reference radix-2 transform costs about 100 ns per butterfly against the
plan's 3.5 ns, so one reference inverse is 2.6 ms at `2 ^ 12` and 53 ms at
`2 ^ 16` — past the sample budget, and the suite's own guidance is that no
ratio may be read off an `n = 1` row. Above this the groups carry the planned
rows alone, and the cross-check lives at the sizes below. -/
def referenceLogNCap : Nat := 12

/-- Time the forward and inverse transforms at one field and one size.

`coeffs` holds two independently drawn inputs of `2 ^ logN` elements each; see
the note above on why the bodies index a pool rather than closing over one. -/
@[specialize] private def runTransformGroup {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (groupKey title fieldName : String) (logN : Nat)
    (domain : CPolynomial.NTT.Domain F) (coeffsA coeffsB : Array F) (checksum : F → Nat)
    (sink : F → UInt64) (preset : BenchPreset) : IO BenchGroup := do
  let plan := CPolynomial.NTTFast.Plan.ofDomain domain
  let polys : Array (CPolynomial.Raw F) := #[coeffsA, coeffsB]
  let spectra : Array (Array F) :=
    polys.map fun p ↦ CPolynomial.NTT.Forward.forwardImpl domain p
  let spectraRev : Array (Array F) := spectra.map (benchBitRevPermute logN 0)
  let poly (i : Nat) : CPolynomial.Raw F := polys.getD (i % 2) coeffsA
  let spectrum (i : Nat) : Array F := spectra.getD (i % 2) coeffsA
  let spectrumRev (i : Nat) : Array F := spectraRev.getD (i % 2) coeffsA
  let shape := s!"n = 2^{logN}, two inputs"
  let units := butterflyCount logN
  let arrayChecksum := checksumArray checksum
  let arraySink := arraySampleSink sink
  let digests := digestPeriod 2
  let forwardPlanned ← runTimedSpec
    { name := s!"ntt-forward-{fieldName}-plan", representation := "Array",
      method := "radix-4 DIF (plan)", field := fieldName, inputShape := shape,
      digestIterations := digests, workUnits := units, digestClass := "forward" }
    preset (fun i ↦ CPolynomial.NTTFast.Plan.forwardImpl plan (poly i))
    (fun a ↦ arrayChecksum (benchBitRevPermute logN 0 a)) (sink := arraySink)
  let inversePlanned ← runTimedSpec
    { name := s!"ntt-inverse-{fieldName}-plan", representation := "Array",
      method := "radix-4 DIT (plan)", field := fieldName, inputShape := shape,
      digestIterations := digests, workUnits := units, digestClass := "inverse" }
    preset (fun i ↦ CPolynomial.NTTFast.Plan.inverseImpl plan (spectrumRev i)) arrayChecksum
    (sink := arraySink)
  if logN > referenceLogNCap then
    pure { groupKey := groupKey, title := title,
           records := #[forwardPlanned, inversePlanned] }
  else
    let forwardReference ← runTimedSpec
      { name := s!"ntt-forward-{fieldName}", representation := "Array", method := "radix-2",
        field := fieldName, inputShape := shape, digestIterations := digests,
        workUnits := units, digestClass := "forward" }
      preset (fun i ↦ CPolynomial.NTT.Forward.forwardImpl domain (poly i)) arrayChecksum
      (sink := arraySink)
    let inverseReference ← runTimedSpec
      { name := s!"ntt-inverse-{fieldName}", representation := "Array", method := "radix-2",
        field := fieldName, inputShape := shape, digestIterations := digests,
        workUnits := units, digestClass := "inverse" }
      preset (fun i ↦ CPolynomial.NTT.Inverse.inverseImpl domain (spectrum i)) arrayChecksum
      (sink := arraySink)
    pure { groupKey := groupKey, title := title,
           records := #[forwardReference, forwardPlanned, inverseReference, inversePlanned] }

/-- Time the KoalaBear transforms at one size. -/
private def runKoalaBearTransform (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity)
    (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (valuesA, gen) := (koalaBearArray (2 ^ logN) false).run gen
  let (valuesB, gen) := (koalaBearArray (2 ^ logN) false).run gen
  let group ← runTransformGroup s!"ntt-koalabear-l{logN}"
    s!"Multiplicative NTT, KoalaBear, n = 2^{logN}" "koalabear" logN
    (CPolynomial.NTT.KoalaBear.fastDomainOfLogN logN hlogN)
    (koalaBearFastArray valuesA) (koalaBearFastArray valuesB)
    checksumKoalaBearFast (fun x ↦ natSink (checksumKoalaBearFast x)) preset
  pure (group, gen)

/-- Time the BabyBear transforms at one size. -/
private def runBabyBearTransform (logN : Nat) (hlogN : logN ≤ BabyBear.twoAdicity)
    (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (valuesA, gen) := (babyBearArray (2 ^ logN) false).run gen
  let (valuesB, gen) := (babyBearArray (2 ^ logN) false).run gen
  let group ← runTransformGroup s!"ntt-babybear-l{logN}"
    s!"Multiplicative NTT, BabyBear, n = 2^{logN}" "babybear" logN
    (CPolynomial.NTT.BabyBear.fastDomainOfLogN logN hlogN)
    (babyBearFastArray valuesA) (babyBearFastArray valuesB)
    checksumBabyBearFast (fun x ↦ natSink (checksumBabyBearFast x)) preset
  pure (group, gen)

/-- Time plan construction, which the transform groups deliberately hoist out.

A `Plan` is a pure value built once per domain and reused, so its cost belongs
to setup rather than to a transform — but it is `O(n)` field multiplications
building the twiddle tables, so a caller that rebuilds one per transform pays
more than the transform. That is what this group is for. -/
private def runPlanConstruction (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  -- `Plan.ofDomain d` for a literal `d` is a closed term, which Lean evaluates
  -- once and caches: the row then reports its true cost divided by the
  -- iteration count. Indexing a pool by a runtime offset keeps the body live.
  let (offsets, gen) := (randomNatArray 1 1).run gen
  let offset := offsets.getD 0 0
  let smallDomain := CPolynomial.NTT.KoalaBear.fastDomainOfLogN 12 (by decide)
  let largeDomain := CPolynomial.NTT.KoalaBear.fastDomainOfLogN 16 (by decide)
  let smallPool := #[smallDomain, smallDomain]
  let largePool := #[largeDomain, largeDomain]
  let planChecksum (P : CPolynomial.NTTFast.Plan KoalaBear.Fast.Field) : Nat :=
    checksumArray (checksumArray checksumKoalaBearFast) P.twiddles
  let planSink (P : CPolynomial.NTTFast.Plan KoalaBear.Fast.Field) : UInt64 :=
    arraySampleSink (arraySampleSink (fun x ↦ natSink (checksumKoalaBearFast x))) P.twiddles
  let small ← runTimedSpec
    { name := "ntt-plan-koalabear", representation := "Plan", method := "ofDomain",
      field := "koalabear", inputShape := "n = 2^12", digestIterations := digestPeriod 2,
      workUnits := 1, digestClass := "l12" }
    preset
    (fun i ↦ CPolynomial.NTTFast.Plan.ofDomain (smallPool.getD ((i + offset) % 2) smallDomain))
    planChecksum (sink := planSink)
  let large ← runTimedSpec
    { name := "ntt-plan-koalabear", representation := "Plan", method := "ofDomain",
      field := "koalabear", inputShape := "n = 2^16", digestIterations := digestPeriod 2,
      workUnits := 1, digestClass := "l16" }
    preset
    (fun i ↦ CPolynomial.NTTFast.Plan.ofDomain (largePool.getD ((i + offset) % 2) largeDomain))
    planChecksum (sink := planSink)
  pure ({ groupKey := "ntt-plan-koalabear", title := "NTT plan construction (KoalaBear)",
          records := #[small, large] }, gen)

/-- Registry entries for the standalone transform benchmarks. -/
def nttTransformTasks : List BenchTask := [
  BenchTask.fromGroupRunner ⟨"ntt-koalabear-l8", "Multiplicative NTT, KoalaBear, n = 2^8"⟩
    (runKoalaBearTransform 8 (by decide)),
  BenchTask.fromGroupRunner ⟨"ntt-koalabear-l10", "Multiplicative NTT, KoalaBear, n = 2^10"⟩
    (runKoalaBearTransform 10 (by decide)),
  BenchTask.fromGroupRunner ⟨"ntt-koalabear-l12", "Multiplicative NTT, KoalaBear, n = 2^12"⟩
    (runKoalaBearTransform 12 (by decide)),
  BenchTask.fromGroupRunner ⟨"ntt-koalabear-l14", "Multiplicative NTT, KoalaBear, n = 2^14"⟩
    (runKoalaBearTransform 14 (by decide)),
  BenchTask.fromGroupRunner ⟨"ntt-koalabear-l16", "Multiplicative NTT, KoalaBear, n = 2^16"⟩
    (runKoalaBearTransform 16 (by decide)),
  BenchTask.fromGroupRunner ⟨"ntt-babybear-l8", "Multiplicative NTT, BabyBear, n = 2^8"⟩
    (runBabyBearTransform 8 (by decide)),
  BenchTask.fromGroupRunner ⟨"ntt-babybear-l10", "Multiplicative NTT, BabyBear, n = 2^10"⟩
    (runBabyBearTransform 10 (by decide)),
  BenchTask.fromGroupRunner ⟨"ntt-babybear-l12", "Multiplicative NTT, BabyBear, n = 2^12"⟩
    (runBabyBearTransform 12 (by decide)),
  BenchTask.fromGroupRunner ⟨"ntt-babybear-l14", "Multiplicative NTT, BabyBear, n = 2^14"⟩
    (runBabyBearTransform 14 (by decide)),
  BenchTask.fromGroupRunner ⟨"ntt-babybear-l16", "Multiplicative NTT, BabyBear, n = 2^16"⟩
    (runBabyBearTransform 16 (by decide)),
  BenchTask.fromGroupRunner ⟨"ntt-plan-koalabear", "NTT plan construction (KoalaBear)"⟩
    runPlanConstruction
]

end CompPolyBench
