/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Univariate.Common
public import CompPoly.Univariate.BatchEval.Interpolation
public import CompPoly.Univariate.NTT.Barycentric
public import CompPoly.Univariate.NTTFast.Coset
public import CompPoly.Univariate.ReedSolomon.GaoNTT

/-!
# Interpolation benchmarks

Every interpolation path the library proves equal to Lagrange's formula, on one input:
values on the nodes `ωⁱ` of a KoalaBear NTT domain. Because the nodes are the same for every
row, every row returns the same polynomial, and the group digest checks that equality rather
than two implementations of a shared spec.

* `univariate-interp-koalabear-l6` carries the definitional `CLagrange.interpolatePow`,
  which is cubic, beside the subproduct tree (naive and NTT contexts), `NTT.interpolate`,
  and `NTTFast.Plan.interpolate`. The cubic row is why the size stops at `2^6`.
* `univariate-interp-koalabear-l12` drops the cubic and the naive-context rows.
* `univariate-interp-coset-koalabear-l12` times coset interpolation, per-coefficient
  powers against the plan's cached ones.
* `univariate-barycentric-koalabear-l8` times one off-node query, with the domain built by
  the generic `BarycentricDomain.mk'` (`O(n²)` weights) and by the closed form
  `NTT.Domain.barycentric`.
* `rs-gao-decode-koalabear-l6` times Gao's decoder, definitional against `decodeNTT` and
  `decodePlan`, on a word with `(n - k) / 2` errors.

`workUnits` is `n` for the interpolation rows and `1` for the others.
-/

public section

open CompPoly

namespace CompPolyBench

private abbrev KF := KoalaBear.Fast.Field

private def polyChecksum (p : CPolynomial KF) : Nat :=
  checksumCPolynomial checksumKoalaBearFast p

private def polySink (p : CPolynomial KF) : UInt64 :=
  arraySampleSink (fun x ↦ natSink (checksumKoalaBearFast x)) p.val

/-- Two value vectors of length `2 ^ logN`, drawn at run time. -/
private def drawValues (D : CPolynomial.NTT.Domain KF) (gen : StdGen) :
    Array (Vector KF D.n) × StdGen :=
  let (a, gen) := (koalaBearArray D.n false).run gen
  let (b, gen) := (koalaBearArray D.n false).run gen
  let toVec (xs : Array KoalaBear.Field) : Vector KF D.n :=
    Vector.ofFn fun i ↦ KoalaBear.Fast.ofField (xs.getD i.1 0)
  (#[toVec a, toVec b], gen)

/-- Time every interpolation path at one domain size. -/
private def runInterpGroup (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity)
    (withQuadratic : Bool) (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let D := CPolynomial.NTT.KoalaBear.fastDomainOfLogN logN hlogN
  let plan := CPolynomial.NTTFast.Plan.ofDomain D
  let nodes : Array KF := Array.ofFn D.node
  let (pool, gen) := drawValues D gen
  let values (i : Nat) : Vector KF D.n := pool.getD (i % 2) (Vector.replicate D.n 0)
  let shape := s!"n = 2^{logN}, nodes ωⁱ, two value vectors"
  let spec (name method : String) : BenchSpec :=
    { name := name, representation := "CPolynomial", method := method, field := "koalabear",
      inputShape := shape, digestIterations := digestPeriod 2, workUnits := D.n }
  let nttMul : CPolynomial.MulContext KF :=
    CPolynomial.MulContext.nttFast koalaBearFastBestDomainForLength?
  let nttMod : CPolynomial.ModContext KF :=
    CPolynomial.ModContext.reversalNttFast koalaBearFastBestDomainForLength?
  let subproductNtt ← runTimedSpec (spec "interp-subproduct-ntt" "subproduct tree, NTTFast")
    preset (fun i ↦ CPolynomial.interpolateSubproduct nttMul nttMod nodes (values i).toArray)
    polyChecksum (sink := polySink)
  let ntt ← runTimedSpec (spec "interp-ntt" "NTT.interpolate") preset
    (fun i ↦ CPolynomial.NTT.interpolate D (values i)) polyChecksum (sink := polySink)
  let planned ← runTimedSpec (spec "interp-ntt-plan" "NTTFast.Plan.interpolate") preset
    (fun i ↦ CPolynomial.NTTFast.Plan.interpolate plan (values i)) polyChecksum
    (sink := polySink)
  let records ← if withQuadratic then do
      let lagrange ← runTimedSpec (spec "interp-lagrange" "CLagrange.interpolatePow") preset
        (fun i ↦ CPolynomial.CLagrange.interpolatePow D.omega (values i)) polyChecksum
        (sink := polySink)
      let subproductNaive ← runTimedSpec
        (spec "interp-subproduct-naive" "subproduct tree, naive") preset
        (fun i ↦ CPolynomial.interpolateSubproduct CPolynomial.MulContext.naive
          CPolynomial.ModContext.naive nodes (values i).toArray) polyChecksum
        (sink := polySink)
      pure #[lagrange, subproductNaive, subproductNtt, ntt, planned]
    else pure #[subproductNtt, ntt, planned]
  pure ({ groupKey := s!"univariate-interp-koalabear-l{logN}",
          title := s!"Interpolation on an NTT domain, KoalaBear, n = 2^{logN}",
          records := records }, gen)

/-- Time coset interpolation with per-coefficient powers against cached ones. -/
private def runCosetGroup (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity)
    (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let D := CPolynomial.NTT.KoalaBear.fastDomainOfLogN logN hlogN
  let shift : KF := KoalaBear.Fast.ofField 3
  let cosetPlan := CPolynomial.NTTFast.CosetPlan.ofPlan (CPolynomial.NTTFast.Plan.ofDomain D) shift
  let (pool, gen) := drawValues D gen
  let values (i : Nat) : Vector KF D.n := pool.getD (i % 2) (Vector.replicate D.n 0)
  let shape := s!"n = 2^{logN}, coset 3·⟨ω⟩, two value vectors"
  let spec (name method : String) : BenchSpec :=
    { name := name, representation := "CPolynomial", method := method, field := "koalabear",
      inputShape := shape, digestIterations := digestPeriod 2, workUnits := D.n }
  let unplanned ← runTimedSpec (spec "interp-coset" "NTT.Coset.interpolate") preset
    (fun i ↦ CPolynomial.NTT.Coset.interpolate D shift (values i)) polyChecksum
    (sink := polySink)
  let planned ← runTimedSpec (spec "interp-coset-plan" "NTTFast.CosetPlan.interpolate") preset
    (fun i ↦ CPolynomial.NTTFast.CosetPlan.interpolate cosetPlan (values i)) polyChecksum
    (sink := polySink)
  pure ({ groupKey := s!"univariate-interp-coset-koalabear-l{logN}",
          title := s!"Coset interpolation, KoalaBear, n = 2^{logN}",
          records := #[unplanned, planned] }, gen)

/-- Time one off-node barycentric query, building the domain inside the body. -/
private def runBarycentricGroup (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity)
    (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let D := CPolynomial.NTT.KoalaBear.fastDomainOfLogN logN hlogN
  let (pool, gen) := drawValues D gen
  let (points, gen) := (koalaBearArray 2 false).run gen
  let values (i : Nat) : Vector KF D.n := pool.getD (i % 2) (Vector.replicate D.n 0)
  let point (i : Nat) : KF := KoalaBear.Fast.ofField (points.getD (i % 2) 0)
  let shape := s!"n = 2^{logN}, one off-node query, domain built per query"
  let spec (name method : String) : BenchSpec :=
    { name := name, representation := "BarycentricDomain", method := method,
      field := "koalabear", inputShape := shape, digestIterations := digestPeriod 2 }
  let generic ← runTimedSpec (spec "barycentric-mk" "BarycentricDomain.mk'") preset
    (fun i ↦ (CPolynomial.CLagrange.BarycentricDomain.mk' D.node D.node_injective).eval
      (values i).get (point i)) checksumKoalaBearFast
  let closed ← runTimedSpec (spec "barycentric-ntt" "NTT.Domain.barycentric") preset
    (fun i ↦ D.barycentric.eval (values i).get (point i)) checksumKoalaBearFast
  pure ({ groupKey := s!"univariate-barycentric-koalabear-l{logN}",
          title := s!"Barycentric evaluation on an NTT domain, KoalaBear, n = 2^{logN}",
          records := #[generic, closed] }, gen)

/-- Time Gao's decoder at one size, rate one half, with `(n - k) / 2` errors. -/
private def runGaoGroup (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity)
    (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let D := CPolynomial.NTT.KoalaBear.fastDomainOfLogN logN hlogN
  let plan := CPolynomial.NTTFast.Plan.ofDomain D
  let k := D.n / 2
  let errors := (D.n - k) / 2
  let (msgA, gen) := (koalaBearArray k false).run gen
  let (msgB, gen) := (koalaBearArray k false).run gen
  let received (msg : Array KoalaBear.Field) : Vector KF D.n :=
    let m : Vector KF k := Vector.ofFn fun i ↦ KoalaBear.Fast.ofField (msg.getD i.1 0)
    let c := (ReedSolomon.encode (ReedSolomon.nttDomainToRS D) m).cast
      (ReedSolomon.nttDomainToRS_n D)
    Vector.ofFn fun i ↦ if i.1 < errors then c.get i + 1 else c.get i
  let pool := #[received msgA, received msgB]
  let word (i : Nat) : Vector KF D.n := pool.getD (i % 2) (Vector.replicate D.n 0)
  let shape := s!"n = 2^{logN}, k = n/2, {errors} errors"
  let spec (name method : String) : BenchSpec :=
    { name := name, representation := "Option CPolynomial", method := method,
      field := "koalabear", inputShape := shape, digestIterations := digestPeriod 2 }
  let checksum (r : Option (CPolynomial KF)) : Nat :=
    match r with
    | none => 0
    | some p => polyChecksum p + 1
  let definitional ← runTimedSpec (spec "gao-decode" "decode (Lagrange interpolant)") preset
    (fun i ↦ ReedSolomon.Gao.decode k (ReedSolomon.nttDomainToRS D)
      (ReedSolomon.Gao.castToRS D (word i))) checksum
  let ntt ← runTimedSpec (spec "gao-decode-ntt" "decodeNTT") preset
    (fun i ↦ ReedSolomon.Gao.decodeNTT k D (word i)) checksum
  let planned ← runTimedSpec (spec "gao-decode-plan" "decodePlan") preset
    (fun i ↦ ReedSolomon.Gao.decodePlan k plan (word i)) checksum
  pure ({ groupKey := s!"rs-gao-decode-koalabear-l{logN}",
          title := s!"Gao decoding, KoalaBear, n = 2^{logN}",
          records := #[definitional, ntt, planned] }, gen)

/-- Registry entries for the interpolation benchmarks. -/
def interpolationTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"univariate-interp-koalabear-l6", "Interpolation on an NTT domain, KoalaBear, n = 2^6"⟩
    (runInterpGroup 6 (by decide) true),
  BenchTask.fromGroupRunner
    ⟨"univariate-interp-koalabear-l12", "Interpolation on an NTT domain, KoalaBear, n = 2^12"⟩
    (runInterpGroup 12 (by decide) false),
  BenchTask.fromGroupRunner
    ⟨"univariate-interp-coset-koalabear-l12", "Coset interpolation, KoalaBear, n = 2^12"⟩
    (runCosetGroup 12 (by decide)),
  BenchTask.fromGroupRunner
    ⟨"univariate-barycentric-koalabear-l8",
      "Barycentric evaluation on an NTT domain, KoalaBear, n = 2^8"⟩
    (runBarycentricGroup 8 (by decide)),
  BenchTask.fromGroupRunner
    ⟨"rs-gao-decode-koalabear-l6", "Gao decoding, KoalaBear, n = 2^6"⟩
    (runGaoGroup 6 (by decide))
]

end CompPolyBench
