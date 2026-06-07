/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Common
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.Binary
import CompPoly.Fields.Binary.GF2_32
import CompPoly.Fields.Binary.GF2_48
import CompPoly.Fields.Binary.GF2_64
import CompPoly.Fields.Binary.GF2_72
import CompPoly.Univariate.Roots

/-!
# Binary-Field Root Benchmarks

Univariate root-search benchmarks over selected executable binary-extension
fields, comparing Shoup trace splitting, smooth cyclic splitting, and
trace-aware Las Vegas splitting.
-/

open CompPoly

namespace CompPolyBench

private def binaryRootGF32PowerCount : Nat :=
  4

private def binaryRootGF48PowerCount : Nat :=
  8

private def binaryRootGF64PowerCount : Nat :=
  3

private def binaryRootGF72PowerCount : Nat :=
  3

private def binaryRootGF32DeepCollisionStride : Nat :=
  255

private def binaryRootGF64DeepCollisionStride : Nat :=
  65535

private def binaryRootWorkloadDegree (powerCount : Nat) : Nat :=
  powerCount + 3

private def binaryRootWorkloadDistinctRoots (powerCount : Nat) : Nat :=
  powerCount + 2

private def binaryRootWorkloadShape (powerCount : Nat) (rootPattern : String) : String :=
  s!"degree={binaryRootWorkloadDegree powerCount}, " ++
    s!"{binaryRootWorkloadDistinctRoots powerCount} distinct roots, " ++
      "zero root, repeated primitive-generator root, " ++ rootPattern

private def binaryRootConsecutiveWorkloadShape (powerCount : Nat) : String :=
  binaryRootWorkloadShape powerCount
    s!"nonzero exponents 1 through {powerCount + 1}"

private def binaryRootStrideCollisionWorkloadShape (powerCount stride : Nat) : String :=
  binaryRootWorkloadShape powerCount s!"nonzero exponents congruent to 1 mod {stride}"

/-
Each binary-root workload uses a field-specific default input shape for every
preset. Presets only scale measured iteration counts. Counts are row-specific
where needed so total row runtimes stay closer within each field group.
-/
private def binaryRootShoupMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 1 1 1

private def binaryRootLasVegasMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 1 1 1

private def binaryRootGF48SmoothMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 500 70 1

private def binaryRootGF72SmoothMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 600 90 1

private def binaryRootGF32HardShoupMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 420 60 12

private def binaryRootGF32HardSmoothMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 315 45 9

private def binaryRootGF64HardShoupMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 35 5 1

private def binaryRootGF64HardSmoothMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 21 3 1

private def primitivePowerRoots {F : Type*} [Pow F Nat] (firstExponent count : Nat)
    (generator : F) :
    List F :=
  (List.range count).map fun i ↦ generator ^ (firstExponent + i)

private def primitiveStrideRoots {F : Type*} [Pow F Nat]
    (firstExponent stride count : Nat) (generator : F) :
    List F :=
  (List.range count).map fun i ↦ generator ^ (firstExponent + stride * i)

private def productOfLinearRoots {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (roots : List F) : CPolynomial F :=
  roots.foldl
    (fun p root ↦ p * CPolynomial.linearFactor root)
    (CPolynomial.C (1 : F))

private def binaryRootConsecutiveWorkloadPolynomial {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (powerCount : Nat) (generator : F) :
    CPolynomial F :=
  let powers := primitivePowerRoots 2 powerCount generator
  productOfLinearRoots ((0 : F) :: generator :: generator :: powers)

private def binaryRootStrideCollisionWorkloadPolynomial {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (powerCount stride : Nat) (generator : F) :
    CPolynomial F :=
  let powers := primitiveStrideRoots (stride + 1) stride powerCount generator
  productOfLinearRoots ((0 : F) :: generator :: generator :: powers)

private def insertSortedNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
      if x ≤ y then
        x :: y :: ys
      else
        y :: insertSortedNat x ys

private def sortNatList (xs : List Nat) : List Nat :=
  xs.foldr insertSortedNat []

private def checksumNatList (xs : List Nat) : Nat :=
  xs.foldl (fun acc x ↦ mixChecksum acc x) 0

private def checksumNormalizedRoots {F : Type*} (toNat : F → Nat) (roots : Array F) : Nat :=
  checksumNatList (sortNatList (roots.toList.map toNat))

private def binaryRootLasVegasInputShape (inputShape : String)
    (cfg : CPolynomial.Roots.FiniteField.LasVegasConfig) : String :=
  inputShape ++ s!", cutoff={cfg.cutoff}, deterministic probes=Shoup trace-basis cycle, seed=none"

private def rootsWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (ctx : CPolynomial.Roots.FiniteField.FiniteFieldContext F)
    (splitter : CPolynomial.Roots.FiniteField.LinearFactorProductSplitter F)
    (p : CPolynomial F) : Array F :=
  CPolynomial.Roots.FiniteField.rootsInFiniteFieldWith
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive ctx splitter p

private def shoupSplitter {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (ctx : CPolynomial.Roots.FiniteField.SmallPrimeTraceContext F) :
    CPolynomial.Roots.FiniteField.LinearFactorProductSplitter F :=
  CPolynomial.Roots.FiniteField.shoupLinearFactorProductSplitterWith
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive ctx

private def smoothSplitter {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (ctx : CPolynomial.Roots.FiniteField.SmoothCyclicRootContext F) :
    CPolynomial.Roots.FiniteField.LinearFactorProductSplitter F :=
  CPolynomial.Roots.FiniteField.smoothLinearFactorProductSplitterWith
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive ctx

private def lasVegasTraceSplitter {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (finiteCtx : CPolynomial.Roots.FiniteField.FiniteFieldContext F)
    (enumeration : CPolynomial.Roots.FiniteField.FieldEnumeration F)
    (traceCtx : CPolynomial.Roots.FiniteField.SmallPrimeTraceContext F)
    (cfg : CPolynomial.Roots.FiniteField.LasVegasConfig)
    (probes : CPolynomial.Roots.FiniteField.ProbeFamily F) :
    CPolynomial.Roots.FiniteField.LinearFactorProductSplitter F :=
  CPolynomial.Roots.FiniteField.lasVegasLinearFactorProductSplitterWithTrace
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
    finiteCtx enumeration traceCtx cfg probes

private def runBinaryRootGroup {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (groupKey title fieldLabel : String) (toNat : F → Nat)
    (workloadPolynomial : F → CPolynomial F) (inputShape : String)
    (finiteCtx : CPolynomial.Roots.FiniteField.FiniteFieldContext F)
    (traceCtx : CPolynomial.Roots.FiniteField.SmallPrimeTraceContext F)
    (enumeration : CPolynomial.Roots.FiniteField.FieldEnumeration F)
    (lasVegasCfg : CPolynomial.Roots.FiniteField.LasVegasConfig)
    (lasVegasProbes : CPolynomial.Roots.FiniteField.ProbeFamily F)
    (smoothHornerCtx smoothSubproductCtx :
      CPolynomial.Roots.FiniteField.SmoothCyclicRootContext F)
    (smoothMeasuredIterations : BenchPreset → Nat)
    (generator : F) (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let p := workloadPolynomial generator
  let warmup := preset.selectNat 1 0 0
  let shoupMeasured := binaryRootShoupMeasuredIterations preset
  let lasVegasMeasured := binaryRootLasVegasMeasuredIterations preset
  let smoothHornerMeasured := smoothMeasuredIterations preset
  let smoothSubproductMeasured := smoothMeasuredIterations preset
  let checksumIterations := groupChecksumIterations shoupMeasured [
    smoothHornerMeasured, smoothSubproductMeasured, lasVegasMeasured
  ]
  let shoupRow ← runTimed
    (groupKey ++ "-shoup") "CPolynomial"
    "binary roots, Shoup trace splitter"
    fieldLabel inputShape preset warmup shoupMeasured
    (fun _ ↦ rootsWith finiteCtx (shoupSplitter traceCtx) p)
    (checksumNormalizedRoots toNat) checksumIterations
  let smoothHornerRow ← runTimed
    (groupKey ++ "-smooth-horner") "CPolynomial"
    "binary roots, smooth cyclic splitter, Horner leaf evaluation"
    fieldLabel inputShape preset warmup smoothHornerMeasured
    (fun _ ↦ rootsWith finiteCtx (smoothSplitter smoothHornerCtx) p)
    (checksumNormalizedRoots toNat) checksumIterations
  let smoothSubproductRow ← runTimed
    (groupKey ++ "-smooth-subproduct") "CPolynomial"
    "binary roots, smooth cyclic splitter, subproduct leaf evaluation"
    fieldLabel inputShape preset warmup smoothSubproductMeasured
    (fun _ ↦ rootsWith finiteCtx (smoothSplitter smoothSubproductCtx) p)
    (checksumNormalizedRoots toNat) checksumIterations
  let lasVegasTraceRow ← runTimed
    (groupKey ++ "-las-vegas-trace") "CPolynomial"
    (s!"binary roots, Las Vegas trace splitter, cutoff={lasVegasCfg.cutoff}, " ++
      "deterministic Shoup trace-basis probes")
    fieldLabel (binaryRootLasVegasInputShape inputShape lasVegasCfg)
    preset warmup lasVegasMeasured
    (fun _ ↦
      rootsWith finiteCtx
        (lasVegasTraceSplitter finiteCtx enumeration traceCtx lasVegasCfg lasVegasProbes) p)
    (checksumNormalizedRoots toNat) checksumIterations
  pure ({
    groupKey := groupKey
    title := title
    records := #[shoupRow, smoothHornerRow, smoothSubproductRow, lasVegasTraceRow]
  }, gen)

private def runBinaryRootSubproductComparisonGroup {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (groupKey title fieldLabel : String) (toNat : F → Nat)
    (workloadPolynomial : F → CPolynomial F) (inputShape : String)
    (finiteCtx : CPolynomial.Roots.FiniteField.FiniteFieldContext F)
    (traceCtx : CPolynomial.Roots.FiniteField.SmallPrimeTraceContext F)
    (enumeration : CPolynomial.Roots.FiniteField.FieldEnumeration F)
    (lasVegasCfg : CPolynomial.Roots.FiniteField.LasVegasConfig)
    (lasVegasProbes : CPolynomial.Roots.FiniteField.ProbeFamily F)
    (smoothSubproductCtx :
      CPolynomial.Roots.FiniteField.SmoothCyclicRootContext F)
    (shoupMeasuredIterations smoothMeasuredIterations : BenchPreset → Nat)
    (generator : F) (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let p := workloadPolynomial generator
  let warmup := preset.selectNat 1 0 0
  let shoupMeasured := shoupMeasuredIterations preset
  let lasVegasMeasured := binaryRootLasVegasMeasuredIterations preset
  let smoothSubproductMeasured := smoothMeasuredIterations preset
  let checksumIterations := groupChecksumIterations shoupMeasured [
    smoothSubproductMeasured, lasVegasMeasured
  ]
  let shoupRow ← runTimed
    (groupKey ++ "-shoup") "CPolynomial"
    "binary roots, Shoup trace splitter"
    fieldLabel inputShape preset warmup shoupMeasured
    (fun _ ↦ rootsWith finiteCtx (shoupSplitter traceCtx) p)
    (checksumNormalizedRoots toNat) checksumIterations
  let smoothSubproductRow ← runTimed
    (groupKey ++ "-smooth-subproduct") "CPolynomial"
    "binary roots, smooth cyclic splitter, subproduct leaf evaluation"
    fieldLabel inputShape preset warmup smoothSubproductMeasured
    (fun _ ↦ rootsWith finiteCtx (smoothSplitter smoothSubproductCtx) p)
    (checksumNormalizedRoots toNat) checksumIterations
  let lasVegasTraceRow ← runTimed
    (groupKey ++ "-las-vegas-trace") "CPolynomial"
    (s!"binary roots, Las Vegas trace splitter, cutoff={lasVegasCfg.cutoff}, " ++
      "deterministic Shoup trace-basis probes")
    fieldLabel (binaryRootLasVegasInputShape inputShape lasVegasCfg)
    preset warmup lasVegasMeasured
    (fun _ ↦
      rootsWith finiteCtx
        (lasVegasTraceSplitter finiteCtx enumeration traceCtx lasVegasCfg lasVegasProbes) p)
    (checksumNormalizedRoots toNat) checksumIterations
  pure ({
    groupKey := groupKey
    title := title
    records := #[shoupRow, smoothSubproductRow, lasVegasTraceRow]
  }, gen)

/-- Benchmark group metadata for binary-field root finding. -/
def univariateBinaryRootGroupInfos : List BenchGroupInfo := [
  ⟨"univariate-roots-binary-gf2-48",
    "Univariate binary-field root finding (GF(2^48))"⟩,
  ⟨"univariate-roots-binary-gf2-72",
    "Univariate binary-field root finding (GF(2^72))"⟩,
  ⟨"univariate-roots-binary-gf2-32",
    "Univariate binary-field root finding (GF(2^32))"⟩,
  ⟨"univariate-roots-binary-gf2-64",
    "Univariate binary-field root finding (GF(2^64))"⟩
]

private def runGF32BinaryRoots (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) :=
  runBinaryRootSubproductComparisonGroup "univariate-roots-binary-gf2-32"
    "Univariate binary-field root finding (GF(2^32))"
    "GF(2^32)" GF2_32.ConcreteField.toNat
    (binaryRootStrideCollisionWorkloadPolynomial
      binaryRootGF32PowerCount binaryRootGF32DeepCollisionStride)
    (binaryRootStrideCollisionWorkloadShape
      binaryRootGF32PowerCount binaryRootGF32DeepCollisionStride)
    GF2_32.finiteFieldContext GF2_32.shoupTraceContext
    GuruswamiSudan.Binary.gf2_32FieldEnumeration
    GuruswamiSudan.Binary.gf2_32LasVegasConfig
    GuruswamiSudan.Binary.gf2_32LasVegasProbeFamily
    GF2_32.smoothSubproductRootContext
    binaryRootGF32HardShoupMeasuredIterations
    binaryRootGF32HardSmoothMeasuredIterations
    GF2_32.primitiveRoot preset gen

private def runGF48BinaryRoots (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) :=
  runBinaryRootGroup "univariate-roots-binary-gf2-48"
    "Univariate binary-field root finding (GF(2^48))"
    "GF(2^48)" GF2_48.ConcreteField.toNat
    (binaryRootConsecutiveWorkloadPolynomial binaryRootGF48PowerCount)
    (binaryRootConsecutiveWorkloadShape binaryRootGF48PowerCount)
    GF2_48.finiteFieldContext GF2_48.shoupTraceContext
    GuruswamiSudan.Binary.gf2_48FieldEnumeration
    GuruswamiSudan.Binary.gf2_48LasVegasConfig
    GuruswamiSudan.Binary.gf2_48LasVegasProbeFamily
    GF2_48.smoothHornerRootContext GF2_48.smoothSubproductRootContext
    binaryRootGF48SmoothMeasuredIterations GF2_48.primitiveRoot preset gen

private def runGF72BinaryRoots (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) :=
  runBinaryRootGroup "univariate-roots-binary-gf2-72"
    "Univariate binary-field root finding (GF(2^72))"
    "GF(2^72)" GF2_72.ConcreteField.toNat
    (binaryRootConsecutiveWorkloadPolynomial binaryRootGF72PowerCount)
    (binaryRootConsecutiveWorkloadShape binaryRootGF72PowerCount)
    GF2_72.finiteFieldContext GF2_72.shoupTraceContext
    GuruswamiSudan.Binary.gf2_72FieldEnumeration
    GuruswamiSudan.Binary.gf2_72LasVegasConfig
    GuruswamiSudan.Binary.gf2_72LasVegasProbeFamily
    GF2_72.smoothHornerRootContext GF2_72.smoothSubproductRootContext
    binaryRootGF72SmoothMeasuredIterations GF2_72.primitiveRoot preset gen

private def runGF64BinaryRoots (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) :=
  runBinaryRootSubproductComparisonGroup "univariate-roots-binary-gf2-64"
    "Univariate binary-field root finding (GF(2^64))"
    "GF(2^64)" GF2_64.ConcreteField.toNat
    (binaryRootStrideCollisionWorkloadPolynomial
      binaryRootGF64PowerCount binaryRootGF64DeepCollisionStride)
    (binaryRootStrideCollisionWorkloadShape
      binaryRootGF64PowerCount binaryRootGF64DeepCollisionStride)
    GF2_64.finiteFieldContext GF2_64.shoupTraceContext
    GuruswamiSudan.Binary.gf2_64FieldEnumeration
    GuruswamiSudan.Binary.gf2_64LasVegasConfig
    GuruswamiSudan.Binary.gf2_64LasVegasProbeFamily
    GF2_64.smoothSubproductRootContext
    binaryRootGF64HardShoupMeasuredIterations
    binaryRootGF64HardSmoothMeasuredIterations
    GF2_64.primitiveRoot preset gen

/-- Runnable binary-field root benchmark tasks. -/
def univariateBinaryRootTasks : List BenchTask := [
  BenchTask.fromGroupRunner (univariateBinaryRootGroupInfos.getD 0
    ⟨"univariate-roots-binary-gf2-48", ""⟩)
    runGF48BinaryRoots,
  BenchTask.fromGroupRunner (univariateBinaryRootGroupInfos.getD 1
    ⟨"univariate-roots-binary-gf2-72", ""⟩)
    runGF72BinaryRoots,
  BenchTask.fromGroupRunner (univariateBinaryRootGroupInfos.getD 2
    ⟨"univariate-roots-binary-gf2-32", ""⟩)
    runGF32BinaryRoots,
  BenchTask.fromGroupRunner (univariateBinaryRootGroupInfos.getD 3
    ⟨"univariate-roots-binary-gf2-64", ""⟩)
    runGF64BinaryRoots
]

end CompPolyBench
