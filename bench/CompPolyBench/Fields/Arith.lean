/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Fields.Inputs
public import CompPolyBench.Harness.Chain

/-!
# Base-field arithmetic benchmarks

`mul`, `add`, `inv` and `pow` over the four small prime fields a STARK prover
spends its time in — KoalaBear, BabyBear, Mersenne31 and Goldilocks — and
`mul` over the three eight-limb pairing scalar fields, BN254, BLS12-381 and
BLS12-377. Each group runs the canonical `ZMod` implementation beside the
verified native-word one on the same inputs, so the group digest cross-checks
the two.

## Why these are chains

A field multiplication is one or two nanoseconds and the harness's own
per-iteration cost is about 1.8 ns, so a row that performs the operation once
per timed iteration reports the harness. Every row here instead performs the
operation `chainRounds` times per iteration and divides by `workUnits`; see
`CompPolyBench.Harness.Chain` for why the chain touches no array and allocates
nothing.

The chain is seeded from an operand pool indexed by the iteration counter. That
costs one boxed array read per `chainRounds` operations — under a tenth of a
percent — and buys two things: the body genuinely depends on `i`, so it is
neither cached as a closed term nor hoisted out of the sample loop, and the
untimed digest sees a whole pool of inputs rather than one.

## Scaffolding other field groups share

`ChainRep`, `chainLatencyRow`, `chainThroughputRow`, `runBinOpGroup` and
`runUnOpGroup` are the chained-group scaffolding, and are used from the binary
tower groups as well. They live here rather than beside `Harness/Chain.lean`
because they need `runTimedSpec`, which `Harness/Chain.lean` deliberately does
not import.

## Latency and throughput

Reported separately, as Plonky3's `benchmark_mul_latency` and
`benchmark_mul_throughput` are, because they are different numbers and a prover
is bounded by different ones in different places. The latency row chains the
operation against a fixed operand, so each step waits on the last. The
throughput row runs ten independent accumulators, so the pipeline can overlap
them. `mul` and `add` carry both; `inv` and `pow` carry latency only, matching
the peer, and use a shorter chain because one operation already costs tens of
multiplications.
-/

public section

open CompPoly

namespace CompPolyBench

/-- Operand-pool size for the chained field benchmarks, and so their digest length. -/
def fieldPoolSize : Nat := 64

/-- Rounds in an inversion or exponentiation chain.

One `unrollBlock`, twenty times shorter than `chainRounds`, because a single
inversion is tens of multiplications and the canonical `ZMod` row is three
orders of magnitude slower again. Still long enough that the harness floor is
under a thousandth of the row. -/
def expChainRounds : Nat := unrollBlock

/-- Latency-chain depth for the eight-limb scalar fields.

A quarter of `chainRounds`: a 256-bit Montgomery multiply is an order of
magnitude more than a 32-bit one and the canonical row three further orders,
so the full depth would put a single iteration past the sample budget. Chosen
to be both a whole number of `unrollBlock`s and `throughputWidth` times a whole
number of `throughputUnroll`s, so the latency and throughput rows of a group
agree on `workUnits` — which the group check enforces. -/
def heavyChainRounds : Nat := 5 * unrollBlock

/-- Throughput-chain depth pairing with `heavyChainRounds`. -/
def heavyThroughputRounds : Nat := 8 * throughputUnroll

/-- Exponent used by the `pow` benchmarks.

A 31-bit exponent of Hamming weight 16, so the binary ladder performs 30
squarings and 15 multiplications on every field. The same exponent everywhere,
so the fields are comparable; nothing about it is field-specific. -/
def powExponent : Nat := 0x5A5A5A5A

/-- One representation of a field, as a chained benchmark row needs it.

The operation itself is deliberately *not* a field of this structure. It is
passed as a direct argument to the `@[specialize]` runners below, so the
compiler sees a known function at the chain's call site; through a structure
field it would be an indirect call per operation, which for a one-nanosecond
multiply is the whole measurement. -/
structure ChainRep (F : Type) where
  /-- Representation label for the report, such as `ZMod` or `UInt32`. -/
  representation : String
  /-- Carrier name for the report, such as `KoalaBear.Fast.Field`. -/
  field : String
  /-- Row-name suffix distinguishing this representation, `zmod` or `fast`. -/
  suffix : String
  /-- Nonzero operands, drawn from the group's random stream. -/
  pool : Array F
  /-- The chain's fixed second operand, and the fallback for an out-of-range read. -/
  constant : F
  /-- Digest for the untimed validation pass. -/
  checksum : F → Nat
  /-- Cheap digest for the timed region. -/
  sink : F → UInt64

/-- Replace zeros, so an inversion chain never meets the field's junk value.

`(0 : F)⁻¹` is `0` in Lean, so a pool containing zero would give an inversion
chain a fixed point and measure one input rather than the pool. -/
def nonzeroPool {F : Type} [Zero F] [One F] [DecidableEq F] (xs : Array F) : Array F :=
  xs.map fun x ↦ if x = 0 then 1 else x

/-- Input-shape label shared by every row of a chained field group. -/
def chainShape (rounds : Nat) : String :=
  s!"{fieldPoolSize} seeds, {rounds}-operation chains"

/-- Time a dependent chain of `op` over one representation. -/
@[specialize] def chainLatencyRow {F : Type} (fieldTag opTag method cls : String)
    (rounds : Nat) (rep : ChainRep F) (op : F → F) (preset : BenchPreset) : IO BenchRecord :=
  runTimedSpec
    { name := s!"{fieldTag}-{opTag}-{rep.suffix}", representation := rep.representation,
      method := method, field := rep.field, inputShape := chainShape rounds,
      digestIterations := digestPeriod fieldPoolSize, workUnits := latencyUnits rounds,
      digestClass := cls }
    preset
    (fun i ↦ chainLatency op rounds (rep.pool.getD (i % fieldPoolSize) rep.constant))
    rep.checksum (sink := rep.sink)

/-- Time ten independent chains of `op` over one representation. -/
@[specialize] def chainThroughputRow {F : Type} (fieldTag opTag method cls : String)
    (rounds : Nat) (rep : ChainRep F) (op : F → F → F) (preset : BenchPreset) : IO BenchRecord :=
  runTimedSpec
    { name := s!"{fieldTag}-{opTag}-{rep.suffix}", representation := rep.representation,
      method := method, field := rep.field, inputShape := chainShape (throughputUnitsOf rounds),
      digestIterations := digestPeriod fieldPoolSize, workUnits := throughputUnitsOf rounds,
      digestClass := cls }
    preset
    (fun i ↦
      let seed (k : Nat) : F := rep.pool.getD ((i + k) % fieldPoolSize) rep.constant
      chainThroughput op op rounds
        (seed 0) (seed 1) (seed 2) (seed 3) (seed 4)
        (seed 5) (seed 6) (seed 7) (seed 8) (seed 9))
    rep.checksum (sink := rep.sink)

/-- Time a binary field operation, both shapes, over both representations. -/
@[specialize] def runBinOpGroup {S F : Type} (groupKey title fieldTag opTag : String)
    (latencyRounds tputRounds : Nat)
    (slow : ChainRep S) (slowOp : S → S → S)
    (fast : ChainRep F) (fastOp : F → F → F)
    (preset : BenchPreset) : IO BenchGroup := do
  -- Bound to locals, not read through `slow.constant` inside the lambda. A
  -- projection there is lifted into the operation itself, so the chain pays a
  -- `lean_ctor_get` and an unbox per operation. Out-of-order execution hides
  -- that behind a long operation — KoalaBear `mul` did not move — but not
  -- behind a short one: KoalaBear `add` went from 1400 ps to 1116 ps.
  let slowConstant := slow.constant
  let fastConstant := fast.constant
  let slowLatency ← chainLatencyRow fieldTag opTag s!"{opTag} (latency)" "latency"
    latencyRounds slow (fun x ↦ slowOp x slowConstant) preset
  let fastLatency ← chainLatencyRow fieldTag opTag s!"{opTag} (latency)" "latency"
    latencyRounds fast (fun x ↦ fastOp x fastConstant) preset
  let slowThroughput ← chainThroughputRow fieldTag opTag s!"{opTag} (throughput)"
    "throughput" tputRounds slow slowOp preset
  let fastThroughput ← chainThroughputRow fieldTag opTag s!"{opTag} (throughput)"
    "throughput" tputRounds fast fastOp preset
  pure { groupKey := groupKey, title := title,
         records := #[slowLatency, fastLatency, slowThroughput, fastThroughput] }

/-- Time a unary field operation as a dependent chain over both representations.

The chained step is `op (x + constant)` rather than `op x`: iterating a bare
inversion alternates between two values, which measures one input rather than
the pool. The addition it costs is a percent of an inversion. -/
@[specialize] def runUnOpGroup {S F : Type} (groupKey title fieldTag opTag method : String)
    (slow : ChainRep S) (slowAdd : S → S → S) (slowOp : S → S)
    (fast : ChainRep F) (fastAdd : F → F → F) (fastOp : F → F)
    (preset : BenchPreset) : IO BenchGroup := do
  let slowConstant := slow.constant
  let fastConstant := fast.constant
  let slowRecord ← chainLatencyRow fieldTag opTag method "" expChainRounds slow
    (fun x ↦ slowOp (slowAdd x slowConstant)) preset
  let fastRecord ← chainLatencyRow fieldTag opTag method "" expChainRounds fast
    (fun x ↦ fastOp (fastAdd x fastConstant)) preset
  pure { groupKey := groupKey, title := title, records := #[slowRecord, fastRecord] }

/-! ## The four fields

Each field contributes a pair of `ChainRep`s drawn from one operand pool, so
the canonical and native-word rows of every group see the same inputs. The
group runners below are written out one per operation rather than generated,
because the operation has to reach `chainLatency` as a statically known
function: routed through a closure it becomes an indirect call per operation,
which for these fields is more than the operation. -/

/-- KoalaBear operands, canonical and native-word, from one pool. -/
private def koalaBearReps (gen : StdGen) :
    ChainRep KoalaBear.Field × ChainRep KoalaBear.Fast.Field × StdGen :=
  let (values, gen) := (koalaBearArray fieldPoolSize false).run gen
  let pool := nonzeroPool values
  let fastPool := koalaBearFastArray pool
  ({ representation := "ZMod", field := "KoalaBear.Field", suffix := "zmod",
     pool := pool, constant := pool.getD 0 1, checksum := checksumKoalaBear,
     sink := fun x ↦ natSink (checksumKoalaBear x) },
   { representation := "UInt32", field := "KoalaBear.Fast.Field", suffix := "fast",
     pool := fastPool, constant := fastPool.getD 0 1, checksum := checksumKoalaBearFast,
     sink := fun x ↦ natSink (checksumKoalaBearFast x) },
   gen)

/-- BabyBear operands, canonical and native-word, from one pool. -/
private def babyBearReps (gen : StdGen) :
    ChainRep BabyBear.Field × ChainRep BabyBear.Fast.Field × StdGen :=
  let (values, gen) := (babyBearArray fieldPoolSize false).run gen
  let pool := nonzeroPool values
  let fastPool := babyBearFastArray pool
  ({ representation := "ZMod", field := "BabyBear.Field", suffix := "zmod",
     pool := pool, constant := pool.getD 0 1, checksum := checksumBabyBear,
     sink := fun x ↦ natSink (checksumBabyBear x) },
   { representation := "UInt32", field := "BabyBear.Fast.Field", suffix := "fast",
     pool := fastPool, constant := fastPool.getD 0 1, checksum := checksumBabyBearFast,
     sink := fun x ↦ natSink (checksumBabyBearFast x) },
   gen)

/-- Mersenne31 operands, canonical and native-word, from one pool. -/
private def mersenne31Reps (gen : StdGen) :
    ChainRep Mersenne31.Field × ChainRep Mersenne31.Fast.Field × StdGen :=
  let (values, gen) := (mersenne31Array fieldPoolSize false).run gen
  let pool := nonzeroPool values
  let fastPool := mersenne31FastArray pool
  ({ representation := "ZMod", field := "Mersenne31.Field", suffix := "zmod",
     pool := pool, constant := pool.getD 0 1, checksum := checksumZMod,
     sink := fun x ↦ natSink (checksumZMod x) },
   { representation := "UInt32", field := "Mersenne31.Fast.Field", suffix := "fast",
     pool := fastPool, constant := fastPool.getD 0 1, checksum := checksumMersenne31Fast,
     sink := fun x ↦ natSink (checksumMersenne31Fast x) },
   gen)

/-- Goldilocks operands, canonical and native-word, from one pool.

Both rows need an explicit sink: the modulus exceeds `2 ^ 63`, so a `Nat`
digest allocates a bignum on most inputs. -/
private def goldilocksReps (gen : StdGen) :
    ChainRep Goldilocks.Field × ChainRep Goldilocks.Fast.Field × StdGen :=
  let (values, gen) := (zmodArray Goldilocks.fieldSize fieldPoolSize false).run gen
  let pool := nonzeroPool values
  let fastPool := goldilocksFastArray pool
  ({ representation := "ZMod", field := "Goldilocks.Field", suffix := "zmod",
     pool := pool, constant := pool.getD 0 1, checksum := checksumZMod,
     sink := sinkZMod },
   { representation := "UInt64", field := "Goldilocks.Fast.Field", suffix := "fast",
     pool := fastPool, constant := fastPool.getD 0 1, checksum := checksumGoldilocksFast,
     sink := sinkGoldilocksFast },
   gen)

/-! ### KoalaBear -/

/-- Time KoalaBear multiplication. -/
private def runKoalaBearMul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := koalaBearReps gen
  let group ← runBinOpGroup "fields-koalabear-mul" "KoalaBear multiplication"
    "koalabear" "mul" chainRounds throughputRounds slow (· * ·) fast Montgomery.Native32.mul preset
  pure (group, gen)

/-- Time KoalaBear addition. -/
private def runKoalaBearAdd (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := koalaBearReps gen
  let group ← runBinOpGroup "fields-koalabear-add" "KoalaBear addition"
    "koalabear" "add" chainRounds throughputRounds slow (· + ·) fast Montgomery.Native32.add preset
  pure (group, gen)

/-- Time KoalaBear inversion. -/
private def runKoalaBearInv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := koalaBearReps gen
  let group ← runUnOpGroup "fields-koalabear-inv" "KoalaBear inversion"
    "koalabear" "inv" "inv" slow (· + ·) (·⁻¹)
    fast Montgomery.Native32.add Montgomery.Native32.inv preset
  pure (group, gen)

/-- Time KoalaBear exponentiation. -/
private def runKoalaBearPow (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := koalaBearReps gen
  let group ← runUnOpGroup "fields-koalabear-pow" "KoalaBear exponentiation"
    "koalabear" "pow" "pow (binary ladder)"
    slow (· + ·) (npowBinRec powExponent ·)
    fast Montgomery.Native32.add
    (Montgomery.Native32.pow · powExponent) preset
  pure (group, gen)

/-! ### BabyBear -/

/-- Time BabyBear multiplication. -/
private def runBabyBearMul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := babyBearReps gen
  let group ← runBinOpGroup "fields-babybear-mul" "BabyBear multiplication"
    "babybear" "mul" chainRounds throughputRounds slow (· * ·) fast Montgomery.Native32.mul preset
  pure (group, gen)

/-- Time BabyBear addition. -/
private def runBabyBearAdd (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := babyBearReps gen
  let group ← runBinOpGroup "fields-babybear-add" "BabyBear addition"
    "babybear" "add" chainRounds throughputRounds slow (· + ·) fast Montgomery.Native32.add preset
  pure (group, gen)

/-- Time BabyBear inversion. -/
private def runBabyBearInv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := babyBearReps gen
  let group ← runUnOpGroup "fields-babybear-inv" "BabyBear inversion"
    "babybear" "inv" "inv" slow (· + ·) (·⁻¹)
    fast Montgomery.Native32.add Montgomery.Native32.inv preset
  pure (group, gen)

/-- Time BabyBear exponentiation. -/
private def runBabyBearPow (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := babyBearReps gen
  let group ← runUnOpGroup "fields-babybear-pow" "BabyBear exponentiation"
    "babybear" "pow" "pow (binary ladder)"
    slow (· + ·) (npowBinRec powExponent ·)
    fast Montgomery.Native32.add
    (Montgomery.Native32.pow · powExponent) preset
  pure (group, gen)

/-! ### Mersenne31 -/

/-- Time Mersenne31 multiplication. -/
private def runMersenne31Mul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := mersenne31Reps gen
  let group ← runBinOpGroup "fields-mersenne31-mul" "Mersenne31 multiplication"
    "mersenne31" "mul" chainRounds throughputRounds slow (· * ·) fast Mersenne31.Fast.mul preset
  pure (group, gen)

/-- Time Mersenne31 addition. -/
private def runMersenne31Add (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := mersenne31Reps gen
  let group ← runBinOpGroup "fields-mersenne31-add" "Mersenne31 addition"
    "mersenne31" "add" chainRounds throughputRounds slow (· + ·) fast Mersenne31.Fast.add preset
  pure (group, gen)

/-- Time Mersenne31 inversion. -/
private def runMersenne31Inv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := mersenne31Reps gen
  let group ← runUnOpGroup "fields-mersenne31-inv" "Mersenne31 inversion"
    "mersenne31" "inv" "inv" slow (· + ·) (·⁻¹)
    fast Mersenne31.Fast.add Mersenne31.Fast.inv preset
  pure (group, gen)

/-- Time Mersenne31 exponentiation. -/
private def runMersenne31Pow (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := mersenne31Reps gen
  let group ← runUnOpGroup "fields-mersenne31-pow" "Mersenne31 exponentiation"
    "mersenne31" "pow" "pow (binary ladder)"
    slow (· + ·) (npowBinRec powExponent ·)
    fast Mersenne31.Fast.add (Mersenne31.Fast.pow · powExponent) preset
  pure (group, gen)

/-! ### Goldilocks -/

/-- Time Goldilocks multiplication. -/
private def runGoldilocksMul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := goldilocksReps gen
  let group ← runBinOpGroup "fields-goldilocks-mul" "Goldilocks multiplication"
    "goldilocks" "mul" chainRounds throughputRounds slow (· * ·) fast Goldilocks.Fast.mul preset
  pure (group, gen)

/-- Time Goldilocks addition. -/
private def runGoldilocksAdd (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := goldilocksReps gen
  let group ← runBinOpGroup "fields-goldilocks-add" "Goldilocks addition"
    "goldilocks" "add" chainRounds throughputRounds slow (· + ·) fast Goldilocks.Fast.add preset
  pure (group, gen)

/-- Time Goldilocks inversion. -/
private def runGoldilocksInv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := goldilocksReps gen
  let group ← runUnOpGroup "fields-goldilocks-inv" "Goldilocks inversion"
    "goldilocks" "inv" "inv (Fermat chain)" slow (· + ·) (·⁻¹)
    fast Goldilocks.Fast.add Goldilocks.Fast.inv preset
  pure (group, gen)

/-- Time Goldilocks exponentiation. -/
private def runGoldilocksPow (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := goldilocksReps gen
  let group ← runUnOpGroup "fields-goldilocks-pow" "Goldilocks exponentiation"
    "goldilocks" "pow" "pow (binary ladder)"
    slow (· + ·) (npowBinRec powExponent ·)
    fast Goldilocks.Fast.add (Goldilocks.Fast.pow · powExponent) preset
  pure (group, gen)

/-! ### Eight-limb pairing scalar fields

`mul` only. Inversion over these carriers already has a group of its own in
`Fields/Montgomery.lean`, which compares three algorithms rather than two
representations. Both rows need an explicit sink: the canonical value is a
254- to 255-bit bignum, and `sinkMont64x8` reads two limbs instead of
reassembling one. -/

/-- BN254 scalar operands, canonical and eight-limb, from one pool. -/
private def bn254Reps (gen : StdGen) :
    ChainRep BN254.ScalarField × ChainRep BN254.Fast.ScalarField × StdGen :=
  let (values, gen) := (zmodArray BN254.scalarFieldSize fieldPoolSize false).run gen
  let pool := nonzeroPool values
  let fastPool := bn254FastArray pool
  ({ representation := "ZMod", field := "BN254.ScalarField", suffix := "zmod",
     pool := pool, constant := pool.getD 0 1, checksum := checksumZMod, sink := sinkZMod },
   { representation := "Limbs8", field := "BN254.Fast.ScalarField", suffix := "fast",
     pool := fastPool, constant := fastPool.getD 0 1, checksum := checksumBn254Fast,
     sink := sinkMont64x8 },
   gen)

/-- BLS12-381 scalar operands, canonical and eight-limb, from one pool. -/
private def bls12_381Reps (gen : StdGen) :
    ChainRep BLS12_381.ScalarField × ChainRep BLS12_381.Fast.ScalarField × StdGen :=
  let (values, gen) := (zmodArray BLS12_381.scalarFieldSize fieldPoolSize false).run gen
  let pool := nonzeroPool values
  let fastPool := bls12_381FastArray pool
  ({ representation := "ZMod", field := "BLS12_381.ScalarField", suffix := "zmod",
     pool := pool, constant := pool.getD 0 1, checksum := checksumZMod, sink := sinkZMod },
   { representation := "Limbs8", field := "BLS12_381.Fast.ScalarField", suffix := "fast",
     pool := fastPool, constant := fastPool.getD 0 1, checksum := checksumBls12_381Fast,
     sink := sinkMont64x8 },
   gen)

/-- BLS12-377 scalar operands, canonical and eight-limb, from one pool. -/
private def bls12_377Reps (gen : StdGen) :
    ChainRep BLS12_377.ScalarField × ChainRep BLS12_377.Fast.ScalarField × StdGen :=
  let (values, gen) := (zmodArray BLS12_377.scalarFieldSize fieldPoolSize false).run gen
  let pool := nonzeroPool values
  let fastPool := bls12_377FastArray pool
  ({ representation := "ZMod", field := "BLS12_377.ScalarField", suffix := "zmod",
     pool := pool, constant := pool.getD 0 1, checksum := checksumZMod, sink := sinkZMod },
   { representation := "Limbs8", field := "BLS12_377.Fast.ScalarField", suffix := "fast",
     pool := fastPool, constant := fastPool.getD 0 1, checksum := checksumBls12_377Fast,
     sink := sinkMont64x8 },
   gen)

/-- Time BN254 scalar multiplication. -/
private def runBn254Mul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := bn254Reps gen
  let group ← runBinOpGroup "fields-bn254-mul" "BN254 scalar multiplication"
    "bn254" "mul" heavyChainRounds heavyThroughputRounds
    slow (· * ·) fast Montgomery.Native64x8.FastField.mul preset
  pure (group, gen)

/-- Time BLS12-381 scalar multiplication. -/
private def runBls12_381Mul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := bls12_381Reps gen
  let group ← runBinOpGroup "fields-bls12-381-mul" "BLS12-381 scalar multiplication"
    "bls12-381" "mul" heavyChainRounds heavyThroughputRounds
    slow (· * ·) fast Montgomery.Native64x8.FastField.mul preset
  pure (group, gen)

/-- Time BLS12-377 scalar multiplication. -/
private def runBls12_377Mul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (slow, fast, gen) := bls12_377Reps gen
  let group ← runBinOpGroup "fields-bls12-377-mul" "BLS12-377 scalar multiplication"
    "bls12-377" "mul" heavyChainRounds heavyThroughputRounds
    slow (· * ·) fast Montgomery.Native64x8.FastField.mul preset
  pure (group, gen)

/-- Registry entries for the base-field arithmetic benchmarks. -/
def fieldArithTasks : List BenchTask := [
  BenchTask.fromGroupRunner ⟨"fields-koalabear-mul", "KoalaBear multiplication"⟩
    runKoalaBearMul,
  BenchTask.fromGroupRunner ⟨"fields-koalabear-add", "KoalaBear addition"⟩
    runKoalaBearAdd,
  BenchTask.fromGroupRunner ⟨"fields-koalabear-inv", "KoalaBear inversion"⟩
    runKoalaBearInv,
  BenchTask.fromGroupRunner ⟨"fields-koalabear-pow", "KoalaBear exponentiation"⟩
    runKoalaBearPow,
  BenchTask.fromGroupRunner ⟨"fields-babybear-mul", "BabyBear multiplication"⟩
    runBabyBearMul,
  BenchTask.fromGroupRunner ⟨"fields-babybear-add", "BabyBear addition"⟩
    runBabyBearAdd,
  BenchTask.fromGroupRunner ⟨"fields-babybear-inv", "BabyBear inversion"⟩
    runBabyBearInv,
  BenchTask.fromGroupRunner ⟨"fields-babybear-pow", "BabyBear exponentiation"⟩
    runBabyBearPow,
  BenchTask.fromGroupRunner ⟨"fields-mersenne31-mul", "Mersenne31 multiplication"⟩
    runMersenne31Mul,
  BenchTask.fromGroupRunner ⟨"fields-mersenne31-add", "Mersenne31 addition"⟩
    runMersenne31Add,
  BenchTask.fromGroupRunner ⟨"fields-mersenne31-inv", "Mersenne31 inversion"⟩
    runMersenne31Inv,
  BenchTask.fromGroupRunner ⟨"fields-mersenne31-pow", "Mersenne31 exponentiation"⟩
    runMersenne31Pow,
  BenchTask.fromGroupRunner ⟨"fields-goldilocks-mul", "Goldilocks multiplication"⟩
    runGoldilocksMul,
  BenchTask.fromGroupRunner ⟨"fields-goldilocks-add", "Goldilocks addition"⟩
    runGoldilocksAdd,
  BenchTask.fromGroupRunner ⟨"fields-goldilocks-inv", "Goldilocks inversion"⟩
    runGoldilocksInv,
  BenchTask.fromGroupRunner ⟨"fields-goldilocks-pow", "Goldilocks exponentiation"⟩
    runGoldilocksPow,
  BenchTask.fromGroupRunner ⟨"fields-bn254-mul", "BN254 scalar multiplication"⟩
    runBn254Mul,
  BenchTask.fromGroupRunner ⟨"fields-bls12-381-mul", "BLS12-381 scalar multiplication"⟩
    runBls12_381Mul,
  BenchTask.fromGroupRunner ⟨"fields-bls12-377-mul", "BLS12-377 scalar multiplication"⟩
    runBls12_377Mul
]

end CompPolyBench
