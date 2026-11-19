/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import CompPolyBench.Univariate.Common
public import CompPoly.Fields.BN254

/-!
# Raw multiplication by a short factor, and balanced raw multiplication

Raw multiplication `CPolynomial.Raw.mulRaw p q` over three coefficient types with different
arithmetic costs. KoalaBear's native-word representation uses unboxed 32-bit arithmetic. The BN254
scalar field as `ZMod` uses arithmetic on big natural numbers through the instance closures of
`ZMod`. `Int` uses boxed integer arithmetic.

The `short` groups multiply a factor with `coeffs` dense coefficients by a factor of one or two
coefficients. The short factors are `C c` and `X - C a`, the shapes of a scalar product and of
one step of a product of linear factors. The rows `*-right` put the short factor on the right
and the rows `*-left` put it on the left. The `cpoly-*` rows multiply by `X - C a` through the
`CPolynomial` instance, which trims the result. One group per size, because the size of the long
factor is the variable of the sweep.

The `balanced` groups multiply two factors with `coeffs` dense coefficients each, in both orders.
The `univariate-mul-crossover-*` groups measure balanced products over KoalaBear's native-word
representation.

All three coefficient types are commutative, so the two orientations of a product give the same
array, and each pair of rows shares a digest class. Every body indexes a pool of two inputs. The
sink reads four entries of the result, so that its cost does not grow with the size of the
result.
-/

public section

open CompPoly

namespace CompPolyBench

/-- A coefficient type of the raw multiplication groups. -/
private structure RawMulCarrier (R : Type) where
  /-- The part of the group key that names the coefficient type. -/
  slug : String
  /-- The name of the coefficient type in the records. -/
  field : String
  /-- Generate `n` dense coefficients. -/
  coeffs : Nat → StateM StdGen (Array R)
  /-- The checksum of one coefficient. -/
  checksum : R → Nat

/-- KoalaBear's native-word representation. -/
private def koalaBearCarrier : RawMulCarrier KoalaBear.Fast.Field :=
  { slug := "koalabear", field := "KoalaBear.Fast.Field",
    coeffs := fun n ↦ koalaBearFastArray <$> koalaBearArray n false,
    checksum := checksumKoalaBearFast }

/-- The BN254 scalar field as `ZMod`. -/
private def bn254Carrier : RawMulCarrier BN254.ScalarField :=
  { slug := "bn254", field := "BN254.ScalarField",
    coeffs := fun n ↦ zmodArray BN254.scalarFieldSize n false, checksum := checksumZMod }

/-- Integers in `[-2^20, 2^20]`. Their products leave the range of Lean's unboxed small
integers. -/
private def intCarrier : RawMulCarrier Int :=
  { slug := "int", field := "Int",
    coeffs := fun n ↦ (·.map fun x ↦ Int.ofNat x - 2 ^ 20) <$> randomNatArray n (2 ^ 21),
    checksum := fun x ↦ x.natAbs * 2 + if x < 0 then 1 else 0 }

/-- Time raw multiplication by `C c` and by `X - C a`, on each side, at one size. -/
private def runRawMulShortGroup {R : Type} [CommRing R] [BEq R] [LawfulBEq R]
    (carrier : RawMulCarrier R) (coeffs : Nat) (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (long, gen) := (carrier.coeffs (2 * coeffs)).run gen
  let (short, gen) := (carrier.coeffs 4).run gen
  let longs : Array (CPolynomial.Raw R) :=
    #[long.extract 0 coeffs, long.extract coeffs (2 * coeffs)]
  let scalars : Array (CPolynomial.Raw R) := #[#[short.getD 0 0], #[short.getD 1 0]]
  let linears : Array (CPolynomial.Raw R) := #[#[-short.getD 2 0, 1], #[-short.getD 3 0, 1]]
  let cpolys := longs.map cpolyOfArray
  let factors := linears.map cpolyOfArray
  let longAt (i : Nat) := longs.getD (i % 2) #[]
  let scalarAt (i : Nat) := scalars.getD (i % 2) #[]
  let linearAt (i : Nat) := linears.getD (i % 2) #[]
  let cpolyAt (i : Nat) := cpolys.getD (i % 2) 0
  let factorAt (i : Nat) := factors.getD (i % 2) 0
  let field := carrier.field
  let shape := s!"degree<{coeffs} dense times a factor of size 1 or 2, two inputs"
  let digests := digestPeriod 2
  let checksum := checksumRawPolynomial carrier.checksum
  let sink := arraySampleSink fun x ↦ natSink (carrier.checksum x)
  let cpolyChecksum := checksumCPolynomial carrier.checksum
  let cpolySink (p : CPolynomial R) : UInt64 := sink p.val
  let scalarRight ← runTimedSpec
    { name := "univariate-raw-mul-scalar-right", representation := "CPolynomial.Raw",
      method := "mulRaw p (C c)", field, inputShape := shape, digestIterations := digests,
      digestClass := "scalar" }
    preset (fun i ↦ CPolynomial.Raw.mulRaw (longAt i) (scalarAt i)) checksum (sink := sink)
  let scalarLeft ← runTimedSpec
    { name := "univariate-raw-mul-scalar-left", representation := "CPolynomial.Raw",
      method := "mulRaw (C c) p", field, inputShape := shape, digestIterations := digests,
      digestClass := "scalar" }
    preset (fun i ↦ CPolynomial.Raw.mulRaw (scalarAt i) (longAt i)) checksum (sink := sink)
  let linearRight ← runTimedSpec
    { name := "univariate-raw-mul-linear-right", representation := "CPolynomial.Raw",
      method := "mulRaw p (X - C a)", field, inputShape := shape, digestIterations := digests,
      digestClass := "linear" }
    preset (fun i ↦ CPolynomial.Raw.mulRaw (longAt i) (linearAt i)) checksum (sink := sink)
  let linearLeft ← runTimedSpec
    { name := "univariate-raw-mul-linear-left", representation := "CPolynomial.Raw",
      method := "mulRaw (X - C a) p", field, inputShape := shape, digestIterations := digests,
      digestClass := "linear" }
    preset (fun i ↦ CPolynomial.Raw.mulRaw (linearAt i) (longAt i)) checksum (sink := sink)
  let cpolyRight ← runTimedSpec
    { name := "univariate-raw-mul-cpoly-linear-right", representation := "CPolynomial",
      method := "p * (X - C a)", field, inputShape := shape, digestIterations := digests,
      digestClass := "cpoly-linear" }
    preset (fun i ↦ cpolyAt i * factorAt i) cpolyChecksum (sink := cpolySink)
  let cpolyLeft ← runTimedSpec
    { name := "univariate-raw-mul-cpoly-linear-left", representation := "CPolynomial",
      method := "(X - C a) * p", field, inputShape := shape, digestIterations := digests,
      digestClass := "cpoly-linear" }
    preset (fun i ↦ factorAt i * cpolyAt i) cpolyChecksum (sink := cpolySink)
  pure ({ groupKey := s!"univariate-raw-mul-short-{carrier.slug}-{coeffs}",
          title := s!"Raw multiplication by a short factor, degree<{coeffs} ({field})",
          records := #[scalarRight, scalarLeft, linearRight, linearLeft, cpolyRight,
            cpolyLeft] }, gen)

/-- Time raw multiplication of two factors of one size, in both orders. -/
private def runRawMulBalancedGroup {R : Type} [CommSemiring R]
    (carrier : RawMulCarrier R) (coeffs : Nat) (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (carrier.coeffs (4 * coeffs)).run gen
  let factors : Array (CPolynomial.Raw R) :=
    #[values.extract 0 coeffs, values.extract coeffs (2 * coeffs),
      values.extract (2 * coeffs) (3 * coeffs), values.extract (3 * coeffs) (4 * coeffs)]
  let lhsAt (i : Nat) := factors.getD (i % 2) #[]
  let rhsAt (i : Nat) := factors.getD (2 + i % 2) #[]
  let field := carrier.field
  let shape := s!"two degree<{coeffs} dense factors, two inputs"
  let digests := digestPeriod 2
  let checksum := checksumRawPolynomial carrier.checksum
  let sink := arraySampleSink fun x ↦ natSink (carrier.checksum x)
  let forward ← runTimedSpec
    { name := "univariate-raw-mul-balanced", representation := "CPolynomial.Raw",
      method := "mulRaw p q", field, inputShape := shape, digestIterations := digests,
      digestClass := "balanced" }
    preset (fun i ↦ CPolynomial.Raw.mulRaw (lhsAt i) (rhsAt i)) checksum (sink := sink)
  let swapped ← runTimedSpec
    { name := "univariate-raw-mul-balanced-swapped", representation := "CPolynomial.Raw",
      method := "mulRaw q p", field, inputShape := shape, digestIterations := digests,
      digestClass := "balanced" }
    preset (fun i ↦ CPolynomial.Raw.mulRaw (rhsAt i) (lhsAt i)) checksum (sink := sink)
  pure ({ groupKey := s!"univariate-raw-mul-balanced-{carrier.slug}-{coeffs}",
          title := s!"Balanced raw multiplication, degree<{coeffs} ({field})",
          records := #[forward, swapped] }, gen)

/-- The registry entry of one `short` group. Each use below passes a concrete carrier, so the
compiler specializes the group runner, and `mulRaw` in it, at that coefficient type. -/
private def rawMulShortTask {R : Type} [CommRing R] [BEq R] [LawfulBEq R]
    (carrier : RawMulCarrier R) (coeffs : Nat) : BenchTask :=
  BenchTask.fromGroupRunner
    ⟨s!"univariate-raw-mul-short-{carrier.slug}-{coeffs}",
      s!"Raw multiplication by a short factor, degree<{coeffs} ({carrier.field})"⟩
    (runRawMulShortGroup carrier coeffs)

/-- The registry entry of one `balanced` group, specialized as `rawMulShortTask` is. -/
private def rawMulBalancedTask {R : Type} [CommSemiring R] (carrier : RawMulCarrier R)
    (coeffs : Nat) : BenchTask :=
  BenchTask.fromGroupRunner
    ⟨s!"univariate-raw-mul-balanced-{carrier.slug}-{coeffs}",
      s!"Balanced raw multiplication, degree<{coeffs} ({carrier.field})"⟩
    (runRawMulBalancedGroup carrier coeffs)

/-- Registry entries for raw multiplication. -/
def rawMulTasks : List BenchTask :=
  [rawMulShortTask koalaBearCarrier 8, rawMulShortTask koalaBearCarrier 64,
    rawMulShortTask koalaBearCarrier 1024, rawMulShortTask bn254Carrier 1024,
    rawMulShortTask intCarrier 1024, rawMulBalancedTask bn254Carrier 64,
    rawMulBalancedTask intCarrier 64]

end CompPolyBench
