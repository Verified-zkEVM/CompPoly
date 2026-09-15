/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Common
public import CompPoly.Fields.Mersenne31
public import CompPoly.Fields.BN254
public import CompPoly.Fields.BLS12_381
public import CompPoly.Fields.BLS12_377

/-!
# Field inputs, checksums and sinks

Per-field benchmark scaffolding for the concrete fields that
`CompPolyBench.Common` does not already carry: Mersenne31 and the three
eight-limb Montgomery scalar fields.

These live here rather than in `CompPolyBench.Common` because that module is
imported by every benchmark, and the field modules below are needed by a
handful. The division is by import cost, not by kind.

Three things are provided per field, and the distinction between the last two
is the one that goes wrong:

* an **input generator**, drawing from the group's random stream;
* a **checksum** into `Nat`, folded by the untimed validation pass and compared
  across the implementations in a group, so it must be a faithful function of
  the canonical value;
* a **sink** into `UInt64`, folded inside the timed region purely to keep the
  result live. A sink is never compared with anything, so it may be as lossy as
  it likes — but it must be *cheap*, and comparably cheap for every row of a
  group, or the group's ratio measures the sinks.
-/

public section

open CompPoly

namespace CompPolyBench

/-! ## Mersenne31

`2 ^ 31 - 1`, the field Plonky3 uses for its Circle STARK. The canonical value
fits a machine word, so the `Nat` checksum doubles as a sink and no explicit
`sink :=` is needed. -/

/-- Generate Mersenne31 coefficients with the same shape controls as `zmodArray`. -/
def mersenne31Array (size : Nat) (sparse : Bool) : StateM StdGen (Array Mersenne31.Field) :=
  zmodArray Mersenne31.fieldSize size sparse

/-- Convert Mersenne31 field inputs to the native-word representation. -/
def mersenne31FastArray (xs : Array Mersenne31.Field) : Array Mersenne31.Fast.Field :=
  xs.map Mersenne31.Fast.ofField

/-- Convert a fast Mersenne31 element to a checksum word.

The carrier is an `abbrev` for a `Subtype`, so dot notation would resolve to
`Subtype.toNat`; call the field's own `toNat` directly. -/
def checksumMersenne31Fast (x : Mersenne31.Fast.Field) : Nat :=
  Mersenne31.Fast.toNat x

/-! ## Eight-limb Montgomery scalar fields

BN254, BLS12-381 and BLS12-377. The canonical value is a 254- to 255-bit
bignum, so both representations need an explicit sink: `sinkZMod` for the
canonical side and `sinkMont64x8` for the fast one. -/

/-- Convert BN254 field inputs to the native eight-limb representation. -/
def bn254FastArray (xs : Array BN254.ScalarField) : Array BN254.Fast.ScalarField :=
  xs.map BN254.Fast.ofField

/-- Convert a fast BN254 element to a checksum word. -/
def checksumBn254Fast (x : BN254.Fast.ScalarField) : Nat :=
  x.toNat

/-- Convert BLS12-381 field inputs to the native eight-limb representation. -/
def bls12_381FastArray (xs : Array BLS12_381.ScalarField) :
    Array BLS12_381.Fast.ScalarField :=
  xs.map BLS12_381.Fast.ofField

/-- Convert a fast BLS12-381 element to a checksum word. -/
def checksumBls12_381Fast (x : BLS12_381.Fast.ScalarField) : Nat :=
  x.toNat

/-- Convert BLS12-377 field inputs to the native eight-limb representation. -/
def bls12_377FastArray (xs : Array BLS12_377.ScalarField) :
    Array BLS12_377.Fast.ScalarField :=
  xs.map BLS12_377.Fast.ofField

/-- Convert a fast BLS12-377 element to a checksum word. -/
def checksumBls12_377Fast (x : BLS12_377.Fast.ScalarField) : Nat :=
  x.toNat

/-- Sink an eight-limb Montgomery element by two of its limbs.

`toNat` reassembles a 256-bit bignum, which costs more than the multiplication
under test. The limbs are already unboxed `UInt64` fields of the carrier, so
this is two loads and an exclusive or. Lossy by construction; the untimed
digest is what establishes correctness. -/
@[inline] def sinkMont64x8 {modulus : Nat} [Montgomery.Native64x8.Mont64x8Field modulus]
    (x : Montgomery.Native64x8.FastField modulus) : UInt64 :=
  (Subtype.val x).l0 ^^^ (Subtype.val x).l7

end CompPolyBench
