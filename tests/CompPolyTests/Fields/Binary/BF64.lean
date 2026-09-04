/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.BF64
public import CompPoly.Fields.Binary.BF64

/-!
# `GF(2^64)` and `GF(2^192)` regression tests

Differential vectors for the polynomial-basis `GF(2^64)` of
`CompPoly/Fields/Binary/BF64/` and its cubic extension, plus guards that the definitions
are not degenerate.

The vectors are independently produced reference values for this modulus and basis. They
are what distinguishes a correct port from a plausible one: a wrong modulus, a wrong
reduction constant, or a wrong extension coefficient vector all compile cleanly and
silently give a *different* field, but fail these.

Base-field vectors are checked with `decide +kernel`, so the kernel evaluates the
carry-less product and the reduction. Extension vectors use `#guard`, which runs the
*compiled* arithmetic at elaboration time, following `CompPolyTests.Fields.Extension`:
that is deliberate, since a `Field` instance that regressed to noncomputable would fail
the build rather than pass silently.
-/

public meta section

namespace CompPolyTests.Fields.Binary.BF64Poly

open _root_.BF64

/-! ## Base-field differential vectors -/

/-- Reference `(a, b, a * b)` triples for `GF(2^64)` multiplication. -/
def multiplicationVectors : List (BitVec 64 × BitVec 64 × BitVec 64) :=
  [(0x01090913877ed8ed, 0x66ab35ac2768468f, 0x50c4519dc383744a),
   (0xa7715ae18f12a3b5, 0x05743059f43fa4f5, 0xeb64cd9cd9cda6df),
   (0xbd3efb4705e79ddd, 0x3aff618604de4ae0, 0xc3d7a95fa9cb59bb)]

/-- Multiplication agrees with the reference on every vector.

This also pins computability: the kernel has to evaluate the carry-less product and the
reduction to check it. -/
theorem multiplication_matches_reference :
    multiplicationVectors.all
      (fun v => reduce (BinaryField.carryLessMul (w := 128) v.1 v.2.1) == v.2.2) = true := by
  decide +kernel

/-! ## Non-vacuity guards -/

/-- The element `x`, a generator of the multiplicative group, is not zero. -/
theorem generator_ne_zero : (0x2 : _root_.BF64) ≠ 0 := by decide +kernel

/-- The generator is not one, so it is not a degenerate choice. -/
theorem generator_ne_one : (0x2 : _root_.BF64) ≠ 1 := by decide +kernel

/-- Multiplication by one is the identity on a sample element, so `reduce` is not
collapsing everything to a constant. -/
theorem one_mul_sample :
    ((1 : _root_.BF64) * 0x01090913877ed8ed : _root_.BF64) = 0x01090913877ed8ed := by
  rw [_root_.BF64.mul_def]; decide +kernel

/-- A product that genuinely wraps: the reduction is exercised, not bypassed.
`x^63 * x = x^64 ≡ x^4 + x^3 + x + 1 = 0x1B`. -/
theorem reduction_is_exercised :
    ((0x8000000000000000 : _root_.BF64) * 0x2 : _root_.BF64) = 0x1B := by
  rw [_root_.BF64.mul_def]; decide +kernel

/-! ## Extension-field vectors

These use `#guard`, which runs the *compiled* arithmetic, so they fail the build if an
instance ever regresses to noncomputable.
-/

section Vectors

open CompPoly.Extension

private def limbs (c0 c1 c2 : _root_.BF64) : Ext3 :=
  Ext.ofFn (fun i => if (i : ℕ) = 0 then c0 else if (i : ℕ) = 1 then c1 else c2)

/-- The adjoined root `y`. -/
private def y : Ext3 := limbs 0 1 0

-- The defining relation `y^3 = y + 1`.
#guard y * y * y == y + 1

-- First reference vector: a product and a square.
#guard limbs 0x950e87d7f5606615 0x2c61275c9e6b6cf8 0x1f00bca0042db923
         * limbs 0x6dbca290a9eab706 0x4c10a4fe30cffdda 0xf26fff4cc4fd394d
       == limbs 0x888a0fc35abaf5f6 0x68a84cbc132b0649 0x9fdeaf613003cabe

#guard limbs 0x950e87d7f5606615 0x2c61275c9e6b6cf8 0x1f00bca0042db923
         * limbs 0x950e87d7f5606615 0x2c61275c9e6b6cf8 0x1f00bca0042db923
       == limbs 0x8fba131ad5d46b8c 0x1c170457f537a805 0x3632cc098ca15135

-- Second reference vector.
#guard limbs 0x6814a2bc786a6d2d 0xa26b351e6c8042c5 0x54760e7fbc051c6c
         * limbs 0xd4c08880a5a4666d 0x29610ae0eed8f1e7 0xc34bd8e2fe5213e5
       == limbs 0x2ad322ebf2f9043b 0x8ac800aa67154c80 0x6d0f76651d3c4d0c

-- Inversion evaluates in both fields.
#guard (0x01090913877ed8ed : _root_.BF64) * (0x01090913877ed8ed : _root_.BF64)⁻¹ == 1
#guard (0 : _root_.BF64)⁻¹ == 0
#guard y * y⁻¹ == 1

end Vectors

end CompPolyTests.Fields.Binary.BF64Poly
