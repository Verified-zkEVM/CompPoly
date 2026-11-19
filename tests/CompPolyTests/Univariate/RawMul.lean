/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

import all CompPoly.Univariate.Raw.Ops
public meta import CompPoly.Univariate.Raw.Ops
public meta import Lean.Compiler.IR.EmitUtil
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Raw multiplication tests

Checks of `CPolynomial.Raw.mulRaw` on concrete inputs. `#guard` compiles its term and runs the
compiler's output in the interpreter. The compiler applies the `@[csimp]` lemma
`mulRaw_eq_mulRawFast`, so these checks compute `mulRaw` with `mulRawFast`. `mulRawRef` repeats
the defining fold of `mulRaw`. No `@[csimp]` lemma applies to it, so a comparison with
`mulRawRef` checks the compiled code against the definition of `mulRaw`.

The inputs cover empty and singleton arrays, zero and trailing-zero coefficients, a short factor
on each side, and balanced factors. The section on zero divisors uses `ZMod 6` and `2 × 2`
matrices over `ZMod 4`. The section on noncommutative coefficients uses `2 × 2` matrices over
`ℕ`. The matrices over `ℕ` do not commute, so these checks also fix the order of the factors in
each product.

Two last checks read the `@[csimp]` map and the compiled code of `mul`. They fail if compiled code
does not compute `mulRaw` with `mulRawFast`.
-/

public meta section

open CompPoly CPolynomial CPolynomial.Raw

namespace CompPolyTests.Univariate.RawMul

/-- The defining fold of `mulRaw`. No `@[csimp]` lemma applies to this copy. -/
def mulRawRef {R : Type*} [Semiring R] (p q : Raw R) : Raw R :=
  p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc.addRaw <| (smul a q).mulPowX i) (mk #[])

example {R : Type*} [Semiring R] (p q : Raw R) : mulRawRef p q = mulRaw p q := rfl

/-! ### Empty and singleton factors -/

#guard mulRaw (#[] : Raw ℕ) #[] == #[]
#guard mulRaw (#[] : Raw ℕ) #[1, 2, 3] == #[]
#guard mulRaw (#[1, 2, 3] : Raw ℕ) #[] == #[0, 0]
#guard mulRaw (#[1] : Raw ℕ) #[] == #[]
#guard mulRaw (#[3] : Raw ℕ) #[5] == #[15]
#guard mulRaw (#[2] : Raw ℕ) #[1, 2, 3] == #[2, 4, 6]
#guard mulRaw (#[1, 2, 3] : Raw ℕ) #[2] == #[2, 4, 6]

/-! ### Zero and trailing-zero coefficients

For a nonempty `p`, the product keeps `p.size + q.size - 1` entries, so zero entries at the end
stay. -/

#guard mulRaw (#[0, 0] : Raw ℕ) #[0, 0, 0] == #[0, 0, 0, 0]
#guard mulRaw (#[1, 0] : Raw ℕ) #[1, 1, 0] == #[1, 1, 0, 0]
#guard mulRaw (#[0, 2] : Raw ℕ) #[0, 3] == #[0, 0, 6]
#guard mulRaw (#[1, 2] : Raw ℕ) #[3, 4] == #[3, 10, 8]

/-! ### A short factor on each side

`#[c]` is `C c` and `#[-a, 1]` is `X - C a`. -/

#guard mulRaw (#[1, -2, 0, 5] : Raw ℤ) #[3] == #[3, -6, 0, 15]
#guard mulRaw (#[1, -2, 0, 5] : Raw ℤ) #[-2, 1] == #[-2, 5, -2, -10, 5]
#guard mulRaw (#[-2, 1] : Raw ℤ) #[1, -2, 0, 5] == #[-2, 5, -2, -10, 5]
#guard mulRaw (#[3] : Raw ℤ) #[1, -2, 0, 5] == #[3, -6, 0, 15]

/-- The array of length `n` whose entry `i` is `i + 1`, or `0` when `i % 3 = 2`. -/
def natInput (n : ℕ) : Raw ℕ := Array.ofFn fun i : Fin n ↦ if i.val % 3 = 2 then 0 else i.val + 1

#guard (List.range 9).all fun m ↦ (List.range 9).all fun n ↦
  mulRaw (natInput m) (natInput n) == mulRawRef (natInput m) (natInput n)
#guard [1, 2, 3].all fun n ↦
  mulRaw (natInput 40) (natInput n) == mulRawRef (natInput 40) (natInput n) &&
    mulRaw (natInput n) (natInput 40) == mulRawRef (natInput n) (natInput 40)
#guard mulRaw (natInput 24) (natInput 24) == mulRawRef (natInput 24) (natInput 24)

/-! ### Zero divisors

In `ZMod 6` and in matrices over `ZMod 4`, a product of nonzero entries can be zero. -/

/-- Inputs over `ZMod 6` of length `n`. Entry `i` is `5 * i + shift`. -/
def zmodInput (n shift : ℕ) : Raw (ZMod 6) :=
  Array.ofFn fun i : Fin n ↦ ((5 * i.val + shift : ℕ) : ZMod 6)

#guard (List.range 12).all fun m ↦ (List.range 12).all fun n ↦
  mulRaw (zmodInput m 1) (zmodInput n 2) == mulRawRef (zmodInput m 1) (zmodInput n 2)

/-- Upper triangular `2 × 2` matrices over `ZMod 4` of length `n`. -/
def zmodMatInput (n shift : ℕ) : Raw (Matrix (Fin 2) (Fin 2) (ZMod 4)) :=
  Array.ofFn fun i : Fin n ↦ !![((i.val + shift : ℕ) : ZMod 4), 2; 0, ((3 * i.val : ℕ) : ZMod 4)]

#guard (List.range 8).all fun m ↦ (List.range 8).all fun n ↦
  mulRaw (zmodMatInput m 0) (zmodMatInput n 1) ==
    mulRawRef (zmodMatInput m 0) (zmodMatInput n 1)

/-! ### Noncommutative coefficients -/

/-- A `2 × 2` matrix over `ℕ`. -/
abbrev M := Matrix (Fin 2) (Fin 2) ℕ

/-- A matrix that does not commute with `b`. -/
def a : M := !![1, 2; 3, 4]

/-- The swap matrix. -/
def b : M := !![0, 1; 1, 0]

#guard a * b != b * a
#guard mulRaw #[a] #[b] == #[a * b]
#guard mulRaw #[a] #[b] == #[!![2, 1; 4, 3]]
#guard mulRaw #[a, b] #[b, a] == #[a * b, a * a + b * b, b * a]
#guard mulRaw #[a, b, a] #[b] == #[a * b, b * b, a * b]
#guard mulRaw #[a, b, a] #[b] != #[b * a, b * b, b * a]
#guard mulRaw #[b] #[a, b, a] == #[b * a, b * b, b * a]

/-- Matrix inputs of length `n`, cycling through six matrices that include `0` and `1`. -/
def matInput (n : ℕ) (shift : ℕ) : Raw M :=
  Array.ofFn fun i : Fin n ↦ #[a, b, 0, a * b, 1, !![0, 0; 5, 0]].getD ((i.val + shift) % 6) 0

#guard (List.range 7).all fun m ↦ (List.range 7).all fun n ↦
  mulRaw (matInput m 0) (matInput n 3) == mulRawRef (matInput m 0) (matInput n 3)
#guard [1, 2].all fun n ↦
  mulRaw (matInput 20 0) (matInput n 1) == mulRawRef (matInput 20 0) (matInput n 1) &&
    mulRaw (matInput n 1) (matInput 20 0) == mulRawRef (matInput n 1) (matInput 20 0)

/-! ### `mulRawFast` called directly -/

#guard (List.range 9).all fun m ↦ (List.range 9).all fun n ↦
  mulRawFast (natInput m) (natInput n) == mulRawRef (natInput m) (natInput n)
#guard (List.range 7).all fun m ↦ (List.range 7).all fun n ↦
  mulRawFast (matInput m 0) (matInput n 3) == mulRawRef (matInput m 0) (matInput n 3)

/-! ### The `@[csimp]` lemma and its placement

The checks above pass without the `@[csimp]` lemma too. The first check below fails if the lemma
is removed. The second fails if `mul` is compiled before the lemma, because then the compiled code
of `mul` keeps the fold of `mulRaw`. -/

open Lean in
run_meta do
  let map := (Compiler.CSimp.ext.getState (← getEnv)).map
  unless (map.find? ``mulRaw).map (·.toDeclName) == some ``mulRawFast do
    throwError "no @[csimp] lemma replaces mulRaw with mulRawFast"

open Lean in
run_meta do
  let env ← getEnv
  let some decl := IR.findEnvDecl env ``mul | throwError "no compiled code for `mul`"
  unless (IR.collectUsedDecls env [decl]).any (``mulRawFast).isPrefixOf do
    throwError "the compiled code of `mul` does not call `mulRawFast`"

end CompPolyTests.Univariate.RawMul
