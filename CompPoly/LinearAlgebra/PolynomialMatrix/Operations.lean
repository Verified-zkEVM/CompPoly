/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Shifted
import CompPoly.Univariate.Context

/-!
# Polynomial-Matrix Operations

Reusable executable operations for polynomial rows and row-major polynomial
matrices.  The multiplication and reduction entry points take explicit
univariate operation contexts so concrete fields can supply fast polynomial
arithmetic.
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*}

/-- Polynomial-matrix low-product backend.  The full multiplication context is
kept beside the low-product operation because recursive PM-basis still needs
ordinary basis composition. -/
structure MulLowContext (F : Type*) [Semiring F] [BEq F] [LawfulBEq F] where
  mulContext : CPolynomial.MulContext F
  mulLow : Nat → CPolynomial F → CPolynomial F → CPolynomial F

namespace MulLowContext

/-- Low-product backend obtained by truncating a full univariate product. -/
def fromMulContext [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) : MulLowContext F where
  mulContext := mulCtx
  mulLow order p q :=
    CPolynomial.ofArray
      ((List.range order).map (fun i ↦ CPolynomial.coeff (mulCtx.mul p q) i) |>.toArray)

/-- Low-product backend backed directly by a raw low-product implementation. -/
def raw [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F)
    (rawCtx : CPolynomial.Raw.MulLowContext F) : MulLowContext F where
  mulContext := mulCtx
  mulLow order p q := CPolynomial.ofArray (rawCtx.mulLow order p.val q.val)

end MulLowContext

/-- Build a row-major polynomial matrix from an indexed entry function. -/
def ofFn [Zero F] (rows width : Nat) (entry : Nat → Nat → CPolynomial F) :
    PolynomialMatrix F :=
  (List.range rows).map
    (fun i ↦ (List.range width).map (fun j ↦ entry i j) |>.toArray) |>.toArray

/-- The zero matrix of a fixed shape. -/
def zero [Zero F] (rows width : Nat) : PolynomialMatrix F :=
  ofFn rows width fun _ _ ↦ 0

/-- The polynomial identity matrix of size `n`. -/
def identity [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] (n : Nat) :
    PolynomialMatrix F :=
  ofFn n n fun i j ↦ if i == j then 1 else 0

/-- Matrix transpose, using zero defaults for ragged input rows. -/
def transpose [Zero F] (M : PolynomialMatrix F) : PolynomialMatrix F :=
  ofFn (MatrixWidth M) M.size fun i j ↦ rowGet (M.getD j #[]) i

/-- Dot product of two polynomial rows using an explicit univariate
multiplication context. -/
def rowDotWith [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (a b : PolynomialRow F) :
    CPolynomial F :=
  (List.range (max a.size b.size)).foldl
    (fun acc k ↦ acc + mulCtx.mul (rowGet a k) (rowGet b k)) 0

/-- Row-by-matrix product using an explicit univariate multiplication context. -/
def rowMulMatrixWith [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (row : PolynomialRow F)
    (M : PolynomialMatrix F) : PolynomialRow F :=
  (List.range (MatrixWidth M)).map
    (fun j ↦
      (List.range row.size).foldl
        (fun acc k ↦ acc + mulCtx.mul (rowGet row k) (rowGet (M.getD k #[]) j)) 0) |>.toArray

/-- Matrix product using an explicit univariate multiplication context. -/
def mulWith [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (A B : PolynomialMatrix F) :
    PolynomialMatrix F :=
  A.map fun row ↦ rowMulMatrixWith mulCtx row B

/-- Matrix product backed by canonical univariate multiplication. -/
def mul [Semiring F] [BEq F] [LawfulBEq F]
    (A B : PolynomialMatrix F) : PolynomialMatrix F :=
  mulWith CPolynomial.MulContext.naive A B

/-- Pointwise matrix addition, using zero defaults for ragged inputs. -/
def add [Semiring F] [BEq F] [LawfulBEq F]
    (A B : PolynomialMatrix F) : PolynomialMatrix F :=
  ofFn (max A.size B.size) (max (MatrixWidth A) (MatrixWidth B)) fun i j ↦
    rowGet (A.getD i #[]) j + rowGet (B.getD i #[]) j

/-- Pointwise matrix subtraction, using zero defaults for ragged inputs. -/
def sub [Ring F] [BEq F] [LawfulBEq F]
    (A B : PolynomialMatrix F) : PolynomialMatrix F :=
  ofFn (max A.size B.size) (max (MatrixWidth A) (MatrixWidth B)) fun i j ↦
    rowGet (A.getD i #[]) j - rowGet (B.getD i #[]) j

/-- Extract a rectangular block with zero defaults for out-of-range entries. -/
def block [Zero F] (M : PolynomialMatrix F)
    (rowStart rowCount colStart colCount : Nat) : PolynomialMatrix F :=
  ofFn rowCount colCount fun i j ↦
    rowGet (M.getD (rowStart + i) #[]) (colStart + j)

/-- Join four equally sized square blocks into one square matrix. -/
def joinSquareBlocks [Zero F] (half : Nat)
    (C₁₁ C₁₂ C₂₁ C₂₂ : PolynomialMatrix F) : PolynomialMatrix F :=
  ofFn (2 * half) (2 * half) fun i j ↦
    if i < half then
      if j < half then
        rowGet (C₁₁.getD i #[]) j
      else
        rowGet (C₁₂.getD i #[]) (j - half)
    else
      if j < half then
        rowGet (C₂₁.getD (i - half) #[]) j
      else
        rowGet (C₂₂.getD (i - half) #[]) (j - half)

/-- Fuel-bounded doubling loop for the smallest power of two at least `target`. -/
def nextPowerOfTwoAtLeastLoop (target : Nat) :
    Nat → Nat → Nat
  | 0, current => current
  | fuel + 1, current =>
      if target ≤ current then
        current
      else
        nextPowerOfTwoAtLeastLoop target fuel (2 * current)

/-- Smallest power of two at least `target`, with `1` returned for `0`. -/
def nextPowerOfTwoAtLeast (target : Nat) : Nat :=
  nextPowerOfTwoAtLeastLoop target (target + 1) 1

/-- Runtime dimension controlling rectangular polynomial-matrix multiplication. -/
def multiplicationDimension [Zero F] (A B : PolynomialMatrix F) : Nat :=
  max A.size (max (MatrixWidth A) (max B.size (MatrixWidth B)))

/-- Pad a matrix to an `n × n` square using the zero-default block extractor. -/
def padSquare [Zero F] (n : Nat) (M : PolynomialMatrix F) :
    PolynomialMatrix F :=
  block M 0 n 0 n

/-- Trim a matrix to a rectangular output shape. -/
def trimShape [Zero F] (rows width : Nat) (M : PolynomialMatrix F) :
    PolynomialMatrix F :=
  block M 0 rows 0 width

/-- Slice `count` natural-number entries, using zero defaults out of bounds. -/
def natArraySlice (values : Array Nat) (start count : Nat) : Array Nat :=
  (List.range count).map (fun i ↦ values.getD (start + i) 0) |>.toArray

/-- Pointwise maximum of two natural-number arrays. -/
def maxNatArrays (a b : Array Nat) : Array Nat :=
  (List.range (max a.size b.size)).map
    (fun i ↦ max (a.getD i 0) (b.getD i 0)) |>.toArray

/-- Number of coefficients needed to represent a polynomial exactly. -/
def polynomialCoeffCap [Zero F] [BEq F] (p : CPolynomial F) : Nat :=
  if p == 0 then 0 else p.natDegree + 1

/-- Number of low coefficients sufficient for one product term exactly. -/
def productCoeffCap [Zero F] [BEq F] (p q : CPolynomial F) : Nat :=
  if p == 0 || q == 0 then 0 else p.natDegree + q.natDegree + 1

/-- Per-entry coefficient cap for one row-by-matrix product entry. -/
def rowMulMatrixEntryCoeffCap [Zero F] [BEq F]
    (row : PolynomialRow F) (M : PolynomialMatrix F) (j : Nat) : Nat :=
  (List.range row.size).foldl
    (fun acc k ↦ max acc
      (productCoeffCap (rowGet row k) (rowGet (M.getD k #[]) j))) 0

/-- Keep the coefficients of degree `< order`. -/
def truncateX [Zero F] [BEq F] [LawfulBEq F] (order : Nat)
    (p : CPolynomial F) : CPolynomial F :=
  CPolynomial.ofArray
    ((List.range order).map (fun i ↦ CPolynomial.coeff p i) |>.toArray)

/-- Truncate one row with independent output-column orders. -/
def rowTruncateColumns [Zero F] [BEq F] [LawfulBEq F]
    (orders : Array Nat) (row : PolynomialRow F) : PolynomialRow F :=
  (List.range row.size).map
    (fun j ↦ truncateX (orders.getD j 0) (rowGet row j)) |>.toArray

/-- Truncate a matrix with independent output-column orders. -/
def truncateColumns [Zero F] [BEq F] [LawfulBEq F]
    (orders : Array Nat) (M : PolynomialMatrix F) : PolynomialMatrix F :=
  M.map fun row ↦ rowTruncateColumns orders row

/-- Multiply and retain only coefficients of degree `< order`. -/
def mulTruncXWith [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (order : Nat)
    (p q : CPolynomial F) : CPolynomial F :=
  truncateX order (mulCtx.mul p q)

/-- Low-product entry point for the first `order` coefficients. -/
def mulLowXWith [Semiring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (order : Nat)
    (p q : CPolynomial F) : CPolynomial F :=
  lowCtx.mulLow order p q

/-- Divide by `X^shift` and keep `order` coefficients. -/
def divXTrunc [Zero F] [BEq F] [LawfulBEq F] (shift order : Nat)
    (p : CPolynomial F) : CPolynomial F :=
  CPolynomial.ofArray
    ((List.range order).map (fun i ↦ CPolynomial.coeff p (i + shift)) |>.toArray)

/-- Reduce by a monic modulus when one is present.  A zero modulus is treated as
an absent modulus and leaves the input unchanged. -/
def modByMonicWith [Field F] [BEq F] [LawfulBEq F]
    (modCtx : CPolynomial.ModContext F) (p modulus : CPolynomial F) :
    CPolynomial F :=
  if modulus == 0 then p else modCtx.modByMonic p modulus

/-- Reduce a row by independent diagonal moduli.  The output width is the number
of supplied moduli. -/
def rowModDiagonalWith [Field F] [BEq F] [LawfulBEq F]
    (modCtx : CPolynomial.ModContext F) (moduli : Array (CPolynomial F))
    (row : PolynomialRow F) : PolynomialRow F :=
  (List.range moduli.size).map
    (fun j ↦ modByMonicWith modCtx (rowGet row j) (moduli.getD j 0)) |>.toArray

/-- Reduce every matrix row by independent diagonal moduli. -/
def modDiagonalWith [Field F] [BEq F] [LawfulBEq F]
    (modCtx : CPolynomial.ModContext F) (moduli : Array (CPolynomial F))
    (M : PolynomialMatrix F) : PolynomialMatrix F :=
  M.map fun row ↦ rowModDiagonalWith modCtx moduli row

/-- Row-by-matrix product followed by diagonal modular reduction. -/
def rowMulMatrixModDiagonalWith [Field F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (row : PolynomialRow F) (M : PolynomialMatrix F)
    (moduli : Array (CPolynomial F)) : PolynomialRow F :=
  rowModDiagonalWith modCtx moduli (rowMulMatrixWith mulCtx row M)

/-- Row-by-matrix product with independent output-column truncation.  Column
`j` keeps coefficients of degree `< orders[j]`; this is the residual-window
primitive used by recursive PM-basis. -/
def rowMulMatrixTruncColumnWith [Semiring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (orders : Array Nat)
    (row : PolynomialRow F) (M : PolynomialMatrix F) : PolynomialRow F :=
  (List.range (MatrixWidth M)).map
    (fun j ↦
      let order := orders.getD j 0
      (List.range row.size).foldl
        (fun acc k ↦
          acc + mulLowXWith lowCtx order
            (rowGet row k) (rowGet (M.getD k #[]) j)) 0) |>.toArray

/-- Matrix product with independent output-column truncation. -/
def mulTruncColumnWith [Semiring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (orders : Array Nat)
    (A B : PolynomialMatrix F) : PolynomialMatrix F :=
  A.map fun row ↦ rowMulMatrixTruncColumnWith lowCtx orders row B

/-- Fuel-bounded Strassen-style matrix product with independent output-column
truncation orders. -/
def mulTruncColumnStrassenWithFuel [Ring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (leafCutoff : Nat) :
    Nat → Array Nat → PolynomialMatrix F → PolynomialMatrix F → PolynomialMatrix F
  | 0, orders, A, B => mulTruncColumnWith lowCtx orders A B
  | fuel + 1, orders, A, B =>
      let n := A.size
      let dimension := multiplicationDimension A B
      if dimension ≤ leafCutoff || dimension ≤ 1 then
        mulTruncColumnWith lowCtx orders A B
      else if
          MatrixWidth A == n && B.size == n && MatrixWidth B == n &&
            n % 2 == 0 then
        let h := n / 2
        let leftOrders := natArraySlice orders 0 h
        let rightOrders := natArraySlice orders h h
        let pairOrders := maxNatArrays leftOrders rightOrders
        let A₁₁ := block A 0 h 0 h
        let A₁₂ := block A 0 h h h
        let A₂₁ := block A h h 0 h
        let A₂₂ := block A h h h h
        let B₁₁ := block B 0 h 0 h
        let B₁₂ := block B 0 h h h
        let B₂₁ := block B h h 0 h
        let B₂₂ := block B h h h h
        let recMul := mulTruncColumnStrassenWithFuel lowCtx leafCutoff fuel
        let M₁ := recMul pairOrders (add A₁₁ A₂₂) (add B₁₁ B₂₂)
        let M₂ := recMul pairOrders (add A₂₁ A₂₂) B₁₁
        let M₃ := recMul rightOrders A₁₁ (sub B₁₂ B₂₂)
        let M₄ := recMul leftOrders A₂₂ (sub B₂₁ B₁₁)
        let M₅ := recMul pairOrders (add A₁₁ A₁₂) B₂₂
        let M₆ := recMul rightOrders (sub A₂₁ A₁₁) (add B₁₁ B₁₂)
        let M₇ := recMul leftOrders (sub A₁₂ A₂₂) (add B₂₁ B₂₂)
        let C₁₁ := add (sub (add M₁ M₄) M₅) M₇
        let C₁₂ := add M₃ M₅
        let C₂₁ := add M₂ M₄
        let C₂₂ := add (sub (add M₁ M₃) M₂) M₆
        truncateColumns orders (joinSquareBlocks h C₁₁ C₁₂ C₂₁ C₂₂)
      else
        let paddedSize := nextPowerOfTwoAtLeast dimension
        let paddedOrders := natArraySlice orders 0 paddedSize
        let product := mulTruncColumnStrassenWithFuel lowCtx leafCutoff fuel
          paddedOrders (padSquare paddedSize A) (padSquare paddedSize B)
        trimShape A.size (MatrixWidth B) product

/-- Strassen-style matrix product with independent output-column truncation
orders and conservative default fuel. -/
def mulTruncColumnStrassenWith [Ring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (leafCutoff : Nat)
    (orders : Array Nat) (A B : PolynomialMatrix F) : PolynomialMatrix F :=
  let n := multiplicationDimension A B
  mulTruncColumnStrassenWithFuel lowCtx leafCutoff (n + 1) orders A B

/-- Row-by-matrix product with per-output-entry degree caps inferred from input
degree profiles.  This reconstructs the exact row product while routing every
term through low-product multiplication. -/
def rowMulMatrixBoundedWith [Semiring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (row : PolynomialRow F)
    (M : PolynomialMatrix F) : PolynomialRow F :=
  (List.range (MatrixWidth M)).map
    (fun j ↦
      let order := rowMulMatrixEntryCoeffCap row M j
      (List.range row.size).foldl
        (fun acc k ↦
          acc + mulLowXWith lowCtx order
            (rowGet row k) (rowGet (M.getD k #[]) j)) 0) |>.toArray

/-- Matrix product reconstructed from inferred per-entry degree caps.  Recursive
composition uses this only as its small-leaf and fuel-exhausted fallback. -/
def mulBoundedWith [Semiring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (A B : PolynomialMatrix F) :
    PolynomialMatrix F :=
  A.map fun row ↦ rowMulMatrixBoundedWith lowCtx row B

/-- Fuel-bounded Strassen-style matrix product.

Small inputs and exhausted fuel use the bounded row-column product.  Larger
rectangular or odd-sized inputs are padded to square power-of-two shape, routed
through the recursive block product, and trimmed back to the requested output
shape. -/
def mulStrassenWithFuel [Ring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (leafCutoff : Nat) :
    Nat → PolynomialMatrix F → PolynomialMatrix F → PolynomialMatrix F
  | 0, A, B => mulBoundedWith lowCtx A B
  | fuel + 1, A, B =>
      let n := A.size
      let dimension := multiplicationDimension A B
      if dimension ≤ leafCutoff || dimension ≤ 1 then
        mulBoundedWith lowCtx A B
      else if
          MatrixWidth A == n && B.size == n && MatrixWidth B == n &&
            n % 2 == 0 then
        let h := n / 2
        let A₁₁ := block A 0 h 0 h
        let A₁₂ := block A 0 h h h
        let A₂₁ := block A h h 0 h
        let A₂₂ := block A h h h h
        let B₁₁ := block B 0 h 0 h
        let B₁₂ := block B 0 h h h
        let B₂₁ := block B h h 0 h
        let B₂₂ := block B h h h h
        let recMul := mulStrassenWithFuel lowCtx leafCutoff fuel
        let M₁ := recMul (add A₁₁ A₂₂) (add B₁₁ B₂₂)
        let M₂ := recMul (add A₂₁ A₂₂) B₁₁
        let M₃ := recMul A₁₁ (sub B₁₂ B₂₂)
        let M₄ := recMul A₂₂ (sub B₂₁ B₁₁)
        let M₅ := recMul (add A₁₁ A₁₂) B₂₂
        let M₆ := recMul (sub A₂₁ A₁₁) (add B₁₁ B₁₂)
        let M₇ := recMul (sub A₁₂ A₂₂) (add B₂₁ B₂₂)
        let C₁₁ := add (sub (add M₁ M₄) M₅) M₇
        let C₁₂ := add M₃ M₅
        let C₂₁ := add M₂ M₄
        let C₂₂ := add (sub (add M₁ M₃) M₂) M₆
        joinSquareBlocks h C₁₁ C₁₂ C₂₁ C₂₂
      else
        let paddedSize := nextPowerOfTwoAtLeast dimension
        let product := mulStrassenWithFuel lowCtx leafCutoff fuel
          (padSquare paddedSize A) (padSquare paddedSize B)
        trimShape A.size (MatrixWidth B) product

/-- Strassen-style matrix product with a conservative default fuel. -/
def mulStrassenWith [Ring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (leafCutoff : Nat)
    (A B : PolynomialMatrix F) : PolynomialMatrix F :=
  let n := multiplicationDimension A B
  mulStrassenWithFuel lowCtx leafCutoff (n + 1) A B

/-- Executable modular-equation row predicate. -/
def rowSatisfiesModularBool [Field F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (row : PolynomialRow F) (M : PolynomialMatrix F)
    (moduli : Array (CPolynomial F)) : Bool :=
  (rowMulMatrixModDiagonalWith mulCtx modCtx row M moduli).all fun p ↦ p == 0

/-- Shifted row-degree profile for all rows. -/
def shiftedRowDegreeProfile [Zero F] [BEq F] (M : PolynomialMatrix F)
    (shift : Array Nat) : Array (Option Nat) :=
  M.map fun row ↦ rowShiftedDegree? row shift

/-- Candidate row selected by least-shifted-degree scanning. -/
structure RowChoice (F : Type*) [Zero F] where
  index : Nat
  row : PolynomialRow F
  degree : Nat

/-- Tie-breaking order for least-shifted-degree row selection. -/
def betterRowChoice [Zero F] (candidate current : RowChoice F) : Bool :=
  candidate.degree < current.degree ||
    (candidate.degree == current.degree && candidate.index < current.index)

/-- One left-to-right scan step for least-shifted-degree row selection. -/
def leastShiftedDegreeRowStep? [Zero F] [BEq F]
    (M : PolynomialMatrix F) (shift : Array Nat)
    (best : Option (RowChoice F)) (i : Nat) : Option (RowChoice F) :=
  let row := M.getD i #[]
  match rowShiftedDegree? row shift with
  | none => best
  | some degree =>
      let candidate : RowChoice F := { index := i, row := row, degree := degree }
      match best with
      | none => some candidate
      | some current =>
          if betterRowChoice candidate current then some candidate else best

/-- Scan row indices for the best least-shifted-degree candidate. -/
def leastShiftedDegreeChoice? [Zero F] [BEq F]
    (M : PolynomialMatrix F) (shift : Array Nat) : Option (RowChoice F) :=
  (List.range M.size).foldl (leastShiftedDegreeRowStep? M shift) none

/-- Select a nonzero row of least shifted degree. -/
def leastShiftedDegreeRow? [Zero F] [BEq F]
    (M : PolynomialMatrix F) (shift : Array Nat) :
    Option (PolynomialRow F) :=
  (leastShiftedDegreeChoice? M shift).map fun choice ↦ choice.row

end PolynomialMatrix

end CompPoly
