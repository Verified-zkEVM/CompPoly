/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/
import CompPoly.Univariate.Basic

/-!
  # Lagrange Interpolation

  This file defines Lagrange interpolation for univariate polynomials. Given evaluation points
  at powers of a root of unity `ω`, it constructs the unique polynomial of degree `n-1` that
  interpolates the given values.
-/
namespace CompPoly

namespace CPolynomial

namespace Lagrange

/-- The nodal polynomial of degree `n` with roots at `ω^i` for `i = 0, 1, ..., n-1`.

  This is the unique monic polynomial of degree `n` that vanishes at all `n`-th roots of unity
  (when `ω` is a primitive `n`-th root of unity). -/
def nodal {R : Type*} [Ring R] [BEq R] (n : ℕ) (ω : R) : CPolynomial R :=
  (List.range n).foldl (fun acc i => acc.mul (X - C (ω ^ i))) (C 1)

/-- Produces the unique polynomial of degree at most n-1 that equals r[i] at ω^i
    for i = 0, 1, ..., n-1.

    Uses Lagrange interpolation: p(X) = Σᵢ rᵢ · Lᵢ(X)
    where Lᵢ(X) = ∏_{j≠i} (X - ωʲ) / (ωⁱ - ωʲ). -/
def interpolate {R : Type*} [Field R] [BEq R] (n : ℕ) (ω : R) (r : Vector R n) : CPolynomial R :=
  -- Lagrange interpolation: p(X) = Σᵢ rᵢ · Lᵢ(X)
  -- where Lᵢ(X) = ∏_{j≠i} (X - ωʲ) / (ωⁱ - ωʲ)
  (List.finRange n).foldl (fun acc i =>
    let Li := lagrangeBasis n ω i
    acc + smul (r.get i) Li
  ) 0
where
  /-- The i-th Lagrange basis polynomial Lᵢ(X) = ∏_{j≠i} (X - ωʲ) / (ωⁱ - ωʲ) -/
  lagrangeBasis (n : ℕ) (ω : R) (i : Fin n) : CPolynomial R :=
    let numerator := (List.finRange n).foldl (fun acc j =>
      if i = j then acc
      else acc.mul (X - C (ω ^ j.val))
    ) (C 1)
    let denominator := (List.finRange n).foldl (fun acc j =>
      if i = j then acc
      else acc * (ω ^ i.val - ω ^ j.val)
    ) 1
    smul denominator⁻¹ numerator

end Lagrange

end CPolynomial

end CompPoly
