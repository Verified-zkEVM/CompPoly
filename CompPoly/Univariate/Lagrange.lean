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
def nodal {R : Type*} [Ring R] (n : ℕ) (ω : R) : CPolynomial R := sorry
  -- .mk (Array.Range n |>.map (fun i => ω^i))

/--
This function produces the polynomial which is of degree n and is equal to r i at ω^i for i = 0, 1,
..., n-1.
-/
def interpolate {R : Type*} [Ring R] (n : ℕ) (ω : R) (r : Vector R n) : CPolynomial R := sorry
  -- .mk (Array.finRange n |>.map (fun i => r[i])) * nodal n ω

end Lagrange

end CPolynomial

end CompPoly
