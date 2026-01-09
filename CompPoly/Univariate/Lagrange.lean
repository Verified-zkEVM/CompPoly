/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/

import CompPoly.Univariate.Basic

namespace CompPoly
namespace CPolynomial
namespace Lagrange

-- unique polynomial of degree n that has nodes at ω^i for i = 0, 1, ..., n-1
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
