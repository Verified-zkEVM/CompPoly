/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Univariate.NTT.Barycentric
public meta import CompPoly.Univariate.NTTFast.Coset
public meta import CompPolyTests.Univariate.NTT.Common

/-!
  # NTT Interpolation Tests

  Executable checks for interpolation on an NTT domain and on its cosets: the unplanned and
  planned entry points against Lagrange's formula, the coset transforms' round trip, and the
  closed-form barycentric domain.
-/

public meta section

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace InterpolationTests

open TestCommon

private def D : Domain _root_.KoalaBear.Field := testDomain8

private def vals : Vector _root_.KoalaBear.Field D.n :=
  Vector.ofFn fun i => ((i.1 * i.1 + 3 : Nat) : _root_.KoalaBear.Field)

private def P : NTTFast.Plan _root_.KoalaBear.Field := NTTFast.Plan.ofDomain D

private def shift : _root_.KoalaBear.Field := 3

private def C : NTTFast.CosetPlan _root_.KoalaBear.Field := NTTFast.CosetPlan.ofPlan P shift

/-! ### Interpolation on the domain -/

#guard interpolate D vals == CLagrange.interpolatePow D.omega vals

#guard Array.ofFn (fun k : D.Idx => (interpolate D vals).eval (D.node k)) == vals.toArray

#guard NTTFast.Plan.interpolate P vals == interpolate D vals

/-! ### Interpolation on a coset -/

#guard Coset.forwardImpl D shift (Coset.inverseImpl D shift vals.toArray) == vals.toArray

#guard Array.ofFn (fun k : D.Idx => (Coset.interpolate D shift vals).eval (shift * D.node k)) ==
  vals.toArray

#guard Coset.interpolate D shift vals ==
  CLagrange.interpolate Finset.univ (fun k : D.Idx => shift * D.node k) vals.get

#guard NTTFast.CosetPlan.interpolate C vals == Coset.interpolate D shift vals

#guard
  let p : CPolynomial.Raw _root_.KoalaBear.Field := #[5, 0, 7, 1, 2]
  NTTFast.CosetPlan.forwardImpl C p ==
    Transform.bitRevPermute D (Coset.forwardImpl D shift p)

#guard
  let p : CPolynomial.Raw _root_.KoalaBear.Field := #[5, 0, 7, 1, 2]
  Coset.forwardImpl D shift p == evalOnCoset D shift p

/-! ### Barycentric evaluation on the domain -/

#guard D.barycentric.eval vals.get 12345 ==
  (CLagrange.interpolatePow D.omega vals).eval 12345

#guard (List.finRange D.n).all fun k => D.barycentric.eval vals.get (D.node k) == vals.get k

#guard (List.finRange D.n).all fun i =>
  D.barycentric.weights i ==
    ((Finset.univ.erase i).prod fun j => (D.node i - D.node j)⁻¹)

end InterpolationTests
end NTT
end CPolynomial
end CompPoly
