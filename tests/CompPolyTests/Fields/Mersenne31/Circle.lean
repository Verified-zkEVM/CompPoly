/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Lacombe
-/
module

public import CompPoly.Fields.Mersenne31.Circle
public meta import CompPoly.Fields.Mersenne31.Circle

/-!
# Mersenne31 Circle Domain Tests

Public-API proofs and executable regression checks for the STWO-style Mersenne31
circle-domain skeleton. Ordinary imports deliberately do not expose implementation bodies.
-/

public section

namespace Mersenne31.Circle

example : OnCircle generatorX generatorY := generator_onCircle

example : generatorX = 2 := generatorX_eq

example : generatorY = 1268011823 := generatorY_eq

example : generator.x = 2 := generator_x

example : generator.y = 1268011823 := generator_y

example (p q r : Point) : (p + q) + r = p + (q + r) := add_assoc p q r

example (p : Point) : Point.nsmul p 0 = 0 := by
  fail_if_success rfl
  simp only [Point.nsmul_zero]

example (p : Point) : (-p).x = p.x := by
  simp only [Point.conjugate_x]

example (c : Coset) : (CircleDomain.new c).halfCoset = c := by
  simp only [CircleDomain.new_halfCoset]

example : OnCircle (generator + generator).x (generator + generator).y :=
  (generator + generator).onCircle

example : OnCircle (Point.antipode generator).x (Point.antipode generator).y :=
  (Point.antipode generator).onCircle

#guard logOrder = 31
#guard order = 2147483648

example : CirclePointIndex.toPoint 0 = 0 := by
  simp

example : CirclePointIndex.toPoint CirclePointIndex.generator = generator := by
  simp

example (p : Point) (n : Nat) : Point.nsmul p n = nsmulRec n p :=
  Point.nsmul_eq_nsmulRec p n

#guard (List.range 64).all fun n =>
  let actual := Point.nsmul generator n
  let expected := nsmulRec n generator
  actual.x == expected.x && actual.y == expected.y

#guard (CirclePointIndex.toPoint (-1)).x = generator.x
#guard (CirclePointIndex.toPoint (-1)).y = -generator.y

example : CirclePointIndex.subgroupGen 0 = 0 := by
  simp

example : CirclePointIndex.subgroupGen logOrder = CirclePointIndex.generator := by
  simp

meta section

/-- A small half-coset fixture for executable regression checks. -/
def smallHalfCoset : Coset :=
  Coset.halfOdds 3 (by decide)

#guard smallHalfCoset.size = 8

example : smallHalfCoset.indexAt 0 = smallHalfCoset.initialIndex := by
  simp [smallHalfCoset]

example (i : Nat) : smallHalfCoset.conjugate.indexAt i = -smallHalfCoset.indexAt i := by
  simp [smallHalfCoset]

/-- A small circle-domain fixture built from `smallHalfCoset`. -/
def smallDomain : CircleDomain :=
  CircleDomain.new smallHalfCoset

#guard smallDomain.logSize = 4
#guard smallDomain.size = 16

example (i : Nat) :
    smallDomain.indexAt (smallHalfCoset.size + i) = -smallHalfCoset.indexAt i := by
  simpa only [smallDomain, CircleDomain.new_halfCoset] using
    CircleDomain.indexAt_right smallDomain i

/-- A small canonical-coset fixture for domain-shape checks. -/
def smallCanonicCoset : CanonicCoset where
  logSize := 4
  one_le_logSize := by decide
  logSize_succ_le_logOrder := by decide

#guard smallCanonicCoset.coset.logSize = 4
#guard smallCanonicCoset.halfCoset.logSize = 3
#guard smallCanonicCoset.circleDomain.logSize = 4
#guard smallCanonicCoset.circleDomain.size = 16

#guard (smallCanonicCoset.circleDomain.indexAt 0).val = 67108864
#guard (smallCanonicCoset.circleDomain.pointAt 0).x = 1179735656
#guard (smallCanonicCoset.circleDomain.pointAt 0).y = 1241207368

#guard (List.range smallCanonicCoset.circleDomain.size).all fun i =>
  let p := smallCanonicCoset.circleDomain.pointAt i
  p.x ^ 2 + p.y ^ 2 == (1 : Field)

#guard (List.range smallHalfCoset.size).all fun i =>
  let p := smallDomain.pointAt i
  let q := smallDomain.pointAt (smallHalfCoset.size + i)
  p.x == q.x && p.y == -q.y

end

end Mersenne31.Circle
