/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Lacombe
-/
module

public meta import CompPoly.Fields.Mersenne31.Circle

/-!
# Mersenne31 Circle Domain Tests

Regression checks for the STWO-style Mersenne31 circle-domain skeleton.
-/

public meta section

namespace Mersenne31.Circle

example : OnCircle generatorX generatorY := generator_onCircle

example : generator.x = 2 := rfl

example : generator.y = 1268011823 := rfl

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

example : CirclePointIndex.subgroupGen 0 = 0 := by
  simp

example : CirclePointIndex.subgroupGen logOrder = CirclePointIndex.generator := by
  simp

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
  change smallDomain.indexAt (smallDomain.halfCoset.size + i) = -smallDomain.halfCoset.indexAt i
  exact CircleDomain.indexAt_right smallDomain i

/-- A small canonical-coset fixture for domain-shape checks. -/
def smallCanonicCoset : CanonicCoset where
  logSize := 4
  one_le_logSize := by decide
  logSize_succ_le_logOrder := by decide

#guard smallCanonicCoset.coset.logSize = 4
#guard smallCanonicCoset.halfCoset.logSize = 3
#guard smallCanonicCoset.circleDomain.logSize = 4
#guard smallCanonicCoset.circleDomain.size = 16

end Mersenne31.Circle
