/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Lacombe
-/
module

public import CompPoly.Fields.Mersenne31.Circle
public meta import CompPoly.Fields.Mersenne31.Circle
import Mathlib.Tactic.Ring

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

example (c : Coset) (_h : c.indexAt 600 = 0) : True := by
  simp at _h
  trivial

example (c : Coset) :
    c.indexAt 600 = c.initialIndex + c.stepSize * (600 : CirclePointIndex) := by
  simp

example (c : Coset) (i : Nat) : c.conjugate.indexAt (i + 1) = -c.indexAt (i + 1) := by
  simp

example (c : Coset) (i : Nat) :
    c.conjugate.indexAt (i + 1) = -(c.indexAt i + c.stepSize) := by
  rw [Coset.conjugate_indexAt, Coset.indexAt_succ]

example (p q : Point) : (p + q).x = p.x * q.x - p.y * q.y := by
  simp only [Point.add_x]

example (p q : Point) : (p + q).y = p.x * q.y + p.y * q.x := by
  simp only [Point.add_y]

example (p : Point) : p.antipode.antipode = p := by
  apply Point.ext
  · simp only [Point.antipode_x, neg_neg]
  · simp only [Point.antipode_y, neg_neg]

example (p : Point) : p + (-p) = 0 := by
  apply Point.ext
  · simpa only [Point.add_x, Point.conjugate_x, Point.conjugate_y, Point.zero_x,
      mul_neg, sub_neg_eq_add, OnCircle, pow_two] using p.onCircle
  · simp only [Point.add_y, Point.conjugate_x, Point.conjugate_y, Point.zero_y]
    ring

example (c : Coset) : c.size = 2 ^ c.logSize := by
  simp only [Coset.size_eq]

example (i : CirclePointIndex) (n : Nat) (h : n ≤ logOrder) :
    (Coset.new i n h).initialIndex = i ∧
      (Coset.new i n h).stepSize = CirclePointIndex.subgroupGen n ∧
      (Coset.new i n h).logSize = n := by
  simp only [Coset.new_initialIndex, Coset.new_stepSize, Coset.new_logSize, and_self]

example (n : Nat) (h : n ≤ logOrder) :
    (Coset.subgroup n h).initialIndex = 0 ∧
      (Coset.subgroup n h).stepSize = CirclePointIndex.subgroupGen n ∧
      (Coset.subgroup n h).logSize = n := by
  simp only [Coset.subgroup_eq, Coset.new_initialIndex, Coset.new_stepSize,
    Coset.new_logSize, and_self]

example (n : Nat) (h : n + 1 ≤ logOrder) :
    (Coset.odds n h).initialIndex = CirclePointIndex.subgroupGen (n + 1) ∧
      (Coset.odds n h).stepSize = CirclePointIndex.subgroupGen n ∧
      (Coset.odds n h).logSize = n := by
  simp only [Coset.odds_eq, Coset.new_initialIndex, Coset.new_stepSize,
    Coset.new_logSize, and_self]

example (n : Nat) (h : n + 2 ≤ logOrder) :
    (Coset.halfOdds n h).initialIndex = CirclePointIndex.subgroupGen (n + 2) ∧
      (Coset.halfOdds n h).stepSize = CirclePointIndex.subgroupGen n ∧
      (Coset.halfOdds n h).logSize = n := by
  simp only [Coset.halfOdds_eq, Coset.new_initialIndex, Coset.new_stepSize,
    Coset.new_logSize, and_self]

example (i : CirclePointIndex) : CirclePointIndex.toPoint i = Point.nsmul generator i.val := by
  rw [CirclePointIndex.toPoint_def]

example (c : Coset) (i : Nat) : c.pointAt i =
    Point.nsmul generator (c.initialIndex + c.stepSize * (i : CirclePointIndex)).val := by
  rw [Coset.pointAt_def, CirclePointIndex.toPoint_def, Coset.indexAt_eq]

example (D : CircleDomain) : D.logSize = D.halfCoset.logSize + 1 := by
  rw [CircleDomain.logSize_eq]

example (D : CircleDomain) : D.size = 2 ^ (D.halfCoset.logSize + 1) := by
  rw [CircleDomain.size_eq, CircleDomain.logSize_eq]

example (D : CircleDomain) : D.indexAt 0 = D.halfCoset.initialIndex := by
  rw [CircleDomain.indexAt_left, Coset.indexAt_zero]
  rw [Coset.size_eq]
  exact pow_pos (by decide) _

example (D : CircleDomain) : D.indexAt (D.halfCoset.size + 0) =
    -D.halfCoset.initialIndex := by
  simp

example (D : CircleDomain) : D.indexAt D.halfCoset.size = -D.halfCoset.initialIndex := by
  simp

example (D : CircleDomain) (i : Nat) : D.pointAt i =
    Point.nsmul generator (if i < D.halfCoset.size then D.halfCoset.indexAt i
      else D.halfCoset.conjugate.indexAt (i - D.halfCoset.size)).val := by
  rw [CircleDomain.pointAt_def, CirclePointIndex.toPoint_def, CircleDomain.indexAt_def]

example (c : CanonicCoset) : c.coset.stepSize = CirclePointIndex.subgroupGen c.logSize := by
  rw [CanonicCoset.coset_eq, Coset.odds_eq, Coset.new_stepSize]

example (c : CanonicCoset) :
    c.halfCoset.stepSize = CirclePointIndex.subgroupGen (c.logSize - 1) := by
  rw [CanonicCoset.halfCoset_eq, Coset.halfOdds_eq, Coset.new_stepSize]

example (c : CanonicCoset) : c.circleDomain.halfCoset = c.halfCoset := by
  rw [CanonicCoset.circleDomain_eq, CircleDomain.new_halfCoset]

example (c : CanonicCoset) : c.circleDomain.logSize = c.logSize := by simp

example (c : CanonicCoset) : c.circleDomain.size = 2 ^ c.logSize := by simp

example : OnCircle (generator + generator).x (generator + generator).y :=
  (generator + generator).onCircle

example : OnCircle (Point.antipode generator).x (Point.antipode generator).y :=
  (Point.antipode generator).onCircle

#guard logOrder = 31
#guard order = 2147483648
#guard ((2147483648 : Nat) : CirclePointIndex) = 0

example : CirclePointIndex.generator = 1 := by simp

example : CirclePointIndex.subgroupGen 5 = ((2 ^ 26 : Nat) : CirclePointIndex) := by
  rw [CirclePointIndex.subgroupGen_eq]
  rfl

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

-- Pin both half-order and full-order behavior, independently of reduction modulo the index order.
#guard (Point.nsmul generator (2 ^ 30)).x = -1
#guard (Point.nsmul generator (2 ^ 30)).y = 0
#guard (Point.nsmul generator (2 ^ 31)).x = 1
#guard (Point.nsmul generator (2 ^ 31)).y = 0
#guard (CirclePointIndex.toPoint ((2 ^ 30 : Nat) : CirclePointIndex)).x = -1
#guard (CirclePointIndex.toPoint ((2 ^ 30 : Nat) : CirclePointIndex)).y = 0

example : CirclePointIndex.subgroupGen 0 = 0 := by
  simp

example : CirclePointIndex.subgroupGen logOrder = CirclePointIndex.generator := by
  simp

meta section

/-- A small half-coset fixture for executable regression checks. -/
def smallHalfCoset : Coset :=
  Coset.halfOdds 3 (by decide)

#guard smallHalfCoset.size = 8
#guard smallHalfCoset.stepSize.val = 268435456

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
#guard (smallCanonicCoset.circleDomain.indexAt 1).val = 335544320
#guard (smallCanonicCoset.circleDomain.pointAt 1).x = 1415090252
#guard (smallCanonicCoset.circleDomain.pointAt 1).y = 2112881577

#guard ((List.range 16).map fun i =>
  let p := smallCanonicCoset.circleDomain.pointAt i
  (p.x, p.y)).eraseDups.length = 16

#guard ((List.range 16).map fun i => (smallCanonicCoset.circleDomain.indexAt i).val).mergeSort
    (fun a b => decide (a ≤ b)) ==
  ((List.range 16).map fun i => (smallCanonicCoset.coset.indexAt i).val).mergeSort
    (fun a b => decide (a ≤ b))

#guard (List.range smallCanonicCoset.circleDomain.size).all fun i =>
  let p := smallCanonicCoset.circleDomain.pointAt i
  p.x ^ 2 + p.y ^ 2 == (1 : Field)

#guard (List.range smallHalfCoset.size).all fun i =>
  let p := smallDomain.pointAt i
  let q := smallDomain.pointAt (smallHalfCoset.size + i)
  p.x == q.x && p.y == -q.y

end

end Mersenne31.Circle
