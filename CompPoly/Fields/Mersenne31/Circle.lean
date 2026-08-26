/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Lacombe
-/
module

public import CompPoly.Fields.Mersenne31.Basic
public meta import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring

/-!
# Mersenne31 Circle Domains

This module mirrors the structural circle-domain layer used by STWO over the
Mersenne31 field. It records the circle equation, the STWO M31 circle generator,
index arithmetic modulo the circle order, and the coset/domain shapes used by
canonical circle domains.

`CirclePointIndex.toPoint` currently interprets an index via `Point.nsmul` on the
canonical natural representative `i.val`. A follow-on PR should prove generator
order `2^31` and that `toPoint` is a group homomorphism on `CirclePointIndex`.
-/

@[expose] public section

namespace Mersenne31
namespace Circle

/-- The canonical Mersenne31 field used by the circle-domain skeleton. -/
abbrev Field := Mersenne31.Field

/-- Predicate for points on the circle `x^2 + y^2 = 1`. -/
def OnCircle (x y : Field) : Prop :=
  x ^ 2 + y ^ 2 = 1

/-- A point on the Mersenne31 circle. -/
structure Point where
  x : Field
  y : Field
  onCircle : OnCircle x y

namespace Point

/-- Two circle points are equal when both coordinates are equal. -/
@[ext]
theorem ext {p q : Point} (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  cases p
  cases q
  simp_all

/-- The identity point of the circle group. -/
def zero : Point where
  x := 1
  y := 0
  onCircle := by
    simp [OnCircle]

/-- The circle-group inverse, equal to complex conjugation. -/
def conjugate (p : Point) : Point where
  x := p.x
  y := -p.y
  onCircle := by
    simpa [OnCircle, pow_two] using p.onCircle

/-- The antipodal point. Reserved for follow-on circle-group lemmas. -/
def antipode (p : Point) : Point where
  x := -p.x
  y := -p.y
  onCircle := by
    simpa [OnCircle, pow_two] using p.onCircle

/-- Circle-group addition, written as multiplication of complex coordinates. -/
def add (p q : Point) : Point where
  x := p.x * q.x - p.y * q.y
  y := p.x * q.y + p.y * q.x
  onCircle := by
    dsimp [OnCircle]
    calc
      (p.x * q.x - p.y * q.y) ^ 2 + (p.x * q.y + p.y * q.x) ^ 2 =
          (p.x ^ 2 + p.y ^ 2) * (q.x ^ 2 + q.y ^ 2) := by
        ring
      _ = 1 := by
        rw [p.onCircle, q.onCircle]
        ring

instance : Zero Point := ⟨zero⟩

instance : Neg Point := ⟨conjugate⟩

instance : Add Point := ⟨add⟩

/-- Repeated circle-group addition. -/
def nsmul (p : Point) : Nat → Point
  | 0 => 0
  | n + 1 => nsmul p n + p

/-- The identity point has x-coordinate one. -/
@[simp]
theorem zero_x : (0 : Point).x = 1 := rfl

/-- The identity point has y-coordinate zero. -/
@[simp]
theorem zero_y : (0 : Point).y = 0 := rfl

/-- Conjugation preserves the x-coordinate. -/
@[simp]
theorem conjugate_x (p : Point) : (-p).x = p.x := rfl

/-- Conjugation negates the y-coordinate. -/
@[simp]
theorem conjugate_y (p : Point) : (-p).y = -p.y := rfl

/-- The identity point is a left identity for circle addition. -/
@[simp]
theorem zero_add (p : Point) : (0 : Point) + p = p := by
  obtain ⟨px, py, hp⟩ := p
  apply Point.ext
  · change (1 : Field) * px - (0 : Field) * py = px
    ring
  · change (1 : Field) * py + (0 : Field) * px = py
    ring

end Point

/-- STWO's Mersenne31 circle generator x-coordinate. -/
def generatorX : Field := 2

/-- STWO's Mersenne31 circle generator y-coordinate. -/
def generatorY : Field := 1268011823

/-- STWO's Mersenne31 circle generator lies on `x^2 + y^2 = 1`. -/
theorem generator_onCircle : OnCircle generatorX generatorY := by
  change ((2 : Field) ^ 2 + (1268011823 : Field) ^ 2 = 1)
  decide

/-- STWO's generator for the Mersenne31 circle group. -/
def generator : Point where
  x := generatorX
  y := generatorY
  onCircle := generator_onCircle

/-- The log order of STWO's Mersenne31 circle group. -/
@[reducible]
def logOrder : Nat := 31

/-- The order of the Mersenne31 circle-index group, `2^31`. -/
@[reducible]
def order : Nat := 2 ^ logOrder

/-- Integer index for multiples of the Mersenne31 circle generator. -/
abbrev CirclePointIndex := ZMod order

namespace CirclePointIndex

/-- The distinguished generator index. -/
def generator : CirclePointIndex := 1

/-- Subgroup generator index for the subgroup of order `2^logSize`. For
`logSize ≤ logOrder` this is the canonical generator of that subgroup; callers
that rely on the bound (`Coset.new`, `odds`, `halfOdds`) carry it themselves. -/
def subgroupGen (logSize : Nat) : CirclePointIndex :=
  (2 ^ (logOrder - logSize) : Nat)

/-- Interpret an index as a repeated multiple of the STWO circle generator.

Uses the canonical natural representative of `i`; see the module docstring for
the planned homomorphism proof. -/
def toPoint (i : CirclePointIndex) : Point :=
  Point.nsmul Circle.generator i.val

/-- Index zero maps to the circle identity. -/
@[simp]
theorem toPoint_zero : toPoint 0 = 0 := by
  unfold toPoint
  simp [Point.nsmul]

/-- The distinguished index maps to the STWO circle generator. -/
@[simp]
theorem toPoint_generator : toPoint CirclePointIndex.generator = Circle.generator := by
  unfold toPoint CirclePointIndex.generator Circle.generator
  change Point.nsmul Circle.generator (0 + 1) = Circle.generator
  simp [Point.nsmul, Point.zero_add]

/-- The subgroup generator for the trivial subgroup is zero modulo the circle order. -/
@[simp]
theorem subgroupGen_zero : subgroupGen 0 = 0 := by
  change ((2 ^ (logOrder - 0) : Nat) : ZMod order) = 0
  simp [order]

/-- The full-order subgroup generator is the distinguished generator index. -/
@[simp]
theorem subgroupGen_logOrder : subgroupGen logOrder = generator := by
  simp [subgroupGen, generator]

end CirclePointIndex

/-- A coset of circle indices with a fixed additive step. -/
structure Coset where
  initialIndex : CirclePointIndex
  stepSize : CirclePointIndex
  logSize : Nat
  logSize_le_logOrder : logSize ≤ logOrder

namespace Coset

/-- Create a coset with STWO's subgroup step for `logSize`. -/
def new (initialIndex : CirclePointIndex) (logSize : Nat) (hlogSize : logSize ≤ logOrder) :
    Coset where
  initialIndex := initialIndex
  stepSize := CirclePointIndex.subgroupGen logSize
  logSize := logSize
  logSize_le_logOrder := hlogSize

/-- The additive subgroup of size `2^logSize`. -/
def subgroup (logSize : Nat) (hlogSize : logSize ≤ logOrder) : Coset :=
  new 0 logSize hlogSize

/-- The STWO coset `G_{2n} + <G_n>`. -/
def odds (logSize : Nat) (hlogSize : logSize + 1 ≤ logOrder) : Coset :=
  new (CirclePointIndex.subgroupGen (logSize + 1)) logSize
    (Nat.le_trans (Nat.le_succ logSize) hlogSize)

/-- The STWO coset `G_{4n} + <G_n>`, whose conjugate completes `odds (logSize + 1)`. -/
def halfOdds (logSize : Nat) (hlogSize : logSize + 2 ≤ logOrder) : Coset :=
  new (CirclePointIndex.subgroupGen (logSize + 2)) logSize
    (Nat.le_trans (Nat.le_add_right logSize 2) hlogSize)

/-- Number of indices in the coset. -/
def size (c : Coset) : Nat :=
  2 ^ c.logSize

/-- The `i`th index in the coset order. -/
def indexAt (c : Coset) (i : Nat) : CirclePointIndex :=
  c.initialIndex + c.stepSize * (i : CirclePointIndex)

/-- The circle point at the `i`th coset index. -/
def pointAt (c : Coset) (i : Nat) : Point :=
  CirclePointIndex.toPoint (c.indexAt i)

/-- The conjugate coset `-initial - <step>`. -/
def conjugate (c : Coset) : Coset where
  initialIndex := -c.initialIndex
  stepSize := -c.stepSize
  logSize := c.logSize
  logSize_le_logOrder := c.logSize_le_logOrder

/-- The first coset index is its initial index. -/
@[simp]
theorem indexAt_zero (c : Coset) : c.indexAt 0 = c.initialIndex := by
  simp [indexAt]

/-- Successive coset indices differ by the fixed step size. -/
@[simp]
theorem indexAt_succ (c : Coset) (i : Nat) :
    c.indexAt (i + 1) = c.indexAt i + c.stepSize := by
  simp [indexAt, Nat.cast_add, Nat.cast_one]
  ring

/-- Conjugation preserves the coset log size. -/
@[simp]
theorem conjugate_logSize (c : Coset) : c.conjugate.logSize = c.logSize := rfl

/-- The conjugate coset starts at the negated initial index. -/
@[simp]
theorem conjugate_initialIndex (c : Coset) :
    c.conjugate.initialIndex = -c.initialIndex := rfl

/-- The conjugate coset uses the negated step size. -/
@[simp]
theorem conjugate_stepSize (c : Coset) : c.conjugate.stepSize = -c.stepSize := rfl

/-- Each conjugate-coset index is the negation of the corresponding original index. -/
@[simp]
theorem conjugate_indexAt (c : Coset) (i : Nat) :
    c.conjugate.indexAt i = -c.indexAt i := by
  simp [indexAt, conjugate]
  ring

end Coset

/-- A valid STWO circle domain: a half coset followed by its conjugate. -/
structure CircleDomain where
  halfCoset : Coset

namespace CircleDomain

/-- Construct a circle domain from the half coset. -/
def new (halfCoset : Coset) : CircleDomain where
  halfCoset := halfCoset

/-- Domain log size. A domain contains a half coset and its conjugate. -/
def logSize (D : CircleDomain) : Nat :=
  D.halfCoset.logSize + 1

/-- Number of indices in the domain. -/
def size (D : CircleDomain) : Nat :=
  2 ^ D.logSize

/-- The `i`th domain index: first the half coset, then the conjugate coset. -/
def indexAt (D : CircleDomain) (i : Nat) : CirclePointIndex :=
  if i < D.halfCoset.size then
    D.halfCoset.indexAt i
  else
    D.halfCoset.conjugate.indexAt (i - D.halfCoset.size)

/-- The circle point at the `i`th domain index. -/
def pointAt (D : CircleDomain) (i : Nat) : Point :=
  CirclePointIndex.toPoint (D.indexAt i)

/-- A circle domain has twice as many indices as its half coset. -/
@[simp]
theorem size_eq_two_mul_halfSize (D : CircleDomain) :
    D.size = 2 * D.halfCoset.size := by
  simp [size, logSize, Coset.size, pow_succ, Nat.mul_comm]

/-- Indices in the first half of a circle domain come from its half coset. -/
@[simp]
theorem indexAt_left (D : CircleDomain) (i : Nat) (hi : i < D.halfCoset.size) :
    D.indexAt i = D.halfCoset.indexAt i := by
  simp [indexAt, hi]

/-- Indices in the second half come from the negated half coset. -/
@[simp]
theorem indexAt_right (D : CircleDomain) (i : Nat) :
    D.indexAt (D.halfCoset.size + i) = -D.halfCoset.indexAt i := by
  have hnot : ¬ D.halfCoset.size + i < D.halfCoset.size := by
    exact Nat.not_lt.mpr (Nat.le_add_right _ _)
  simp [indexAt, hnot, Coset.conjugate_indexAt]

end CircleDomain

/-- A canonical STWO coset `G_{2n} + <G_n>` for `1 ≤ logSize < logOrder`. -/
structure CanonicCoset where
  logSize : Nat
  one_le_logSize : 1 ≤ logSize
  logSize_succ_le_logOrder : logSize + 1 ≤ logOrder

namespace CanonicCoset

/-- The full canonical coset `G_{2n} + <G_n>`. -/
def coset (c : CanonicCoset) : Coset :=
  Coset.odds c.logSize c.logSize_succ_le_logOrder

/-- The half coset used to form the canonical circle domain. -/
def halfCoset (c : CanonicCoset) : Coset :=
  Coset.halfOdds (c.logSize - 1) (by
    have hEq : c.logSize - 1 + 2 = c.logSize + 1 := by
      have hOne : 1 ≤ c.logSize := c.one_le_logSize
      omega
    rw [hEq]
    exact c.logSize_succ_le_logOrder)

/-- The canonical circle domain with the same log size. -/
def circleDomain (c : CanonicCoset) : CircleDomain :=
  CircleDomain.new c.halfCoset

/-- The canonical circle domain preserves the canonical coset log size. -/
@[simp]
theorem circleDomain_logSize (c : CanonicCoset) : c.circleDomain.logSize = c.logSize := by
  unfold circleDomain CircleDomain.new CircleDomain.logSize halfCoset Coset.halfOdds Coset.new
  dsimp
  have hOne : 1 ≤ c.logSize := c.one_le_logSize
  omega

/-- The canonical circle domain has `2^logSize` indices. -/
@[simp]
theorem circleDomain_size (c : CanonicCoset) : c.circleDomain.size = 2 ^ c.logSize := by
  simp [CircleDomain.size]

end CanonicCoset

end Circle
end Mersenne31
