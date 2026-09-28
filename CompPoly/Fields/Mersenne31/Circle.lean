/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Lacombe
-/
module

public import CompPoly.Fields.Mersenne31.Basic
meta import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

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

public section

namespace Mersenne31
namespace Circle

/-- The canonical Mersenne31 field used by the circle-domain skeleton. -/
abbrev Field := Mersenne31.Field

/-- Predicate for points on the circle `x^2 + y^2 = 1`. -/
@[expose]
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

instance : AddSemigroup Point where
  add := Point.add
  add_assoc p q r := by
    apply Point.ext
    · change (p.x * q.x - p.y * q.y) * r.x - (p.x * q.y + p.y * q.x) * r.y =
        p.x * (q.x * r.x - q.y * r.y) - p.y * (q.x * r.y + q.y * r.x)
      ring
    · change (p.x * q.x - p.y * q.y) * r.y + (p.x * q.y + p.y * q.x) * r.x =
        p.x * (q.x * r.y + q.y * r.x) + p.y * (q.x * r.x - q.y * r.y)
      ring

/-- Circle scalar multiplication by binary doubling and addition. -/
def nsmul (p : Point) (n : Nat) : Point :=
  nsmulBinRec n p

/-- Binary scalar multiplication agrees with repeated circle-group addition. -/
theorem nsmul_eq_nsmulRec (p : Point) (n : Nat) : nsmul p n = nsmulRec n p := by
  change nsmulBinRecAuto n p = nsmulRecAuto n p
  rw [nsmulRec_eq_nsmulBinRec]

/-- The zero multiple is the circle identity. -/
@[simp]
theorem nsmul_zero (p : Point) : nsmul p 0 = 0 := by rfl

/-- Increasing the scalar by one adds one copy of the point. -/
theorem nsmul_succ (p : Point) (n : Nat) : nsmul p (n + 1) = nsmul p n + p :=
  nsmulBinRec_succ n p

/-- The identity point has x-coordinate one. -/
@[simp]
theorem zero_x : (0 : Point).x = 1 := by rfl

/-- The identity point has y-coordinate zero. -/
@[simp]
theorem zero_y : (0 : Point).y = 0 := by rfl

/-- Conjugation preserves the x-coordinate. -/
@[simp]
theorem conjugate_x (p : Point) : (-p).x = p.x := by rfl

/-- Conjugation negates the y-coordinate. -/
@[simp]
theorem conjugate_y (p : Point) : (-p).y = -p.y := by rfl

/-- The antipode negates the x-coordinate. -/
@[simp]
theorem antipode_x (p : Point) : p.antipode.x = -p.x := by rfl

/-- The antipode negates the y-coordinate. -/
@[simp]
theorem antipode_y (p : Point) : p.antipode.y = -p.y := by rfl

/-- The x-coordinate of circle addition. -/
@[simp]
theorem add_x (p q : Point) : (p + q).x = p.x * q.x - p.y * q.y := by rfl

/-- The y-coordinate of circle addition. -/
@[simp]
theorem add_y (p q : Point) : (p + q).y = p.x * q.y + p.y * q.x := by rfl

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

/-- The STWO generator's x-coordinate constant is two. -/
@[simp]
theorem generatorX_eq : generatorX = 2 := by rfl

/-- The value of the STWO generator's y-coordinate constant. -/
@[simp]
theorem generatorY_eq : generatorY = 1268011823 := by rfl

/-- STWO's Mersenne31 circle generator lies on `x^2 + y^2 = 1`. -/
theorem generator_onCircle : OnCircle generatorX generatorY := by
  change ((2 : Field) ^ 2 + (1268011823 : Field) ^ 2 = 1)
  decide

/-- STWO's generator for the Mersenne31 circle group. -/
def generator : Point where
  x := generatorX
  y := generatorY
  onCircle := generator_onCircle

/-- The STWO generator has x-coordinate two. -/
@[simp]
theorem generator_x : generator.x = 2 := by rfl

/-- The STWO generator's y-coordinate. -/
@[simp]
theorem generator_y : generator.y = 1268011823 := by rfl

/-- The log order of STWO's Mersenne31 circle group. -/
@[expose, reducible]
def logOrder : Nat := 31

/-- The order of the Mersenne31 circle-index group, `2^31`. -/
@[expose, reducible]
def order : Nat := 2 ^ logOrder

/-- Integer index for multiples of the Mersenne31 circle generator. -/
abbrev CirclePointIndex := ZMod order

namespace CirclePointIndex

/-- The distinguished generator index. -/
def generator : CirclePointIndex := 1

/-- The distinguished generator index is one. -/
@[simp]
theorem generator_eq : generator = 1 := by rfl

/-- Subgroup generator index for the subgroup of order `2^logSize`. For
`logSize ≤ logOrder` this is the canonical generator of that subgroup; callers
that rely on the bound (`Coset.new`, `odds`, `halfOdds`) carry it themselves. -/
def subgroupGen (logSize : Nat) : CirclePointIndex :=
  (2 ^ (logOrder - logSize) : Nat)

/-- The subgroup step is the corresponding power of two modulo the circle order. -/
theorem subgroupGen_eq (logSize : Nat) :
    subgroupGen logSize = ((2 ^ (logOrder - logSize) : Nat) : CirclePointIndex) := by rfl

/-- Interpret an index as a repeated multiple of the STWO circle generator.

Uses the canonical natural representative of `i`; see the module docstring for
the planned homomorphism proof. -/
def toPoint (i : CirclePointIndex) : Point :=
  Point.nsmul Circle.generator i.val

/-- Index interpretation uses the canonical natural representative. -/
theorem toPoint_def (i : CirclePointIndex) :
    toPoint i = Point.nsmul Circle.generator i.val := by rfl

/-- Index zero maps to the circle identity. -/
@[simp]
theorem toPoint_zero : toPoint 0 = 0 := by
  unfold toPoint
  simp

/-- The distinguished index maps to the STWO circle generator. -/
@[simp]
theorem toPoint_generator : toPoint CirclePointIndex.generator = Circle.generator := by
  unfold toPoint CirclePointIndex.generator Circle.generator
  change Point.nsmul Circle.generator (0 + 1) = Circle.generator
  simp only [Point.nsmul_succ, Point.nsmul_zero, Point.zero_add]

/-- Index one maps to the STWO circle generator. -/
@[simp]
theorem toPoint_one : toPoint 1 = Circle.generator := by
  simpa only [generator_eq] using toPoint_generator

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

/-- The coset constructor preserves the initial index. -/
@[simp]
theorem new_initialIndex (i : CirclePointIndex) (n : Nat) (h : n ≤ logOrder) :
    (new i n h).initialIndex = i := by rfl

/-- The coset constructor uses the subgroup generator as its step. -/
@[simp]
theorem new_stepSize (i : CirclePointIndex) (n : Nat) (h : n ≤ logOrder) :
    (new i n h).stepSize = CirclePointIndex.subgroupGen n := by rfl

/-- The coset constructor preserves the log size. -/
@[simp]
theorem new_logSize (i : CirclePointIndex) (n : Nat) (h : n ≤ logOrder) :
    (new i n h).logSize = n := by rfl

/-- The additive subgroup of size `2^logSize`. -/
def subgroup (logSize : Nat) (hlogSize : logSize ≤ logOrder) : Coset :=
  new 0 logSize hlogSize

/-- A subgroup is the coset starting at zero. -/
theorem subgroup_eq (n : Nat) (h : n ≤ logOrder) : subgroup n h = new 0 n h := by rfl

/-- The STWO coset `G_{2n} + <G_n>`. -/
def odds (logSize : Nat) (hlogSize : logSize + 1 ≤ logOrder) : Coset :=
  new (CirclePointIndex.subgroupGen (logSize + 1)) logSize
    (Nat.le_trans (Nat.le_succ logSize) hlogSize)

/-- The odds coset starts at the next larger subgroup's generator. -/
theorem odds_eq (n : Nat) (h : n + 1 ≤ logOrder) :
    odds n h = new (CirclePointIndex.subgroupGen (n + 1)) n
      (Nat.le_trans (Nat.le_succ n) h) := by rfl

/-- The STWO coset `G_{4n} + <G_n>`, whose conjugate completes `odds (logSize + 1)`. -/
def halfOdds (logSize : Nat) (hlogSize : logSize + 2 ≤ logOrder) : Coset :=
  new (CirclePointIndex.subgroupGen (logSize + 2)) logSize
    (Nat.le_trans (Nat.le_add_right logSize 2) hlogSize)

/-- The half-odds coset starts two subgroup levels above its step. -/
theorem halfOdds_eq (n : Nat) (h : n + 2 ≤ logOrder) :
    halfOdds n h = new (CirclePointIndex.subgroupGen (n + 2)) n
      (Nat.le_trans (Nat.le_add_right n 2) h) := by rfl

/-- Number of indices in the coset. -/
def size (c : Coset) : Nat :=
  2 ^ c.logSize

/-- A coset's size is two to its log size. -/
@[simp]
theorem size_eq (c : Coset) : c.size = 2 ^ c.logSize := by rfl

/-- The `i`th index in the coset order. -/
def indexAt (c : Coset) (i : Nat) : CirclePointIndex :=
  c.initialIndex + c.stepSize * (i : CirclePointIndex)

/-- Closed-form coset indexing, without recursive expansion of literal indices.
Lower priority lets the zero and conjugation lemmas simplify first. -/
@[simp low]
theorem indexAt_eq (c : Coset) (i : Nat) :
    c.indexAt i = c.initialIndex + c.stepSize * (i : CirclePointIndex) := by rfl

/-- The circle point at the `i`th coset index. -/
def pointAt (c : Coset) (i : Nat) : Point :=
  CirclePointIndex.toPoint (c.indexAt i)

/-- A coset point is the interpretation of its index. -/
theorem pointAt_def (c : Coset) (i : Nat) :
    c.pointAt i = CirclePointIndex.toPoint (c.indexAt i) := by rfl

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
theorem indexAt_succ (c : Coset) (i : Nat) :
    c.indexAt (i + 1) = c.indexAt i + c.stepSize := by
  simp [indexAt, Nat.cast_add, Nat.cast_one]
  ring

/-- Conjugation preserves the coset log size. -/
@[simp]
theorem conjugate_logSize (c : Coset) : c.conjugate.logSize = c.logSize := by rfl

/-- The conjugate coset starts at the negated initial index. -/
@[simp]
theorem conjugate_initialIndex (c : Coset) :
    c.conjugate.initialIndex = -c.initialIndex := by rfl

/-- The conjugate coset uses the negated step size. -/
@[simp]
theorem conjugate_stepSize (c : Coset) : c.conjugate.stepSize = -c.stepSize := by rfl

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

/-- The domain constructor preserves its half coset. -/
@[simp]
theorem new_halfCoset (c : Coset) : (new c).halfCoset = c := by rfl

/-- Domain log size. A domain contains a half coset and its conjugate. -/
def logSize (D : CircleDomain) : Nat :=
  D.halfCoset.logSize + 1

/-- A domain's log size is one more than its half coset's log size. -/
@[simp low]
theorem logSize_eq (D : CircleDomain) : D.logSize = D.halfCoset.logSize + 1 := by rfl

/-- Number of indices in the domain. -/
def size (D : CircleDomain) : Nat :=
  2 ^ D.logSize

/-- A domain's size is two to its log size. -/
theorem size_eq (D : CircleDomain) : D.size = 2 ^ D.logSize := by rfl

/-- The `i`th domain index: first the half coset, then the conjugate coset. -/
def indexAt (D : CircleDomain) (i : Nat) : CirclePointIndex :=
  if i < D.halfCoset.size then
    D.halfCoset.indexAt i
  else
    D.halfCoset.conjugate.indexAt (i - D.halfCoset.size)

/-- Domain indexing splits at the half-coset size. -/
theorem indexAt_def (D : CircleDomain) (i : Nat) :
    D.indexAt i = if i < D.halfCoset.size then D.halfCoset.indexAt i
      else D.halfCoset.conjugate.indexAt (i - D.halfCoset.size) := by rfl

/-- The circle point at the `i`th domain index. -/
def pointAt (D : CircleDomain) (i : Nat) : Point :=
  CirclePointIndex.toPoint (D.indexAt i)

/-- A domain point is the interpretation of its index. -/
theorem pointAt_def (D : CircleDomain) (i : Nat) :
    D.pointAt i = CirclePointIndex.toPoint (D.indexAt i) := by rfl

/-- A circle domain has twice as many indices as its half coset. -/
@[simp low]
theorem size_eq_two_mul_halfSize (D : CircleDomain) :
    D.size = 2 * D.halfCoset.size := by
  simp [size, logSize, Coset.size, pow_succ, Nat.mul_comm]

/-- Indices in the first half of a circle domain come from its half coset. -/
@[simp]
theorem indexAt_left (D : CircleDomain) (i : Nat) (hi : i < D.halfCoset.size) :
    D.indexAt i = D.halfCoset.indexAt i := by
  rw [indexAt_def, if_pos hi]

/-- Indices at or beyond the half-coset size come from the conjugate half. -/
@[simp]
theorem indexAt_of_le (D : CircleDomain) (i : Nat) (hi : D.halfCoset.size ≤ i) :
    D.indexAt i = -D.halfCoset.indexAt (i - D.halfCoset.size) := by
  rw [indexAt_def, if_neg (Nat.not_lt.mpr hi), Coset.conjugate_indexAt]

/-- Indices in the second half come from the negated half coset. -/
@[simp]
theorem indexAt_right (D : CircleDomain) (i : Nat) :
    D.indexAt (D.halfCoset.size + i) = -D.halfCoset.indexAt i := by
  rw [indexAt_of_le D _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

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

/-- A canonical coset is the odds coset at its log size. -/
theorem coset_eq (c : CanonicCoset) :
    c.coset = Coset.odds c.logSize c.logSize_succ_le_logOrder := by rfl

/-- The half coset used to form the canonical circle domain. -/
def halfCoset (c : CanonicCoset) : Coset :=
  Coset.halfOdds (c.logSize - 1) (by
    have hEq : c.logSize - 1 + 2 = c.logSize + 1 := by
      have hOne : 1 ≤ c.logSize := c.one_le_logSize
      omega
    rw [hEq]
    exact c.logSize_succ_le_logOrder)

/-- The canonical half coset is the half-odds coset one log size below. -/
theorem halfCoset_eq (c : CanonicCoset) :
    c.halfCoset = Coset.halfOdds (c.logSize - 1) (by
      have hOne := c.one_le_logSize
      have hBound := c.logSize_succ_le_logOrder
      omega) := by rfl

/-- The canonical circle domain with the same log size. -/
def circleDomain (c : CanonicCoset) : CircleDomain :=
  CircleDomain.new c.halfCoset

/-- The canonical domain is built from the canonical half coset. -/
theorem circleDomain_eq (c : CanonicCoset) :
    c.circleDomain = CircleDomain.new c.halfCoset := by rfl

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
  rw [CircleDomain.size_eq, circleDomain_logSize]

end CanonicCoset

end Circle
end Mersenne31
