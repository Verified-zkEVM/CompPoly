/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import CompPoly.Univariate.Raw.Size
public meta import CompPoly.Univariate.Raw.Ops

/-!
# Raw polynomial buffer-size tests

The minimal import exposes size bounds without requiring canonical polynomial structures.
The executable checks distinguish raw multiplication's empty-left and empty-right behavior.
-/

public section

open CompPoly CPolynomial CPolynomial.Raw

example {R : Type*} (x : R) : (C x).size = 1 := size_C x

example {R : Type*} [Mul R] (x : R) (p : Raw R) : (smul x p).size = p.size :=
  size_smul x p

example {R : Type*} [Zero R] (i : Nat) (p : Raw R) :
    (mulPowX i p).size = i + p.size := size_mulPowX i p

example {R : Type*} [Zero R] [Add R] (p q : Raw R) :
    (addRaw p q).size = max p.size q.size := by simp

example {R : Type*} [Semiring R] (p q : Raw R) :
    (mulRaw p q).size ≤ p.size + q.size - 1 := size_mulRaw_le p q

#guard (C (0 : Nat)).size == 1
#guard smul (0 : Nat) #[1, 2, 3] == #[0, 0, 0]
#guard mulPowX 3 (#[] : Raw Nat) == #[0, 0, 0]
#guard addRaw (#[] : Raw Nat) #[0, 0] == #[0, 0]
#guard mulRaw (#[] : Raw Nat) #[1, 2, 3] == #[]
#guard mulRaw (#[1, 2, 3] : Raw Nat) #[] == #[0, 0]
#guard mulRaw (#[1] : Raw Nat) #[] == #[]
#guard mulRaw (#[] : Raw Nat) #[] == #[]
#guard (mulRaw (#[1, 2, 3] : Raw Nat) #[]).trim == #[]

example (p : Raw Nat) : (mulRaw p #[]).size = p.size - 1 := by
  rw [size_mulRaw]
  split_ifs with hp
  · simp only [hp, Nat.zero_sub]
  · simp only [Array.size_empty, Nat.zero_add]
