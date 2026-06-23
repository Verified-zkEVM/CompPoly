/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Zitek-Estrada
-/
import Mathlib.Init

/-!
# `LawfulBEq` from `DecidableEq`

A canonical `LawfulBEq` derived from `DecidableEq`, suitable for `letI` use at
call sites that need to satisfy `BEq`/`LawfulBEq` constraints (for example on
`CMvPolynomial` API surfaces) from a `DecidableEq`-only context.

This is intentionally *not* registered as an instance: doing so would conflict
with other `BEq` paths chosen by typeclass synthesis.
-/

namespace CPoly

/-- A canonical `LawfulBEq` instance derived from `DecidableEq`. Intended for
`letI` use at call sites that need to satisfy `BEq`/`LawfulBEq` constraints
from a `DecidableEq`-only context. -/
@[reducible] def lawfulBEqOfDecidableEq {α : Type*} [DecidableEq α] :
    @LawfulBEq α (instBEqOfDecidableEq) where
  rfl := by intro a; simp
  eq_of_beq := by
    intro a b h
    simpa [instBEqOfDecidableEq] using of_decide_eq_true h

end CPoly
