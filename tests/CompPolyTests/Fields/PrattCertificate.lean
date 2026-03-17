/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Fields.PrattCertificate

/-!
  # Pratt Certificate Tests

  Small regression checks for the pratt tactic
-/

example : Nat.Prime 5915587277 := by pratt
example : Nat.Prime 1500450271 := by pratt
example : Nat.Prime 3267000013 := by pratt
example : Nat.Prime 5754853343 := by pratt
example : Nat.Prime 4093082899 := by pratt
example : Nat.Prime 9576890767 := by pratt
example : Nat.Prime 3628273133 := by pratt
example : Nat.Prime 2860486313 := by pratt
example : Nat.Prime 5463458053 := by pratt
example : Nat.Prime 3367900313 := by pratt
