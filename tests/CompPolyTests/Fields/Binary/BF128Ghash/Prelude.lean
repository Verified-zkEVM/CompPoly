/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public meta import CompPoly.Fields.Binary.BF128Ghash.Prelude

/-!
  # BF128 GHASH Prelude Tests

  Small regression checks for the public certificate checkers.
-/

public meta section

open BF128Ghash

-- High quotient bits must still participate in the public `B256` checker.
#guard
  checkDivStep (0 : B256) (((1 : B256) <<< 200)) (1 : B256) (0 : B256) == false

#guard
  checkDivStep (((1 : B256) <<< 200)) (((1 : B256) <<< 200)) (1 : B256) (0 : B256) == true
