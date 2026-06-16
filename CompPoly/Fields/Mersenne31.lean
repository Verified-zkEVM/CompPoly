/-
Copyright (c) 2024 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Varun Thakore
-/

import CompPoly.Fields.Mersenne31.Basic
import CompPoly.Fields.Mersenne31.Fast

/-!
  # Mersenne31 prime field `2^{31} - 1`

  Facade module for the Mersenne31 field. It re-exports the canonical `ZMod` model
  from `CompPoly.Fields.Mersenne31.Basic` and the native-word implementation from
  `CompPoly.Fields.Mersenne31.Fast`.
-/
