/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.KoalaBear.Basic
import CompPoly.Fields.Montgomery.Native32Field

/-! # Fast KoalaBear field definitions -/

namespace KoalaBear.Fast
open Montgomery.Native32 (Mont32Field FastField)

/-- The per-field data realizing KoalaBear as a fast 32-bit-word Montgomery field. The five
word constants are the only runtime data; every other field is a `decide`-checked fact. -/
instance instMont32Field : Mont32Field KoalaBear.fieldSize where
  prime := KoalaBear.is_prime
  modulus32 := 0x7F000001
  modulus64 := 0x7F000001
  rModModulus := 0x01FFFFFE
  r2ModModulus := 0x17F7EFE4
  montgomeryNegInv := 0x7EFFFFFF

/-- The fast native-word KoalaBear field carrier, stored as a Montgomery residue. -/
abbrev Field : Type := FastField KoalaBear.fieldSize

end KoalaBear.Fast
