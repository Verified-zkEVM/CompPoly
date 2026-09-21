/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Data.Bytes.Bias
public meta import CompPoly.Fields.BabyBear.Basic
public import CompPoly.Data.Bytes.Bias
public import CompPoly.Fields.BabyBear.Basic

/-!
# Bias of the reduce-modulo-order decoder

Fiber counts on a small field checked by evaluation against the closed form, and the bound
instantiated at the sizes a protocol would use.
-/

public meta section

namespace CompPolyTests.Bias

open CompPoly CompPoly.Bytes CompPoly.CanonicalNat

#guard Fintype.card (Vector UInt8 1) = 256
#guard Fintype.card (Vector UInt8 2) = 65536

-- One byte into `ZMod 5`: `256 = 5 * 51 + 1`, so residue `0` gets `52` strings and the rest `51`.
#guard Fintype.card {v : Vector UInt8 1 // ofBytesModOrder v = (0 : ZMod 5)} = 52
#guard Fintype.card {v : Vector UInt8 1 // ofBytesModOrder v = (1 : ZMod 5)} = 51
#guard Fintype.card {v : Vector UInt8 1 // ofBytesModOrder v = (4 : ZMod 5)} = 51
-- The closed form agrees.
#guard (256 / 5 + if (0 : ℕ) < 256 % 5 then 1 else 0) = 52
#guard (256 / 5 + if (1 : ℕ) < 256 % 5 then 1 else 0) = 51

example (x : ZMod 5) :
    Fintype.card {v : Vector UInt8 1 // ofBytesModOrder v = x}
      = 256 / 5 + if x.val < 256 % 5 then 1 else 0 :=
  card_fiber_ofBytesModOrder 1 x

-- The distance bound at a protocol's sizes: width plus sixteen bytes gives below `2 ^ -128`.
example :
    ∑ x : BabyBear.Field,
      |((Fintype.card {v : Vector UInt8 20 // ofBytesModOrder v = x} : ℚ) / 256 ^ 20)
        - 1 / (bound BabyBear.Field : ℚ)| ≤ (bound BabyBear.Field : ℚ) / 256 ^ 20 :=
  tv_ofBytesModOrder_le 20
#guard bound BabyBear.Field = 2013265921
example : ((2013265921 : ℕ) : ℚ) / 256 ^ 20 ≤ 1 / 2 ^ 128 := by norm_num

end CompPolyTests.Bias
