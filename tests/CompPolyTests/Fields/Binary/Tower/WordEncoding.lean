/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.Tower.Concrete.Core
public import CompPoly.Fields.Binary.Tower.Concrete.Core

/-!
# Concrete tower word-coordinate regressions

The explicit encoding API preserves complete stored words and natural-word truncation.
Field numerals and operations remain distinct from raw word construction and arithmetic.
These are representation-map tests; the underlying carrier is still a bitvector alias.
-/

public meta section

namespace CompPolyTests.TowerWordEncoding

open ConcreteBinaryTower

example {k : ℕ} (x : ConcreteBTField k) : ConcreteBTField.ofBitVec x.toBitVec = x :=
  ConcreteBTField.ofBitVec_toBitVec x

example {k : ℕ} (x : BitVec (2 ^ k)) : (ConcreteBTField.ofBitVec x).toBitVec = x :=
  ConcreteBTField.toBitVec_ofBitVec x

example {k : ℕ} (x y : ConcreteBTField k) (h : x.toBitVec = y.toBitVec) : x = y :=
  ConcreteBTField.ext h

example {k : ℕ} (x : ConcreteBTField k) : fromNat x.toNat = x :=
  ConcreteBTField.fromNat_toNat x

example {k : ℕ} (n : ℕ) : (fromNat (k := k) n).toNat = n % 2 ^ (2 ^ k) :=
  ConcreteBTField.toNat_fromNat n

#guard (ConcreteBTField.ofBitVec (k := 1) (2#2)).toNat == 2
#guard (ConcreteBTField.ofBitVec (k := 1) (2#2) *
  ConcreteBTField.ofBitVec (k := 1) (2#2)).toNat == 3
#guard (2 : ConcreteBTField 1).toNat == 0
#guard (fromNat (k := 1) 2).toNat == 2
#guard (fromNat (k := 0) 5).toNat == 1
#guard (fromNat (k := 3) (2 ^ 8 + 129)).toNat == 129
#guard (fromNat (k := 7) (2 ^ 127 + 2 ^ 64 + 7)).toBitVec ==
  BitVec.ofNat 128 (2 ^ 127 + 2 ^ 64 + 7)
#guard (fromNat (k := 8) (2 ^ 256 + 2 ^ 255 + 1)).toNat == 2 ^ 255 + 1

-- Importing the representation API does not change ordinary raw-word operations.
#guard (2#2) * (2#2) == 0#2
#guard (2#4) * (2#4) == 4#4
#guard (1#4) + (1#4) == 2#4

end CompPolyTests.TowerWordEncoding
