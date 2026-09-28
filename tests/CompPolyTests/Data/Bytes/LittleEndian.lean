/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Data.Bytes.LittleEndian
public import CompPoly.Data.Bytes.LittleEndian

/-!
# Little-endian encoder tests

Known vectors for `toListLE` / `ofListLE`, the width function `bytesFor` on the field sizes
used in the library, and kernel evaluation of `bytesFor` by `decide`.
-/

public meta section

namespace CompPolyTests.Bytes

open CompPoly.Bytes

-- Little-endian, least significant byte first.
#guard toListLE 4 0x78000000 = [0x00, 0x00, 0x00, 0x78]
#guard toListLE 4 1 = [1, 0, 0, 0]
#guard toListLE 2 0x0102 = [0x02, 0x01]
#guard toListLE 0 12345 = []
-- Bits above the width are dropped.
#guard toListLE 1 0x1ff = [0xff]

#guard ofListLE [0x00, 0x00, 0x00, 0x78] = 0x78000000
#guard ofListLE [] = 0
#guard ofListLE (toListLE 8 (2 ^ 64 - 2 ^ 32)) = 2 ^ 64 - 2 ^ 32
#guard ofListLE [1, 0, 0, 0, 1, 0, 0, 0] = 1 + 2 ^ 32

#guard toVecLE 4 1 = #v[1, 0, 0, 0]
#guard ofVecLE #v[0, 0, 0, 0x78] = 0x78000000
#guard (toByteArrayLE 4 1).data = #[1, 0, 0, 0]
#guard ofByteArrayLE ⟨#[0, 0, 0, 0x78]⟩ = 0x78000000

-- Widths of the library's field sizes.
#guard bytesFor 0 = 1
#guard bytesFor 1 = 1
#guard bytesFor 2 = 1
#guard bytesFor 256 = 1
#guard bytesFor 257 = 2
#guard bytesFor 65536 = 2
#guard bytesFor 65537 = 3
#guard bytesFor (2 ^ 31 - 2 ^ 27 + 1) = 4  -- BabyBear
#guard bytesFor (2 ^ 31 - 2 ^ 24 + 1) = 4  -- KoalaBear
#guard bytesFor (2 ^ 31 - 1) = 4           -- Mersenne31
#guard bytesFor (2 ^ 64 - 2 ^ 32 + 1) = 8  -- Goldilocks
#guard bytesFor (2 ^ 64) = 8               -- BF64 bit patterns
#guard bytesFor (2 ^ 128) = 16             -- BF128 bit patterns
#guard bytesFor (2 ^ 255 - 19) = 32
#guard bytesFor (2 ^ 256) = 32

-- The kernel evaluates `bytesFor` on numerals.
example : bytesFor (2 ^ 31 - 2 ^ 27 + 1) = 4 := by decide
example : bytesFor (2 ^ 64 - 2 ^ 32 + 1) = 8 := by decide
example : bytesFor
    21888242871839275222246405745257275088548364400416034343698204186575808495617 = 32 := by
  decide

end CompPolyTests.Bytes
