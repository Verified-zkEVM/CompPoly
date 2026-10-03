/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Native

/-! # Compiled packed-storage agreement checks

These exercise the two C storage replacements, which are outside the kernel proof.
Bytewise Lean operations provide the oracle, including sharing and growth behavior.
-/

public section
namespace CompPolyTests.NTT.NativeStorage

open CompPoly.CPolynomial.NTTFast.Packed.Native

@[noinline] private def storeBytes (b : ByteArray) (offset : USize) (count : UInt8)
    (append : Bool) (values : Array UInt32) : ByteArray := Id.run do
  if count.toNat > 16 then return b
  if !append && (!(offset.toNat + 4 * count.toNat ≤ b.size) ||
      !(offset.toNat + 4 * count.toNat < USize.size)) then return b
  let mut out := b
  for j in [:count.toNat] do
    for q in [:4] do
      let byte := (values[j]! >>> (8 * q).toUInt32).toUInt8
      out := if append then out.push byte else out.set! (offset.toNat + 4 * j + q) byte
  return out

/-- Check native batch stores against independent bytewise stores and word reads. -/
def run : IO Unit := do
  let values : Array UInt32 := #[0, 1, 0xffffffff, 0x12345678,
    0x01020304, 0x80000000, 0x7fffffff, 0xabcdef01,
    0, 1, 0xffffffff, 0x12345678, 0x01020304, 0x80000000, 0x7fffffff, 0xabcdef01]
  let mut cases := 0
  for size in [0, 1, 4, 8, 64, 65, 128] do
    for capacity in [size, size + 128] do
      for count in [0, 1, 3, 16, 17] do
        for offset in [0, 1, 4, 60, 64, 129, USize.size - 2] do
          for append in [false, true] do
            let source := (List.range size).foldl (fun b n ↦ b.push n.toUInt8)
              (ByteArray.emptyWithCapacity capacity)
            let expected := storeBytes source offset.toUSize count.toUInt8 append values
            let actual := storeWords source offset.toUSize count.toUInt8 append
              values[0]! values[1]! values[2]! values[3]! values[4]! values[5]! values[6]!
              values[7]! values[8]! values[9]! values[10]! values[11]! values[12]!
              values[13]! values[14]! values[15]!
            if actual != expected then
              throw <| IO.userError s!"packed store mismatch: {size}/{count}/{offset}/{append}"
            if source.toList != (List.range size).map Nat.toUInt8 then
              throw <| IO.userError "packed store mutated shared input"
            cases := cases + 1
      let source := (List.range size).foldl (fun b n ↦ b.push n.toUInt8)
        (ByteArray.emptyWithCapacity capacity)
      for i in [:size + 2] do
        let expected := if 4 * i + 3 < source.size then
          UInt32.ofNat (CompPoly.Bytes.ofListLE ((source.toList.drop (4 * i)).take 4)) else 0
        if read source i != expected then
          throw <| IO.userError s!"packed read mismatch: {size}/{i}"
        cases := cases + 1
  IO.println s!"packed storage agreement: {cases} checks passed"

end CompPolyTests.NTT.NativeStorage
