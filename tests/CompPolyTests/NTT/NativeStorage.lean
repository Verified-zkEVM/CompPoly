/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Data.ByteArray.Pack
public import CompPoly.Data.Bytes.LittleEndian

/-! # Compiled word-accessor agreement checks

These exercise the inline C of the backported `ByteArray` word accessors, which is outside the
kernel proof. Bytewise Lean operations provide the oracle, including out-of-range offsets and
shared inputs. The packed FFT's batch stores and reads are Lean definitions over these accessors,
proved against the byte-level `PackedRepr.encode` specification.
-/

public section
namespace CompPolyTests.NTT.NativeStorage

/-- Check the native word accessors against independent bytewise reads and writes. -/
def run : IO Unit := do
  let mut cases := 0
  for size in [0, 1, 3, 4, 5, 8, 64, 65] do
    let source := (List.range size).foldl (fun b n ↦ b.push (n * 37 + 11).toUInt8)
      (ByteArray.emptyWithCapacity size)
    for off in [:size + 3] do
      let fits := off + 4 ≤ size
      let expected := if fits then
        UInt32.ofNat (CompPoly.Bytes.ofListLE ((source.toList.drop off).take 4)) else 0
      if source.getUInt32LE! off != expected then
        throw <| IO.userError s!"getUInt32LE! mismatch: {size}/{off}"
      let v : UInt32 := 0x89abcdef
      let written := if fits then
        (List.range 4).foldl (fun b q ↦ b.set! (off + q) (v >>> (8 * q).toUInt32).toUInt8) source
      else source
      if source.setUInt32LE! off v != written then
        throw <| IO.userError s!"setUInt32LE! mismatch: {size}/{off}"
      if h : off + 4 ≤ source.size ∧ off < USize.size then
        have hu : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' h.2
        if source.ugetUInt32LE off.toUSize (by rw [hu]; exact h.1) != expected then
          throw <| IO.userError s!"ugetUInt32LE mismatch: {size}/{off}"
        if source.usetUInt32LE off.toUSize v (by rw [hu]; exact h.1) != written then
          throw <| IO.userError s!"usetUInt32LE mismatch: {size}/{off}"
      if source.toList != (List.range size).map fun n ↦ (n * 37 + 11).toUInt8 then
        throw <| IO.userError "word store mutated shared input"
      cases := cases + 1
  IO.println s!"word accessor agreement: {cases} checks passed"

end CompPolyTests.NTT.NativeStorage
