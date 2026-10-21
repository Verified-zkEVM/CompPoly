/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.StorageLemmas
public import CompPoly.Univariate.NTTFast.Packed.BitReversal
import all CompPoly.Univariate.NTTFast.Packed.Native
import all CompPoly.Univariate.NTTFast.Packed.NativeOrder
public import CompPoly.Univariate.NTTFast.Packed.NativeOrder
public import CompPoly.Univariate.NTTFast.Packed.Rows
import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas
public import CompPoly.Univariate.NTTFast.Packed.DifSpec

/-! # Correctness of the parallel natural-order output

Every loop of `NativeOrder` appends sixteen words at a time. Their results are stated as
`rows`, a concatenation of sixteen-word literals with a single indexing lemma, so the
tile, leaf-reversal and join proofs reduce to index arithmetic.
-/

@[expose] public section
open CompPoly
namespace CompPoly.CPolynomial.NTTFast.Packed
open Montgomery.Native32 (Mont32Field FastField)

variable {p : ℕ} [Mont32Field p]

open CompPoly.PackedRepr (encode size_encode_uint32)

namespace Native

/-- A line inside a packed word array that fits machine indices passes the range check. -/
theorem lineFits_encodeWords (v : Array UInt32) (q : USize) (h : q.toNat + 16 ≤ v.size)
    (hs : (encode v).size < USize.size) : LineFits (encode v) q := by
  have hu : (encode v).usize.toNat = 4 * v.size := by
    rw [ByteArray.usize, Nat.toUSize, USize.toNat_ofNat_of_lt' hs, size_encode_uint32]
  have h16 : (16 : USize).toNat = 16 := usize_numeral 16 (by decide)
  have h4 : (4 : USize).toNat = 4 := usize_numeral 4 (by decide)
  have h1 : 16 ≤ (encode v).usize / 4 := by
    rw [USize.le_iff_toNat_le, USize.toNat_div, h4, h16, hu]; omega
  refine ⟨h1, ?_⟩
  rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ h1, USize.toNat_div, h4, h16, hu]
  omega

/-- One aligned line of a packed word array. -/
theorem line_encodeWords (v : Array UInt32) (q : USize) (hl) :
    line (encode v) q hl = ⟨v.getD (q.toNat + 0) 0, v.getD (q.toNat + 1) 0, v.getD (q.toNat + 2) 0,
      v.getD (q.toNat + 3) 0, v.getD (q.toNat + 4) 0, v.getD (q.toNat + 5) 0,
      v.getD (q.toNat + 6) 0, v.getD (q.toNat + 7) 0, v.getD (q.toNat + 8) 0,
      v.getD (q.toNat + 9) 0, v.getD (q.toNat + 10) 0, v.getD (q.toNat + 11) 0,
      v.getD (q.toNat + 12) 0, v.getD (q.toNat + 13) 0, v.getD (q.toNat + 14) 0,
      v.getD (q.toNat + 15) 0⟩ := by
  unfold line
  simp only [ugetUInt32LE_eq, (lineFits_toNat hl 0 (by decide)).1,
    (lineFits_toNat hl 1 (by decide)).1, (lineFits_toNat hl 2 (by decide)).1,
    (lineFits_toNat hl 3 (by decide)).1, (lineFits_toNat hl 4 (by decide)).1,
    (lineFits_toNat hl 5 (by decide)).1, (lineFits_toNat hl 6 (by decide)).1,
    (lineFits_toNat hl 7 (by decide)).1, (lineFits_toNat hl 8 (by decide)).1,
    (lineFits_toNat hl 9 (by decide)).1, (lineFits_toNat hl 10 (by decide)).1,
    (lineFits_toNat hl 11 (by decide)).1, (lineFits_toNat hl 12 (by decide)).1,
    (lineFits_toNat hl 13 (by decide)).1, (lineFits_toNat hl 14 (by decide)).1,
    (lineFits_toNat hl 15 (by decide)).1, PackedRepr.getUInt32LE!_encode]

/-- The `c`-th of sixteen word arrays. -/
def sel16 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Array UInt32) (c : Nat) :
    Array UInt32 :=
  #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15].getD c #[]

/-- A sixteen-element literal is its own leading segment. -/
theorem extract_literal16 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt32) :
    (#[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] : Array UInt32).extract
      0 16 = #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] :=
  Array.extract_size

/-- A sixteen-word store at the end of a written prefix extends the prefix. -/
theorem write16U_pack_cursor (o Z : Array UInt32) (p : USize) (hp : p.toNat = o.size)
    (hZ : 16 ≤ Z.size) (hs : (encode (o ++ Z)).size < USize.size)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) :
    write16U (encode (o ++ Z)) p v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      encode (o ++ #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] ++
        Z.extract 16 Z.size) := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [size_encode_uint32, Array.size_append] at hs
  unfold write16U
  rw [storeWords_replace_encodeWords (o ++ Z) (p * 4) 16 o.size (by decide)
    (by rw [USize.toNat_mul, usize_numeral 4 (by decide), hsize, Nat.mod_eq_of_lt (by omega)]
        omega)
    (by simp only [Array.size_append, show (16 : UInt8).toNat = 16 from rfl]; omega)
    (by rw [size_encode_uint32, Array.size_append]; omega)]
  simp only [show (16 : UInt8).toNat = 16 from rfl, extract_literal16]
  have := splice_cursor o Z
    #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] hZ
  simp only [splice, List.size_toArray, List.length_cons, List.length_nil] at this
  rw [this]

/-- Adding a small numeral to a machine index that cannot wrap. -/
theorem usize_add_numeral (q : USize) (k : Nat) (hk : k < 4294967296)
    (h : q.toNat + k < USize.size) : (q + OfNat.ofNat k).toNat = q.toNat + k := by
  rw [USize.toNat_add, usize_numeral k hk, Nat.mod_eq_of_lt h]

set_option maxHeartbeats 1000000 in
/-- One transposed tile stores rows `q, …, q + 15` of the sixteen-stream interleave at output
word `p`, the end of the written prefix. -/
theorem transposeStep_encodeWords (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 o Z :
    Array UInt32) (q p : USize)
    (h : ∀ c < 16, q.toNat + 16 ≤
      (sel16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 c).size)
    (hs : ∀ c < 16,
      (encode (sel16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 c)).size < USize.size)
    (hp : p.toNat = o.size) (hZ : 256 ≤ Z.size) (ho : (encode (o ++ Z)).size < USize.size) :
    transposeStep (encode v0) (encode v1) (encode v2) (encode v3) (encode v4) (encode v5) (encode
        v6)
      (encode v7) (encode v8) (encode v9) (encode v10) (encode v11) (encode v12) (encode v13)
          (encode v14)
      (encode v15) q (encode (o ++ Z)) p =
      encode (o ++ rows (fun u c ↦
        (sel16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 c).getD (q.toNat + u) 0)
        16 ++ Z.extract 256 Z.size) := by
  have hsz := ho
  rw [size_encode_uint32, Array.size_append] at hsz
  have hf : ∀ c < 16,
      LineFits (encode (sel16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 c)) q :=
    fun c hc ↦ lineFits_encodeWords _ q (h c hc) (hs c hc)
  have hcond := And.intro (hf 0 (by decide)) <| And.intro (hf 1 (by decide)) <|
    And.intro (hf 2 (by decide)) <| And.intro (hf 3 (by decide)) <|
    And.intro (hf 4 (by decide)) <| And.intro (hf 5 (by decide)) <|
    And.intro (hf 6 (by decide)) <| And.intro (hf 7 (by decide)) <|
    And.intro (hf 8 (by decide)) <| And.intro (hf 9 (by decide)) <|
    And.intro (hf 10 (by decide)) <| And.intro (hf 11 (by decide)) <|
    And.intro (hf 12 (by decide)) <| And.intro (hf 13 (by decide)) <|
    And.intro (hf 14 (by decide)) (hf 15 (by decide))
  unfold transposeStep
  split
  swap
  · rename_i hneg; exact absurd hcond hneg
  simp only [line_encodeWords]
  rw [write16U_pack_cursor _ _ p ?hp0 ?hz0 ?hs0]
  rw [write16U_pack_cursor _ _ (p + 16) ?hp1 ?hz1 ?hs1]
  rw [write16U_pack_cursor _ _ (p + 32) ?hp2 ?hz2 ?hs2]
  rw [write16U_pack_cursor _ _ (p + 48) ?hp3 ?hz3 ?hs3]
  rw [write16U_pack_cursor _ _ (p + 64) ?hp4 ?hz4 ?hs4]
  rw [write16U_pack_cursor _ _ (p + 80) ?hp5 ?hz5 ?hs5]
  rw [write16U_pack_cursor _ _ (p + 96) ?hp6 ?hz6 ?hs6]
  rw [write16U_pack_cursor _ _ (p + 112) ?hp7 ?hz7 ?hs7]
  rw [write16U_pack_cursor _ _ (p + 128) ?hp8 ?hz8 ?hs8]
  rw [write16U_pack_cursor _ _ (p + 144) ?hp9 ?hz9 ?hs9]
  rw [write16U_pack_cursor _ _ (p + 160) ?hp10 ?hz10 ?hs10]
  rw [write16U_pack_cursor _ _ (p + 176) ?hp11 ?hz11 ?hs11]
  rw [write16U_pack_cursor _ _ (p + 192) ?hp12 ?hz12 ?hs12]
  rw [write16U_pack_cursor _ _ (p + 208) ?hp13 ?hz13 ?hs13]
  rw [write16U_pack_cursor _ _ (p + 224) ?hp14 ?hz14 ?hs14]
  rw [write16U_pack_cursor _ _ (p + 240) ?hp15 ?hz15 ?hs15]
  · simp only [extract_extract_tail, Nat.reduceAdd]
    simp only [rows, lit16, Array.append_assoc, Array.empty_append]
    rfl
  all_goals (try rw [usize_add_numeral])
  all_goals (try simp only [size_encode_uint32, Array.size_append, Array.size_extract,
      List.size_toArray,
    List.length_cons, List.length_nil])
  all_goals omega

/-- Repeated transposed tiles append consecutive interleave rows to a written prefix. -/
theorem transposeGo_encodeWords (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Array
    UInt32)
    (count : Nat) (q p : USize) (o : Array UInt32)
    (h : ∀ c < 16, q.toNat + 16 * count ≤
      (sel16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 c).size)
    (hs : ∀ c < 16,
      (encode (sel16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 c)).size < USize.size)
    (hp : p.toNat = o.size) (ho : 4 * (o.size + 256 * count) < USize.size) :
    transposeGo (encode v0) (encode v1) (encode v2) (encode v3) (encode v4) (encode v5) (encode
        v6) (encode v7)
      (encode v8) (encode v9) (encode v10) (encode v11) (encode v12) (encode v13) (encode v14)
          (encode v15)
      count q p (encode o) =
      encode (o ++ rows (fun u c ↦
        (sel16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 c).getD (q.toNat + u) 0)
        (16 * count)) := by
  induction count generalizing q p o with
  | zero => simp only [transposeGo, rows, Array.append_empty]
  | succ count ih =>
    have hq : q.toNat + 16 < USize.size := by
      have h0 := h 0 (by decide)
      have hs0 := hs 0 (by decide)
      rw [size_encode_uint32] at hs0
      omega
    have hZ : (Array.replicate 256 (0 : UInt32)).extract 256
        (Array.replicate 256 (0 : UInt32)).size = #[] :=
      Array.extract_eq_empty_of_le (by simp)
    have hoZ : (encode (o ++ Array.replicate 256 0)).size < USize.size := by
      rw [size_encode_uint32, Array.size_append, Array.size_replicate]
      exact Nat.lt_of_le_of_lt (by omega) ho
    rw [transposeGo, extendZeros_encodeWords,
      transposeStep_encodeWords v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        o (Array.replicate 256 0) q p (fun c hc ↦ by have := h c hc; omega) hs hp
        (by rw [Array.size_replicate]) hoZ,
      hZ, Array.append_empty,
      ih (q + 16) (p + 256) (o ++ rows (fun u c ↦
          (sel16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 c).getD (q.toNat + u) 0) 16)
        (fun c hc ↦ by rw [usize_add_numeral q 16 (by decide) hq]; have := h c hc; omega)
        (by rw [usize_add_numeral p 256 (by decide) (by omega), Array.size_append, size_rows,
          hp])
        (by rw [Array.size_append, size_rows]; omega),
      show 16 * (count + 1) = 16 + 16 * count by omega, rows_add, Array.append_assoc,
      usize_add_numeral q 16 (by decide) hq]
    simp only [Nat.add_assoc]

/-- The interleave streams are the reversed leaves in four-bit reversed order. -/
theorem sel16_bitRev (V : Nat → Array UInt32) (c : Nat) (hc : c < 16) :
    sel16 (V 0) (V 8) (V 4) (V 12) (V 2) (V 10) (V 6) (V 14) (V 1) (V 9) (V 5) (V 13) (V 3)
      (V 11) (V 7) (V 15) c = V (NTT.Transform.bitRevNat 4 c) := by
  interval_cases c <;> rfl

/-- One interleave block: rows `q` up to `q + 16 * count` of the sixteen reversed leaves. -/
theorem interleaveRange_encodeWords (V : Nat → Array UInt32) (M q count : Nat)
    (hV : ∀ l < 16, (V l).size = M) (hq : q + 16 * count ≤ M) (hs : 64 * M < USize.size) :
    interleaveRange ((Array.range 16).map fun l ↦ encode (V l)) q count =
      encode (rows (fun u c ↦ (V (NTT.Transform.bitRevNat 4 c)).getD (q + u) 0) (16 * count)) := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hqu : q.toUSize.toNat = q := USize.toNat_ofNat_of_lt' (by omega)
  unfold interleaveRange
  simp only [getD_map_range _ 16 0 (by decide), getD_map_range _ 16 1 (by decide),
    getD_map_range _ 16 2 (by decide), getD_map_range _ 16 3 (by decide),
    getD_map_range _ 16 4 (by decide), getD_map_range _ 16 5 (by decide),
    getD_map_range _ 16 6 (by decide), getD_map_range _ 16 7 (by decide),
    getD_map_range _ 16 8 (by decide), getD_map_range _ 16 9 (by decide),
    getD_map_range _ 16 10 (by decide), getD_map_range _ 16 11 (by decide),
    getD_map_range _ 16 12 (by decide), getD_map_range _ 16 13 (by decide),
    getD_map_range _ 16 14 (by decide), getD_map_range _ 16 15 (by decide)]
  rw [show ByteArray.emptyWithCapacity (1024 * count) = encode (#[] : Array UInt32) from rfl,
    transposeGo_encodeWords (V 0) (V 8) (V 4) (V 12) (V 2) (V 10) (V 6)
    (V 14) (V 1) (V 9) (V 5) (V 13) (V 3) (V 11) (V 7) (V 15) count q.toUSize 0 #[]
    (fun c hc ↦ by rw [sel16_bitRev V c hc, hqu, hV _ (NTT.Transform.bitRevNat_lt 4 c)]; exact hq)
    (fun c hc ↦ by
      rw [sel16_bitRev V c hc, size_encode_uint32, hV _ (NTT.Transform.bitRevNat_lt 4 c)]; omega)
    rfl (by rw [Array.size_empty]; omega),
    Array.empty_append, hqu]
  congr 1
  exact rows_congr _ _ _ (fun j c hc ↦ by rw [sel16_bitRev V c hc])

/-- Joining the interleave blocks in task order concatenates their rows. -/
theorem foldl_blocks (g : Nat → Nat → UInt32) (B : Nat → ByteArray) (count k : Nat)
    (o : Array UInt32)
    (hB : ∀ t < k, B t = encode (rows (fun u c ↦ g (16 * count * t + u) c) (16 * count))) :
    (Array.range k).foldl (fun acc t ↦ acc ++ B t) (encode o) =
      encode (o ++ rows g (16 * count * k)) := by
  induction k with
  | zero =>
    rw [show Array.range 0 = #[] from Array.eq_empty_of_size_eq_zero Array.size_range]
    simp only [Array.foldl_empty, Nat.mul_zero, rows, Array.append_empty]
  | succ k ih =>
    rw [Array.range_succ, Array.foldl_append, ih (fun t ht ↦ hB t (by omega))]
    have hs : (#[k] : Array Nat).foldl (fun acc t ↦ acc ++ B t)
        (encode (o ++ rows g (16 * count * k))) =
        encode (o ++ rows g (16 * count * k)) ++ B k := by simp
    rw [hs, hB k (by omega), ← PackedRepr.encode_append, Nat.mul_succ, rows_add, Array.append_assoc]

/-- Interleaving sixteen reversed leaves: output word `16 * q + c` is word `q` of leaf
`bitrev₄ c`. -/
theorem naturalLeaves_encodeWords (V : Nat → Array UInt32) (logN : Nat) (h12 : 12 ≤ logN)
    (hV : ∀ l < 16, (V l).size = 2 ^ (logN - 4)) (hs : 4 * 2 ^ logN < USize.size) :
    naturalLeaves ((Array.range 16).map fun l ↦ encode (V l)) logN =
      encode (Array.ofFn (n := 2 ^ logN) fun i ↦
        (V (NTT.Transform.bitRevNat 4 (i % 16))).getD (i / 16) 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, logN = m + 4 := ⟨logN - 4, by omega⟩
  have hsub : m + 4 - 4 = m := by omega
  have hpow : 2 ^ (m + 4) = 16 * 2 ^ m := by rw [Nat.pow_add]; omega
  have hm8 : 2 ^ m = 256 * (2 ^ m / 256) := by
    have : 256 ∣ 2 ^ m := by
      rw [show m = 8 + (m - 8) by omega, Nat.pow_add]
      exact Nat.dvd_mul_right _ _
    omega
  have hV' : ∀ l < 16, (V l).size = 2 ^ m := by
    intro l hl
    rw [hV l hl, hsub]
  unfold naturalLeaves
  simp only [Task.spawn, hsub]
  rw [Array.foldl_map, emptyWithCapacity_eq_encodeWords,
    foldl_blocks (fun u c ↦ (V (NTT.Transform.bitRevNat 4 c)).getD u 0) _ (2 ^ m / 256) 16 #[]
      (fun t ht ↦ by
        rw [interleaveRange_encodeWords V (2 ^ m) _ _ hV' (by
          have := Nat.mul_le_mul_left (16 * (2 ^ m / 256)) (show t + 1 ≤ 16 by omega)
          rw [Nat.mul_add, Nat.mul_one] at this
          omega) (by omega)]),
    Array.empty_append]
  congr 1
  apply array_eq_of_getD _ _ 0 (by rw [size_rows, Array.size_ofFn, hpow]; omega)
  intro i
  by_cases hi : i < 2 ^ (m + 4)
  · rw [getD_rows _ _ _ (by omega), getD_ofFn_bounded _ _ hi]
  · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by rw [size_rows]; omega),
      Array.getElem?_eq_none (by rw [Array.size_ofFn]; omega)]

/-- Interleaving the natural-order reads of sixteen blocks reads the whole array in natural
order. -/
theorem naturalLeaves_encode (S : Array (FastField p)) (logN : Nat)
    (factor : FastField p) (sc : Bool) (h12 : 12 ≤ logN) (h32 : logN ≤ 32)
    (hS : S.size = 2 ^ logN) (hs : 4 * 2 ^ logN < USize.size) :
    naturalLeaves ((Array.range 16).map fun l ↦ encode (decodedFields (logN - 4)
      (S.extract (l * 2 ^ (logN - 4)) ((l + 1) * 2 ^ (logN - 4))) factor sc)) logN =
      encode (decodedFields logN S factor sc) := by
  obtain ⟨m, rfl⟩ : ∃ m, logN = m + 4 := ⟨logN - 4, by omega⟩
  have hsub : m + 4 - 4 = m := by omega
  have hpow : 2 ^ (m + 4) = 16 * 2 ^ m := by rw [Nat.pow_add]; omega
  let V : Nat → Array UInt32 := fun l ↦ (decodedFields m
    (S.extract (l * 2 ^ m) ((l + 1) * 2 ^ m)) factor sc).map Subtype.val
  have hV : ∀ l < 16, (V l).size = 2 ^ (m + 4 - 4) := by
    intro l _
    simp only [V, Array.size_map, decodedFields, Array.size_ofFn, hsub]
  have hr : ((Array.range 16).map fun l ↦ encode (decodedFields (m + 4 - 4)
      (S.extract (l * 2 ^ (m + 4 - 4)) ((l + 1) * 2 ^ (m + 4 - 4))) factor sc)) =
      (Array.range 16).map fun l ↦ encode (V l) := by
    simp only [hsub, V, ← encode_eq_map_val]
  rw [hr, naturalLeaves_encodeWords V (m + 4) h12 hV hs, encode_eq_map_val]
  congr 1
  simp only [decodedFields, Array.map_ofFn]
  apply Array.ext (by simp only [Array.size_ofFn])
  intro i h1 _
  simp only [Array.size_ofFn] at h1
  rw [Array.getElem_ofFn, Array.getElem_ofFn]
  simp only [Function.comp_apply]
  have hc := Nat.mod_lt i (show 0 < 16 by decide)
  have hbr := NTT.Transform.bitRevNat_lt 4 (i % 16)
  have hbq := NTT.Transform.bitRevNat_lt m (i / 16)
  have hq : i / 16 < 2 ^ m := by omega
  have hle : NTT.Transform.bitRevNat 4 (i % 16) * 2 ^ m + 2 ^ m ≤ S.size := by
    rw [hS, hpow]
    have := Nat.mul_le_mul_right (2 ^ m) (show NTT.Transform.bitRevNat 4 (i % 16) + 1 ≤ 16 by
      omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    exact this
  simp only [V]
  rw [getD_map_val, decodedFields, getD_ofFn_bounded _ _ hq,
    show (NTT.Transform.bitRevNat 4 (i % 16) + 1) * 2 ^ m =
      NTT.Transform.bitRevNat 4 (i % 16) * 2 ^ m + 2 ^ m by ring,
    getD_extract _ _ _ _ _ hle hbq]
  have hcat := bitRevNat_concat m 4 (i / 16) (i % 16) hc
  rw [show 2 ^ 4 * (i / 16) + i % 16 = i by omega] at hcat
  rw [show NTT.Transform.bitRevNat 4 (i % 16) * 2 ^ m + NTT.Transform.bitRevNat m (i / 16) =
    NTT.Transform.bitRevNat (m + 4) i by rw [hcat]; ring]

end Native
end CompPoly.CPolynomial.NTTFast.Packed
