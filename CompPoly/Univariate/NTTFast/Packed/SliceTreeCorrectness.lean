/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Packed.Native
import all CompPoly.Univariate.NTTFast.Packed.SliceTree
public import CompPoly.Univariate.NTTFast.Packed.SliceTree
public import CompPoly.Univariate.NTTFast.Packed.Rows
public import CompPoly.Univariate.NTTFast.Packed.Correctness
public import CompPoly.Univariate.NTTFast.Packed.KernelRefinement
public import CompPoly.Univariate.NTTFast.Packed.SplitRefinement

/-! # Correctness of the sliced split tree

The pair kernels append the ordinary first-layer sums and twiddle-scaled differences of their
index ranges. Joining the chunk outputs of one level therefore reproduces `splitLeft` and
`splitRight` of the concatenated input, and the sliced tree assembles to the same leaves as
`splitChunks`; the existing tree theorems then apply unchanged.
-/

@[expose] public section
open CompPoly
namespace CompPoly.CPolynomial.NTTFast.Packed
open CompPoly.PackedRepr (encode)

/-- Sixteen consecutive values of `f` from `16 * j` on, as concatenated rows. -/
theorem rows_eq_ofFn (f : Nat → α) (count : Nat) :
    rows (fun j k ↦ f (16 * j + k)) count = Array.ofFn (n := 16 * count) fun i ↦ f i := by
  apply Array.ext (by rw [size_rows, Array.size_ofFn])
  intro i h1 h2
  have hg := getD_rows (fun j k ↦ f (16 * j + k)) count i (by rw [size_rows] at h1; exact h1)
    (f 0)
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Option.getD_some] at hg
  rw [hg, Array.getElem_ofFn]
  congr 1
  show 16 * (i / 16) + i % 16 = i
  omega

namespace Native

/-- Joining tasks collects their results in order. -/
theorem joinTasks_get (ts : Array (Task α)) : (joinTasks ts).get = ts.map Task.get := by
  unfold joinTasks
  rw [← Array.foldl_toList, ← Array.toList_inj, Array.toList_map]
  suffices h : ∀ (xs : List (Task α)) (acc : Task (Array α)),
      (xs.foldl (fun acc t ↦ acc.bind (sync := true) fun xs ↦ t.map (sync := true) fun x ↦
        xs.push x) acc).get.toList = acc.get.toList ++ xs.map Task.get by
    simpa using h ts.toList (.pure #[])
  intro xs
  induction xs with
  | nil => intro acc; simp
  | cons t ts ih =>
    intro acc
    rw [List.foldl_cons, ih]
    simp [Task.bind, Task.map]

/-- Parallel post-processing maps every leaf. -/
theorem postLeaves_get (post : ByteArray → ByteArray) (leaves : Array ByteArray) :
    (postLeaves post leaves).get = leaves.map post := by
  rw [postLeaves, joinTasks_get, Array.map_map]
  rfl

/-- One sum batch of two packed field arrays. -/
theorem pairLeft_encode (A B l Z : Array KoalaBear.Fast.Field) (ia ib p : USize)
    (hp : p.toNat = l.size) (hZ : 16 ≤ Z.size) (hs : (encode (l ++ Z)).size < USize.size)
    (h) :
    pairLeft (encode A) (encode B) ia ib (encode (l ++ Z)) p h =
      encode (l ++ (lit16 fun k ↦ A.getD (ia.toNat + k) 0 + B.getD (ib.toNat + k) 0) ++
        Z.extract 16 Z.size) := by
  unfold pairLeft
  simp only [readUOffset_encode, add_val, usize_numeral 0 (by decide),
    usize_numeral 1 (by decide), usize_numeral 2 (by decide), usize_numeral 3 (by decide),
    usize_numeral 4 (by decide), usize_numeral 5 (by decide), usize_numeral 6 (by decide),
    usize_numeral 7 (by decide), usize_numeral 8 (by decide), usize_numeral 9 (by decide),
    usize_numeral 10 (by decide), usize_numeral 11 (by decide), usize_numeral 12 (by decide),
    usize_numeral 13 (by decide), usize_numeral 14 (by decide), usize_numeral 15 (by decide)]
  rw [write16U_cursor _ _ _ hp hZ hs]
  rfl

/-- One twiddle-scaled difference batch of two packed field arrays. -/
theorem pairRight_encode (A B w l Z : Array KoalaBear.Fast.Field) (ia ib iw p : USize)
    (hp : p.toNat = l.size) (hZ : 16 ≤ Z.size) (hs : (encode (l ++ Z)).size < USize.size)
    (h) :
    pairRight (encode A) (encode B) (encode w) ia ib iw (encode (l ++ Z)) p h =
      encode (l ++ (lit16 fun k ↦
        w.getD (iw.toNat + k) 0 * (A.getD (ia.toNat + k) 0 - B.getD (ib.toNat + k) 0)) ++
        Z.extract 16 Z.size) := by
  unfold pairRight
  simp only [readUOffset_encode, sub_val, mul_val, usize_numeral 0 (by decide),
    usize_numeral 1 (by decide), usize_numeral 2 (by decide), usize_numeral 3 (by decide),
    usize_numeral 4 (by decide), usize_numeral 5 (by decide), usize_numeral 6 (by decide),
    usize_numeral 7 (by decide), usize_numeral 8 (by decide), usize_numeral 9 (by decide),
    usize_numeral 10 (by decide), usize_numeral 11 (by decide), usize_numeral 12 (by decide),
    usize_numeral 13 (by decide), usize_numeral 14 (by decide), usize_numeral 15 (by decide)]
  rw [write16U_cursor _ _ _ hp hZ hs]
  rfl

/-- One more row in front of the remaining rows. -/
theorem lit16_rows_succ (F : Nat → α) (count : Nat) :
    lit16 (fun k ↦ F k) ++ rows (fun j k ↦ F (16 + (16 * j + k))) count =
      rows (fun j k ↦ F (16 * j + k)) (count + 1) := by
  rw [Nat.add_comm count 1, rows_add]
  have e1 : rows (fun j k ↦ F (16 * j + k)) 1 = lit16 (fun k ↦ F k) := by
    simp only [rows, Array.empty_append, Nat.mul_zero, Nat.zero_add]
  have e2 : (fun j k ↦ F (16 * (1 + j) + k)) = (fun j k ↦ F (16 + (16 * j + k))) := by
    funext j k
    congr 1
    omega
  rw [e1, e2]

theorem extract_extract16 (Z : Array α) (count : Nat) :
    (Z.extract 16 Z.size).extract (16 * count) (Z.extract 16 Z.size).size =
      Z.extract (16 * (count + 1)) Z.size := by
  rw [Array.extract_extract, Array.size_extract]
  congr 1 <;> omega

/-- The paired split loop at machine indices stores its batches from word `p`. -/
theorem pairLoop_encode (A B w : Array KoalaBear.Fast.Field) :
    ∀ (count : Nat) (ia ib iw p : USize) (l r ZL ZR : Array KoalaBear.Fast.Field),
    p.toNat = l.size → r.size = l.size → 16 * count ≤ ZL.size → 16 * count ≤ ZR.size →
    (encode (l ++ ZL)).size < USize.size → (encode (r ++ ZR)).size < USize.size → ∀ h,
    pairLoop (encode A) (encode B) (encode w) count ia ib iw p
      (encode (l ++ ZL)) (encode (r ++ ZR)) h =
      (encode (l ++ rows (fun j k ↦
          A.getD (ia.toNat + (16 * j + k)) 0 + B.getD (ib.toNat + (16 * j + k)) 0) count ++
          ZL.extract (16 * count) ZL.size),
        encode (r ++ rows (fun j k ↦ w.getD (iw.toNat + (16 * j + k)) 0 *
          (A.getD (ia.toNat + (16 * j + k)) 0 - B.getD (ib.toNat + (16 * j + k)) 0)) count ++
          ZR.extract (16 * count) ZR.size)) := by
  intro count
  induction count with
  | zero =>
    intro ia ib iw p l r ZL ZR _ _ _ _ _ _ h
    simp only [pairLoop, rows, Array.append_empty, Nat.mul_zero]
    rw [Array.extract_size, Array.extract_size]
  | succ count ih =>
    intro ia ib iw p l r ZL ZR hp hr hL hR hsL hsR h
    rw [pairLoop, pairLeft_encode _ _ _ _ _ _ _ hp (by omega) hsL,
      pairRight_encode _ _ _ _ _ _ _ _ _ (by rw [hp, hr]) (by omega) hsR]
    simp only [size_encode_fields, Array.size_append] at hsL hsR
    have ha := usize_add16 ia _ (by omega) h.2.2.2.1
    have hb := usize_add16 ib _ (by omega) h.2.2.2.2.1
    have hw := usize_add16 iw _ (by omega) h.2.2.2.2.2
    have hpp : (p + 16).toNat = p.toNat + 16 := by
      have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
      rw [USize.toNat_add, usize_numeral 16 (by decide), hsize, Nat.mod_eq_of_lt (by omega)]
    rw [ih _ _ _ _ _ _ _ _ (by rw [hpp, Array.size_append, size_lit16, hp])
      (by simp only [Array.size_append, size_lit16, hr])
      (by rw [Array.size_extract]; omega) (by rw [Array.size_extract]; omega)
      (by simp only [size_encode_fields, Array.size_append, size_lit16, Array.size_extract]; omega)
      (by simp only [size_encode_fields, Array.size_append, size_lit16, Array.size_extract]; omega)]
    rw [ha, hb, hw, extract_extract16, extract_extract16]
    simp only [Array.append_assoc]
    rw [← lit16_rows_succ (fun k ↦ A.getD (ia.toNat + k) 0 + B.getD (ib.toNat + k) 0),
      ← lit16_rows_succ (fun k ↦ w.getD (iw.toNat + k) 0 *
        (A.getD (ia.toNat + k) 0 - B.getD (ib.toNat + k) 0))]
    simp only [Nat.add_assoc, Array.append_assoc]

/-- The paired split loop stores its batches into fresh zero buffers. -/
theorem pairGo_encode (A B w : Array KoalaBear.Fast.Field) (count ia ib iw : Nat)
    (hA : ia + 16 * count ≤ A.size)
    (hB : ib + 16 * count ≤ B.size) (hw : iw + 16 * count ≤ w.size)
    (hsA : 4 * A.size < USize.size) (hsB : 4 * B.size < USize.size)
    (hsw : 4 * w.size < USize.size) :
    pairGo (encode A) (encode B) (encode w) count ia ib iw =
      (encode (rows (fun j k ↦
          A.getD (ia + (16 * j + k)) 0 + B.getD (ib + (16 * j + k)) 0) count),
        encode (rows (fun j k ↦ w.getD (iw + (16 * j + k)) 0 *
          (A.getD (ia + (16 * j + k)) 0 - B.getD (ib + (16 * j + k)) 0)) count)) := by
  have hcond : 4 * (ia + 16 * count) ≤ (encode A).size ∧
      4 * (ib + 16 * count) ≤ (encode B).size ∧
      4 * (iw + 16 * count) ≤ (encode w).size ∧ (encode A).size < USize.size ∧
      (encode B).size < USize.size ∧ (encode w).size < USize.size := by
    simp only [size_encode_fields]
    omega
  have hz : zeroWords (16 * count) = encode (#[] ++ Array.replicate (16 * count) (0 :
      KoalaBear.Fast.Field)) := by
    rw [Array.empty_append, zeroWords_encode]
  rw [pairGo, dite_eq_left_of_eq_true (eq_true hcond), hz,
    pairLoop_encode _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
      (by rw [Array.size_replicate]) (by rw [Array.size_replicate])
      (by simp only [size_encode_fields, Array.size_append, Array.size_replicate,
        Array.size_empty]; omega)
      (by simp only [size_encode_fields, Array.size_append, Array.size_replicate,
        Array.size_empty]; omega)]
  have he : (Array.replicate (16 * count) (0 : KoalaBear.Fast.Field)).extract (16 * count)
      (16 * count) = #[] := Array.extract_eq_empty_of_le (by simp)
  simp only [USize.toNat_ofNatLT, Array.empty_append, Array.size_replicate, he,
    Array.append_empty]

/-- Reserved capacity does not change an empty packed buffer. -/
theorem emptyWithCapacity_eq_encode (k : Nat) :
    ByteArray.emptyWithCapacity k = encode (#[] : Array KoalaBear.Fast.Field) := rfl

private theorem foldl_encode_append (xs : List (Array KoalaBear.Fast.Field))
    (init : Array KoalaBear.Fast.Field) :
    xs.foldl (fun acc x ↦ acc ++ encode x) (encode init) =
      encode (xs.foldl (· ++ ·) init) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [← PackedRepr.encode_append, ih]

/-- Assembling packed slices packs the flattened field arrays. -/
theorem assemble_encode (c : Nat) (S : Array (Array KoalaBear.Fast.Field)) :
    assembleChunks c (S.map encode) = encode S.flatten := by
  rw [assembleChunks_capacity]
  unfold assembleChunks
  rw [emptyWithCapacity_eq_encode, Array.foldl_map, ← Array.foldl_toList,
    foldl_encode_append, Array.foldl_toList]
  rfl

/-- Reading a packed slice. -/
theorem getD_map_encode' (S : Array (Array KoalaBear.Fast.Field)) (q : Nat) :
    (S.map encode).getD q ByteArray.empty = encode (S.getD q #[]) :=
  getD_map_encode S q

/-- `k` consecutive blocks of `s` values of `g`. -/
def slicesOf (k s : Nat) (g : Nat → KoalaBear.Fast.Field) : Array (Array KoalaBear.Fast.Field) :=
  (Array.range k).map fun q ↦ Array.ofFn (n := s) fun i ↦ g (q * s + i)

/-- Flattening consecutive blocks of a function's values. -/
theorem flatten_slicesOf (g : Nat → KoalaBear.Fast.Field) (s : Nat) :
    ∀ k, (slicesOf k s g).flatten = Array.ofFn (n := k * s) fun i ↦ g i
  | 0 => by
    rw [slicesOf, show Array.range 0 = #[] from Array.eq_empty_of_size_eq_zero Array.size_range]
    simp only [Array.map_empty, Array.flatten_empty]
    exact (Array.eq_empty_of_size_eq_zero (by simp only [Array.size_ofFn, Nat.zero_mul])).symm
  | k + 1 => by
    have ih := flatten_slicesOf g s k
    rw [slicesOf] at ih ⊢
    rw [Array.range_succ, Array.map_append, Array.flatten_append, ih]
    apply Array.ext (by simp only [Array.size_append, Array.size_ofFn, Array.map_singleton,
      Array.flatten_singleton]; ring)
    intro i h1 h2
    rw [Array.getElem_ofFn]
    simp only [Array.size_append, Array.size_ofFn, Array.map_singleton,
      Array.flatten_singleton] at h1
    by_cases hi : i < k * s
    · rw [Array.getElem_append_left (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]
    · rw [Array.getElem_append_right (by rw [Array.size_ofFn]; omega)]
      simp only [Array.map_singleton, Array.flatten_singleton, Array.size_ofFn,
        Array.getElem_ofFn]
      congr 1
      omega

@[simp] theorem size_slicesOf (k s : Nat) (g : Nat → KoalaBear.Fast.Field) :
    (slicesOf k s g).size = k := by
  simp only [slicesOf, Array.size_map, Array.size_range]

/-- Slice `q` of `slicesOf`. -/
theorem getD_slicesOf (k s : Nat) (g : Nat → KoalaBear.Fast.Field) (q : Nat) (hq : q < k) :
    (slicesOf k s g).getD q #[] = Array.ofFn (n := s) fun i ↦ g (q * s + i) := by
  simp only [slicesOf, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range,
    hq, ↓reduceIte, Option.map_some, Option.getD_some]

/-- The packed chunk outputs of one split level, over the left and right child values. -/
def levelOut (W : Array KoalaBear.Fast.Field) (half m c : Nat) (g : Nat → KoalaBear.Fast.Field) :
    Array (ByteArray × ByteArray) :=
  (Array.range m).map fun q ↦
    (encode (Array.ofFn (n := c) fun i ↦ g (q * c + i) + g (half + (q * c + i))),
      encode (Array.ofFn (n := c) fun i ↦
        W.getD (q * c + i) 0 * (g (q * c + i) - g (half + (q * c + i)))))

/-- One chunk: the pair loop over two blocks of `g` whose offsets differ by `half`. -/
theorem pairGo_blocks (W : Array KoalaBear.Fast.Field) (g : Nat → KoalaBear.Fast.Field)
    (half c q oa ob sa sb : Nat) (hc : 16 ∣ c)
    (hA : oa + c ≤ sa) (hB : ob + c ≤ sb) (hW : q * c + c ≤ W.size)
    (hsa : 4 * sa < USize.size) (hsb : 4 * sb < USize.size) (hsw : 4 * W.size < USize.size)
    (ga gb : Nat → Nat) (hga : ∀ i < c, ga (oa + i) = q * c + i)
    (hgb : ∀ i < c, gb (ob + i) = half + (q * c + i)) :
    pairGo (encode (Array.ofFn (n := sa) fun i ↦ g (ga i)))
        (encode (Array.ofFn (n := sb) fun i ↦ g (gb i))) (encode W) (c / 16) oa ob
        (q * c) =
      (encode (Array.ofFn (n := c) fun i ↦ g (q * c + i) + g (half + (q * c + i))),
        encode (Array.ofFn (n := c) fun i ↦
          W.getD (q * c + i) 0 * (g (q * c + i) - g (half + (q * c + i))))) := by
  have h16 : 16 * (c / 16) = c := Nat.mul_div_cancel' hc
  rw [pairGo_encode _ _ _ _ _ _ _ (by rw [Array.size_ofFn]; omega)
      (by rw [Array.size_ofFn]; omega) (by omega) (by rw [Array.size_ofFn]; exact hsa)
      (by rw [Array.size_ofFn]; exact hsb) hsw]
  rw [rows_eq_ofFn (fun i ↦ (Array.ofFn (n := sa) fun i ↦ g (ga i)).getD (oa + i) 0 +
      (Array.ofFn (n := sb) fun i ↦ g (gb i)).getD (ob + i) 0),
    rows_eq_ofFn (fun i ↦ W.getD (q * c + i) 0 *
      ((Array.ofFn (n := sa) fun i ↦ g (ga i)).getD (oa + i) 0 -
        (Array.ofFn (n := sb) fun i ↦ g (gb i)).getD (ob + i) 0))]
  congr 1
  · congr 1
    apply Array.ext (by simp only [Array.size_ofFn, h16])
    intro i h1 _
    simp only [Array.size_ofFn] at h1
    rw [Array.getElem_ofFn, Array.getElem_ofFn, getD_ofFn_bounded _ _ (by omega),
      getD_ofFn_bounded _ _ (by omega), hga i (by omega), hgb i (by omega)]
  · congr 1
    apply Array.ext (by simp only [Array.size_ofFn, h16])
    intro i h1 _
    simp only [Array.size_ofFn] at h1
    rw [Array.getElem_ofFn, Array.getElem_ofFn, getD_ofFn_bounded _ _ (by omega),
      getD_ofFn_bounded _ _ (by omega), hga i (by omega), hgb i (by omega)]

/-- A single buffer splits into `P` chunks. -/
theorem sliceSplit_one (W : Array KoalaBear.Fast.Field) (logN P : Nat)
    (g : Nat → KoalaBear.Fast.Field) (hshape : sliceShape logN 1 P = true)
    (hW : 2 ^ (logN - 1) ≤ W.size) (hu : 4 * 2 ^ logN < USize.size)
    (hWu : 4 * W.size < USize.size) :
    (sliceSplit (encode W) logN ((slicesOf 1 (2 ^ logN) g).map encode) P).map Task.get =
      levelOut W (2 ^ (logN - 1)) P (2 ^ (logN - 1) / P) g := by
  simp only [sliceShape, bne_iff_ne, ne_eq, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true,
    beq_iff_eq] at hshape
  obtain ⟨hlog, hP, hdiv⟩ := hshape
  have hhalf : 2 ^ logN = 2 * 2 ^ (logN - 1) := by
    rw [show logN = logN - 1 + 1 by omega, Nat.pow_succ]; simp only [Nat.add_sub_cancel]; ring
  obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hdiv
  have hcs : 2 ^ (logN - 1) / P = 16 * t := by
    rw [ht, show 16 * P * t = P * (16 * t) by ring, Nat.mul_div_cancel_left _ (by omega)]
  have hPc : P * (2 ^ (logN - 1) / P) = 2 ^ (logN - 1) := by
    rw [hcs, ht]
    ring
  have hc16 : 16 ∣ 2 ^ (logN - 1) / P := by
    rw [hcs]
    exact Nat.dvd_mul_right _ _
  unfold sliceSplit levelOut
  simp only [Array.size_map, size_slicesOf, beq_self_eq_true, ↓reduceIte, Array.map_map]
  rw [show (Array.map encode (slicesOf 1 (2 ^ logN) g)).getD 0 ByteArray.empty =
      encode (Array.ofFn (n := 2 ^ logN) fun i ↦ g i) by
    rw [getD_map_encode', getD_slicesOf _ _ _ 0 (by decide)]
    simp only [Nat.zero_mul, Nat.zero_add]]
  apply Array.map_congr_left
  intro q hq
  have hq' := Array.mem_range.mp hq
  have hqc : q * (2 ^ (logN - 1) / P) + 2 ^ (logN - 1) / P ≤ 2 ^ (logN - 1) := by
    have := Nat.mul_le_mul_right (2 ^ (logN - 1) / P) (show q + 1 ≤ P by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  simp only [Function.comp_apply, Task.spawn]
  exact pairGo_blocks W g _ _ q _ _ (2 ^ logN) (2 ^ logN) hc16 (by omega) (by omega) (by omega)
    hu hu hWu id id (fun i _ ↦ rfl) (fun i _ ↦ by simp only [id]; omega)

/-- An even number of slices splits into slice pairs. -/
theorem sliceSplit_pairs (W : Array KoalaBear.Fast.Field) (logN k s P : Nat)
    (g : Nat → KoalaBear.Fast.Field) (hshape : sliceShape logN k P = true) (hk1 : k ≠ 1)
    (hks : k * s = 2 ^ logN) (hW : 2 ^ (logN - 1) ≤ W.size) (hu : 4 * 2 ^ logN < USize.size)
    (hWu : 4 * W.size < USize.size) :
    (sliceSplit (encode W) logN ((slicesOf k s g).map encode) P).map Task.get =
      levelOut W (2 ^ (logN - 1)) (k / 2) s g := by
  have hk1' : (k == 1) = false := by simp only [beq_eq_false_iff_ne]; exact hk1
  simp only [sliceShape, bne_iff_ne, ne_eq, hk1', Bool.false_eq_true, ↓reduceIte,
    Bool.and_eq_true, beq_iff_eq] at hshape
  obtain ⟨hlog, ⟨hk2, hkd⟩, hs16⟩ := hshape
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      have := Nat.two_pow_pos logN
      rw [Nat.zero_mul] at hks
      omega
    · exact h
  have hsk : 2 ^ logN / k = s := by
    rw [← hks, Nat.mul_div_cancel_left _ hk0]
  have hhalf : 2 ^ logN = 2 * 2 ^ (logN - 1) := by
    rw [show logN = logN - 1 + 1 by omega, Nat.pow_succ]; simp only [Nat.add_sub_cancel]; ring
  have hks2 : k / 2 * s = 2 ^ (logN - 1) := by
    have : k = 2 * (k / 2) := by omega
    rw [this, Nat.mul_assoc] at hks
    omega
  unfold sliceSplit levelOut
  simp only [Array.size_map, size_slicesOf, hk1', Bool.false_eq_true, ↓reduceIte, Array.map_map,
    hsk]
  apply Array.map_congr_left
  intro q hq
  have hq' := Array.mem_range.mp hq
  have hqs : q * s + s ≤ 2 ^ (logN - 1) := by
    have := Nat.mul_le_mul_right s (show q + 1 ≤ k / 2 by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  simp only [Function.comp_apply, Task.spawn]
  rw [getD_map_encode', getD_map_encode', getD_slicesOf _ _ _ q (by omega),
    getD_slicesOf _ _ _ (q + k / 2) (by omega)]
  have hsize : s ≤ 2 ^ logN := by omega
  exact pairGo_blocks W g (2 ^ (logN - 1)) s q 0 0 s s (Nat.dvd_of_mod_eq_zero (hsk ▸ hs16))
    (by omega) (by omega) (by omega) (by omega) (by omega) hWu (fun i ↦ q * s + i)
    (fun i ↦ (q + k / 2) * s + i) (fun i _ ↦ by simp only [Nat.zero_add])
    (fun i _ ↦ by simp only [Nat.zero_add, Nat.add_mul]; omega)

/-- `Array.ofFn` at equal sizes. -/
theorem ofFn_size_congr (g : Nat → α) {m n : Nat} (h : m = n) :
    (Array.ofFn (n := m) fun i ↦ g i) = Array.ofFn (n := n) fun i ↦ g i := by
  subst h
  rfl

/-- Assembling `slicesOf` packs the values of `g`. -/
theorem assemble_slicesOf (c k s n : Nat) (g : Nat → KoalaBear.Fast.Field) (h : k * s = n) :
    assembleChunks c ((slicesOf k s g).map encode) =
      encode (Array.ofFn (n := n) fun i ↦ g i) := by
  rw [assemble_encode, flatten_slicesOf, ofFn_size_congr g h]

/-- Joining `slicesOf` packs the values of `g`. -/
theorem joinSlices_slicesOf (c k s n : Nat) (g : Nat → KoalaBear.Fast.Field) (h : k * s = n) :
    joinSlices c ((slicesOf k s g).map encode) =
      encode (Array.ofFn (n := n) fun i ↦ g i) := by
  unfold joinSlices
  split
  · rename_i hk
    simp only [Array.size_map, size_slicesOf, beq_iff_eq] at hk
    subst hk
    rw [getD_map_encode', getD_slicesOf _ _ _ 0 (by decide)]
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [ofFn_size_congr g (show s = n by omega)]
  · exact assemble_slicesOf c k s n g h

/-- The left and right child slices of one level. -/
theorem levelOut_fst (W : Array KoalaBear.Fast.Field) (half m c : Nat)
    (g : Nat → KoalaBear.Fast.Field) :
    (levelOut W half m c g).map (fun x ↦ x.1) =
      (slicesOf m c fun j ↦ g j + g (half + j)).map encode := by
  simp only [levelOut, slicesOf, Array.map_map]
  rfl

theorem levelOut_snd (W : Array KoalaBear.Fast.Field) (half m c : Nat)
    (g : Nat → KoalaBear.Fast.Field) :
    (levelOut W half m c g).map (fun x ↦ x.2) =
      (slicesOf m c fun j ↦ W.getD j 0 * (g j - g (half + j))).map encode := by
  simp only [levelOut, slicesOf, Array.map_map]
  rfl

/-- The sliced task tree computes the leaves of the binary split tree, post-processed. -/
theorem sliceChunks_eq (twF : Array (Array KoalaBear.Fast.Field)) (nInv : UInt32)
    (normalize : Bool) (P : Nat) (post : ByteArray → ByteArray)
    (leaf : Nat → ByteArray → ByteArray) :
    ∀ (depth logN k s : Nat) (g : Nat → KoalaBear.Fast.Field), k * s = 2 ^ logN → 0 < k →
      (∀ L < logN, (twF.getD L #[]).size = 2 ^ L) → 4 * 2 ^ logN < USize.size →
      (∀ X : Array KoalaBear.Fast.Field, X.size = 2 ^ (logN - depth) →
        leaf (logN - depth) (encode X) =
          post (stages (logN - depth) (twF.map encode) (encode X) nInv normalize)) →
      (sliceChunks (twF.map encode) logN ((slicesOf k s g).map encode)
        nInv normalize P post leaf depth).get =
      (splitChunks (twF.map encode) logN
        (encode (Array.ofFn (n := 2 ^ logN) fun i ↦ g i)) nInv normalize depth).get.map
          post := by
  intro depth
  induction depth with
  | zero =>
    intro logN k s g hks _ _ _ hleaf
    simp only [sliceChunks, splitChunks, Task.spawn, assemble_slicesOf _ k s _ g hks,
      Array.map_singleton]
    rw [← Nat.sub_zero logN, hleaf _ (by rw [Array.size_ofFn]), Nat.sub_zero]
  | succ depth ih =>
    intro logN k s g hks hk htw hu hleaf
    have hleaf' : ∀ X : Array KoalaBear.Fast.Field, X.size = 2 ^ (logN - 1 - depth) →
        leaf (logN - 1 - depth) (encode X) =
          post (stages (logN - 1 - depth) (twF.map encode) (encode X) nInv normalize) := by
      rw [Nat.sub_sub, Nat.add_comm 1 depth]; exact hleaf
    rw [sliceChunks]
    simp only [Array.size_map, size_slicesOf]
    split
    · rename_i hshape
      have hlog : logN ≠ 0 := by
        simp only [sliceShape, bne_iff_ne, ne_eq, Bool.and_eq_true] at hshape
        exact hshape.1
      have hhalf : 2 ^ logN = 2 * 2 ^ (logN - 1) := by
        rw [show logN = logN - 1 + 1 by omega, Nat.pow_succ]; simp only [Nat.add_sub_cancel]; ring
      have hW : (twF.getD (logN - 1) #[]).size = 2 ^ (logN - 1) := htw (logN - 1) (by omega)
      have hWu : 4 * (twF.getD (logN - 1) #[]).size < USize.size := by omega
      rw [getD_map_encode]
      -- the chunk outputs of this level
      obtain ⟨m, c, hmc, hm, hlevel⟩ : ∃ m c, m * c = 2 ^ (logN - 1) ∧ 0 < m ∧
          (sliceSplit (encode (twF.getD (logN - 1) #[])) logN ((slicesOf k s g).map encode)
            P).map Task.get = levelOut (twF.getD (logN - 1) #[]) (2 ^ (logN - 1)) m c g := by
        by_cases hk1 : k = 1
        · subst hk1
          have hs : s = 2 ^ logN := by omega
          subst hs
          have hP : P ≠ 0 ∧ 2 ^ (logN - 1) % (16 * P) = 0 := by
            simp only [sliceShape, bne_iff_ne, ne_eq, beq_self_eq_true, ↓reduceIte,
              Bool.and_eq_true, beq_iff_eq] at hshape
            exact hshape.2
          obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hP.2
          refine ⟨P, 2 ^ (logN - 1) / P, ?_, Nat.pos_of_ne_zero hP.1,
            sliceSplit_one _ logN P g hshape (by omega) hu hWu⟩
          rw [ht, show 16 * P * t = P * (16 * t) by ring, Nat.mul_div_cancel_left _
            (Nat.pos_of_ne_zero hP.1)]
        · have hk2 : k % 2 = 0 := by
            have hk1' : (k == 1) = false := by simp only [beq_eq_false_iff_ne]; exact hk1
            simp only [sliceShape, bne_iff_ne, ne_eq, hk1', Bool.false_eq_true, ↓reduceIte,
              Bool.and_eq_true, beq_iff_eq] at hshape
            exact hshape.2.1.1
          refine ⟨k / 2, s, ?_, by omega,
            sliceSplit_pairs _ logN k s P g hshape hk1 hks (by omega) hu hWu⟩
          have : k = 2 * (k / 2) := by omega
          rw [this, Nat.mul_assoc] at hks
          omega
      simp only [Task.bind, Task.map, joinTasks_get, hlevel, levelOut_fst, levelOut_snd]
      have htw' : ∀ L < logN - 1, (twF.getD L #[]).size = 2 ^ L := fun L hL ↦ htw L (by omega)
      have hu' : 4 * 2 ^ (logN - 1) < USize.size := by omega
      rw [ih (logN - 1) m c _ hmc hm htw' hu' hleaf', ih (logN - 1) m c _ hmc hm htw' hu' hleaf',
        splitChunks]
      simp only [hlog, ↓reduceIte, Task.bind, Task.map, Task.spawn, getD_map_encode]
      rw [Array.map_append]
      have hX : (encode (Array.ofFn (n := 2 ^ logN) fun i ↦ g i)).size < USize.size := by
        rw [size_encode_fields, Array.size_ofFn]; exact hu
      have hWs : (encode (twF.getD (logN - 1) #[])).size < USize.size := by
        rw [size_encode_fields]; exact hWu
      rw [Native.splitLeft_encode _ _ _ hX hWs (by rw [Array.size_ofFn]; omega) (by omega),
        Native.splitRight_encode _ _ _ hX hWs (by rw [Array.size_ofFn]; omega) (by omega)]
      have hg1 : ∀ i : Fin (2 ^ (logN - 1)),
          (Array.ofFn (n := 2 ^ logN) fun i ↦ g i).getD i.val 0 = g i := fun i ↦
        getD_ofFn_bounded _ _ (by omega) _
      have hg2 : ∀ i : Fin (2 ^ (logN - 1)),
          (Array.ofFn (n := 2 ^ logN) fun i ↦ g i).getD (i.val + 2 ^ (logN - 1)) 0 =
            g (2 ^ (logN - 1) + i) := by
        intro i
        rw [getD_ofFn_bounded _ _ (by omega) _]
        exact congrArg g (Nat.add_comm _ _)
      have hL : (Array.ofFn fun i : Fin (2 ^ (logN - 1)) ↦
          (Array.ofFn (n := 2 ^ logN) fun i ↦ g i).getD i.val 0 +
            (Array.ofFn (n := 2 ^ logN) fun i ↦ g i).getD (i.val + 2 ^ (logN - 1)) 0) =
          Array.ofFn fun i : Fin (2 ^ (logN - 1)) ↦ g i + g (2 ^ (logN - 1) + i) := by
        refine congrArg Array.ofFn (funext fun i ↦ ?_)
        rw [hg1 i, hg2 i]
      have hR : (Array.ofFn fun i : Fin (2 ^ (logN - 1)) ↦
          (twF.getD (logN - 1) #[]).getD i.val 0 *
            ((Array.ofFn (n := 2 ^ logN) fun i ↦ g i).getD i.val 0 -
              (Array.ofFn (n := 2 ^ logN) fun i ↦ g i).getD (i.val + 2 ^ (logN - 1)) 0)) =
          Array.ofFn fun i : Fin (2 ^ (logN - 1)) ↦
            (twF.getD (logN - 1) #[]).getD i 0 * (g i - g (2 ^ (logN - 1) + i)) := by
        refine congrArg Array.ofFn (funext fun i ↦ ?_)
        rw [hg1 i, hg2 i]
      rw [hL, hR]
    · simp only [Task.bind, postLeaves_get, joinSlices_slicesOf _ k s _ g hks]

/-- An array as the values of its `getD` function. -/
theorem ofFn_getD (a : Array KoalaBear.Fast.Field) (n : Nat) (ha : a.size = n) :
    (Array.ofFn (n := n) fun i ↦ a.getD i 0) = a := by
  apply Array.ext (by rw [Array.size_ofFn, ha])
  intro i h1 h2
  rw [Array.getElem_ofFn, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2,
    Option.getD_some]

/-- A single packed buffer is one slice of its values. -/
theorem slicesOf_one (a : Array KoalaBear.Fast.Field) (n : Nat) (ha : a.size = n) :
    (slicesOf 1 n fun i ↦ a.getD i 0).map encode = #[encode a] := by
  simp only [slicesOf, Array.map_map]
  rw [show Array.range 1 = #[0] by
    rw [show 1 = Nat.succ 0 from rfl, Array.range_succ,
      Array.eq_empty_of_size_eq_zero (Array.size_range (n := 0))]
    rfl]
  simp only [Array.map_singleton, Function.comp_apply, Nat.zero_mul, Nat.zero_add,
    ofFn_getD a n ha]

end Native

/-- Blocks of a concatenation of two equally blocked arrays. -/
theorem extract_append_blocks (SL SR : Array α) (M m l : Nat) (hL : SL.size = m * M)
    (hR : SR.size = m * M) (hl : l < 2 * m) :
    (SL ++ SR).extract (l * M) ((l + 1) * M) =
      if l < m then SL.extract (l * M) ((l + 1) * M)
      else SR.extract ((l - m) * M) ((l - m + 1) * M) := by
  have hl1 : (l + 1) * M ≤ 2 * m * M := Nat.mul_le_mul_right M (by omega)
  split
  · rename_i hlm
    have hle : (l + 1) * M ≤ m * M := Nat.mul_le_mul_right M (by omega)
    apply Array.ext (by simp only [Array.size_extract, Array.size_append, hL, hR]; omega)
    intro i h1 h2
    simp only [Array.size_extract, Array.size_append, hL, hR] at h1
    have hmin := Nat.min_le_left ((l + 1) * M) (m * M + m * M)
    rw [Array.getElem_extract, Array.getElem_extract,
      Array.getElem_append_left (by rw [hL]; omega)]
  · rename_i hlm
    have hge : m * M ≤ l * M := Nat.mul_le_mul_right M (by omega)
    have hsub : (l - m) * M = l * M - m * M := Nat.sub_mul l m M
    have hsub1 : (l - m + 1) * M = (l + 1) * M - m * M := by
      rw [show l - m + 1 = l + 1 - m by omega, Nat.sub_mul]
    apply Array.ext (by
      simp only [Array.size_extract, Array.size_append, hL, hR]
      rw [hsub, hsub1]
      omega)
    intro i h1 h2
    simp only [Array.size_extract, Array.size_append, hL, hR] at h1
    rw [Array.getElem_extract, Array.getElem_extract,
      Array.getElem_append_right (by rw [hL]; omega)]
    congr 1
    rw [hL, hsub]
    omega

/-- Joining the leaf blocks of two equally blocked halves. -/
theorem ofFn_blocks_append (SL SR : Array α) (M d : Nat) (hL : SL.size = 2 ^ d * M)
    (hR : SR.size = 2 ^ d * M) (f : Array α → β) :
    (Array.ofFn (n := 2 ^ d) fun l ↦ f (SL.extract (l * M) ((l + 1) * M))) ++
      (Array.ofFn (n := 2 ^ d) fun l ↦ f (SR.extract (l * M) ((l + 1) * M))) =
      Array.ofFn (n := 2 ^ (d + 1)) fun l ↦ f ((SL ++ SR).extract (l * M) ((l + 1) * M)) := by
  have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; ring
  apply Array.ext (by simp only [Array.size_append, Array.size_ofFn]; omega)
  intro i h1 h2
  simp only [Array.size_append, Array.size_ofFn] at h1
  rw [Array.getElem_ofFn, extract_append_blocks SL SR M (2 ^ d) i hL hR (by omega)]
  by_cases hi : i < 2 ^ d
  · rw [Array.getElem_append_left (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]
    simp only [hi, ↓reduceIte]
  · rw [Array.getElem_append_right (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]
    simp only [hi, ↓reduceIte, Array.size_ofFn]

/-- Every leaf of the binary split tree holds its block of the mathematical DIF output. -/
theorem Native.splitChunks_leaves (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (factor : KoalaBear.Fast.Field) (normalize : Bool) (depth : Nat)
    (ht : TwiddlesFor D tw) (hs : a.size = D.n) (hu : 4 * D.n < USize.size)
    (hn : ValidLeafNormalization D.logN depth normalize) (hd : depth ≤ D.logN) :
    (Native.splitChunks (tw.map encode) D.logN (encode a) factor.val normalize
      depth).get = Array.ofFn (n := 2 ^ depth) fun l ↦
        encode ((normalizedDifSpec D a factor normalize).extract
          (l * 2 ^ (D.logN - depth)) ((l + 1) * 2 ^ (D.logN - depth))) := by
  induction depth generalizing D a with
  | zero =>
    simp only [Native.splitChunks, Task.spawn]
    rw [Native.stages_difSpec D tw a factor normalize ht hs hu
      (by intro h; simpa only [Nat.sub_zero] using hn h)]
    apply Array.ext (by simp only [List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add, Array.size_ofFn, Nat.pow_zero])
    intro i h1 _
    have hi : i = 0 := by
      simp only [List.size_toArray, List.length_cons, List.length_nil] at h1
      omega
    subst hi
    simp only [Array.getElem_ofFn, Nat.zero_mul, Nat.zero_add, Nat.one_mul, Nat.sub_zero]
    have hsz := size_normalizedDifSpec D a factor normalize
    change encode _ = encode _
    congr 1
    rw [show 2 ^ D.logN = (normalizedDifSpec D a factor normalize).size from hsz.symm]
    simp only [normalizedDifSpec]
    split <;> exact Array.extract_size.symm
  | succ depth ih =>
    have hlog : 0 < D.logN := by omega
    rw [Native.splitChunks]
    simp only [show D.logN ≠ 0 by omega, ↓reduceIte, Task.bind, Task.map, Task.spawn]
    rw [Native.splitLeft_correct D hlog tw a ht hs hu,
      Native.splitRight_correct D hlog tw a ht hs hu]
    have ht' := TwiddlesFor.half D hlog tw ht
    have hu' : 4 * (halfDomain D hlog).n < USize.size := by
      have hh := halfDomain_size D hlog
      omega
    have hn' : ValidLeafNormalization (halfDomain D hlog).logN depth normalize := by
      intro h
      have he : (halfDomain D hlog).logN - depth = D.logN - (depth + 1) := by
        change D.logN - 1 - depth = D.logN - (depth + 1)
        omega
      rw [he]
      exact hn h
    have hl : (splitFieldsLeft D a).size = (halfDomain D hlog).n := Array.size_ofFn
    have hr : (splitFieldsRight D a).size = (halfDomain D hlog).n := Array.size_ofFn
    have hd' : depth ≤ (halfDomain D hlog).logN := by change depth ≤ D.logN - 1; omega
    change (Native.splitChunks _ (halfDomain D hlog).logN _ _ _ depth).get ++
      (Native.splitChunks _ (halfDomain D hlog).logN _ _ _ depth).get = _
    rw [ih (halfDomain D hlog) (splitFieldsLeft D a) ht' hl hu' hn' hd',
      ih (halfDomain D hlog) (splitFieldsRight D a) ht' hr hu' hn' hd']
    have he : (halfDomain D hlog).logN - depth = D.logN - (depth + 1) := by
      change D.logN - 1 - depth = D.logN - (depth + 1)
      omega
    have hsz : ∀ x, (normalizedDifSpec (halfDomain D hlog) x factor normalize).size =
        2 ^ depth * 2 ^ (D.logN - (depth + 1)) := by
      intro x
      rw [size_normalizedDifSpec]
      change 2 ^ (D.logN - 1) = _
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [he, ofFn_blocks_append _ _ _ depth (hsz _) (hsz _), normalizedDifSpec_split]
end CompPoly.CPolynomial.NTTFast.Packed
