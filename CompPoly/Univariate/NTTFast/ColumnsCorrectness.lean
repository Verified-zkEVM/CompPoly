/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Plan
import all CompPoly.Univariate.NTTFast.Columns
public import CompPoly.Univariate.NTTFast.Columns
public import CompPoly.Univariate.NTTFast.Packed.Radix4Lemmas
import Mathlib.Tactic.Ring
import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas
import CompPoly.Univariate.NTTFast.Packed.BitReversal
import all CompPoly.Univariate.NTTFast.Correctness.Basic

/-! # Correctness of the column-parallel transform

The copies are characterized by their entries. Each radix-four pass has a coordinate formula
in row/column form, so the top two passes commute with gathering a column range: the column
tasks compute exactly the gathered columns of the global passes.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Columns

variable {α R : Type*}

/-- An unchecked read is the entry at its index. -/
theorem uget_eq_getD (a : Array α) (j : USize) (h : j.toNat < a.size) (d : α) (n : Nat)
    (hn : j.toNat = n) : a.uget j h = a.getD n d := by
  subst hn
  simp only [Array.uget, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h,
    Option.getD_some]

/-- An unchecked write changes exactly its index. -/
theorem getD_uset (a : Array α) (j : USize) (v : α) (h : j.toNat < a.size) (i : Nat) (d : α) :
    (a.uset j v h).getD i d = if j.toNat = i then v else a.getD i d := by
  simp only [Array.uset, Array.getD_eq_getD_getElem?, Array.getElem?_set]
  split <;> rfl

/-- The copy loop keeps the size and writes the remaining range. -/
theorem copyGo_spec (src : Array α) (si di cnt : USize) (d : α) :
    ∀ (m : Nat) (k : USize) (dst : Array α) (hk hs hd hu), cnt.toNat - k.toNat = m →
      (copyGo src si di cnt k dst hk hs hd hu).size = dst.size ∧
      ∀ i, (copyGo src si di cnt k dst hk hs hd hu).getD i d =
        if di.toNat + k.toNat ≤ i ∧ i < di.toNat + cnt.toNat then
          src.getD (si.toNat + (i - di.toNat)) d
        else dst.getD i d := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  intro m
  induction m with
  | zero =>
    intro k dst hk hs hd hu hm
    have hk' := USize.le_iff_toNat_le.mp hk
    rw [copyGo]
    have hnot : ¬k < cnt := by rw [USize.lt_iff_toNat_lt]; omega
    simp only [hnot, ↓reduceDIte, true_and]
    intro i
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  | succ m ih =>
    intro k dst hk hs hd hu hm
    have hk' := USize.le_iff_toNat_le.mp hk
    have hlt : k < cnt := by rw [USize.lt_iff_toNat_lt]; omega
    have hcs := cnt.toNat_lt_size
    have hds := di.toNat_lt_size
    have ha : (si + k).toNat = si.toNat + k.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hb : (di + k).toNat = di.toNat + k.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hk1 : (k + 1).toNat = k.toNat + 1 := Plan.usize_add_one k (by omega)
    rw [copyGo]
    simp only [hlt, ↓reduceDIte]
    obtain ⟨h1, h2⟩ := ih (k + 1) _ _ _ _ _ (by rw [hk1]; omega)
    refine ⟨by rw [h1, Array.size_uset], fun i ↦ ?_⟩
    rw [h2 i, hk1, getD_uset, hb]
    split_ifs <;> first
      | rfl
      | omega
      | (rw [uget_eq_getD _ _ _ d _ ha]; congr 1; omega)

/-- A guarded range copy writes exactly its range. -/
theorem copyRange_getD (src : Array α) (si : Nat) (dst : Array α) (di cnt : Nat) (d : α)
    (h : si + cnt ≤ src.size ∧ di + cnt ≤ dst.size ∧ src.size < USize.size ∧
      dst.size < USize.size) (i : Nat) :
    (copyRange src si dst di cnt).getD i d =
      if di ≤ i ∧ i < di + cnt then src.getD (si + (i - di)) d else dst.getD i d := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  unfold copyRange
  rw [dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨_, h2⟩ := copyGo_spec src (USize.ofNatLT si (by omega)) (USize.ofNatLT di (by omega))
    (USize.ofNatLT cnt (by omega)) d _ 0 dst (by simp only [USize.zero_le])
    (by simp only [USize.toNat_ofNatLT]; omega) (by simp only [USize.toNat_ofNatLT]; omega)
    ⟨h.2.2.1, h.2.2.2⟩ rfl
  rw [h2 i]
  simp only [USize.toNat_ofNatLT, USize.toNat_zero, Nat.add_zero]

/-- The copy loop keeps the destination size. -/
theorem size_copyGo (src : Array α) (si di cnt : USize) :
    ∀ (m : Nat) (k : USize) (dst : Array α) (hk hs hd hu), cnt.toNat - k.toNat = m →
      (copyGo src si di cnt k dst hk hs hd hu).size = dst.size := by
  intro m
  induction m with
  | zero =>
    intro k dst hk hs hd hu hm
    have hk' := USize.le_iff_toNat_le.mp hk
    rw [copyGo]
    have hnot : ¬k < cnt := by rw [USize.lt_iff_toNat_lt]; omega
    simp only [hnot, ↓reduceDIte]
  | succ m ih =>
    intro k dst hk hs hd hu hm
    have hk' := USize.le_iff_toNat_le.mp hk
    have hlt : k < cnt := by rw [USize.lt_iff_toNat_lt]; omega
    have hk1 : (k + 1).toNat = k.toNat + 1 := Plan.usize_add_one k (by
      have := cnt.toNat_lt_size; omega)
    rw [copyGo]
    simp only [hlt, ↓reduceDIte]
    rw [ih (k + 1) _ _ _ _ _ (by rw [hk1]; omega), Array.size_uset]

/-- A range copy keeps the destination size. -/
@[simp] theorem size_copyRange (src : Array α) (si : Nat) (dst : Array α) (di cnt : Nat) :
    (copyRange src si dst di cnt).size = dst.size := by
  unfold copyRange
  split
  · exact size_copyGo src _ _ _ _ 0 dst _ _ _ _ rfl
  · rfl

/-- Filling row `k` of a fresh `r × cs` array by `op k`, for every `k < r`. -/
theorem foldl_rows_spec [Zero α] (op : Nat → Array α → Array α) (val : Nat → Nat → α)
    (cs r : Nat) (hop : ∀ k < r, ∀ acc : Array α, acc.size = r * cs →
      (op k acc).size = r * cs ∧ ∀ i, (op k acc).getD i 0 =
        if k * cs ≤ i ∧ i < k * cs + cs then val k (i - k * cs) else acc.getD i 0) :
    ((List.range r).foldl (fun acc k ↦ op k acc) (Array.replicate (r * cs) 0)).size = r * cs ∧
      ∀ k < r, ∀ c < cs,
        ((List.range r).foldl (fun acc k ↦ op k acc) (Array.replicate (r * cs) 0)).getD
          (k * cs + c) 0 = val k c := by
  suffices h : ∀ t ≤ r,
      ((List.range t).foldl (fun acc k ↦ op k acc) (Array.replicate (r * cs) 0)).size = r * cs ∧
      ∀ k < t, ∀ c < cs,
        ((List.range t).foldl (fun acc k ↦ op k acc) (Array.replicate (r * cs) 0)).getD
          (k * cs + c) 0 = val k c by
    exact h r (Nat.le_refl r)
  intro t
  induction t with
  | zero => intro _; simp only [List.range_zero, List.foldl_nil, Array.size_replicate,
      Nat.not_lt_zero, false_imp_iff, implies_true, and_self]
  | succ t ih =>
    intro ht
    obtain ⟨hsz, hval⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨h1, h2⟩ := hop t (by omega) _ hsz
    refine ⟨h1, fun k hk c hc ↦ ?_⟩
    rw [h2]
    by_cases hkt : k = t
    · subst k
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), show t * cs + c - t * cs = c by omega]
    · have hlt : k * cs + c < t * cs := by
        have := Nat.mul_le_mul_right cs (show k + 1 ≤ t by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      exact hval k (by omega) c hc

/-- Gathered rows have the requested shape and entries. -/
theorem gatherRows_spec [Zero α] (src : Array α) (M j0 cs r : Nat)
    (hsrc : ∀ k < r, k * M + j0 + cs ≤ src.size)
    (hu : src.size < USize.size ∧ r * cs < USize.size) :
    (gatherRows src M j0 cs r).size = r * cs ∧
      ∀ k < r, ∀ c < cs, (gatherRows src M j0 cs r).getD (k * cs + c) 0 =
        src.getD (k * M + (j0 + c)) 0 := by
  refine foldl_rows_spec (fun k acc ↦ copyRange src (k * M + j0) acc (k * cs) cs)
    (fun k c ↦ src.getD (k * M + (j0 + c)) 0) cs r (fun k hk acc hacc ↦ ?_)
  have hcopy : k * cs + cs ≤ r * cs := by
    have := Nat.mul_le_mul_right cs (show k + 1 ≤ r by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    exact this
  refine ⟨by rw [size_copyRange, hacc], fun i ↦ ?_⟩
  rw [copyRange_getD _ _ _ _ _ _ ⟨hsrc k hk, by omega, hu.1, by omega⟩, Nat.add_assoc]

/-- The word loop keeps the size and decodes the remaining range. -/
theorem decodeGo_spec [Zero α] [PackedRepr α] (src : ByteArray) (si di cnt : USize) :
    ∀ (m : Nat) (k : USize) (dst : Array α) (hk hs hd hu), cnt.toNat - k.toNat = m →
      (decodeGo src si di cnt k dst hk hs hd hu).size = dst.size ∧
      ∀ i, (decodeGo src si di cnt k dst hk hs hd hu).getD i 0 =
        if di.toNat + k.toNat ≤ i ∧ i < di.toNat + cnt.toNat then
          (PackedRepr.get src (si.toNat + (i - di.toNat)) : α)
        else dst.getD i 0 := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hsl := Nat.div_le_self src.size (PackedRepr.width α)
  intro m
  induction m with
  | zero =>
    intro k dst hk hs hd hu hm
    have hk' := USize.le_iff_toNat_le.mp hk
    rw [decodeGo]
    have hnot : ¬k < cnt := by rw [USize.lt_iff_toNat_lt]; omega
    simp only [hnot, ↓reduceDIte, true_and]
    intro i
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  | succ m ih =>
    intro k dst hk hs hd hu hm
    have hk' := USize.le_iff_toNat_le.mp hk
    have hlt : k < cnt := by rw [USize.lt_iff_toNat_lt]; omega
    have hcs := cnt.toNat_lt_size
    have hds := di.toNat_lt_size
    have ha : (si + k).toNat = si.toNat + k.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hb : (di + k).toNat = di.toNat + k.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hk1 : (k + 1).toNat = k.toNat + 1 := Plan.usize_add_one k (by omega)
    rw [decodeGo]
    simp only [hlt, ↓reduceDIte]
    obtain ⟨h1, h2⟩ := ih (k + 1) _ _ _ _ _ (by rw [hk1]; omega)
    refine ⟨by rw [h1, Array.size_uset], fun i ↦ ?_⟩
    rw [h2 i, hk1, getD_uset, hb, PackedRepr.getAt_eq, ha]
    split_ifs <;> first
      | rfl
      | omega
      | (congr 2; omega)

/-- A guarded range decode writes exactly its range. -/
theorem decodeRange_getD [Zero α] [PackedRepr α] (src : ByteArray) (si : Nat) (dst : Array α)
    (di cnt : Nat)
    (h : si + cnt ≤ src.size / PackedRepr.width α ∧ di + cnt ≤ dst.size ∧ src.size < USize.size ∧
      dst.size < USize.size) (i : Nat) :
    (decodeRange src si dst di cnt).getD i 0 =
      if di ≤ i ∧ i < di + cnt then (PackedRepr.get src (si + (i - di)) : α)
      else dst.getD i 0 := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hsl := Nat.div_le_self src.size (PackedRepr.width α)
  unfold decodeRange
  rw [dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨_, h2⟩ := decodeGo_spec src (USize.ofNatLT si (by omega))
    (USize.ofNatLT di (by omega)) (USize.ofNatLT cnt (by omega)) _ 0 dst
    (by simp only [USize.zero_le]) (by simp only [USize.toNat_ofNatLT]; omega)
    (by simp only [USize.toNat_ofNatLT]; omega) ⟨h.2.2.1, h.2.2.2⟩ rfl
  rw [h2 i]
  simp only [USize.toNat_ofNatLT, USize.toNat_zero, Nat.add_zero]

/-- A range decode keeps the destination size. -/
@[simp] theorem size_decodeRange [Zero α] [PackedRepr α] (src : ByteArray) (si : Nat)
    (dst : Array α) (di cnt : Nat) : (decodeRange src si dst di cnt).size = dst.size := by
  unfold decodeRange
  split
  · exact (decodeGo_spec src _ _ _ _ 0 dst _ _ _ _ rfl).1
  · rfl

/-- Row `l` of every stored column result, decoded. -/
theorem gatherLeaf_spec [Zero α] [PackedRepr α] (cols : Array ByteArray) (cs l : Nat)
    (hsrc : ∀ s < cols.size,
      l * cs + cs ≤ (cols.getD s ByteArray.empty).size / PackedRepr.width α)
    (hu : ∀ s < cols.size, (cols.getD s ByteArray.empty).size < USize.size)
    (hr : cols.size * cs < USize.size) :
    (gatherLeaf cols cs l : Array α).size = cols.size * cs ∧
      ∀ s < cols.size, ∀ c < cs, (gatherLeaf cols cs l : Array α).getD (s * cs + c) 0 =
        (PackedRepr.get (cols.getD s ByteArray.empty) (l * cs + c) : α) := by
  refine foldl_rows_spec (fun s acc ↦ decodeRange (cols.getD s ByteArray.empty) (l * cs) acc
    (s * cs) cs) (fun s c ↦ (PackedRepr.get (cols.getD s ByteArray.empty) (l * cs + c) : α))
    cs cols.size (fun s hs acc hacc ↦ ?_)
  have hcopy : s * cs + cs ≤ cols.size * cs := by
    have := Nat.mul_le_mul_right cs (show s + 1 ≤ cols.size by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    exact this
  refine ⟨by rw [size_decodeRange, hacc], fun i ↦ ?_⟩
  rw [decodeRange_getD _ _ _ _ _ ⟨by have := hsrc s hs; omega, by omega, hu s hs, by omega⟩ i]

/-- The encoding loop keeps the size and stores the remaining range. -/
theorem encodeGo_spec [Zero α] [PackedRepr α] (src : Array α) (off cnt : USize) :
    ∀ (m : Nat) (k : USize) (dst : ByteArray) (hk hs hd hu), cnt.toNat - k.toNat = m →
      (encodeGo src off cnt k dst hk hs hd hu).size = dst.size ∧
      ∀ j, (PackedRepr.get (encodeGo src off cnt k dst hk hs hd hu) j : α) =
        if off.toNat + k.toNat ≤ j ∧ j < off.toNat + cnt.toNat then
          src.getD (j - off.toNat) 0
        else PackedRepr.get dst j := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  intro m
  induction m with
  | zero =>
    intro k dst hk hs hd hu hm
    have hk' := USize.le_iff_toNat_le.mp hk
    rw [encodeGo]
    have hnot : ¬k < cnt := by rw [USize.lt_iff_toNat_lt]; omega
    simp only [hnot, ↓reduceDIte, true_and]
    intro j
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  | succ m ih =>
    intro k dst hk hs hd hu hm
    have hk' := USize.le_iff_toNat_le.mp hk
    have hlt : k < cnt := by rw [USize.lt_iff_toNat_lt]; omega
    have hcs := cnt.toNat_lt_size
    have hdl := Nat.div_le_self dst.size (PackedRepr.width α)
    have ha : (off + k).toNat = off.toNat + k.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hk1 : (k + 1).toNat = k.toNat + 1 := Plan.usize_add_one k (by omega)
    rw [encodeGo]
    simp only [hlt, ↓reduceDIte]
    obtain ⟨h1, h2⟩ := ih (k + 1) _ _ _ _ _ (by rw [hk1]; omega)
    refine ⟨by rw [h1, PackedRepr.size_setAt], fun j ↦ ?_⟩
    rw [h2 j, hk1, PackedRepr.get_setAt, ha]
    split_ifs <;> first
      | rfl
      | omega
      | (rw [uget_eq_getD _ _ _ 0 _ rfl]; congr 2; omega)

/-- An encoded array: `off` padding slots, then the entries. -/
theorem encode_spec [Zero α] [PackedRepr α] (a : Array α) (off : Nat)
    (hu : PackedRepr.width α * (off + a.size) < USize.size) :
    (encode a off).size = PackedRepr.width α * (off + a.size) ∧
      ∀ i < a.size, (PackedRepr.get (encode a off) (off + i) : α) = a.getD i 0 := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hs : off + a.size < USize.size :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ PackedRepr.width_pos) hu
  unfold encode
  rw [dite_eq_left_of_eq_true (eq_true (by rwa [PackedRepr.size_alloc]))]
  obtain ⟨h1, h2⟩ := encodeGo_spec a (USize.ofNatLT off (by omega))
    (USize.ofNatLT a.size (by omega))
    _ 0 (PackedRepr.alloc α (off + a.size)) (by simp only [USize.zero_le])
    (by simp only [USize.toNat_ofNatLT]; omega)
    (by simp only [USize.toNat_ofNatLT, PackedRepr.size_alloc_div]; omega)
    (by rwa [PackedRepr.size_alloc]) rfl
  refine ⟨by rw [h1, PackedRepr.size_alloc], fun i hi ↦ ?_⟩
  rw [h2]
  simp only [USize.toNat_ofNatLT, USize.toNat_zero, Nat.add_zero]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), Nat.add_sub_cancel_left]

/-- A guarded store changes exactly its index. -/
theorem getD_setW (a : Array α) (i : USize) (v : α) (k : Nat) (d : α) (hu : a.size < USize.size) :
    (setW a i v).getD k d = if i.toNat = k ∧ i.toNat < a.size then v else a.getD k d := by
  have hus : a.usize.toNat = a.size := by
    simp only [Array.usize, Nat.toUSize, USize.toNat_ofNat']
    exact Nat.mod_eq_of_lt hu
  unfold setW
  split
  · rename_i h
    have h' : i.toNat < a.size := by rw [← hus]; exact h
    rw [getD_uset]
    by_cases hk : i.toNat = k
    · simp only [hk, true_and, ↓reduceIte, show k < a.size by omega]
    · simp only [hk, false_and, ↓reduceIte]
  · rename_i h
    have h' : ¬i.toNat < a.size := by rw [← hus]; exact h
    simp only [h', and_false, ↓reduceIte]

@[simp] theorem size_setW (a : Array α) (i : USize) (v : α) : (setW a i v).size = a.size := by
  unfold setW
  split
  · exact Array.size_uset ..
  · rfl

/-- Joining tasks keeps their results in order. -/
theorem joinTasks_get (ts : Array (Task α)) : (joinTasks ts).get = ts.map Task.get := by
  suffices h : ∀ (l : List (Task α)) (acc : Task (Array α)),
      (l.foldl (fun acc t ↦ acc.bind (sync := true) fun xs ↦
        t.map (sync := true) fun x ↦ xs.push x) acc).get = acc.get ++ (l.map Task.get).toArray by
    rw [joinTasks, ← Array.foldl_toList, h]
    apply Array.toList_inj.mp
    simp
  intro l
  induction l with
  | nil => intro acc; simp
  | cons t l ih =>
    intro acc
    rw [List.foldl_cons, ih]
    apply Array.toList_inj.mp
    simp [Task.bind, Task.map]

/-- Component `t` of a radix-four cell's outputs. -/
def qsel (t : Nat) (o : R × R × R × R) : R :=
  match t with
  | 0 => o.1
  | 1 => o.2.1
  | 2 => o.2.2.1
  | _ => o.2.2.2

open Packed in
/-- Output `t` at lane `o` of one block of radix-four cells. -/
theorem inner_getD [Field R] (th tl : Array R) (q base : Nat) (a : Array R)
    (hs : base + 4 * q ≤ a.size) (t o : Nat) (ht : t < 4) (ho : o < q) :
    (Plan.butterflyDIFRadix4Inner th tl q 0 base (base + q) (base + 2 * q) (base + 3 * q)
      a).getD (base + t * q + o) 0 =
      qsel t (quadOutputs (th.getD o 0) (th.getD (o + q) 0) (tl.getD o 0) (a.getD (base + o) 0)
        (a.getD (base + q + o) 0) (a.getD (base + 2 * q + o) 0) (a.getD (base + 3 * q + o) 0)) := by
  rw [getD_butterflyDIFRadix4Inner _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
    (by omega)]
  simp only [quadValue, quadAt, Nat.zero_add]
  interval_cases t
  · rw [ite_eq_left (by omega), show base + 0 * q + o - base = o by omega]
    simp only [qsel, Nat.add_assoc]
  · rw [ite_eq_right (by omega), ite_eq_left (by omega),
      show base + 1 * q + o - (base + q) = o by omega]
    simp only [qsel, Nat.add_assoc]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      show base + 2 * q + o - (base + 2 * q) = o by omega]
    simp only [qsel, Nat.add_assoc]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left (by omega), show base + 3 * q + o - (base + 3 * q) = o by omega]
    simp only [qsel, Nat.add_assoc]

open Packed in
/-- One block of radix-four cells leaves every entry outside the block unchanged. -/
theorem inner_frame [Field R] (th tl : Array R) (q base : Nat) (a : Array R)
    (hs : base + 4 * q ≤ a.size) (k : Nat) (hk : k < base ∨ base + 4 * q ≤ k) :
    (Plan.butterflyDIFRadix4Inner th tl q 0 base (base + q) (base + 2 * q) (base + 3 * q)
      a).getD k 0 = a.getD k 0 := by
  rw [getD_butterflyDIFRadix4Inner _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
    (by omega)]
  simp only [quadValue]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega)]

open Packed in
/-- Coordinates of a run of radix-four blocks of `4 * q` entries: output `t` at lane `o` of
block `b ≥ block` is the cell of block `b`'s quarters; earlier blocks are unchanged. -/
theorem blocks_getD [Field R] (th tl : Array R) (q blocks : Nat) :
    ∀ (block : Nat) (a : Array R), a.size = blocks * (4 * q) →
      (∀ b, block ≤ b → b < blocks → ∀ t < 4, ∀ o < q,
        (Plan.butterflyDIFRadix4Blocks th tl (4 * q) q blocks block a).getD
          (b * (4 * q) + t * q + o) 0 =
        qsel t (quadOutputs (th.getD o 0) (th.getD (o + q) 0) (tl.getD o 0)
          (a.getD (b * (4 * q) + o) 0) (a.getD (b * (4 * q) + q + o) 0)
          (a.getD (b * (4 * q) + 2 * q + o) 0) (a.getD (b * (4 * q) + 3 * q + o) 0))) ∧
      ∀ k < block * (4 * q),
        (Plan.butterflyDIFRadix4Blocks th tl (4 * q) q blocks block a).getD k 0 = a.getD k 0 := by
  intro block
  induction h : blocks - block generalizing block with
  | zero =>
    intro a _
    rw [Plan.butterflyDIFRadix4Blocks, ite_eq_right (by omega)]
    exact ⟨fun b hb hb' ↦ absurd hb' (by omega), fun _ _ ↦ rfl⟩
  | succ n ih =>
    intro a ha
    have hlt : block < blocks := by omega
    rw [Plan.butterflyDIFRadix4Blocks, ite_eq_left hlt]
    have hb1 : (block + 1) * (4 * q) ≤ blocks * (4 * q) := Nat.mul_le_mul_right _ hlt
    have hb2 : (block + 1) * (4 * q) = block * (4 * q) + 4 * q := Nat.succ_mul _ _
    have hsz : block * (4 * q) + 4 * q ≤ a.size := by omega
    have hs' : (Plan.butterflyDIFRadix4Inner th tl q 0 (block * (4 * q))
        (block * (4 * q) + q) (block * (4 * q) + 2 * q) (block * (4 * q) + 3 * q) a).size =
        blocks * (4 * q) := by rw [Plan.size_butterflyDIFRadix4Inner, ha]
    obtain ⟨ihA, ihB⟩ := ih (block + 1) (by omega) _ hs'
    have hframe := inner_frame th tl q (block * (4 * q)) a hsz
    refine ⟨fun b hb hb' t ht o ho ↦ ?_, fun k hk ↦ ?_⟩
    · rcases Nat.eq_or_lt_of_le hb with rfl | hgt
      · rw [ihB _ (by
          have : t * q + o < 4 * q := by
            have := Nat.mul_le_mul_right q (show t + 1 ≤ 4 by omega)
            rw [Nat.succ_mul] at this; omega
          omega)]
        exact inner_getD th tl q _ a hsz t o ht ho
      · have hge : (block + 1) * (4 * q) ≤ b * (4 * q) := Nat.mul_le_mul_right _ hgt
        rw [ihA b hgt hb' t ht o ho]
        rw [hframe _ (by omega), hframe _ (by omega), hframe _ (by omega), hframe _ (by omega)]
    · rw [ihB k (by omega), hframe k (by omega)]

open Packed in
/-- The first top pass in row/column coordinates: sixteen rows of length `L`, entry
`(4 u + v, col)` is output `u` of the cell on rows `v, v + 4, v + 8, v + 12`. -/
theorem passA_getD [Field R] [DecidableEq R] (th tl Z : Array R) (L : Nat)
    (hZ : Z.size = 16 * L) (u v col : Nat) (hu : u < 4) (hv : v < 4) (hc : col < L) :
    (Plan.stageBlocksDIF th tl (4 * (4 * L)) (4 * L) 1 0 Z).getD ((4 * u + v) * L + col) 0 =
      qsel u (quadOutputs (th.getD (v * L + col) 0) (th.getD ((v + 4) * L + col) 0)
        (tl.getD (v * L + col) 0) (Z.getD (v * L + col) 0) (Z.getD ((v + 4) * L + col) 0)
        (Z.getD ((v + 8) * L + col) 0) (Z.getD ((v + 12) * L + col) 0)) := by
  rw [Plan.stageBlocksDIF_eq, Plan.checkedBlocks_eq]
  have hv' : v * L + col < 4 * L := by
    have := Nat.mul_le_mul_right L (show v + 1 ≤ 4 by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  rw [show (4 * u + v) * L + col = 0 * (4 * (4 * L)) + u * (4 * L) + (v * L + col) by ring,
    (blocks_getD th tl (4 * L) 1 0 Z (by omega)).1 0 le_rfl one_pos u hu _ hv']
  rw [show v * L + col + 4 * L = (v + 4) * L + col by ring,
    show 0 * (4 * (4 * L)) + (v * L + col) = v * L + col by ring,
    show 0 * (4 * (4 * L)) + 4 * L + (v * L + col) = (v + 4) * L + col by ring,
    show 0 * (4 * (4 * L)) + 2 * (4 * L) + (v * L + col) = (v + 8) * L + col by ring,
    show 0 * (4 * (4 * L)) + 3 * (4 * L) + (v * L + col) = (v + 12) * L + col by ring]

open Packed in
/-- The second top pass in row/column coordinates: entry `(4 u + v, col)` is output `v` of
the cell on rows `4 u, …, 4 u + 3`. -/
theorem passB_getD [Field R] [DecidableEq R] (th tl Z : Array R) (L : Nat)
    (hZ : Z.size = 16 * L) (u v col : Nat) (hu : u < 4) (hv : v < 4) (hc : col < L) :
    (Plan.stageBlocksDIF th tl (4 * L) L 4 0 Z).getD ((4 * u + v) * L + col) 0 =
      qsel v (quadOutputs (th.getD (0 * L + col) 0) (th.getD (1 * L + col) 0)
        (tl.getD (0 * L + col) 0)
        (Z.getD (4 * u * L + col) 0) (Z.getD ((4 * u + 1) * L + col) 0)
        (Z.getD ((4 * u + 2) * L + col) 0) (Z.getD ((4 * u + 3) * L + col) 0)) := by
  rw [Plan.stageBlocksDIF_eq, Plan.checkedBlocks_eq]
  rw [show (4 * u + v) * L + col = u * (4 * L) + v * L + col by ring,
    (blocks_getD th tl L 4 0 Z (by omega)).1 u (Nat.zero_le _) hu v hv col hc]
  simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul]
  rw [show col + L = L + col by ring,
    show u * (4 * L) + col = 4 * u * L + col by ring,
    show u * (4 * L) + L + col = (4 * u + 1) * L + col by ring,
    show u * (4 * L) + 2 * L + col = (4 * u + 2) * L + col by ring,
    show u * (4 * L) + 3 * L + col = (4 * u + 3) * L + col by ring]

/-- `l` holds rows `0, …, rows - 1` of the `M`-column matrix `g`, restricted to the columns
`j0, …, j0 + cs - 1`. -/
def ColAgree [Zero α] (l g : Array α) (rows cs M j0 : Nat) : Prop :=
  ∀ r < rows, ∀ c < cs, l.getD (r * cs + c) 0 = g.getD (r * M + (j0 + c)) 0

/-- The first top pass commutes with restricting to a column range. -/
theorem passA_col [Field R] [DecidableEq R] (thl tll Zl thg tlg Zg : Array R) (cs M j0 : Nat)
    (hl : Zl.size = 16 * cs) (hg : Zg.size = 16 * M) (hj : j0 + cs ≤ M)
    (hZ : ColAgree Zl Zg 16 cs M j0) (hth : ColAgree thl thg 8 cs M j0)
    (htl : ColAgree tll tlg 4 cs M j0) :
    ColAgree (Plan.stageBlocksDIF thl tll (4 * (4 * cs)) (4 * cs) 1 0 Zl)
      (Plan.stageBlocksDIF thg tlg (4 * (4 * M)) (4 * M) 1 0 Zg) 16 cs M j0 := by
  intro r hr c hc
  obtain ⟨u, v, rfl, hu, hv⟩ : ∃ u v, r = 4 * u + v ∧ u < 4 ∧ v < 4 :=
    ⟨r / 4, r % 4, by omega, by omega, by omega⟩
  rw [passA_getD _ _ _ _ hl u v c hu hv hc, passA_getD _ _ _ _ hg u v (j0 + c) hu hv (by omega),
    hZ v (by omega) c hc, hZ (v + 4) (by omega) c hc, hZ (v + 8) (by omega) c hc,
    hZ (v + 12) (by omega) c hc, hth v (by omega) c hc, hth (v + 4) (by omega) c hc,
    htl v (by omega) c hc]

/-- The second top pass commutes with restricting to a column range. -/
theorem passB_col [Field R] [DecidableEq R] (thl tll Zl thg tlg Zg : Array R) (cs M j0 : Nat)
    (hl : Zl.size = 16 * cs) (hg : Zg.size = 16 * M) (hj : j0 + cs ≤ M)
    (hZ : ColAgree Zl Zg 16 cs M j0) (hth : ColAgree thl thg 2 cs M j0)
    (htl : ColAgree tll tlg 1 cs M j0) :
    ColAgree (Plan.stageBlocksDIF thl tll (4 * cs) cs 4 0 Zl)
      (Plan.stageBlocksDIF thg tlg (4 * M) M 4 0 Zg) 16 cs M j0 := by
  intro r hr c hc
  obtain ⟨u, v, rfl, hu, hv⟩ : ∃ u v, r = 4 * u + v ∧ u < 4 ∧ v < 4 :=
    ⟨r / 4, r % 4, by omega, by omega, by omega⟩
  rw [passB_getD _ _ _ _ hl u v c hu hv hc, passB_getD _ _ _ _ hg u v (j0 + c) hu hv (by omega),
    hZ (4 * u) (by omega) c hc, hZ (4 * u + 1) (by omega) c hc, hZ (4 * u + 2) (by omega) c hc,
    hZ (4 * u + 3) (by omega) c hc, hth 0 (by omega) c hc, hth 1 (by omega) c hc,
    htl 0 (by omega) c hc]

theorem size_stageBlocksDIF [Field R] [DecidableEq R] (th tl : Array R)
    (blockSize quarter blocks block : Nat) (a : Array R) :
    (Plan.stageBlocksDIF th tl blockSize quarter blocks block a).size = a.size := by
  rw [Plan.stageBlocksDIF_eq, Plan.checkedBlocks_eq, Plan.size_butterflyDIFRadix4Blocks]

/-- The top two passes of the whole transform, as a function of the input. -/
def topPasses [Field R] [DecidableEq R] (tw : Array (Array R)) (logN : Nat) (x : Array R) :
    Array R :=
  Parallel.step false tw (logN - 4) (Parallel.step false tw (logN - 2) x)

/-- A column task computes its column range of the top two passes. -/
theorem columnTask_col [Field R] [DecidableEq R] (x : Array R) (tw : Array (Array R))
    (logN cs j0 : Nat) (h4 : 4 ≤ logN) (hx : x.size = 2 ^ logN)
    (htw : ∀ s < logN, (tw.getD s #[]).size = 2 ^ s) (hu : 2 ^ logN < USize.size)
    (hj : j0 + cs ≤ 2 ^ (logN - 4)) :
    (columnTask x tw logN (2 ^ (logN - 4)) cs j0).size = 16 * cs ∧
      ColAgree (columnTask x tw logN (2 ^ (logN - 4)) cs j0) (topPasses tw logN x) 16 cs
        (2 ^ (logN - 4)) j0 := by
  obtain ⟨m, rfl⟩ : ∃ m, logN = m + 4 := ⟨logN - 4, by omega⟩
  simp only [show m + 4 - 4 = m by omega] at hj ⊢
  have hp (k : Nat) : 2 ^ (m + k) = 2 ^ k * 2 ^ m := by rw [Nat.pow_add, Nat.mul_comm]
  have hM := Nat.two_pow_pos m
  have hx' : x.size = 16 * 2 ^ m := by rw [hx, hp 4]; rfl
  have hcs : 16 * cs ≤ 16 * 2 ^ m := by omega
  have hrow (s k : Nat) (hs : s < m + 4) (hk : 2 ^ s = k * 2 ^ m) :
      ∀ r < k, r * 2 ^ m + j0 + cs ≤ (tw.getD s #[]).size := by
    intro r hr
    rw [htw s hs, hk]
    have := Nat.mul_le_mul_right (2 ^ m) (show r + 1 ≤ k by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have hts (s : Nat) (hs : s < m + 4) : (tw.getD s #[]).size < USize.size := by
    rw [htw s hs]
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by omega)) hu
  have hu16 (k : Nat) (hk : k ≤ 16) : k * cs < USize.size := by
    have : k * cs ≤ 16 * cs := Nat.mul_le_mul_right _ hk
    rw [hx] at hx'
    omega
  have hg (s k : Nat) (hs : s < m + 4) (hk : 2 ^ s = k * 2 ^ m) (hk16 : k ≤ 16) :=
    gatherRows_spec (tw.getD s #[]) (2 ^ m) j0 cs k (hrow s k hs hk) ⟨hts s hs, hu16 k hk16⟩
  obtain ⟨hs1, hv1⟩ := hg (m + 4 - 1) 8 (by omega)
    (by rw [show m + 4 - 1 = m + 3 by omega, hp]; rfl) (by omega)
  obtain ⟨hs2, hv2⟩ := hg (m + 4 - 2) 4 (by omega)
    (by rw [show m + 4 - 2 = m + 2 by omega, hp]; rfl) (by omega)
  obtain ⟨hs3, hv3⟩ := hg (m + 4 - 3) 2 (by omega)
    (by rw [show m + 4 - 3 = m + 1 by omega, hp]; rfl) (by omega)
  obtain ⟨hs4, hv4⟩ := hg (m + 4 - 4) 1 (by omega) (by rw [show m + 4 - 4 = m by omega]; omega)
    (by omega)
  obtain ⟨hsx, hvx⟩ := gatherRows_spec x (2 ^ m) j0 cs 16 (fun r hr ↦ by
    have := Nat.mul_le_mul_right (2 ^ m) (show r + 1 ≤ 16 by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega) ⟨by omega, hu16 16 le_rfl⟩
  have hA := passA_col _ _ _ _ _ _ cs (2 ^ m) j0 hsx hx' hj hvx hv1 hv2
  have hB := passB_col _ _ _ _ _ _ cs (2 ^ m) j0 (by rw [size_stageBlocksDIF, hsx])
    (by rw [size_stageBlocksDIF, hx']) hj hA hv3 hv4
  refine ⟨by simp only [columnTask, columnPasses, size_stageBlocksDIF, hsx], ?_⟩
  have e1 : m + 4 - 2 = m + 2 := by omega
  have e2 : m + 4 - 4 = m := by omega
  have hq1 : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [hp]; rfl
  have hd1 : x.size / (4 * 2 ^ (m + 2)) = 1 := by
    rw [hx', hq1, show 4 * (4 * 2 ^ m) = 16 * 2 ^ m by ring]; exact Nat.div_self (by omega)
  have hd2 : x.size / (4 * 2 ^ m) = 4 := by
    rw [hx', show 16 * 2 ^ m = 4 * (4 * 2 ^ m) by ring]
    exact Nat.mul_div_cancel _ (by omega)
  unfold topPasses
  rw [e1, e2]
  unfold columnTask columnPasses Parallel.step
  simp only [Bool.false_eq_true, ↓reduceIte, size_stageBlocksDIF]
  rw [hd2, hd1, show m + 2 + 1 = m + 4 - 1 by omega, show m + 1 = m + 4 - 3 by omega,
    show m + 4 - 2 = m + 2 by omega, show m + 4 - 4 = m by omega, hq1]
  rw [show 16 * cs = 4 * (4 * cs) by ring]
  simp only [show m + 4 - 2 = m + 2 by omega, show m + 4 - 4 = m by omega] at hB
  exact hB

/-- The optional scaling of a reversed leaf. -/
def scaleBy [Mul α] (scale : Bool) (f v : α) : α := if scale then f * v else v

/-- Reversal steps store bit-reversed, optionally scaled words from position `q` on. -/
theorem reverseEncodeGo_spec [Zero α] [Mul α] [PackedRepr α] (a : Array α) (m : Nat)
    (scale : Bool) (f : α) (hm : 0 < m) (h32 : m ≤ 32) (ha : a.size = 2 ^ m) (off M : USize)
    (hM : M.toNat = 2 ^ m) :
    ∀ (n : Nat) (q : USize) (out : ByteArray) (hd hu), M.toNat - q.toNat = n →
      (reverseEncodeGo a (32 - m).toUInt32 scale f off M q out hd hu).size = out.size ∧
        ∀ k, (PackedRepr.get (reverseEncodeGo a (32 - m).toUInt32 scale f off M q out hd hu) k :
            α) =
          if off.toNat + q.toNat ≤ k ∧ k < off.toNat + 2 ^ m then
            scaleBy scale f (a.getD (NTT.Transform.bitRevNat m (k - off.toNat)) 0)
          else PackedRepr.get out k := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  intro n
  induction n with
  | zero =>
    intro q out hd hu hn
    rw [reverseEncodeGo, dite_eq_right_iff.mpr (fun h ↦ absurd h (by
      rw [USize.lt_iff_toNat_lt]; omega))]
    exact ⟨rfl, fun k ↦ by rw [ite_eq_right (by omega)]⟩
  | succ n ih =>
    intro q out hd hu hn
    have hq : q < M := by rw [USize.lt_iff_toNat_lt]; omega
    have hMs := M.toNat_lt_size
    have hq1 : (q + 1).toNat = q.toNat + 1 := Plan.usize_add_one q (by omega)
    have hol := Nat.div_le_self out.size (PackedRepr.width α)
    have ho : (off + q).toNat = off.toNat + q.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hr : (reverse32 q.toUInt32 >>> (32 - m).toUInt32).toUSize.toNat =
        NTT.Transform.bitRevNat m q.toNat := by
      rw [UInt32.toNat_toUSize, show q.toUInt32 = q.toNat.toUInt32 from UInt32.toFin_inj.mp rfl]
      exact reverse32_shift_eq_bitRevNat m q.toNat hm h32
    have hb : (reverse32 q.toUInt32 >>> (32 - m).toUInt32).toUSize.toNat < a.size := by
      rw [hr, ha]; exact NTT.Transform.bitRevNat_lt _ _
    rw [reverseEncodeGo, dite_eq_left_of_eq_true (eq_true hq)]
    dsimp only
    rw [dite_eq_left_of_eq_true (eq_true hb)]
    obtain ⟨hs', hv'⟩ := ih (q + 1) _ _ _ (by rw [hq1]; omega)
    refine ⟨by rw [hs', PackedRepr.size_setAt], fun k ↦ ?_⟩
    rw [hv' k, hq1, PackedRepr.get_setAt, ho]
    by_cases hk : k = off.toNat + q.toNat
    · subst k
      simp only [show ¬(off.toNat + (q.toNat + 1) ≤ off.toNat + q.toNat) by omega, false_and,
        ↓reduceIte, Nat.le_refl, true_and, show off.toNat + q.toNat < off.toNat + 2 ^ m by omega,
        Nat.add_sub_cancel_left, scaleBy]
      rw [uget_eq_getD _ _ _ 0 _ hr]
    · by_cases hk' : off.toNat + (q.toNat + 1) ≤ k ∧ k < off.toNat + 2 ^ m
      · rw [ite_eq_left hk', ite_eq_left (by omega)]
      · rw [ite_eq_right hk', ite_eq_right hk, ite_eq_right (by omega)]

/-- A reversed leaf: element `off + k` is entry `bitrev k`, optionally scaled. -/
theorem reverseEncode_spec [Zero α] [Mul α] [PackedRepr α] (a : Array α) (m : Nat)
    (scale : Bool) (f : α) (off : Nat) (hm : 0 < m) (h32 : m ≤ 32) (ha : a.size = 2 ^ m)
    (hu : PackedRepr.width α * (off + 2 ^ m) < USize.size) :
    (reverseEncode m scale f a off).size = PackedRepr.width α * (off + 2 ^ m) ∧ ∀ k < 2 ^ m,
      (PackedRepr.get (reverseEncode m scale f a off) (off + k) : α) =
        scaleBy scale f (a.getD (NTT.Transform.bitRevNat m k) 0) := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have h2 := Nat.two_pow_pos m
  have hs0 : off + 2 ^ m < USize.size :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ PackedRepr.width_pos) hu
  unfold reverseEncode
  rw [dite_eq_left_of_eq_true (eq_true (by rwa [PackedRepr.size_alloc]))]
  obtain ⟨hs, hv⟩ := reverseEncodeGo_spec a m scale f hm h32 ha (USize.ofNatLT off (by omega))
    (USize.ofNatLT (2 ^ m) (by omega)) (by simp only [USize.toNat_ofNatLT]) _ 0
    (PackedRepr.alloc α (off + 2 ^ m))
    (by simp only [USize.toNat_ofNatLT, PackedRepr.size_alloc_div]; omega)
    (by rwa [PackedRepr.size_alloc]) rfl
  refine ⟨by rw [hs, PackedRepr.size_alloc], fun k hk ↦ ?_⟩
  rw [hv]
  simp only [USize.toNat_ofNatLT, USize.toNat_zero, Nat.add_zero]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), Nat.add_sub_cancel_left]

theorem getD_set! (a : Array α) (i : Nat) (v : α) (k : Nat) (d : α) :
    (a.set! i v).getD k d = if i = k ∧ i < a.size then v else a.getD k d := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : i = k
  · subst h
    by_cases hi : i < a.size
    · simp only [hi, and_self, ↓reduceIte, Option.getD_some]
    · simp only [hi, and_false, ↓reduceIte, Option.getD_none,
        Array.getElem?_eq_none (Nat.le_of_not_lt hi)]
  · simp only [h, false_and, ↓reduceIte]

/-- Machine indices `16 q + c` and `o + q` of the assembly do not overflow. -/
theorem toNat_rowIndex (q c : USize) (n : Nat) (hc : c.toNat < 16) (hq : 16 * q.toNat + 16 ≤ n)
    (hn : n < USize.size) : (16 * q + c).toNat = 16 * q.toNat + c.toNat := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  simp only [USize.toNat_add, USize.toNat_mul, USize.reduceToNat, Nat.mod_add_mod, hsize]
  exact Nat.mod_eq_of_lt (by omega)

theorem getElem_eq_getD (r : Array β) (l : Nat) (h : l < r.size) (d : β) : r[l] = r.getD l d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some]

set_option maxHeartbeats 1000000 in
/-- One assembly step stores the sixteen entries of row `q`. -/
theorem assembleGo_spec [Zero α] [PackedRepr α] (r : Array ByteArray) (M : USize)
    (hr : r.size = 16)
    (hb : ∀ l (h : l < 16), 16 * l + M.toNat ≤ (r[l]'(by omega)).size / PackedRepr.width α ∧
      (r[l]'(by omega)).size < USize.size) (hM : 16 * M.toNat < USize.size) :
    ∀ (n : Nat) (q : USize) (out : Array α), M.toNat - q.toNat = n → out.size = 16 * M.toNat →
      (assembleGo setW r M hr hb q out).size = 16 * M.toNat ∧
      ∀ k, (assembleGo setW r M hr hb q out).getD k 0 =
        if 16 * q.toNat ≤ k ∧ k < 16 * M.toNat then
          (PackedRepr.get (r.getD (NTT.Transform.bitRevNat 4 (k % 16))
            ByteArray.empty) (16 * NTT.Transform.bitRevNat 4 (k % 16) + k / 16) : α)
        else out.getD k 0 := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  intro n
  induction n with
  | zero =>
    intro q out hn hout
    rw [assembleGo]
    have hnot : ¬q < M := by rw [USize.lt_iff_toNat_lt]; omega
    simp only [hnot, ↓reduceDIte]
    exact ⟨hout, fun k ↦ by rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]⟩
  | succ n ih =>
    intro q out hn hout
    have hq : q < M := by rw [USize.lt_iff_toNat_lt]; omega
    have hq1 : (q + 1).toNat = q.toNat + 1 := Plan.usize_add_one q (by omega)
    rw [assembleGo]
    simp only [hq, ↓reduceDIte]
    refine ⟨(ih (q + 1) _ (by rw [hq1]; omega) ?_).1, fun k ↦ ?_⟩
    · simp only [size_setW, hout]
    rw [(ih (q + 1) _ (by rw [hq1]; omega) (by simp only [size_setW, hout])).2 k, hq1]
    by_cases hk : 16 * (q.toNat + 1) ≤ k ∧ k < 16 * M.toNat
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hk), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hk)]
    have hrow (c : USize) (hc : c.toNat < 16) : (16 * q + c).toNat = 16 * q.toNat + c.toNat :=
      toNat_rowIndex q c (16 * M.toNat) hc (by omega) hM
    have hrow0 : (16 * q).toNat = 16 * q.toNat := by
      simpa only [USize.add_zero, USize.reduceToNat, Nat.add_zero] using
        hrow 0 (by simp only [USize.reduceToNat]; omega)
    simp only [PackedRepr.getAt_eq]
    simp only [getD_setW, size_setW, hout, hM]
    have hqM : q.toNat < M.toNat := hq
    have hbig : 4294967296 ≤ USize.size := by
      cases System.Platform.numBits_eq <;> simp_all [USize.size]
    have hoq (o : USize) (ho : o.toNat ≤ 240) : (o + q).toNat = o.toNat + q.toNat := by
      rw [USize.toNat_add, hsize, Nat.mod_eq_of_lt (by omega)]
    simp only [hrow 1 (by simp only [USize.reduceToNat]; omega),
      hrow 2 (by simp only [USize.reduceToNat]; omega),
      hrow 3 (by simp only [USize.reduceToNat]; omega),
      hrow 4 (by simp only [USize.reduceToNat]; omega),
      hrow 5 (by simp only [USize.reduceToNat]; omega),
      hrow 6 (by simp only [USize.reduceToNat]; omega),
      hrow 7 (by simp only [USize.reduceToNat]; omega),
      hrow 8 (by simp only [USize.reduceToNat]; omega),
      hrow 9 (by simp only [USize.reduceToNat]; omega),
      hrow 10 (by simp only [USize.reduceToNat]; omega),
      hrow 11 (by simp only [USize.reduceToNat]; omega),
      hrow 12 (by simp only [USize.reduceToNat]; omega),
      hrow 13 (by simp only [USize.reduceToNat]; omega),
      hrow 14 (by simp only [USize.reduceToNat]; omega),
      hrow 15 (by simp only [USize.reduceToNat]; omega)]
    simp only [hoq 0 (by simp only [USize.reduceToNat]; omega),
      hoq 16 (by simp only [USize.reduceToNat]; omega),
      hoq 32 (by simp only [USize.reduceToNat]; omega),
      hoq 48 (by simp only [USize.reduceToNat]; omega),
      hoq 64 (by simp only [USize.reduceToNat]; omega),
      hoq 80 (by simp only [USize.reduceToNat]; omega),
      hoq 96 (by simp only [USize.reduceToNat]; omega),
      hoq 112 (by simp only [USize.reduceToNat]; omega),
      hoq 128 (by simp only [USize.reduceToNat]; omega),
      hoq 144 (by simp only [USize.reduceToNat]; omega),
      hoq 160 (by simp only [USize.reduceToNat]; omega),
      hoq 176 (by simp only [USize.reduceToNat]; omega),
      hoq 192 (by simp only [USize.reduceToNat]; omega),
      hoq 208 (by simp only [USize.reduceToNat]; omega),
      hoq 224 (by simp only [USize.reduceToNat]; omega),
      hoq 240 (by simp only [USize.reduceToNat]; omega)]
    simp only [USize.reduceToNat, Nat.zero_add, hrow0,
      getElem_eq_getD _ _ _ ByteArray.empty]
    by_cases hr : 16 * q.toNat ≤ k ∧ k < 16 * q.toNat + 16
    · obtain ⟨c, rfl, hc⟩ : ∃ c, k = 16 * q.toNat + c ∧ c < 16 :=
        ⟨k - 16 * q.toNat, by omega, by omega⟩
      rw [ite_eq_left_of_eq_true _ _
          (eq_true (show 16 * q.toNat ≤ 16 * q.toNat + c ∧ 16 * q.toNat + c < 16 * M.toNat by
            omega)),
        show (16 * q.toNat + c) % 16 = c by omega, show (16 * q.toNat + c) / 16 = q.toNat by omega]
      have hlt : ∀ i, i < 16 → (16 * q.toNat + i < 16 * M.toNat) = True :=
        fun i hi ↦ eq_true (by omega)
      have hlt0 : (16 * q.toNat < 16 * M.toNat) = True := eq_true (by omega)
      interval_cases c <;> simp (disch := decide) only [Nat.add_zero, hlt, hlt0, and_true,
        Nat.reduceEqDiff, ↓reduceIte, Nat.add_eq_left, Nat.add_left_cancel_iff]
      all_goals first | rfl | simp only [show NTT.Transform.bitRevNat 4 0 = 0 by decide,
        Nat.mul_zero, Nat.zero_add]
    · have hne : ∀ i, i < 16 → (16 * q.toNat + i = k) = False := fun i hi ↦ eq_false (by omega)
      have hne0 : (16 * q.toNat = k) = False := eq_false (by omega)
      simp (disch := decide) only [hne, hne0, false_and, ↓reduceIte]
      rw [ite_eq_right_of_eq_false _ _
        (eq_false (show ¬(16 * q.toNat ≤ k ∧ k < 16 * M.toNat) by omega))]

theorem getD_extract [Zero α] (a : Array α) (i j k : Nat) (hk : k < j - i) (hj : j ≤ a.size) :
    (a.extract i j).getD k 0 = a.getD (i + k) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract, Nat.min_eq_left hj,
    show k < j - i from hk, ↓reduceIte]

/-- Later passes run independently on each aligned block of `M` entries. -/
theorem runPasses_extract [Field R] [DecidableEq R] (tw : Array (Array R)) (rest : List Nat)
    (Y : Array R) (M k l : Nat) (hY : Y.size = k * M) (hl : l < k)
    (hrest : ∀ low ∈ rest, 4 * 2 ^ low ∣ M) :
    Parallel.runPasses false tw rest (Y.extract (l * M) ((l + 1) * M)) =
      (Parallel.runPasses false tw rest Y).extract (l * M) ((l + 1) * M) := by
  have h1 : (l + 1) * M ≤ k * M := Nat.mul_le_mul_right _ hl
  have h2 : l * M ≤ (l + 1) * M := Nat.mul_le_mul_right _ (Nat.le_succ l)
  have hsplit : Y = Y.extract 0 (l * M) ++
      (Y.extract (l * M) ((l + 1) * M) ++ Y.extract ((l + 1) * M) Y.size) := by
    rw [Array.extract_append_extract, Nat.min_eq_left (by omega), Nat.max_eq_right (by omega),
      Array.extract_append_extract, Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]
    exact (Array.extract_eq_self_of_le (Nat.le_refl _)).symm
  have hd (i j : Nat) (hij : i ≤ j) (hj : j ≤ Y.size) (hi : M ∣ i) (hj' : M ∣ j) :
      ∀ low ∈ rest, 4 * 2 ^ low ∣ (Y.extract i j).size := by
    intro low hlow
    rw [Array.size_extract_of_le hj]
    exact Nat.dvd_trans (hrest low hlow) (Nat.dvd_sub hj' hi)
  conv_rhs => rw [hsplit]
  rw [Parallel.runPasses_append, Parallel.runPasses_append]
  · rw [Array.extract_append, Array.extract_append]
    simp only [Parallel.size_runPasses, Array.size_extract_of_le (show l * M ≤ Y.size by omega),
      Array.size_extract_of_le (show (l + 1) * M ≤ Y.size by omega), Nat.sub_zero, Nat.sub_self]
    rw [show (l + 1) * M - l * M = M by rw [Nat.succ_mul]; omega]
    have hA : (Parallel.runPasses false tw rest (Y.extract 0 (l * M))).extract (l * M)
        ((l + 1) * M) = #[] := Array.extract_eq_empty_of_le (by
      simp only [Parallel.size_runPasses, Array.size_extract]; omega)
    have hB : (Parallel.runPasses false tw rest (Y.extract (l * M) ((l + 1) * M))).extract 0 M =
        Parallel.runPasses false tw rest (Y.extract (l * M) ((l + 1) * M)) :=
      Array.extract_eq_self_of_le (by
        simp only [Parallel.size_runPasses, Array.size_extract]; rw [Nat.succ_mul]; omega)
    rw [hA, hB, Nat.zero_sub, Array.extract_eq_empty_of_le
      (as := Parallel.runPasses false tw rest (Y.extract ((l + 1) * M) Y.size)) (i := 0) (j := 0)
      (Nat.min_le_left _ _), Array.empty_append, Array.append_empty]
  · intro low hlow
    exact ⟨hd _ _ h2 (by omega) (Nat.dvd_mul_left _ _) (Nat.dvd_mul_left _ _) low hlow,
      hd _ _ (by omega) (le_refl _) (Nat.dvd_mul_left _ _) (by rw [hY]; exact Nat.dvd_mul_left _ _)
        low hlow⟩
  · intro low hlow
    refine ⟨hd _ _ (Nat.zero_le _) (by omega) (Nat.dvd_zero _) (Nat.dvd_mul_left _ _) low hlow, ?_⟩
    rw [Array.size_append]
    exact Nat.dvd_add (hd _ _ h2 (by omega) (Nat.dvd_mul_left _ _) (Nat.dvd_mul_left _ _) low hlow)
      (hd _ _ (by omega) (le_refl _) (Nat.dvd_mul_left _ _) (by rw [hY]; exact Nat.dvd_mul_left _ _)
        low hlow)

theorem getD_of_size_le [Zero α] (a : Array α) (k : Nat) (hk : a.size ≤ k) : a.getD k 0 = 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hk, Option.getD_none]

theorem getD_map_range (F : Nat → α) (n k : Nat) (hk : k < n) (d : α) :
    ((Array.range n).map F).getD k d = F k := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hk,
    ↓reduceIte, Option.map_some, Option.getD_some]


/-! ### The radix-two layer of odd sizes -/

/-- The value of entry `k` after the pair butterflies of `a`. -/
def pairValue [Field R] (tw0 : Array R) (a : Array R) (k : Nat) : R :=
  if k % 2 = 0 then a.getD k 0 + a.getD (k + 1) 0
  else tw0.getD 0 0 * (a.getD (k - 1) 0 - a.getD k 0)

theorem butterflyDIFBlocks_pairs_getD [Field R] (tw0 : Array R) (a : Array R) :
    ∀ (n block : Nat) (acc : Array R), n = (a.size / 2) - block →
      acc.size = a.size → (∀ k, 2 * block ≤ k → acc.getD k 0 = a.getD k 0) →
      ∀ k, (Plan.butterflyDIFBlocks tw0 2 1 (a.size / 2) block acc).getD k 0 =
        if 2 * block ≤ k ∧ k < 2 * (a.size / 2) then pairValue tw0 a k else acc.getD k 0 := by
  intro n
  induction n with
  | zero =>
    intro block acc hn _ _ k
    rw [Plan.butterflyDIFBlocks]
    simp only [show ¬block < a.size / 2 by omega, ↓reduceIte]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  | succ n ih =>
    intro block acc hn hs ha k
    rw [Plan.butterflyDIFBlocks]
    simp only [show block < a.size / 2 by omega, ↓reduceIte]
    have hstep : Plan.butterflyDIFInner tw0 1 0 (block * 2) (block * 2 + 1) acc =
        (acc.set! (block * 2) (acc.getD (block * 2) 0 + acc.getD (block * 2 + 1) 0)).set!
          (block * 2 + 1) (tw0.getD 0 0 * (acc.getD (block * 2) 0 -
            acc.getD (block * 2 + 1) 0)) := by
      rw [Plan.butterflyDIFInner]
      simp only [Nat.zero_lt_one, ↓reduceIte]
      rw [Plan.butterflyDIFInner]
      simp only [Nat.lt_irrefl, ↓reduceIte]
    rw [hstep]
    have hsz : ((acc.set! (block * 2) (acc.getD (block * 2) 0 + acc.getD (block * 2 + 1) 0)).set!
        (block * 2 + 1) (tw0.getD 0 0 * (acc.getD (block * 2) 0 -
          acc.getD (block * 2 + 1) 0))).size = a.size := by
      simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hs]
    rw [ih (block + 1) _ (by omega) hsz (fun j hj ↦ by
      rw [getD_set!, getD_set!]
      simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      exact ha j (by omega)) k]
    have h0 := ha (block * 2) (by omega)
    have h1 := ha (block * 2 + 1) (by omega)
    by_cases hk : 2 * (block + 1) ≤ k ∧ k < 2 * (a.size / 2)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hk), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hk), getD_set!, getD_set!]
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    by_cases hk1 : k = block * 2 + 1
    · subst hk1
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, by omega⟩),
        ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
      simp only [pairValue, show (block * 2 + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte,
        Nat.add_sub_cancel, h0, h1]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ hk1 h.1.symm))]
    by_cases hk0 : k = block * 2
    · subst hk0
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, by omega⟩),
        ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
      simp only [pairValue, show block * 2 % 2 = 0 by omega, ↓reduceIte, h0, h1]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ hk0 h.1.symm)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem lastPair_getD [Field R] (tw0 a : Array R) (k : Nat) :
    (Columns.lastPair tw0 a).getD k 0 =
      if k < 2 * (a.size / 2) then pairValue tw0 a k else a.getD k 0 := by
  rw [Columns.lastPair, butterflyDIFBlocks_pairs_getD tw0 a _ 0 a rfl rfl (fun _ _ ↦ rfl) k]
  simp only [Nat.mul_zero, Nat.zero_le, true_and]

@[simp] theorem size_lastPair [Field R] (tw0 a : Array R) :
    (Columns.lastPair tw0 a).size = a.size := by
  simp only [Columns.lastPair, Plan.size_butterflyDIFBlocks]

/-- Pair butterflies on an even-aligned slice are the slice of the pair butterflies. -/
theorem lastPair_extract [Field R] (tw0 Y : Array R) (i j : Nat) (hi : i % 2 = 0)
    (hj : j % 2 = 0) (hij : i ≤ j) (hjY : j ≤ Y.size) :
    Columns.lastPair tw0 (Y.extract i j) = (Columns.lastPair tw0 Y).extract i j := by
  apply Packed.array_eq_of_getD _ _ 0 (by simp only [size_lastPair, Array.size_extract])
  intro k
  by_cases hk : k < j - i
  · rw [getD_extract _ _ _ _ hk (by rw [size_lastPair]; exact hjY), lastPair_getD,
      lastPair_getD]
    have hs : (Y.extract i j).size = j - i := by rw [Array.size_extract]; omega
    rw [hs, ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    unfold pairValue
    rw [show (i + k) % 2 = k % 2 by omega]
    split
    · rw [getD_extract _ _ _ _ hk hjY, getD_extract _ _ _ _ (by omega) hjY]
      rw [show i + (k + 1) = i + k + 1 by omega]
    · rw [getD_extract _ _ _ _ hk hjY, getD_extract _ _ _ _ (by omega) hjY]
      rw [show i + (k - 1) = i + k - 1 by omega]
  · rw [getD_of_size_le _ _ (by simp only [size_lastPair, Array.size_extract]; omega),
      getD_of_size_le _ _ (by simp only [Array.size_extract]; omega)]

@[simp] theorem size_leafPasses [Field R] [DecidableEq R] (tw : Array (Array R))
    (rest : List Nat) (odd : Bool) (a : Array R) :
    (leafPasses tw rest odd a).size = a.size := by
  unfold leafPasses
  split <;> simp only [size_lastPair, Parallel.size_runPasses]

/-- The leaf layers of block `l` are block `l` of the leaf layers of the whole array. -/
theorem leafPasses_extract [Field R] [DecidableEq R] (tw : Array (Array R)) (rest : List Nat)
    (odd : Bool) (Y : Array R) (M k l : Nat) (hY : Y.size = k * M) (hl : l < k)
    (hM : M % 2 = 0) (hrest : ∀ low ∈ rest, 4 * 2 ^ low ∣ M) :
    leafPasses tw rest odd (Y.extract (l * M) ((l + 1) * M)) =
      (leafPasses tw rest odd Y).extract (l * M) ((l + 1) * M) := by
  unfold leafPasses
  rw [runPasses_extract tw rest _ _ k l hY hl hrest]
  split
  · have h1 : (l + 1) * M ≤ k * M := Nat.mul_le_mul_right _ hl
    exact lastPair_extract _ _ _ _ (by rw [Nat.mul_mod, hM, Nat.mul_zero, Nat.zero_mod])
      (by rw [Nat.mul_mod, hM, Nat.mul_zero, Nat.zero_mod]) (Nat.mul_le_mul_right _ (by omega))
      (by rw [Parallel.size_runPasses, hY]; exact h1)
  · rfl

/-- The column-parallel transform: the top two passes, the remaining passes on every block, and
the bit-reversal permutation, optionally scaled. -/
theorem transform_eq [Field R] [DecidableEq R] [PackedRepr R] (tw : Array (Array R)) (logN S : Nat)
    (rest : List Nat) (scale : Bool) (f : R) (x : Array R) (h4 : 4 < logN) (h36 : logN ≤ 36)
    (hx : x.size = 2 ^ logN) (htw : ∀ s < logN, (tw.getD s #[]).size = 2 ^ s)
    (hu : PackedRepr.width R * (2 ^ logN + 256) ≤ USize.size) (hS : 0 < S)
    (hdiv : S ∣ 2 ^ (logN - 4))
    (hrest : ∀ low ∈ rest, 4 * 2 ^ low ∣ 2 ^ (logN - 4)) :
    transform tw logN S rest scale f x = Array.ofFn (n := 2 ^ logN) fun i ↦
      scaleBy scale f ((leafPasses tw rest (logN % 2 == 1) (topPasses tw logN x)).getD
        (NTT.Transform.bitRevNat logN i) 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, logN = m + 4 := ⟨logN - 4, by omega⟩
  have hm4 : m + 4 - 4 = m := by omega
  rw [hm4] at hdiv hrest
  have hp : 2 ^ (m + 4) = 16 * 2 ^ m := by rw [Nat.pow_add, Nat.mul_comm]
  have hM := Nat.two_pow_pos m
  obtain ⟨cs, hcs⟩ := hdiv
  have hcs0 : 0 < cs := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hcsM : 2 ^ m / S = cs := by rw [hcs, Nat.mul_div_cancel_left _ hS]
  have hw := PackedRepr.width_pos (R := R)
  have hu1 : 2 ^ (m + 4) + 256 ≤ USize.size := le_trans (Nat.le_mul_of_pos_left _ hw) hu
  have hmono (t : Nat) (ht : t ≤ 2 ^ (m + 4) + 255) : PackedRepr.width R * t < USize.size :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left (by omega) hw) hu
  have hu' : 2 ^ (m + 4) < USize.size := by omega
  have hY : (topPasses tw (m + 4) x).size = 16 * 2 ^ m := by
    rw [topPasses, Parallel.size_step, Parallel.size_step, hx, hp]
  let cols := (Array.range S).map fun s ↦ encode (columnTask x tw (m + 4) (2 ^ m) cs (s * cs)) 0
  have hcolsz : cols.size = S := by simp only [cols, Array.size_map, Array.size_range]
  have hcol (s : Nat) (hs : s < S) :
      (columnTask x tw (m + 4) (2 ^ m) cs (s * cs)).size = 16 * cs ∧
        ColAgree (columnTask x tw (m + 4) (2 ^ m) cs (s * cs)) (topPasses tw (m + 4) x) 16 cs
          (2 ^ m) (s * cs) := by
    have := columnTask_col x tw (m + 4) cs (s * cs) (by omega) hx htw hu' (by
      rw [hm4, hcs]
      have := Nat.mul_le_mul_right cs (show s + 1 ≤ S by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega)
    rwa [hm4] at this
  have hcolsg (s : Nat) (hs : s < S) :
      cols.getD s ByteArray.empty = encode (columnTask x tw (m + 4) (2 ^ m) cs (s * cs)) 0 :=
    getD_map_range _ S s hs _
  have hcs16 : 16 * cs ≤ 16 * 2 ^ m := by
    have : cs ≤ 2 ^ m := by rw [hcs]; exact Nat.le_mul_of_pos_left _ hS
    omega
  have henc (s : Nat) (hs : s < S) :=
    encode_spec (columnTask x tw (m + 4) (2 ^ m) cs (s * cs)) 0
      (hmono _ (by rw [(hcol s hs).1]; omega))
  have hleafIn (l : Nat) (hl : l < 16) :
      (gatherLeaf cols cs l : Array R) =
        (topPasses tw (m + 4) x).extract (l * 2 ^ m) ((l + 1) * 2 ^ m) := by
    have hlM : (l + 1) * 2 ^ m ≤ 16 * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
    have hlc : l * cs + cs ≤ 16 * cs := by
      have := Nat.mul_le_mul_right cs (show l + 1 ≤ 16 by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; exact this
    obtain ⟨hgs, hgv⟩ := gatherLeaf_spec (α := R) cols cs l
      (fun s hs ↦ by
        rw [hcolsz] at hs
        rw [hcolsg s hs, (henc s hs).1, (hcol s hs).1, Nat.mul_div_cancel_left _ hw]; omega)
      (fun s hs ↦ by
        rw [hcolsz] at hs
        rw [hcolsg s hs, (henc s hs).1, (hcol s hs).1]
        exact hmono _ (by omega))
      (by rw [hcolsz, ← hcs]; rw [hp] at hu1; omega)
    apply Packed.array_eq_of_getD _ _ 0 (by
      rw [hgs, hcolsz, Array.size_extract_of_le (by omega), ← hcs, Nat.succ_mul]; omega)
    intro k
    by_cases hk : k < 2 ^ m
    · have hkd : k = k / cs * cs + k % cs := (Nat.div_add_mod' k cs).symm
      have hks : k / cs < S := by
        rw [Nat.div_lt_iff_lt_mul hcs0, ← hcs]; exact hk
      rw [getD_extract _ _ _ _ (by rw [Nat.succ_mul]; omega) (by omega), hkd,
        hgv _ (by rw [hcolsz]; exact hks) _ (Nat.mod_lt _ hcs0), hcolsg _ hks]
      have hlk : l * cs + k % cs < (columnTask x tw (m + 4) (2 ^ m) cs (k / cs * cs)).size := by
        rw [(hcol _ hks).1]; have := Nat.mod_lt k hcs0; omega
      have he := (henc _ hks).2 _ hlk
      rw [Nat.zero_add] at he
      rw [he]
      exact (hcol _ hks).2 l hl (k % cs) (Nat.mod_lt _ hcs0)
    · rw [getD_of_size_le _ _ (by rw [hgs, hcolsz, ← hcs]; omega),
        getD_of_size_le _ _ (by rw [Array.size_extract_of_le (by omega), Nat.succ_mul]; omega)]
  have hZ : (Parallel.runPasses false tw rest (topPasses tw (m + 4) x)).size = 16 * 2 ^ m := by
    rw [Parallel.size_runPasses, hY]
  let odd := (m + 4) % 2 == 1
  let L := fun l ↦ leafPasses tw rest odd (gatherLeaf cols cs l : Array R)
  have hm2 : 2 ^ m % 2 = 0 := by
    rw [show m = (m - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left]
  have hleaf (l : Nat) (hl : l < 16) :
      (L l).size = 2 ^ m ∧ ∀ i < 2 ^ m, (L l).getD i 0 =
        (leafPasses tw rest odd (topPasses tw (m + 4) x)).getD (l * 2 ^ m + i) 0 := by
    have hlM : (l + 1) * 2 ^ m ≤ 16 * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
    refine ⟨?_, fun i hi ↦ ?_⟩
    · simp only [L]
      rw [size_leafPasses, hleafIn l hl, Array.size_extract_of_le (by omega),
        Nat.succ_mul]; omega
    · simp only [L]
      rw [hleafIn l hl, leafPasses_extract tw rest _ _ _ 16 l hY hl hm2 hrest,
        getD_extract _ _ _ _ (by rw [Nat.succ_mul]; omega) (by
          rw [size_leafPasses, hY]; omega)]
  have hT : (((Array.range 16).map fun l ↦ (joinTasks ((Array.range S).map fun s ↦
      Task.spawn fun _ ↦ encode (columnTask x tw (m + 4) (2 ^ (m + 4 - 4)) (2 ^ (m + 4 - 4) / S)
        (s * (2 ^ (m + 4 - 4) / S))) 0)).bind fun cols ↦ Task.spawn fun _ ↦
          leafTask cols tw rest ((m + 4) % 2 == 1) (m + 4 - 4) (2 ^ (m + 4 - 4) / S) l scale
            f).map Task.get) =
      (Array.range 16).map fun l ↦ leafTask cols tw rest odd m cs l scale f := by
    simp only [Array.map_map, hm4, hcsM]
    congr 1
    funext l
    change leafTask (joinTasks _).get tw rest odd m cs l scale f = _
    rw [joinTasks_get, Array.map_map]
    rfl
  have hL (l : Nat) (hl : l < 16) := reverseEncode_spec (L l) m scale f (16 * l) (by omega)
    (by omega) (hleaf l hl).1 (hmono _ (by omega))
  unfold transform
  dsimp only
  rw [hT, hm4]
  let r := (Array.range 16).map fun l ↦ leafTask cols tw rest odd m cs l scale f
  have hr16 : r.size = 16 := by simp only [r, Array.size_map, Array.size_range]
  have hrg (l : Nat) (hl : l < 16) :
      r.getD l ByteArray.empty = reverseEncode m scale f (L l) (16 * l) :=
    getD_map_range _ 16 l hl _
  have hMu : 2 ^ m < USize.size := by omega
  have hall : (List.range 16).all (fun l ↦ decide (16 * l + 2 ^ m ≤
      (r.getD l ByteArray.empty).size / PackedRepr.width R ∧
      (r.getD l ByteArray.empty).size < USize.size)) = true :=
    List.all_eq_true.mpr fun l hl ↦ by
      have hl' := List.mem_range.mp hl
      rw [hrg l hl', (hL l hl').1]
      exact decide_eq_true ⟨by rw [Nat.mul_div_cancel_left _ hw], hmono _ (by omega)⟩
  change assemble setW r (2 ^ m) (Array.replicate (16 * 2 ^ m) 0) = _
  unfold assemble
  rw [dite_eq_left_of_eq_true (eq_true hMu), dite_eq_left_of_eq_true (eq_true hr16),
    dite_eq_left_of_eq_true (eq_true hall)]
  obtain ⟨has, hav⟩ := assembleGo_spec (α := R) r (USize.ofNatLT (2 ^ m) hMu) hr16 _
    (by simp only [USize.toNat_ofNatLT]; omega) _ 0 (Array.replicate (16 * 2 ^ m) 0) rfl
    (by simp only [Array.size_replicate, USize.toNat_ofNatLT])
  simp only [USize.toNat_ofNatLT, USize.toNat_zero, Nat.mul_zero] at has hav
  apply Packed.array_eq_of_getD _ _ 0 (by rw [has, Array.size_ofFn, hp])
  intro k
  by_cases hk : k < 16 * 2 ^ m
  · have hb := NTT.Transform.bitRevNat_lt 4 (k % 16)
    rw [hav k, ite_eq_left_of_eq_true _ _ (eq_true ⟨Nat.zero_le _, hk⟩),
      Packed.getD_ofFn_bounded _ _ (by rw [hp]; exact hk), hrg _ hb,
      (hL _ hb).2 _ (by omega),
      (hleaf _ hb).2 _ (NTT.Transform.bitRevNat_lt _ _)]
    have hc := Packed.bitRevNat_concat m 4 (k / 16) (k % 16) (Nat.mod_lt _ (by decide))
    rw [show 2 ^ 4 * (k / 16) + k % 16 = k by omega] at hc
    rw [hc, Nat.mul_comm (2 ^ m)]
  · rw [getD_of_size_le _ _ (by rw [has]; omega),
      getD_of_size_le _ _ (by rw [Array.size_ofFn, hp]; omega)]

/-! ### Packed input and output -/

theorem setW_eq (a : Array α) (i : USize) (v : α) (hu : a.size < USize.size) :
    setW a i v = a.setIfInBounds i.toNat v := by
  have hus : a.usize.toNat = a.size := by
    simp only [Array.usize, Nat.toUSize, USize.toNat_ofNat']
    exact Nat.mod_eq_of_lt hu
  unfold setW
  split
  · rename_i h
    have hi : i.toNat < a.size := by rw [← hus]; exact USize.lt_iff_toNat_lt.mp h
    simp only [Array.uset, Array.setIfInBounds, hi, ↓reduceDIte]
  · rename_i h
    have hi : ¬ i.toNat < a.size := fun h' ↦ h (USize.lt_iff_toNat_lt.mpr (by rw [hus]; exact h'))
    simp only [Array.setIfInBounds, hi, ↓reduceDIte]

theorem setIf_encode_setW [PackedRepr α] (a : Array α) (i : USize) (v : α)
    (hu : PackedRepr.width α * a.size < USize.size) :
    PackedRepr.setIf _ hu (PackedRepr.encode a) i v = PackedRepr.encode (setW a i v) := by
  rw [PackedRepr.setIf_encode _ _ _ hu, setW_eq _ _ _
    (Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ PackedRepr.width_pos) hu)]

theorem setIf_encode_setW_of_eq [PackedRepr α] (a : Array α) (i : USize) (v : α) (m : Nat)
    (hm : m < USize.size) (hu : PackedRepr.width α * a.size = m) :
    PackedRepr.setIf m hm (PackedRepr.encode a) i v = PackedRepr.encode (setW a i v) := by
  subst hu
  exact setIf_encode_setW a i v hm

/-- Two interleave runs whose stores preserve a relation on every index they store at keep
the relation. -/
theorem assembleGo_rel [PackedRepr α] {β₁ β₂ : Type*} (set₁ : β₁ → USize → α → β₁)
    (set₂ : β₂ → USize → α → β₂) (Rel : β₁ → β₂ → Prop) (r : Array ByteArray) (M : USize)
    (hr : r.size = 16) (hb) (lo : Nat) (hM : 16 * M.toNat < USize.size)
    (hstep : ∀ b₁ b₂ (i : USize) v, lo ≤ i.toNat → i.toNat < 16 * M.toNat → Rel b₁ b₂ →
      Rel (set₁ b₁ i v) (set₂ b₂ i v)) :
    ∀ (n : Nat) (q : USize) b₁ b₂, M.toNat - q.toNat = n → lo ≤ 16 * q.toNat → Rel b₁ b₂ →
      Rel (assembleGo set₁ r M hr hb q b₁) (assembleGo set₂ r M hr hb q b₂) := by
  intro n
  induction n with
  | zero =>
    intro q b₁ b₂ hn _ hR
    have hnot : ¬q < M := by rw [USize.lt_iff_toNat_lt]; omega
    rw [assembleGo, assembleGo]
    simp only [hnot, ↓reduceDIte]
    exact hR
  | succ n ih =>
    intro q b₁ b₂ hn hlo hR
    have hq : q < M := by rw [USize.lt_iff_toNat_lt]; omega
    have hqM : q.toNat < M.toNat := hq
    have hq1 : (q + 1).toNat = q.toNat + 1 := Plan.usize_add_one q (by omega)
    have hrow (c : USize) (hc : c.toNat < 16) : (16 * q + c).toNat = 16 * q.toNat + c.toNat :=
      toNat_rowIndex q c (16 * M.toNat) hc (by omega) hM
    have hrow0 : (16 * q).toNat = 16 * q.toNat := by
      simpa only [USize.add_zero, USize.reduceToNat, Nat.add_zero] using
        hrow 0 (by simp only [USize.reduceToNat]; omega)
    rw [assembleGo, assembleGo]
    simp only [hq, ↓reduceDIte]
    apply ih (q + 1) _ _ (by rw [hq1]; omega) (by rw [hq1]; omega)
    repeat' (refine hstep _ _ _ _ ?_ ?_ ?_)
    all_goals first
      | exact hR
      | (rw [hrow0]; omega)
      | (rw [hrow _ (by simp only [USize.reduceToNat]; omega)]; simp only [USize.reduceToNat]
         omega)

theorem setW_extract (F : Array α) (i d : USize) (e : Nat) (v : α) (hF : F.size = e)
    (he : e < USize.size) (hd : d.toNat ≤ i.toNat) (hi : i.toNat < e) :
    (setW F i v).extract d.toNat e = setW (F.extract d.toNat e) (i - d) v := by
  have hs : (F.extract d.toNat e).size < USize.size := by
    rw [Array.size_extract]; omega
  rw [setW_eq _ _ _ (by omega), setW_eq _ _ _ hs, USize.toNat_sub_of_le _ _
    (USize.le_iff_toNat_le.mpr hd)]
  apply Array.ext
  · simp only [Array.size_extract, Array.size_setIfInBounds]
  · intro j h1 h2
    simp only [Array.size_extract, Array.size_setIfInBounds] at h1 h2
    simp only [Array.getElem_extract, Array.getElem_setIfInBounds (show d.toNat + j < F.size by
      omega), Array.getElem_setIfInBounds (show j < (F.extract d.toNat e).size by
        rw [Array.size_extract]; omega)]
    split <;> split <;> first | rfl | omega

/-- Decoding a range of packed elements is copying the range of the elements. -/
theorem decodeRange_encode [Zero α] [PackedRepr α] (xs : Array α) (si : Nat) (dst : Array α)
    (di cnt : Nat) (hx : PackedRepr.width α * xs.size < USize.size) :
    decodeRange (PackedRepr.encode xs) si dst di cnt = copyRange xs si dst di cnt := by
  have hdiv : (PackedRepr.encode xs).size / PackedRepr.width α = xs.size := by
    rw [PackedRepr.size_encode, Nat.mul_div_cancel_left _ PackedRepr.width_pos]
  have hxs : xs.size < USize.size :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ PackedRepr.width_pos) hx
  by_cases h : si + cnt ≤ xs.size ∧ di + cnt ≤ dst.size ∧ dst.size < USize.size
  · apply Packed.array_eq_of_getD _ _ 0 (by rw [size_decodeRange, size_copyRange])
    intro i
    rw [decodeRange_getD _ _ _ _ _ ⟨by rw [hdiv]; exact h.1, h.2.1,
        by rw [PackedRepr.size_encode]; exact hx, h.2.2⟩,
      copyRange_getD _ _ _ _ _ _ ⟨h.1, h.2.1, hxs, h.2.2⟩]
    split
    · rw [PackedRepr.get_encode _ _ (by omega), Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem (by omega), Option.getD_some]
    · rfl
  · have h1 : decodeRange (PackedRepr.encode xs) si dst di cnt = dst := by
      unfold decodeRange
      rw [dite_eq_right_iff.mpr (fun hc ↦ absurd ⟨by rw [← hdiv]; exact hc.1, hc.2.1,
        hc.2.2.2⟩ h)]
    have h2 : copyRange xs si dst di cnt = dst := by
      unfold copyRange
      rw [dite_eq_right_iff.mpr (fun hc ↦ absurd ⟨hc.1, hc.2.1, hc.2.2.2⟩ h)]
    rw [h1, h2]

theorem gatherRowsPacked_encode [Zero α] [PackedRepr α] (xs : Array α) (M j0 cs r : Nat)
    (hx : PackedRepr.width α * xs.size < USize.size) :
    gatherRowsPacked (PackedRepr.encode xs) M j0 cs r = gatherRows xs M j0 cs r := by
  simp only [gatherRowsPacked, gatherRows, decodeRange_encode _ _ _ _ _ hx]

/-- `setW` at index `i - d`. -/
def setWOff (d : USize) (a : Array α) (i : USize) (v : α) : Array α := setW a (i - d) v

@[simp] theorem size_assembleGo_setW [PackedRepr α] (r : Array ByteArray) (M : USize) (hr hb) :
    ∀ (n : Nat) (q : USize) (out : Array α), M.toNat - q.toNat = n →
      (assembleGo setW r M hr hb q out).size = out.size := by
  intro n
  induction n with
  | zero =>
    intro q out hn
    have hnot : ¬q < M := by rw [USize.lt_iff_toNat_lt]; omega
    rw [assembleGo]
    simp only [hnot, ↓reduceDIte]
  | succ n ih =>
    intro q out hn
    have hq : q < M := by rw [USize.lt_iff_toNat_lt]; omega
    have hq1 : (q + 1).toNat = q.toNat + 1 := Plan.usize_add_one q (by
      have := M.toNat_lt_size; omega)
    rw [assembleGo]
    simp only [hq, ↓reduceDIte]
    rw [ih (q + 1) _ (by rw [hq1]; omega)]
    simp only [size_setW]

theorem size_assemble_setW [PackedRepr α] (r : Array ByteArray) (M : Nat) (out : Array α) :
    (assemble setW r M out).size = out.size := by
  unfold assemble
  split_ifs
  · exact size_assembleGo_setW _ _ _ _ _ 0 _ rfl
  all_goals rfl

/-- A chunk run with offset packed stores is the packed slice of the global array run. -/
theorem assembleGo_chunk [Zero α] [PackedRepr α] (r : Array ByteArray) (M : USize) (hr hb)
    (q : USize) (q0 K : Nat) (hq0 : q.toNat = q0) (hK : M.toNat = q0 + K)
    (hm : PackedRepr.width α * (16 * K) < USize.size) (hMU : 16 * M.toNat < USize.size) :
    assembleGo (fun b i v ↦ PackedRepr.setIf (R := α) _ hm b (i - (16 * q0).toUSize) v)
        r M hr hb q (PackedRepr.encode (Array.replicate (16 * K) (0 : α))) =
      PackedRepr.encode ((assembleGo setW r M hr hb q
        (Array.replicate (16 * M.toNat) (0 : α))).extract (16 * q0) (16 * M.toNat)) := by
  have hd : ((16 * q0).toUSize : USize).toNat = 16 * q0 :=
    USize.toNat_ofNat_of_lt' (by omega)
  have e1 := assembleGo_rel (fun b i v ↦ setWOff (16 * q0).toUSize b i v)
    (fun b i v ↦ PackedRepr.setIf (R := α) _ hm b (i - (16 * q0).toUSize) v)
    (fun (b₁ : Array α) b₂ ↦ b₂ = PackedRepr.encode b₁ ∧
      PackedRepr.width α * b₁.size = PackedRepr.width α * (16 * K))
    r M hr hb 0 hMU
    (fun b₁ b₂ i v _ _ hR ↦ by
      obtain ⟨rfl, hs⟩ := hR
      refine ⟨?_, by simp only [setWOff, size_setW]; exact hs⟩
      exact setIf_encode_setW_of_eq _ _ _ _ _ hs)
    _ q (Array.replicate (16 * K) 0) _ rfl (Nat.zero_le _)
    ⟨rfl, by rw [Array.size_replicate]⟩
  rw [e1.1]
  congr 1
  have e2 := assembleGo_rel setW (fun b i v ↦ setWOff (16 * q0).toUSize b i v)
    (fun (F : Array α) S ↦ S = F.extract (16 * q0) (16 * M.toNat) ∧ F.size = 16 * M.toNat)
    r M hr hb (16 * q0) hMU
    (fun F S i v hlo hhi hR ↦ by
      obtain ⟨rfl, hs⟩ := hR
      refine ⟨?_, by simp only [size_setW]; exact hs⟩
      have := setW_extract F i (16 * q0).toUSize (16 * M.toNat) v hs hMU
        (by rw [hd]; exact hlo) hhi
      rw [hd] at this
      exact this.symm)
    _ q (Array.replicate (16 * M.toNat) 0) (Array.replicate (16 * K) 0) rfl (by rw [hq0])
    ⟨by rw [Array.extract_replicate, show min (16 * M.toNat) (16 * M.toNat) - 16 * q0 = 16 * K
      by omega], by rw [Array.size_replicate]⟩
  exact e2.1

/-- One interleave chunk is the packed slice of the whole interleave. -/
theorem assembleChunk_eq [Zero α] [PackedRepr α] (r : Array ByteArray) (M q0 K : Nat)
    (hq : q0 + K ≤ M) (hm : PackedRepr.width α * (16 * M) < USize.size) :
    assembleChunk (α := α) r M q0 K = PackedRepr.encode
      ((assemble setW r M (Array.replicate (16 * M) (0 : α))).extract (16 * q0)
        (16 * (q0 + K))) := by
  have hw := PackedRepr.width_pos (R := α)
  have hmK : PackedRepr.width α * (16 * K) < USize.size :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hm
  have hMU : 16 * M < USize.size := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hw) hm
  have hrep : ((Array.replicate (16 * M) (0 : α)).extract (16 * q0) (16 * (q0 + K))) =
      Array.replicate (16 * K) 0 := by
    rw [Array.extract_replicate]; congr 1; omega
  unfold assembleChunk
  simp only [dite_eq_left_of_eq_true (eq_true hmK), PackedRepr.replicate_eq]
  unfold assembleRows assemble
  by_cases hg : M < USize.size ∧ r.size = 16
  · obtain ⟨hM, hr⟩ := hg
    have hg' : q0 ≤ q0 + K ∧ q0 + K ≤ M ∧ M < USize.size ∧ r.size = 16 :=
      ⟨by omega, hq, hM, hr⟩
    rw [dite_eq_left_of_eq_true (eq_true hg'), dite_eq_left_of_eq_true (eq_true hM),
      dite_eq_left_of_eq_true (eq_true hr)]
    split
    · rw [assembleGo_chunk r _ hr _ _ q0 K rfl rfl hmK (by simp only [USize.toNat_ofNatLT]; omega)]
      congr 1
      simp only [USize.toNat_ofNatLT]
      -- both runs store the same entries on the slice
      apply Packed.array_eq_of_getD _ _ 0 (by
        simp only [Array.size_extract, size_assembleGo_setW _ _ _ _ _ _ _ rfl,
          Array.size_replicate]; omega)
      intro j
      by_cases hj : j < 16 * K
      · rw [getD_extract _ _ _ _ (by omega) (by
            rw [size_assembleGo_setW _ _ _ _ _ _ _ rfl, Array.size_replicate]),
          getD_extract _ _ _ _ (by omega) (by
            rw [size_assembleGo_setW _ _ _ _ _ _ _ rfl, Array.size_replicate]; omega),
          (assembleGo_spec (α := α) r _ hr _ ?h1 _ _ _ rfl ?h2).2,
          (assembleGo_spec (α := α) r _ hr _ ?h3 _ _ _ rfl ?h4).2]
        · simp only [USize.toNat_zero, USize.toNat_ofNatLT, Nat.mul_zero]
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩),
            ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
        all_goals simp only [USize.toNat_ofNatLT, Array.size_replicate]
        all_goals omega
      · rw [getD_of_size_le _ _ (by
            simp only [Array.size_extract, size_assembleGo_setW _ _ _ _ _ _ _ rfl,
              Array.size_replicate]; omega),
          getD_of_size_le _ _ (by
            simp only [Array.size_extract, size_assembleGo_setW _ _ _ _ _ _ _ rfl,
              Array.size_replicate]; omega)]
    · rw [hrep]
  · rw [dite_eq_right_of_eq_false (eq_false (fun h ↦ hg ⟨h.2.2.1, h.2.2.2⟩))]
    by_cases hM : M < USize.size
    · rw [dite_eq_left_of_eq_true (eq_true hM),
        dite_eq_right_of_eq_false (eq_false (fun h ↦ hg ⟨hM, h⟩)), hrep]
    · rw [dite_eq_right_of_eq_false (eq_false hM), hrep]

theorem foldl_chunks [PackedRepr α] (A : Array α) (K : Nat) (init : ByteArray)
    (f : Nat → ByteArray) : ∀ n, (∀ c < n, f c =
      PackedRepr.encode (A.extract (16 * (c * K)) (16 * (c * K + K)))) →
      (List.range n).foldl (fun acc c ↦ acc ++ f c) init =
        init ++ PackedRepr.encode (A.extract 0 (16 * (n * K))) := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [List.range_zero, List.foldl_nil, Nat.zero_mul, Nat.mul_zero]
    rw [Array.extract_eq_empty_of_le (by omega), PackedRepr.encode_empty,
      ByteArray.append_empty]
  | succ n ih =>
    intro hf
    rw [List.range_succ, List.foldl_append, ih (fun c hc ↦ hf c (by omega)), List.foldl_cons,
      List.foldl_nil, hf n (by omega), ByteArray.append_assoc, ← PackedRepr.encode_append,
      Array.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
      Nat.max_eq_right (by omega), show 16 * (n * K + K) = 16 * ((n + 1) * K) by ring]

theorem get_bind_spawn (L : Array (Task ByteArray)) (g : Array ByteArray → ByteArray) :
    ((joinTasks L).bind fun r ↦ Task.spawn fun _ ↦ g r).get = g (L.map Task.get) := by
  change g (joinTasks L).get = _
  rw [joinTasks_get]

/-- Joining the sixteen interleave chunks packs the whole interleave. -/
theorem foldl_assembleChunk [Zero α] [PackedRepr α] (LS : Array ByteArray) (K : Nat)
    (ho : PackedRepr.width α * (16 * (16 * K)) < USize.size) :
    ((Array.range 16).map fun c ↦ assembleChunk (α := α) LS (16 * K) (c * (16 * K / 16))
        (16 * K / 16)).foldl (· ++ ·) (ByteArray.emptyWithCapacity
          (PackedRepr.width α * (16 * (16 * K)))) =
      PackedRepr.encode (assemble setW LS (16 * K) (Array.replicate (16 * (16 * K)) (0 : α))) := by
  rw [show 16 * K / 16 = K by omega, Array.foldl_map, ← Array.foldl_toList, Array.toList_range,
    foldl_chunks (assemble setW LS (16 * K) (Array.replicate (16 * (16 * K)) (0 : α)))
      K _ _ 16 (fun c hc ↦ assembleChunk_eq _ _ _ _ (by
        have := Nat.mul_le_mul_right K (show c + 1 ≤ 16 by omega)
        rw [Nat.succ_mul] at this; exact this) ho)]
  rw [show ByteArray.emptyWithCapacity (PackedRepr.width α * (16 * (16 * K))) =
      ByteArray.empty from rfl, ByteArray.empty_append]
  congr 1
  exact Array.extract_eq_self_of_le (by rw [size_assemble_setW, Array.size_replicate])

/-- The packed transform of packed elements is the packed array transform. -/
theorem transformPacked_encode [Field R] [DecidableEq R] [PackedRepr R] (tw : Array (Array R))
    (logN S : Nat) (rest : List Nat) (scale : Bool) (f : R) (xs : Array R)
    (hx : PackedRepr.width R * xs.size < USize.size)
    (ho : PackedRepr.width R * (16 * 2 ^ (logN - 4)) < USize.size)
    (h16 : 16 ∣ 2 ^ (logN - 4)) :
    transformPacked tw logN S rest scale f (PackedRepr.encode xs) =
      PackedRepr.encode (transform tw logN S rest scale f xs) := by
  unfold transformPacked transform
  simp only [gatherRowsPacked_encode _ _ _ _ _ hx, columnTask, Array.map_map,
    Function.comp_def, get_bind_spawn]
  generalize 2 ^ (logN - 4) = M at ho h16 ⊢
  obtain ⟨K, rfl⟩ := h16
  exact foldl_assembleChunk _ K ho

theorem decodeRange_all [Zero α] [PackedRepr α] (xs : Array α)
    (hx : PackedRepr.width α * xs.size < USize.size) :
    decodeRange (PackedRepr.encode xs) 0
      (Array.replicate ((PackedRepr.encode xs).size / PackedRepr.width α) 0) 0
      ((PackedRepr.encode xs).size / PackedRepr.width α) = xs := by
  have hdiv : (PackedRepr.encode xs).size / PackedRepr.width α = xs.size := by
    rw [PackedRepr.size_encode, Nat.mul_div_cancel_left _ PackedRepr.width_pos]
  have hxs : xs.size < USize.size :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ PackedRepr.width_pos) hx
  rw [hdiv, decodeRange_encode _ _ _ _ _ hx]
  apply Packed.array_eq_of_getD _ _ 0 (by rw [size_copyRange, Array.size_replicate])
  intro i
  rw [copyRange_getD xs 0 (Array.replicate xs.size 0) 0 xs.size 0 ⟨by omega,
    by rw [Array.size_replicate]; omega, hxs, by rw [Array.size_replicate]; exact hxs⟩]
  split
  · simp only [Nat.zero_add, Nat.sub_zero]
  · rename_i h
    rw [getD_of_size_le _ _ (by rw [Array.size_replicate]; omega),
      getD_of_size_le _ _ (by omega)]

/-- Decoding all slots of packed elements. -/
theorem decodeAll_encode [Zero α] [PackedRepr α] (xs : Array α) :
    decodeAll (PackedRepr.encode xs) = xs := by
  unfold decodeAll
  split
  · rename_i hx
    rw [PackedRepr.size_encode] at hx
    exact decodeRange_all xs hx
  · exact PackedRepr.decode_encode xs

theorem encodeAllGo_encode [Zero α] [PackedRepr α] (a : Array α)
    (hu : PackedRepr.width α * a.size < USize.size) :
    ∀ (n i : Nat) (B : Array α), B.size = a.size → i + n = a.size →
      encodeAllGo a _ hu n i (PackedRepr.encode B) =
        PackedRepr.encode (B.extract 0 i ++ a.extract i a.size) := by
  intro n
  induction n with
  | zero =>
    intro i B hB hi
    simp only [encodeAllGo, Nat.add_zero] at hi ⊢
    have e1 : a.extract a.size a.size = #[] := Array.extract_eq_empty_of_le (by omega)
    have e2 : B.extract 0 a.size = B := by rw [← hB, Array.extract_size]
    rw [hi, e1, e2, Array.append_empty]
  | succ n ih =>
    intro i B hB hi
    have hiu : i < USize.size := Nat.lt_of_lt_of_le (by omega)
      (Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ PackedRepr.width_pos) hu))
    rw [encodeAllGo, PackedRepr.setIf_encode_of_eq _ _ _ _ _ (by rw [hB]),
      USize.toNat_ofNat_of_lt' hiu,
      ih (i + 1) _ (by simp only [Array.size_setIfInBounds, hB]) (by omega)]
    congr 1
    apply Array.ext
    · simp only [Array.size_append, Array.size_extract, Array.size_setIfInBounds]
      omega
    · intro j h1 h2
      simp only [Array.getElem_append, Array.getElem_extract, Array.size_extract,
        Array.size_setIfInBounds, Nat.zero_add, Nat.sub_zero]
      split_ifs with ha hb hb
      · rw [Array.getElem_setIfInBounds (by omega)]
        split
        · omega
        · rfl
      · rw [Array.getElem_setIfInBounds (by omega)]
        split
        · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega),
            Option.getD_some]
          simp only [show i + (j - min i B.size) = i by omega]
        · omega
      · omega
      · simp only [show i + 1 + (j - min (i + 1) B.size) = i + (j - min i B.size) by omega]

/-- The fast encoder packs every element. -/
theorem encodeAll_eq [Zero α] [PackedRepr α] (a : Array α) :
    encodeAll a = PackedRepr.encode a := by
  unfold encodeAll
  split
  · rename_i hu
    rw [PackedRepr.replicate_eq, encodeAllGo_encode a hu _ 0 _ Array.size_replicate (by omega)]
    simp only [Array.extract_zero, Array.empty_append, Array.extract_size]
  · rfl

end CompPoly.CPolynomial.NTTFast.Columns
