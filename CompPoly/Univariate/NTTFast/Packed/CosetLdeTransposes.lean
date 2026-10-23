/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.CosetLde
public import CompPoly.Univariate.NTTFast.Packed.NativeOrderCorrectness
import all CompPoly.Univariate.NTTFast.Packed.CosetLde
import all CompPoly.Univariate.NTTFast.Packed.Native
import all CompPoly.Univariate.NTTFast.Packed.NativeOrder
import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas

/-! # Correctness of the coset LDE transposes

The transposes write every output word once or more, and every write stores the word's final
value. `Fill T S N g` says that `g` overwrites words of an `N`-word buffer only with their
targets `T`, among them every word in `S`. Fills compose along folds with the union of their
sets, so a transpose whose kernels and edge loops together cover every word computes the buffer
of targets, whatever the order and overlap of its writes.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed.Native
open Montgomery.Native32 (Mont32Field FastField)

variable {p : ℕ} [Mont32Field p]

open CompPoly.PackedRepr (encode size_encode_uint32)

/-! ### Fills -/

/-- `o'` is `o` with words overwritten by their targets `T`, among them every word in `S`. -/
def Fills (T : Nat → UInt32) (S : Nat → Prop) (o o' : Array UInt32) : Prop :=
  o'.size = o.size ∧ (∀ k, o.getD k 0 = T k → o'.getD k 0 = T k) ∧
    ∀ k, S k → o'.getD k 0 = T k

/-- `g` maps every packed `N`-word buffer to one that fills `S` with targets `T`. -/
def Fill (T : Nat → UInt32) (S : Nat → Prop) (N : Nat) (g : ByteArray → ByteArray) : Prop :=
  ∀ o : Array UInt32, o.size = N → ∃ o', g (encode o) = encode o' ∧ Fills T S o o'

/-- The identity fills nothing. -/
theorem Fill.id (T : Nat → UInt32) (N : Nat) : Fill T (fun _ ↦ False) N id :=
  fun o _ ↦ ⟨o, rfl, rfl, fun _ h ↦ h, fun _ h ↦ h.elim⟩

/-- One fill after another fills both sets. -/
theorem Fill.comp {T : Nat → UInt32} {S S' : Nat → Prop} {N : Nat} {g g' : ByteArray → ByteArray}
    (h : Fill T S N g) (h' : Fill T S' N g') : Fill T (fun k ↦ S k ∨ S' k) N (g' ∘ g) := by
  intro o ho
  obtain ⟨o1, e1, s1, k1, f1⟩ := h o ho
  obtain ⟨o2, e2, s2, k2, f2⟩ := h' o1 (by rw [s1, ho])
  refine ⟨o2, by rw [Function.comp_apply, e1, e2], by rw [s2, s1], fun k hk ↦ k2 k (k1 k hk), ?_⟩
  rintro k (hk | hk)
  · exact k2 k (f1 k hk)
  · exact f2 k hk

/-- A fill fills every subset of its set. -/
theorem Fill.mono {T : Nat → UInt32} {S S' : Nat → Prop} {N : Nat} {g : ByteArray → ByteArray}
    (h : Fill T S N g) (hS : ∀ k, S' k → S k) : Fill T S' N g := by
  intro o ho
  obtain ⟨o', e, s, k, f⟩ := h o ho
  exact ⟨o', e, s, k, fun j hj ↦ f j (hS j hj)⟩

/-- Fills transfer along pointwise equal functions. -/
theorem Fill.congr {T : Nat → UInt32} {S : Nat → Prop} {N : Nat} {g g' : ByteArray → ByteArray}
    (h : Fill T S N g) (he : ∀ b, g b = g' b) : Fill T S N g' := by
  intro o ho
  obtain ⟨o', e, f⟩ := h o ho
  exact ⟨o', by rw [← he, e], f⟩

/-- Fills transfer along functions equal on packed `N`-word buffers. -/
theorem Fill.congr_encode {T : Nat → UInt32} {S : Nat → Prop} {N : Nat}
    {g g' : ByteArray → ByteArray} (h : Fill T S N g)
    (he : ∀ o : Array UInt32, o.size = N → g (encode o) = g' (encode o)) : Fill T S N g' := by
  intro o ho
  obtain ⟨o', e, f⟩ := h o ho
  exact ⟨o', by rw [← he o ho, e], f⟩

/-- A fold of fills fills the union of their sets. -/
theorem Fill.foldl {ι : Type*} (T : Nat → UInt32) (S : ι → Nat → Prop) (N : Nat) (L : List ι)
    (f : ByteArray → ι → ByteArray) (hf : ∀ x ∈ L, Fill T (S x) N (f · x)) :
    Fill T (fun k ↦ ∃ x ∈ L, S x k) N (fun b ↦ L.foldl f b) := by
  induction L with
  | nil => exact (Fill.id T N).mono fun k ⟨_, h, _⟩ ↦ absurd h List.not_mem_nil
  | cons x L ih =>
    have h := (hf x List.mem_cons_self).comp (ih fun y hy ↦ hf y (List.mem_cons_of_mem x hy))
    refine (h.congr fun b ↦ rfl).mono ?_
    rintro k ⟨y, hy, hk⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact Or.inl hk
    · exact Or.inr ⟨y, hy, hk⟩

/-- A fill that covers every word computes the buffer of targets. -/
theorem Fill.eq_ofFn {T : Nat → UInt32} {S : Nat → Prop} {N : Nat} {g : ByteArray → ByteArray}
    (h : Fill T S N g) (hS : ∀ k < N, S k) (o : Array UInt32) (ho : o.size = N) :
    g (encode o) = encode (Array.ofFn (n := N) fun k ↦ T k.val) := by
  obtain ⟨o', e, s, -, f⟩ := h o ho
  rw [e]
  congr 1
  apply array_eq_of_getD _ _ 0 (by rw [s, ho, Array.size_ofFn])
  intro k
  by_cases hk : k < N
  · rw [f k (hS k hk), getD_ofFn_bounded _ _ hk]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [s, ho]; omega),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [Array.size_ofFn]; omega)]

/-- A splice of target values fills its range. -/
theorem fills_splice (T : Nat → UInt32) (o V : Array UInt32) (i : Nat)
    (hi : i + V.size ≤ o.size) (hV : ∀ t < V.size, V.getD t 0 = T (i + t)) :
    Fills T (fun k ↦ i ≤ k ∧ k < i + V.size) o (splice o i V) := by
  refine ⟨size_splice o i V hi, fun k hk ↦ ?_, fun k ⟨h1, h2⟩ ↦ ?_⟩
  · rw [getD_splice o i V hi]
    split
    · exact hk
    · split
      · rw [hV _ (by omega), show i + (k - i) = k by omega]
      · exact hk
  · rw [getD_splice o i V hi, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true h2), hV _ (by omega),
      show i + (k - i) = k by omega]

/-! ### Word stores -/

/-- A sixteen-word store splices the words in. -/
theorem write16U_encodeWords (o : Array UInt32) (i : USize) (hs : 4 * o.size < USize.size)
    (hi : i.toNat + 16 ≤ o.size)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) :
    write16U (encode o) i v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      encode (splice o i.toNat
        #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]) := by
  have ho : (i * 4).toNat = 4 * i.toNat := by
    have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
    rw [USize.toNat_mul, usize_numeral 4 (by decide), hsize, Nat.mod_eq_of_lt (by omega)]
    omega
  unfold write16U
  rw [storeWords_replace_encodeWords o (i * 4) 16 i.toNat (by decide) ho
    (by rw [show (16 : UInt8).toNat = 16 from rfl]; omega) (by rw [size_encode_uint32]; exact hs)]
  rfl

/-- An eight-word store splices the words in. -/
theorem storeWords8_encodeWords (o : Array UInt32) (off : USize) (i : Nat)
    (ho : off.toNat = 4 * i) (hs : 4 * o.size < USize.size) (hi : i + 8 ≤ o.size)
    (v0 v1 v2 v3 v4 v5 v6 v7 : UInt32) :
    storeWords (encode o) off 8 v0 v1 v2 v3 v4 v5 v6 v7 0 0 0 0 0 0 0 0 =
      encode (splice o i #[v0, v1, v2, v3, v4, v5, v6, v7]) := by
  rw [storeWords_replace_encodeWords o off 8 i (by decide) ho
    (by rw [show (8 : UInt8).toNat = 8 from rfl]; omega) (by rw [size_encode_uint32]; exact hs)]
  rfl

/-- A single-word store sets the word. -/
theorem write_encodeWords (o : Array UInt32) (i : Nat) (v : UInt32)
    (hs : 4 * o.size < USize.size) (hi : i < o.size) :
    write (encode o) i v = encode (splice o i #[v]) := by
  have hin : i < USize.size := by omega
  have ho : (i.toUSize * 4).toNat = 4 * i := by
    have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
    rw [USize.toNat_mul, USize.toNat_ofNat_of_lt' hin, usize_numeral 4 (by decide), hsize,
      Nat.mod_eq_of_lt (by omega)]
    omega
  unfold write
  rw [storeWords_replace_encodeWords o (i.toUSize * 4) 1 i (by decide) ho
    (by rw [show (1 : UInt8).toNat = 1 from rfl]; omega) (by rw [size_encode_uint32]; exact hs)]
  rfl

/-- A single-word store of the target fills the word. -/
theorem fill_write (T : Nat → UInt32) (N i : Nat) (v : UInt32) (hs : 4 * N < USize.size)
    (hi : i < N) (hv : v = T i) : Fill T (· = i) N (fun b ↦ write b i v) := by
  intro o ho
  have hf := fills_splice T o #[v] i (by change i + 1 ≤ o.size; omega) fun t ht ↦ by
    change t < 1 at ht
    rw [show t = 0 by omega, hv]
    rfl
  exact ⟨_, write_encodeWords o i v (by omega) (by omega), hf.1, hf.2.1,
    fun k hk ↦ hf.2.2 k ⟨by omega, by change k < i + 1; omega⟩⟩

/-- A sixteen-word store of targets fills its range. -/
theorem fill_write16U (T : Nat → UInt32) (N : Nat) (i : USize) (g : Nat → UInt32)
    (hs : 4 * N < USize.size) (hi : i.toNat + 16 ≤ N) (hg : ∀ t < 16, g t = T (i.toNat + t)) :
    Fill T (fun k ↦ i.toNat ≤ k ∧ k < i.toNat + 16) N (fun b ↦ write16U b i (g 0) (g 1) (g 2)
      (g 3) (g 4) (g 5) (g 6) (g 7) (g 8) (g 9) (g 10) (g 11) (g 12) (g 13) (g 14) (g 15)) := by
  intro o ho
  have hf := fills_splice T o (lit16 g) i.toNat (by rw [size_lit16]; omega) fun t ht ↦ by
    rw [getD_lit16 g t (by simpa using ht), hg t (by simpa using ht)]
  exact ⟨_, write16U_encodeWords o i (by omega) (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, hf⟩

/-- An eight-word store of targets fills its range. -/
theorem fill_storeWords8 (T : Nat → UInt32) (N : Nat) (off : USize) (i : Nat) (g : Nat → UInt32)
    (ho : off.toNat = 4 * i) (hs : 4 * N < USize.size) (hi : i + 8 ≤ N)
    (hg : ∀ t < 8, g t = T (i + t)) :
    Fill T (fun k ↦ i ≤ k ∧ k < i + 8) N (fun b ↦ storeWords b off 8 (g 0) (g 1) (g 2) (g 3)
      (g 4) (g 5) (g 6) (g 7) 0 0 0 0 0 0 0 0) := by
  intro o ho'
  have hf := fills_splice T o #[g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7] i
    (by change i + 8 ≤ o.size; omega) fun t ht ↦ by
      change t < 8 at ht
      rw [← hg t ht]
      interval_cases t <;> rfl
  exact ⟨_, storeWords8_encodeWords o off i ho (by omega) (by omega) _ _ _ _ _ _ _ _, hf⟩

/-! ### Tile kernels -/

/-- A machine offset `p + u * ps` that cannot wrap. -/
theorem usize_add_mul_numeral (p ps : USize) (u : Nat) (hu : u < 4294967296)
    (h : p.toNat + u * ps.toNat < USize.size) :
    (p + OfNat.ofNat u * ps).toNat = p.toNat + u * ps.toNat := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, USize.toNat_mul, usize_numeral u hu, hsize,
    Nat.mod_eq_of_lt (show u * ps.toNat < USize.size by omega), Nat.mod_eq_of_lt h]

/-- The strided tile kernel stores its sixteen transposed lines one after another. -/
theorem tileStrided_eq_foldl (src : Array UInt32) (q qs : USize) (out : ByteArray) (p ps : USize)
    (hl : ∀ t < 16, (q + OfNat.ofNat t * qs).toNat + 16 ≤ src.size)
    (hs : 4 * src.size < USize.size) :
    tileStrided (encode src) q qs out p ps = (List.range 16).foldl (fun b u ↦
      let g (t : Nat) : UInt32 := src.getD ((q + OfNat.ofNat t * qs).toNat + u) 0
      write16U b (p + OfNat.ofNat u * ps) (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) (g 8)
        (g 9) (g 10) (g 11) (g 12) (g 13) (g 14) (g 15)) out := by
  have hf (t : Nat) (ht : t < 16) : LineFits (encode src) (q + OfNat.ofNat t * qs) :=
    lineFits_encodeWords _ _ (hl t ht) (by rw [size_encode_uint32]; exact hs)
  unfold tileStrided
  rw [dite_eq_left_of_eq_true (eq_true ⟨hf 0 (by decide), hf 1 (by decide), hf 2 (by decide),
    hf 3 (by decide), hf 4 (by decide), hf 5 (by decide), hf 6 (by decide), hf 7 (by decide),
    hf 8 (by decide), hf 9 (by decide), hf 10 (by decide), hf 11 (by decide), hf 12 (by decide),
    hf 13 (by decide), hf 14 (by decide), hf 15 (by decide)⟩)]
  simp only [line_encodeWords]
  rfl

/-- The strided tile kernel fills the transposed tile with its targets. -/
theorem fill_tileStrided (T : Nat → UInt32) (N : Nat) (src : Array UInt32) (q qs p ps : USize)
    (hs : 4 * src.size < USize.size) (hN : 4 * N < USize.size)
    (hq : q.toNat + 15 * qs.toNat + 16 ≤ src.size) (hp : p.toNat + 15 * ps.toNat + 16 ≤ N)
    (hT : ∀ u < 16, ∀ t < 16,
      src.getD (q.toNat + t * qs.toNat + u) 0 = T (p.toNat + u * ps.toNat + t)) :
    Fill T (fun k ↦ ∃ u < 16, ∃ t < 16, k = p.toNat + u * ps.toNat + t) N
      (fun b ↦ tileStrided (encode src) q qs b p ps) := by
  have hqt (t : Nat) (ht : t < 16) : (q + OfNat.ofNat t * qs).toNat = q.toNat + t * qs.toNat := by
    have := Nat.mul_le_mul_right qs.toNat (show t ≤ 15 by omega)
    exact usize_add_mul_numeral q qs t (by omega) (by omega)
  have hpu (u : Nat) (hu : u < 16) : (p + OfNat.ofNat u * ps).toNat = p.toNat + u * ps.toNat := by
    have := Nat.mul_le_mul_right ps.toNat (show u ≤ 15 by omega)
    exact usize_add_mul_numeral p ps u (by omega) (by omega)
  let f (b : ByteArray) (u : Nat) : ByteArray :=
    let g (t : Nat) : UInt32 := src.getD ((q + OfNat.ofNat t * qs).toNat + u) 0
    write16U b (p + OfNat.ofNat u * ps) (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) (g 8)
      (g 9) (g 10) (g 11) (g 12) (g 13) (g 14) (g 15)
  have hstep (u : Nat) (hu : u ∈ List.range 16) :
      Fill T (fun k ↦ (p + OfNat.ofNat u * ps).toNat ≤ k ∧ k < (p + OfNat.ofNat u * ps).toNat + 16)
        N (f · u) := by
    have hu := List.mem_range.mp hu
    have := Nat.mul_le_mul_right ps.toNat (show u ≤ 15 by omega)
    refine fill_write16U T N (p + OfNat.ofNat u * ps)
      (fun t ↦ src.getD ((q + OfNat.ofNat t * qs).toNat + u) 0) hN
      (by rw [hpu u hu]; omega) fun t ht ↦ ?_
    rw [hqt t ht, hpu u hu, hT u hu t ht]
  have he (b : ByteArray) : (List.range 16).foldl f b = tileStrided (encode src) q qs b p ps :=
    (tileStrided_eq_foldl src q qs b p ps (fun t ht ↦ by
      have := Nat.mul_le_mul_right qs.toNat (show t ≤ 15 by omega)
      rw [hqt t ht]
      omega) hs).symm
  refine ((Fill.foldl T _ N (List.range 16) f hstep).congr he).mono ?_
  rintro k ⟨u, hu, t, ht, rfl⟩
  exact ⟨u, List.mem_range.mpr hu, by rw [hpu u hu]; omega, by rw [hpu u hu]; omega⟩

/-! ### Input transpose -/

/-- Quotient and remainder of `a * n + b`, `b < n`. -/
theorem divMod_add (a b n : Nat) (hb : b < n) : (a * n + b) / n = a ∧ (a * n + b) % n = b := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- Rows `r0, …, r0 + rows - 1` of columns `c0, …, c0 + n - 1` of a row-major matrix of width
`w`, transposed: word `j * rows + r` is entry `(r0 + r, c0 + j)`. -/
theorem transposeRows_encodeWords (M : Array UInt32) (w c0 n r0 rows : Nat) (hn : c0 + n ≤ w)
    (hM : (r0 + rows) * w ≤ M.size) (hs : 4 * M.size < USize.size) :
    transposeRows (encode M) w c0 n r0 rows = encode (Array.ofFn (n := n * rows) fun k ↦
      M.getD ((r0 + k.val % rows) * w + c0 + k.val / rows) 0) := by
  let T (k : Nat) : UInt32 := M.getD ((r0 + k % rows) * w + c0 + k / rows) 0
  have hrw : rows * w ≤ (r0 + rows) * w := Nat.mul_le_mul_right w (by omega)
  have hnr : n * rows ≤ w * rows := Nat.mul_le_mul_right rows (by omega)
  have hwr : w * rows = rows * w := Nat.mul_comm w rows
  have hN : 4 * (n * rows) < USize.size := by omega
  have hu (n : Nat) (hn : n ≤ M.size) : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' (by omega)
  have htile (rt : Nat) (hrt : rt < rows / 16) (ct : Nat)
      (hct : ct ∈ List.range (n / 16)) :
      Fill T (fun k ↦ ∃ u < 16, ∃ t < 16, k = (16 * ct + u) * rows + (16 * rt + t)) (n * rows)
        (fun b ↦ tileStrided (encode M) ((r0 + 16 * rt) * w + c0 + 16 * ct).toUSize w.toUSize b
          (16 * ct * rows + 16 * rt).toUSize rows.toUSize) := by
    have hct := List.mem_range.mp hct
    have h1 : (r0 + 16 * rt + 16) * w ≤ (r0 + rows) * w := Nat.mul_le_mul_right w (by omega)
    have h2 : (16 * ct + 16) * rows ≤ n * rows := Nat.mul_le_mul_right rows (by omega)
    have e1 : (r0 + 16 * rt + 16) * w = (r0 + 16 * rt) * w + 16 * w := by ring
    have e2 : (16 * ct + 16) * rows = 16 * ct * rows + 16 * rows := by ring
    have hq : (r0 + 16 * rt) * w + c0 + 16 * ct ≤ M.size := by omega
    have hp : 16 * ct * rows + 16 * rt ≤ M.size := by omega
    refine (fill_tileStrided T (n * rows) M _ _ _ _ (by omega) hN ?_ ?_ ?_).mono ?_
    · rw [hu _ hq, hu _ (by omega)]; omega
    · rw [hu _ hp, hu _ (by omega)]; omega
    · intro u hu' t ht
      rw [hu _ hq, hu _ (by omega), hu _ hp, hu _ (by omega)]
      have hd := divMod_add (16 * ct + u) (16 * rt + t) rows (by omega)
      simp only [T, show 16 * ct * rows + 16 * rt + u * rows + t =
        (16 * ct + u) * rows + (16 * rt + t) by ring, hd.1, hd.2]
      congr 1
      ring
    · rintro k ⟨u, hu', t, ht, rfl⟩
      exact ⟨u, hu', t, ht, by rw [hu _ hp, hu _ (by omega)]; ring⟩
  have hedge (j : Nat) (hj : j ∈ List.range n) (r : Nat)
      (hr : r ∈ List.range' (if j < 16 * (n / 16) then 16 * (rows / 16) else 0)
        (rows - if j < 16 * (n / 16) then 16 * (rows / 16) else 0)) :
      Fill T (· = j * rows + r) (n * rows)
        (fun b ↦ write b (j * rows + r) (read (encode M) ((r0 + r) * w + c0 + j))) := by
    have hj := List.mem_range.mp hj
    have hr : r < rows := by have := List.mem_range'_1.mp hr; split at this <;> omega
    have h1 : (r0 + r + 1) * w ≤ (r0 + rows) * w := Nat.mul_le_mul_right w (by omega)
    have h2 : (j + 1) * rows ≤ n * rows := Nat.mul_le_mul_right rows (by omega)
    have e1 : (r0 + r + 1) * w = (r0 + r) * w + w := by ring
    have e2 : (j + 1) * rows = j * rows + rows := by ring
    refine fill_write T (n * rows) _ _ hN (by omega) ?_
    have hd := divMod_add j r rows hr
    rw [read_encodeWords M _ (by rw [size_encode_uint32]; exact hs) (by omega)]
    simp only [T, hd.1, hd.2]
  have hall := (Fill.foldl T _ (n * rows) (List.range ((rows / 16 + 63) / 64)) _ fun rb _ ↦
    Fill.foldl T _ (n * rows) _ _ fun ct hct ↦
      Fill.foldl T _ (n * rows) (List.range' (64 * rb) (min (64 * rb + 64) (rows / 16) - 64 * rb))
        _ fun rt hrt ↦ htile rt (by have := List.mem_range'_1.mp hrt; omega) ct hct).comp
    (Fill.foldl T _ (n * rows) _ _ fun j hj ↦ Fill.foldl T _ (n * rows) _ _ (hedge j hj))
  unfold transposeRows
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure, pure_bind, zeroWords_eq]
  refine hall.eq_ofFn (fun k hk ↦ ?_) _ Array.size_replicate
  have hrows : 0 < rows := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  have hk' := Nat.div_add_mod k rows
  have hj : k / rows < n := (Nat.div_lt_iff_lt_mul hrows).mpr hk
  have hr := Nat.mod_lt k hrows
  by_cases hin : k / rows < 16 * (n / 16) ∧ k % rows < 16 * (rows / 16)
  · refine Or.inl ⟨k % rows / 16 / 64, List.mem_range.mpr (by omega), k / rows / 16,
      List.mem_range.mpr (by omega), k % rows / 16, List.mem_range'_1.mpr (by omega),
      k / rows % 16, Nat.mod_lt _ (by decide), k % rows % 16, Nat.mod_lt _ (by decide), ?_⟩
    rw [show 16 * (k / rows / 16) + k / rows % 16 = k / rows by omega,
      show 16 * (k % rows / 16) + k % rows % 16 = k % rows by omega, Nat.mul_comm]
    omega
  · refine Or.inr ⟨k / rows, List.mem_range.mpr hj, k % rows, List.mem_range'_1.mpr ?_, ?_⟩
    · split <;> omega
    · rw [Nat.mul_comm]; omega

/-! ### Output transpose -/

/-- A checked line of eight words reads as the bounds-proved load. -/
theorem line8Fits_readAt {b : ByteArray} {q : USize} (h : Line8Fits b q) (k : Nat) (hk : k < 8)
    (hp) : b.ugetUInt32LE ((q + OfNat.ofNat k) * 4) hp = readAt b q (OfNat.ofNat k) := by
  have hf := line8Fits_toNat h k hk
  have hb := toNat_usize_le b
  have hU := b.usize.toNat_lt_size
  have h4 := usize_numeral 4 (by decide)
  have h8 := h.1
  rw [USize.le_iff_toNat_le, USize.toNat_div, h4, usize_numeral 8 (by decide)] at h8
  have h2 := h.2
  rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ h.1, USize.toNat_div, h4,
    usize_numeral 8 (by decide)] at h2
  have hc : 4 ≤ b.usize ∧ (q + OfNat.ofNat k) * 4 ≤ b.usize - 4 := by
    have h4' : 4 ≤ b.usize := by rw [USize.le_iff_toNat_le, h4]; omega
    refine ⟨h4', ?_⟩
    rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ h4', h4, hf.1]
    omega
  unfold readAt
  rw [dite_eq_left_of_eq_true (eq_true hc)]

/-- The eight-source tile kernel stores its eight transposed lines one after another. -/
theorem tile8_eq_foldl (s : Nat → ByteArray) (q : USize) (out : ByteArray) (p ps : USize)
    (hs : ∀ t < 8, Line8Fits (s t) q) (ho : Tile8Fits out p ps) (hn : out.size < USize.size) :
    tile8 (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) (s 7) q out p ps =
      (List.range 8).foldl (fun b u ↦
        let g (t : Nat) : UInt32 := readAt (s t) q (OfNat.ofNat u)
        storeWords b ((p + OfNat.ofNat u * ps) * 4) 8 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6)
          (g 7) 0 0 0 0 0 0 0 0) out := by
  unfold tile8
  rw [dite_eq_left_of_eq_true (eq_true ⟨hs 0 (by decide), hs 1 (by decide), hs 2 (by decide),
    hs 3 (by decide), hs 4 (by decide), hs 5 (by decide), hs 6 (by decide), hs 7 (by decide),
    ho⟩)]
  simp only [store8_val _ _ _ _ _ _ _ _ _ _ _ hn, touchLast, touch_eq]
  simp (disch := decide) only [line8Fits_readAt (hs 0 (by decide)),
    line8Fits_readAt (hs 1 (by decide)), line8Fits_readAt (hs 2 (by decide)),
    line8Fits_readAt (hs 3 (by decide)), line8Fits_readAt (hs 4 (by decide)),
    line8Fits_readAt (hs 5 (by decide)), line8Fits_readAt (hs 6 (by decide)),
    line8Fits_readAt (hs 7 (by decide))]
  rfl

/-- The eight-source tile kernel fills the transposed tile with its targets. -/
theorem fill_tile8 (T : Nat → UInt32) (N : Nat) (s : Nat → ByteArray) (V : Nat → Array UInt32)
    (q p ps : USize) (hsV : ∀ t < 8, s t = encode (V t))
    (hV : ∀ t < 8, q.toNat + 8 ≤ (V t).size ∧ 4 * (V t).size < USize.size)
    (hN : 4 * N < USize.size) (hp : p.toNat + 7 * ps.toNat + 8 ≤ N)
    (hT : ∀ u < 8, ∀ t < 8, (V t).getD (q.toNat + u) 0 = T (p.toNat + u * ps.toNat + t)) :
    Fill T (fun k ↦ ∃ u < 8, ∃ t < 8, k = p.toNat + u * ps.toNat + t) N
      (fun b ↦ tile8 (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) (s 7) q b p ps) := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hpu (u : Nat) (hu : u < 8) : (p + OfNat.ofNat u * ps).toNat = p.toNat + u * ps.toNat := by
    have := Nat.mul_le_mul_right ps.toNat (show u ≤ 7 by omega)
    exact usize_add_mul_numeral p ps u (by omega) (by omega)
  let f (b : ByteArray) (u : Nat) : ByteArray :=
    let g (t : Nat) : UInt32 := readAt (s t) q (OfNat.ofNat u)
    storeWords b ((p + OfNat.ofNat u * ps) * 4) 8 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6)
      (g 7) 0 0 0 0 0 0 0 0
  have hstep (u : Nat) (hu : u ∈ List.range 8) :
      Fill T (fun k ↦ p.toNat + u * ps.toNat ≤ k ∧ k < p.toNat + u * ps.toNat + 8) N (f · u) := by
    have hu := List.mem_range.mp hu
    have := Nat.mul_le_mul_right ps.toNat (show u ≤ 7 by omega)
    refine fill_storeWords8 T N _ (p.toNat + u * ps.toNat) (fun t ↦ readAt (s t) q (OfNat.ofNat u))
      ?_ hN (by omega) fun t ht ↦ ?_
    · rw [USize.toNat_mul, hpu u hu, usize_numeral 4 (by decide), hsize,
        Nat.mod_eq_of_lt (by omega)]
      omega
    · have hq := hV t ht
      rw [hsV t ht, readAt_encodeWords _ _ _ (by
        rw [size_encode_uint32, usize_numeral u (by omega)]; omega), usize_numeral u (by omega),
        hT u hu t ht]
  have hs (t : Nat) (ht : t < 8) : Line8Fits (s t) q := by
    have hq := hV t ht
    have hu : (s t).usize.toNat = 4 * (V t).size := by
      rw [hsV t ht, ByteArray.usize, Nat.toUSize, USize.toNat_ofNat_of_lt' (by
        rw [size_encode_uint32]; exact hq.2), size_encode_uint32]
    have h4 := usize_numeral 4 (by decide)
    have h8 := usize_numeral 8 (by decide)
    have h1 : 8 ≤ (s t).usize / 4 := by
      rw [USize.le_iff_toNat_le, USize.toNat_div, h4, h8, hu]; omega
    refine ⟨h1, ?_⟩
    rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ h1, USize.toNat_div, h4, h8, hu]
    omega
  refine ((Fill.foldl T _ N (List.range 8) f hstep).congr_encode fun o ho ↦
    (tile8_eq_foldl s q (encode o) p ps hs (by
      have hu : (encode o).usize.toNat = 4 * N := by
        rw [ByteArray.usize, Nat.toUSize, USize.toNat_ofNat_of_lt' (by
          rw [size_encode_uint32]; omega), size_encode_uint32, ho]
      have := Nat.mul_le_mul_right ps.toNat (show 7 ≤ 7 by omega)
      rw [tile8Fits_iff, hu]
      omega) (by rw [size_encode_uint32]; omega)).symm).mono ?_
  rintro k ⟨u, hu, t, ht, rfl⟩
  exact ⟨u, List.mem_range.mpr hu, by omega, by omega⟩

/-- `count` tiles fill `count` consecutive tiles of eight output rows. -/
theorem fill_rowsTiles (T : Nat → UInt32) (N : Nat) (s : Nat → ByteArray)
    (V : Nat → Array UInt32) (w : USize) (hsV : ∀ t < 8, s t = encode (V t))
    (hN : 4 * N < USize.size) (count : Nat) (q p : USize)
    (hV : ∀ t < 8, q.toNat + 8 * count ≤ (V t).size ∧ 4 * (V t).size < USize.size)
    (hp : ∀ c < count, p.toNat + 8 * c * w.toNat + 7 * w.toNat + 8 ≤ N)
    (hT : ∀ c < count, ∀ u < 8, ∀ t < 8,
      (V t).getD (q.toNat + 8 * c + u) 0 = T (p.toNat + 8 * c * w.toNat + u * w.toNat + t)) :
    Fill T (fun k ↦ ∃ c < count, ∃ u < 8, ∃ t < 8, k = p.toNat + 8 * c * w.toNat + u * w.toNat + t)
      N (fun b ↦ rowsTiles (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) (s 7) w count q p b) := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  induction count generalizing q p with
  | zero => exact (Fill.id T N).mono fun k ⟨c, hc, _⟩ ↦ absurd hc (Nat.not_lt_zero c)
  | succ count ih =>
    have h0 := fill_tile8 T N s V q p w hsV (fun t ht ↦ ⟨by have := hV t ht; omega, (hV t ht).2⟩)
      hN (by have := hp 0 (by omega); omega) fun u hu t ht ↦ by
        have := hT 0 (by omega) u hu t ht
        simpa using this
    have hrest : Fill T (fun k ↦ ∃ c < count, ∃ u < 8, ∃ t < 8,
        k = p.toNat + 8 * (c + 1) * w.toNat + u * w.toNat + t) N
        (fun b ↦ rowsTiles (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) (s 7) w count (q + 8)
          (p + 8 * w) b) := by
      rcases Nat.eq_zero_or_pos count with rfl | hc
      · exact (Fill.id T N).mono fun k ⟨c, hc, _⟩ ↦ absurd hc (Nat.not_lt_zero c)
      have hq8 : (q + 8).toNat = q.toNat + 8 := by
        have := hV 0 (by decide)
        rw [USize.toNat_add, usize_numeral 8 (by decide), hsize, Nat.mod_eq_of_lt (by omega)]
      have hp8 : (p + 8 * w).toNat = p.toNat + 8 * w.toNat := by
        have := hp 1 (by omega)
        exact usize_add_mul_numeral p w 8 (by decide) (by omega)
      refine (ih (q + 8) (p + 8 * w) (fun t ht ↦ ⟨by rw [hq8]; have := hV t ht; omega,
        (hV t ht).2⟩) (fun c hc ↦ ?_) fun c hc u hu t ht ↦ ?_).mono ?_
      · rw [hp8]
        have := hp (c + 1) (by omega)
        rw [show 8 * (c + 1) * w.toNat = 8 * c * w.toNat + 8 * w.toNat by ring] at this
        omega
      · rw [hq8, hp8, show q.toNat + 8 + 8 * c + u = q.toNat + 8 * (c + 1) + u by ring,
          hT (c + 1) (by omega) u hu t ht]
        congr 1
        ring
      · rintro k ⟨c, hc, u, hu, t, ht, rfl⟩
        exact ⟨c, hc, u, hu, t, ht, by rw [hp8]; ring⟩
    refine (h0.comp hrest).mono ?_
    rintro k ⟨c, hc, u, hu, t, ht, rfl⟩
    rcases c with _ | c
    · exact Or.inl ⟨u, hu, t, ht, by ring⟩
    · exact Or.inr ⟨c, by omega, u, hu, t, ht, rfl⟩

/-- Packed word arrays keep the empty default. -/
theorem getD_map_encodeWords (C : Array (Array UInt32)) (j : Nat) :
    (C.map encode).getD j ByteArray.empty = encode (C.getD j #[]) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases C[j]? <;> rfl

/-- Rows `r0, …, r0 + rows - 1` of the matrix with columns `C`: word `r * C.size + j` is word
`r0 + r` of column `j`. A block size dividing the rows, `rows < 512 ∨ 512 ∣ rows`, lets the tiles
and edges cover every word. -/
theorem rowsOfColumns_encodeWords (C : Array (Array UInt32)) (r0 rows : Nat)
    (hC : ∀ j < C.size, r0 + rows ≤ (C.getD j #[]).size ∧ 4 * (C.getD j #[]).size < USize.size)
    (hN : 4 * (rows * C.size) < USize.size) (hrows : rows < 512 ∨ 512 ∣ rows) :
    rowsOfColumns (C.map encode) r0 rows = encode (Array.ofFn (n := rows * C.size) fun k ↦
      (C.getD (k.val % C.size) #[]).getD (r0 + k.val / C.size) 0) := by
  let w := C.size
  have hwC : w = C.size := rfl
  have hN' : 4 * (rows * w) < USize.size := hN
  let T (k : Nat) : UInt32 := (C.getD (k % w) #[]).getD (r0 + k / w) 0
  let B := min rows 512
  have hB : (rows < 512 ∧ B = rows) ∨ (512 ≤ rows ∧ B = 512 ∧ 512 ∣ rows) := by
    simp only [B]; omega
  have htile (rb : Nat) (hrb : rb ∈ List.range (rows / B)) (ct : Nat)
      (hct : ct ∈ List.range (w / 8)) :
      Fill T (fun k ↦ ∃ c < B / 8, ∃ u < 8, ∃ t < 8, k = (rb * B + 8 * c + u) * w + (8 * ct + t))
        (rows * w) (fun b ↦ rowsTiles ((C.map encode).getD (8 * ct + 0) .empty)
          ((C.map encode).getD (8 * ct + 1) .empty) ((C.map encode).getD (8 * ct + 2) .empty)
          ((C.map encode).getD (8 * ct + 3) .empty) ((C.map encode).getD (8 * ct + 4) .empty)
          ((C.map encode).getD (8 * ct + 5) .empty) ((C.map encode).getD (8 * ct + 6) .empty)
          ((C.map encode).getD (8 * ct + 7) .empty) w.toUSize (B / 8) (r0 + rb * B).toUSize
          (rb * B * w + 8 * ct).toUSize b) := by
    have hrb := List.mem_range.mp hrb
    have hct := List.mem_range.mp hct
    have hB0 : 0 < B := Nat.pos_of_ne_zero (by rintro h; rw [h, Nat.div_zero] at hrb; omega)
    have hrb' : (rb + 1) * B ≤ rows := (Nat.le_div_iff_mul_le hB0).mp hrb
    have e0 : (rb + 1) * B = rb * B + B := by ring
    have hw : (8 * ct + 8) * 1 ≤ w := by omega
    have hrw : (rb + 1) * B * w ≤ rows * w := Nat.mul_le_mul_right w hrb'
    have h1 : 1 * w ≤ (rb + 1) * B * w := Nat.mul_le_mul_right w (by nlinarith)
    have hwu : w.toUSize.toNat = w := USize.toNat_ofNat_of_lt' (by omega)
    have hcol (t : Nat) (ht : t < 8) := hC (8 * ct + t) (by omega)
    have hq : (r0 + rb * B).toUSize.toNat = r0 + rb * B := USize.toNat_ofNat_of_lt' (by
      have := hcol 0 (by decide)
      have : rb * B ≤ rows := by nlinarith
      omega)
    have e1 : (rb + 1) * B * w = rb * B * w + B * w := by ring
    have hBw : 8 * (B / 8) * w ≤ B * w := Nat.mul_le_mul_right w (by omega)
    have hp : (rb * B * w + 8 * ct).toUSize.toNat = rb * B * w + 8 * ct :=
      USize.toNat_ofNat_of_lt' (by omega)
    refine (fill_rowsTiles T (rows * w) (fun t ↦ (C.map encode).getD (8 * ct + t) .empty)
      (fun t ↦ C.getD (8 * ct + t) #[]) w.toUSize (fun t _ ↦ getD_map_encodeWords C _)
      (by omega) (B / 8) _ _ (fun t ht ↦ ⟨?_, (hcol t ht).2⟩) (fun c hc ↦ ?_)
      fun c hc u hu t ht ↦ ?_).mono ?_
    · rw [hq]; have := (hcol t ht).1; omega
    · rw [hp, hwu]
      have : (rb * B + 8 * c + 8) * w ≤ rows * w := Nat.mul_le_mul_right w (by omega)
      have e : (rb * B + 8 * c + 8) * w = rb * B * w + 8 * c * w + 8 * w := by ring
      omega
    · rw [hq, hp, hwu]
      have hd := divMod_add (rb * B + 8 * c + u) (8 * ct + t) w (by omega)
      simp only [T, show rb * B * w + 8 * ct + 8 * c * w + u * w + t =
        (rb * B + 8 * c + u) * w + (8 * ct + t) by ring, hd.1, hd.2]
      congr 1
      omega
    · rintro k ⟨c, hc, u, hu, t, ht, rfl⟩
      exact ⟨c, hc, u, hu, t, ht, by rw [hp, hwu]; ring⟩
  have hedge (r : Nat) (hr : r ∈ List.range rows) (j : Nat)
      (hj : j ∈ List.range' (if r < 8 * (rows / 8) then 8 * (w / 8) else 0)
        (w - if r < 8 * (rows / 8) then 8 * (w / 8) else 0)) :
      Fill T (· = r * w + j) (rows * w)
        (fun b ↦ write b (r * w + j) (read ((C.map encode).getD j .empty) (r0 + r))) := by
    have hr := List.mem_range.mp hr
    have hj : j < w := by have := List.mem_range'_1.mp hj; split at this <;> omega
    have h2 : (r + 1) * w ≤ rows * w := Nat.mul_le_mul_right w (by omega)
    have e2 : (r + 1) * w = r * w + w := by ring
    refine fill_write T (rows * w) _ _ hN (by omega) ?_
    have hd := divMod_add r j w hj
    have hc := hC j hj
    rw [getD_map_encodeWords, read_encodeWords _ _ (by rw [size_encode_uint32]; exact hc.2)
      (by omega)]
    simp only [T, hd.1, hd.2]
  have hall := (Fill.foldl T _ (rows * w) _ _ fun rb hrb ↦
    Fill.foldl T _ (rows * w) _ _ (htile rb hrb)).comp
    (Fill.foldl T _ (rows * w) _ _ fun r hr ↦ Fill.foldl T _ (rows * w) _ _ (hedge r hr))
  unfold rowsOfColumns
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure, pure_bind, zeroWords_eq,
    Array.size_map]
  refine hall.eq_ofFn (fun k hk ↦ ?_) _ Array.size_replicate
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro h; rw [h] at hk; simp at hk)
  have hk' := Nat.div_add_mod k w
  have hR : k / w < rows := (Nat.div_lt_iff_lt_mul hw).mpr hk
  have hJ := Nat.mod_lt k hw
  by_cases hin : k / w < 8 * (rows / 8) ∧ k % w < 8 * (w / 8)
  · have hc : k / w % B < 8 * (B / 8) := by
      rcases hB with ⟨_, hB⟩ | ⟨_, hB, _⟩ <;> rw [hB]
      · rw [Nat.mod_eq_of_lt hR]; exact hin.1
      · omega
    have hrb : k / w / B < rows / B := by
      rcases hB with ⟨_, hB⟩ | ⟨_, hB, _⟩ <;> rw [hB]
      · rw [Nat.div_eq_of_lt hR, Nat.div_self (by omega)]; decide
      · omega
    refine Or.inl ⟨k / w / B, List.mem_range.mpr hrb, k % w / 8, List.mem_range.mpr (by omega),
      k / w % B / 8, by omega, k / w % B % 8, Nat.mod_lt _ (by decide), k % w % 8,
      Nat.mod_lt _ (by decide), ?_⟩
    have := Nat.div_add_mod (k / w) B
    rw [show k / w / B * B + 8 * (k / w % B / 8) + k / w % B % 8 = k / w by
      rw [Nat.mul_comm]; omega, show 8 * (k % w / 8) + k % w % 8 = k % w by omega, Nat.mul_comm]
    omega
  · refine Or.inr ⟨k / w, List.mem_range.mpr hR, k % w, List.mem_range'_1.mpr ?_, ?_⟩
    · split <;> omega
    · rw [Nat.mul_comm]; omega

/-! ### Input columns -/

/-- Appending one range of words of a packed array. -/
theorem copySlice_encodeWords (a o : Array UInt32) (i c : Nat) :
    (encode a).copySlice (4 * i) (encode o) (encode o).size (4 * c) =
      encode (o ++ a.extract i (i + c)) :=
  PackedRepr.copySlice_encode a o i c

/-- Gathering word range `j` of every piece concatenates the ranges. -/
theorem gatherColumn_encodeWords (P : Nat → Array UInt32) (R rows j : Nat)
    (hP : ∀ k < R, j * rows + rows ≤ (P k).size) :
    gatherColumn ((Array.range R).map fun k ↦ encode (P k)) rows j =
      encode (Array.ofFn (n := R * rows) fun i ↦
        (P (i.val / rows)).getD (j * rows + i.val % rows) 0) := by
  unfold gatherColumn
  rw [Array.foldl_map, ← Array.foldl_toList, Array.toList_range, Array.size_map, Array.size_range,
    show ByteArray.emptyWithCapacity (4 * (R * rows)) = encode (#[] : Array UInt32) from rfl]
  induction R with
  | zero =>
    simp only [List.range_zero, List.foldl_nil]
    congr 1
    exact (Array.eq_empty_of_size_eq_zero (by simp)).symm
  | succ R ih =>
    rw [List.range_succ, List.foldl_append, ih fun k hk ↦ hP k (by omega), List.foldl_cons,
      List.foldl_nil, copySlice_encodeWords]
    congr 1
    have hR := hP R (by omega)
    apply array_eq_of_getD _ _ 0 (by
      rw [Array.size_append, Array.size_ofFn, Array.size_extract, Array.size_ofFn]
      rw [Nat.succ_mul]; omega)
    intro i
    rw [getD_append_eq, Array.size_ofFn]
    by_cases hi : i < R * rows
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hi), getD_ofFn_bounded _ _ hi,
        getD_ofFn_bounded _ _ (by rw [Nat.succ_mul]; omega)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hi)]
      by_cases hi' : i < (R + 1) * rows
      · have hrows : 0 < rows := Nat.pos_of_ne_zero (by rintro rfl; simp at hi')
        have hd := divMod_add R (i - R * rows) rows (by rw [Nat.succ_mul] at hi'; omega)
        rw [getD_ofFn_bounded _ _ hi',
          getD_extract _ _ _ _ _ hR (by rw [Nat.succ_mul] at hi'; omega)]
        rw [show R * rows + (i - R * rows) = i by omega] at hd
        rw [hd.1, hd.2]
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
          rw [Array.size_extract]; rw [Nat.succ_mul] at hi'; omega),
          Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [Array.size_ofFn]; omega)]

/-- The columns of a matrix from its transposed row ranges of columns `c0, …, c0 + n - 1`: entry
`i` of column `j` is entry `(i, c0 + j)` of the matrix. -/
theorem gatherColumn_transposeRows (M : Array UInt32) (w c0 n R rows j : Nat) (hn : c0 + n ≤ w)
    (hj : j < n) (hM : R * rows * w ≤ M.size) (hs : 4 * M.size < USize.size) :
    gatherColumn ((Array.range R).map fun k ↦ transposeRows (encode M) w c0 n (k * rows) rows)
      rows j = encode (Array.ofFn (n := R * rows) fun i ↦ M.getD (i.val * w + c0 + j) 0) := by
  have hpiece (k : Nat) (hk : k < R) : (k * rows + rows) * w ≤ M.size := by
    have := Nat.mul_le_mul_right w (show k * rows + rows ≤ R * rows by
      have := Nat.mul_le_mul_right rows (show k + 1 ≤ R by omega)
      rw [Nat.succ_mul] at this; exact this)
    omega
  have hm : (Array.range R).map (fun k ↦ transposeRows (encode M) w c0 n (k * rows) rows) =
      (Array.range R).map fun k ↦ encode (Array.ofFn (n := n * rows) fun i ↦
        M.getD ((k * rows + i.val % rows) * w + c0 + i.val / rows) 0) := by
    apply Array.ext (by simp only [Array.size_map])
    intro k h1 _
    simp only [Array.size_map, Array.size_range] at h1
    simp only [Array.getElem_map, Array.getElem_range]
    exact transposeRows_encodeWords M w c0 n _ rows hn (hpiece k h1) hs
  rw [hm, gatherColumn_encodeWords _ R rows j fun k hk ↦ by
    rw [Array.size_ofFn]
    have := Nat.mul_le_mul_right rows (show j + 1 ≤ n by omega)
    rw [Nat.succ_mul] at this; exact this]
  congr 1
  apply Array.ext (by simp only [Array.size_ofFn])
  intro i h1 _
  simp only [Array.size_ofFn] at h1
  have hrows : 0 < rows := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
  have hr := Nat.mod_lt i hrows
  have hd := divMod_add j (i % rows) rows hr
  have hjr : j * rows + i % rows < n * rows := by
    have := Nat.mul_le_mul_right rows (show j + 1 ≤ n by omega)
    rw [Nat.succ_mul] at this; omega
  simp only [Array.getElem_ofFn]
  rw [getD_ofFn_bounded _ _ hjr]
  dsimp only
  rw [hd.1, hd.2, show i / rows * rows + i % rows = i by
    rw [Nat.mul_comm]; exact Nat.div_add_mod i rows]

end CompPoly.CPolynomial.NTTFast.Packed.Native
