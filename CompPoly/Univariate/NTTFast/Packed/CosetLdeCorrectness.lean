/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.CosetLdeTransposes
public import CompPoly.Univariate.NTTFast.Packed.NativeLastCorrectness
public import CompPoly.Univariate.NTTFast.Packed.LeafStages
import all CompPoly.Univariate.NTTFast.Packed.CosetLde
import all CompPoly.Univariate.NTTFast.Packed.NativeLast
import all CompPoly.Univariate.NTTFast.Packed.Native
import all CompPoly.Univariate.NTTFast.Packed.KernelModels
import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas
import CompPoly.Univariate.NTT.Interpolation
import all CompPoly.Univariate.ToPoly.Core
import Mathlib.Tactic.Ring

/-! # Correctness of the batched coset low-degree extension

Each column's coefficients are the unnormalized inverse transform of the column, and block `t`
of its extension is the DIF transform of the coefficients scaled by coset table `bitrev t`. In
the bit-reversed row order the blocks concatenate to the values of the column's interpolant on
the coset `shift · ⟨ω⟩`; the transposes move columns and rows between them.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open Montgomery.Native32 (Mont32Field FastField)

variable {p : ℕ} [Mont32Field p]

open CompPoly.PackedRepr (encode size_encode_uint32)

/-! ### Kernels -/

/-- A loop whose body guards a single update is a fold of the guarded update. -/
theorem forIn_dite_yield {α β : Type} (L : List α) (init : β) (c : α → β → Prop)
    [∀ x b, Decidable (c x b)] (f : ∀ x b, c x b → β) :
    (forIn (m := Id) L init fun x b ↦
      if h : c x b then pure (ForInStep.yield (f x b h)) else pure (ForInStep.yield b)) =
      pure (L.foldl (fun b x ↦ if h : c x b then f x b h else b) init) := by
  induction L generalizing init with
  | nil => rfl
  | cons x L ih =>
    rw [List.forIn_cons, List.foldl_cons]
    split <;> exact ih _

/-- The in-place final-layer word kernel agrees with its field expression graph. -/
theorem Native.leaf16_encode (t3 t2 t1 : Array (FastField p)) (i : USize) (a : Array
    (FastField p)) (h) :
    Native.leaf16 p (encode t3) (encode t2) (encode t1) i (encode a) h =
      encode (leaf16Field t3 t2 t1 i a) := by
  have hi : i.toNat + 16 ≤ a.size := by
    have hh := h.1
    rw [size_encode_fields] at hh
    omega
  unfold Native.leaf16
  simp only [Native.readUOffset_encode, add_val, sub_val, mul_val]
  rw [Native.write16U_encode _ _ h.2.1 hi]
  rfl

/-- The in-place final-layer kernel runs the four last DIF layers of its block. -/
theorem Native.leaf16_correct (t3 t2 t1 : Array (FastField p)) (i : USize) (a : Array
    (FastField p)) (h)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) :
    Native.leaf16 p (encode t3) (encode t2) (encode t1) i (encode a) h =
      encode (Expressions.leaf16Stages t3 t2 t1 a i.toNat) := by
  have hi : i.toNat + 16 ≤ a.size := by
    have hi := h.1
    rw [size_encode_fields] at hi
    omega
  rw [Native.leaf16_encode, leaf16Field_eq_expression,
    Expressions.leaf16Field_eq_stages t3 t2 t1 a i hi h3 h2 h1]

/-- An eight-word store into encoded field values splices the values in. -/
theorem Native.storeWords8_encode (a : Array (FastField p)) (off : USize) (i : Nat)
    (ho : off.toNat = 4 * i) (hs : (encode a).size < USize.size) (hi : i + 8 ≤ a.size)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FastField p) :
    Native.storeWords (encode a) off 8 x0.val x1.val x2.val x3.val x4.val x5.val x6.val x7.val
      0 0 0 0 0 0 0 0 = encode (splice a i #[x0, x1, x2, x3, x4, x5, x6, x7]) := by
  rw [encode_eq_map_val] at hs ⊢
  rw [Native.storeWords8_encodeWords _ off i ho (by rwa [size_encode_uint32] at hs)
    (by rw [Array.size_map]; exact hi), encode_eq_map_val]
  congr 1
  simp only [splice, Array.map_append, map_val_extract, Array.size_map, List.map_toArray,
    List.map_cons, List.map_nil, List.size_toArray, List.length_cons, List.length_nil]

/-- An eight-word store from word `i + c` of encoded field values splices the values in. -/
theorem Native.storeWords8_encode_at (a : Array (FastField p)) (i c : USize)
    (hs : 4 * a.size < USize.size) (hi : i.toNat + c.toNat + 8 ≤ a.size)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FastField p) :
    Native.storeWords (encode a) ((i + c) * 4) 8 x0.val x1.val x2.val x3.val x4.val
      x5.val x6.val x7.val 0 0 0 0 0 0 0 0 =
      encode (splice8 a (i.toNat + c.toNat) x0 x1 x2 x3 x4 x5 x6 x7) := by
  rw [splice8_eq_splice _ _ _ _ _ _ _ _ _ _ hi]
  exact Native.storeWords8_encode a _ _ (Native.wordOffset_toNat _ _ (by omega))
    (by rw [size_encode_fields]; exact hs) hi _ _ _ _ _ _ _ _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The first stage kernel runs the first layer's model on its four blocks in turn. -/
theorem Native.leafStage8_encode (t a : Array (FastField p)) (i : USize) (h) :
    (Native.leafStage8 p (encode t) i (encode a) h).1 =
      encode (Expressions.leafStage8Field t (i.toNat + 48)
        (Expressions.leafStage8Field t (i.toNat + 32)
          (Expressions.leafStage8Field t (i.toNat + 16)
            (Expressions.leafStage8Field t i.toNat a)))) := by
  obtain ⟨h1, h2, -, -⟩ := h
  have hb : 4 * (i.toNat + 64) ≤ 4 * a.size := by rwa [size_encode_fields] at h1
  have hs : 4 * a.size < USize.size := by rwa [size_encode_fields] at h2
  unfold Native.leafStage8
  simp only [Native.store8_val _ _ _ _ _ _ _ _ _ _ _ h2, Native.touchLast, Native.touch_eq]
  simp only [Native.readUOffset_encode, add_val, sub_val, mul_val]
  simp (disch := ((try simp only [size_splice8, USize.reduceToNat, USize.toNat_zero]); omega))
    only [Native.storeWords8_encode_at]
  apply congrArg encode
  unfold Expressions.leafStage8Field
  simp (disch := omega) only [getD_splice8_out]
  simp only [Expressions.fieldAdd, Expressions.fieldSub, Expressions.fieldMul, USize.reduceToNat,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The second stage kernel runs the second layer's model on its four blocks in turn. -/
theorem Native.leafStage4_encode (t a : Array (FastField p)) (i : USize) (h) :
    (Native.leafStage4 p (encode t) i (encode a) h).1 =
      encode (Expressions.leafStage4Field t (i.toNat + 48)
        (Expressions.leafStage4Field t (i.toNat + 32)
          (Expressions.leafStage4Field t (i.toNat + 16)
            (Expressions.leafStage4Field t i.toNat a)))) := by
  obtain ⟨h1, h2, -, -⟩ := h
  have hb : 4 * (i.toNat + 64) ≤ 4 * a.size := by rwa [size_encode_fields] at h1
  have hs : 4 * a.size < USize.size := by rwa [size_encode_fields] at h2
  unfold Native.leafStage4
  simp only [Native.store8_val _ _ _ _ _ _ _ _ _ _ _ h2, Native.touchLast, Native.touch_eq]
  simp only [Native.readUOffset_encode, add_val, sub_val, mul_val]
  simp (disch := ((try simp only [size_splice8, USize.reduceToNat, USize.toNat_zero]); omega))
    only [Native.storeWords8_encode_at]
  apply congrArg encode
  unfold Expressions.leafStage4Field
  simp (disch := omega) only [getD_splice8_out]
  simp only [Expressions.fieldAdd, Expressions.fieldSub, Expressions.fieldMul, USize.reduceToNat,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The third stage kernel runs the third layer's model on its four blocks in turn. -/
theorem Native.leafStage2_encode (t a : Array (FastField p)) (i : USize) (h) :
    (Native.leafStage2 p (encode t) i (encode a) h).1 =
      encode (Expressions.leafStage2Field t (i.toNat + 48)
        (Expressions.leafStage2Field t (i.toNat + 32)
          (Expressions.leafStage2Field t (i.toNat + 16)
            (Expressions.leafStage2Field t i.toNat a)))) := by
  obtain ⟨h1, h2, -, -⟩ := h
  have hb : 4 * (i.toNat + 64) ≤ 4 * a.size := by rwa [size_encode_fields] at h1
  have hs : 4 * a.size < USize.size := by rwa [size_encode_fields] at h2
  unfold Native.leafStage2
  simp only [Native.store8_val _ _ _ _ _ _ _ _ _ _ _ h2, Native.touchLast, Native.touch_eq]
  simp only [Native.readUOffset_encode, add_val, sub_val, mul_val]
  simp (disch := ((try simp only [size_splice8, USize.reduceToNat, USize.toNat_zero]); omega))
    only [Native.storeWords8_encode_at]
  apply congrArg encode
  unfold Expressions.leafStage2Field
  simp (disch := omega) only [getD_splice8_out]
  simp only [Expressions.fieldAdd, Expressions.fieldSub, Expressions.fieldMul, USize.reduceToNat,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The last stage kernel runs the last layer's model on its four blocks in turn. -/
theorem Native.leafStage1_encode (t : ByteArray) (a : Array (FastField p)) (i : USize) (h) :
    (Native.leafStage1 p t i (encode a) h).1 =
      encode (Expressions.leafStage1Field (i.toNat + 48)
        (Expressions.leafStage1Field (i.toNat + 32)
          (Expressions.leafStage1Field (i.toNat + 16)
            (Expressions.leafStage1Field i.toNat a)))) := by
  obtain ⟨h1, h2, -, -⟩ := h
  have hb : 4 * (i.toNat + 64) ≤ 4 * a.size := by rwa [size_encode_fields] at h1
  have hs : 4 * a.size < USize.size := by rwa [size_encode_fields] at h2
  unfold Native.leafStage1
  simp only [Native.store8_val _ _ _ _ _ _ _ _ _ _ _ h2, Native.touchLast, Native.touch_eq]
  simp only [Native.readUOffset_encode, add_val, sub_val]
  simp (disch := ((try simp only [size_splice8, USize.reduceToNat, USize.toNat_zero]); omega))
    only [Native.storeWords8_encode_at]
  apply congrArg encode
  unfold Expressions.leafStage1Field
  simp (disch := omega) only [getD_splice8_out]
  simp only [Expressions.fieldAdd, Expressions.fieldSub, USize.reduceToNat,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_zero]


/-- The stage loop depends only on the buffer's value. -/
theorem Native.leafStageLoop_congr {K : Nat}
    {k : (t : ByteArray) → (i : USize) → (b : ByteArray) → Native.LeafStageFits b t i K →
      Native.Buf b.size}
    {t : ByteArray} {count : Nat} {i : USize} {b b' : ByteArray} (h) (e : b = b') :
    Native.leafStageLoop K k t count i b h = Native.leafStageLoop K k t count i b' (e ▸ h) := by
  subst e
  rfl

/-- A stage loop whose kernel runs `F` on its four blocks in turn runs `F` on blocks
`4 g, …, 4 (g + count) - 1`. -/
theorem Native.leafStageLoop_encode {K : Nat}
    (k : (t : ByteArray) → (i : USize) → (b : ByteArray) → Native.LeafStageFits b t i K →
      Native.Buf b.size)
    (t : ByteArray) (F : Array (FastField p) → Nat → Array (FastField p))
    (hk : ∀ i (b : Array (FastField p)) h, (k t i (encode b) h).1 =
      encode (F (F (F (F b i.toNat) (i.toNat + 16)) (i.toNat + 32)) (i.toNat + 48))) :
    ∀ (count g : Nat) (i : USize) (b : Array (FastField p)) (h), i.toNat = 64 * g →
      Native.leafStageLoop K k t count i (encode b) h =
        encode ((List.range' (4 * g) (4 * count)).foldl (fun b blk ↦ F b (blk * 16)) b) := by
  intro count
  induction count with
  | zero => intro _ _ _ _ _; rfl
  | succ count ih =>
    intro g i b h hi
    have hb := h.1
    have hs := h.2.1
    rw [size_encode_fields] at hb hs
    have h64 : (i + 64).toNat = i.toNat + 64 := by
      rw [Native.usize_add_toNat _ _ (by rw [Native.usize_numeral 64 (by decide)]; omega),
        Native.usize_numeral 64 (by decide)]
    rw [Native.leafStageLoop, Native.leafStageLoop_congr _ (hk i b _),
      ih (g + 1) _ _ _ (by rw [h64, hi]; ring), show 4 * (count + 1) = 4 + 4 * count by ring,
      ← List.range'_append, List.foldl_append, show 4 * (g + 1) = 4 * g + 4 by ring]
    simp only [List.range'_succ, List.range'_zero, List.foldl_cons, List.foldl_nil, hi]
    rw [show 4 * g * 16 = 64 * g by ring, show (4 * g + 1) * 16 = 64 * g + 16 by ring,
      show (4 * g + 1 + 1) * 16 = 64 * g + 32 by ring,
      show (4 * g + 1 + 1 + 1) * 16 = 64 * g + 48 by ring, Nat.one_mul]

/-- A fold of block operations agreeing with `G` on arrays of the original size is the fold of
`G`. -/
theorem foldl_blocks_congr (F G : Array (FastField p) → Nat → Array (FastField p)) (n : Nat)
    (a : Array (FastField p)) (hn : n * 16 ≤ a.size)
    (hFG : ∀ b base, base + 16 ≤ b.size → F b base = G b base)
    (hG : ∀ b base, base + 16 ≤ b.size → (G b base).size = b.size) :
    (List.range n).foldl (fun b blk ↦ F b (blk * 16)) a =
      (List.range n).foldl (fun b blk ↦ G b (blk * 16)) a := by
  suffices ∀ (xs : List Nat) (b : Array (FastField p)), b.size = a.size → (∀ x ∈ xs, x < n) →
      xs.foldl (fun b blk ↦ F b (blk * 16)) b = xs.foldl (fun b blk ↦ G b (blk * 16)) b from
    this _ a rfl (fun x hx ↦ List.mem_range.mp hx)
  intro xs
  induction xs with
  | nil => intro _ _ _; rfl
  | cons x xs ih =>
    intro b hb hx
    have hx' := hx x (List.mem_cons_self ..)
    have hfit : x * 16 + 16 ≤ b.size := by rw [hb]; nlinarith
    rw [List.foldl_cons, List.foldl_cons, hFG b _ hfit]
    exact ih _ (by rw [hG b _ hfit, hb]) (fun y hy ↦ hx y (List.mem_cons_of_mem x hy))

/-- The first stage's pass over `4 count` blocks is the first final layer on each block. -/
theorem Native.leafStage8Loop_encode (t a : Array (FastField p)) (count : Nat) (h) :
    Native.leafStageLoop 8 (Native.leafStage8 p) (encode t) count 0 (encode a) h =
      encode ((List.range (4 * count)).foldl (fun b blk ↦ layer16_8 t b (blk * 16)) a) := by
  have hb := h.1
  rw [size_encode_fields, USize.toNat_zero] at hb
  rw [Native.leafStageLoop_encode _ _ (fun b base ↦ Expressions.leafStage8Field t base b)
    (fun i b h ↦ Native.leafStage8_encode t b i h) count 0 0 a h rfl, Nat.mul_zero,
    ← List.range_eq_range',
    foldl_blocks_congr _ _ _ a (by omega)
      (fun b base hb ↦ Expressions.leafStage8Field_eq t b base hb)
      (fun b base _ ↦ size_layer16_8 t b base)]

/-- The second stage's pass over `4 count` blocks is the second final layer on each block. -/
theorem Native.leafStage4Loop_encode (t a : Array (FastField p)) (count : Nat) (h) :
    Native.leafStageLoop 4 (Native.leafStage4 p) (encode t) count 0 (encode a) h =
      encode ((List.range (4 * count)).foldl (fun b blk ↦ layer16_4 t b (blk * 16)) a) := by
  have hb := h.1
  rw [size_encode_fields, USize.toNat_zero] at hb
  rw [Native.leafStageLoop_encode _ _ (fun b base ↦ Expressions.leafStage4Field t base b)
    (fun i b h ↦ Native.leafStage4_encode t b i h) count 0 0 a h rfl, Nat.mul_zero,
    ← List.range_eq_range',
    foldl_blocks_congr _ _ _ a (by omega)
      (fun b base hb ↦ Expressions.leafStage4Field_eq t b base hb)
      (fun b base _ ↦ size_layer16_4 t b base)]

/-- The third stage's pass over `4 count` blocks is the third final layer on each block. -/
theorem Native.leafStage2Loop_encode (t a : Array (FastField p)) (count : Nat) (h) :
    Native.leafStageLoop 2 (Native.leafStage2 p) (encode t) count 0 (encode a) h =
      encode ((List.range (4 * count)).foldl (fun b blk ↦ layer16_2 t b (blk * 16)) a) := by
  have hb := h.1
  rw [size_encode_fields, USize.toNat_zero] at hb
  rw [Native.leafStageLoop_encode _ _ (fun b base ↦ Expressions.leafStage2Field t base b)
    (fun i b h ↦ Native.leafStage2_encode t b i h) count 0 0 a h rfl, Nat.mul_zero,
    ← List.range_eq_range',
    foldl_blocks_congr _ _ _ a (by omega)
      (fun b base hb ↦ Expressions.leafStage2Field_eq t b base hb)
      (fun b base _ ↦ size_layer16_2 t b base)]

/-- The last stage's pass over `4 count` blocks is the last final layer on each block. -/
theorem Native.leafStage1Loop_encode (t : ByteArray) (a : Array (FastField p)) (count : Nat) (h) :
    Native.leafStageLoop 0 (Native.leafStage1 p) t count 0 (encode a) h =
      encode ((List.range (4 * count)).foldl (fun b blk ↦ layer16_1 #[1] b (blk * 16)) a) := by
  have hb := h.1
  rw [size_encode_fields, USize.toNat_zero] at hb
  rw [Native.leafStageLoop_encode _ _ (fun b base ↦ Expressions.leafStage1Field base b)
    (fun i b h ↦ Native.leafStage1_encode t b i h) count 0 0 a h rfl, Nat.mul_zero,
    ← List.range_eq_range',
    foldl_blocks_congr _ _ _ a (by omega)
      (fun b base hb ↦ Expressions.leafStage1Field_eq b base hb)
      (fun b base _ ↦ size_layer16_1 #[1] b base)]

/-- The final layers of `blocks` sixteen-word blocks. -/
theorem Native.leaf16Blocks_encode (t3 t2 t1 : Array (FastField p)) (blocks : Nat) (a : Array
    (FastField p))
    (ha : 4 * a.size < USize.size) (hs : blocks * 16 ≤ a.size)
    (ht3 : t3.size = 8) (ht2 : t2.size = 4) (ht1 : t1.size = 2)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) :
    Native.leaf16Blocks p (encode t3) (encode t2) (encode t1) blocks (encode a) =
      encode ((List.range blocks).foldl (fun b block ↦
        Expressions.leaf16Stages t3 t2 t1 b (block * 16)) a) := by
  let st (b : Array (FastField p)) (block : Nat) : Array (FastField p) :=
    Expressions.leaf16Stages t3 t2 t1 b (block * 16)
  have hsize (b : Array (FastField p)) : (encode b).size = 4 * b.size := size_encode_fields b
  unfold Native.leaf16Blocks
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, bind_pure, forIn_dite_yield]
  rw [dite_eq_left_of_eq_true (eq_true (by
      simp only [hsize, ht3, ht2, ht1]
      have := USize.le_size
      omega))]
  simp only [Native.leafStage8Loop_encode, Native.leafStage4Loop_encode,
    Native.leafStage2Loop_encode, Native.leafStage1Loop_encode, layer16_8_eq_localLayer,
    layer16_4_eq_localLayer, layer16_2_eq_localLayer, layer16_1_eq_localLayer]
  rw [fold_localLayer _ 8 1 _ (by decide), fold_localLayer _ 4 2 _ (by decide),
    fold_localLayer _ 2 4 _ (by decide), fold_localLayer _ 1 8 _ (by decide)]
  simp only [Nat.reduceMul, Nat.one_mul]
  rw [← fold_leaf16Stages]
  rw [foldl_encode _ (fun b ↦ b.size = a.size) _ st (fun block hblock b hb ↦ by
      have hblock := List.mem_range'_1.mp hblock
      have hc : 4 * (16 * block + 15) + 3 < (encode b).size ∧ (encode b).size < USize.size ∧
          31 < (encode t3).size ∧ (encode t3).size < USize.size ∧
          15 < (encode t2).size ∧ (encode t2).size < USize.size ∧
          7 < (encode t1).size ∧ (encode t1).size < USize.size := by
        rw [hsize, hsize, hsize, hsize, ht3, ht2, ht1, hb]
        have := USize.le_size
        omega
      rw [dite_eq_left_of_eq_true (eq_true hc), Native.leaf16_correct _ _ _ _ _ _ h3 h2 h1,
        USize.toNat_ofNatLT, Nat.mul_comm])
    (fun _ _ b hb ↦ by simp only [st, Expressions.size_leaf16Stages, hb]) _
    (foldl_invariant _ (fun b ↦ b.size = a.size) _
      (fun _ _ b hb ↦ by simp only [Expressions.size_leaf16Stages, hb]) a rfl)]
  have hn : blocks = 4 * (blocks / 4) + (blocks - 4 * (blocks / 4)) := by omega
  conv => rhs; rw [hn, List.range_eq_range', ← List.range'_append, List.foldl_append,
    ← List.range_eq_range', Nat.zero_add, Nat.one_mul]
  rfl

/-- A DIF-order leaf is the mixed radix-four DIF stages. -/
theorem Native.leafReversed_encode (D : NTT.Domain (FastField p)) (tw : Array (Array
    (FastField p))) (X : Array (FastField p))
    (htw : TwiddleSizes D.logN tw) (hone : TwiddleOnes D.logN tw) (hs : X.size = D.n)
    (hu : 4 * D.n < USize.size) :
    Native.leafReversed p (tw.map encode) D.logN (encode X) =
      encode (Plan.runStagesDIFRadix4WithTwiddles D tw X) := by
  have hn : X.size = 2 ^ D.logN := hs
  have hu' : 4 * 2 ^ D.logN < USize.size := hu
  rw [← fieldLayers_eq D tw X hs]
  unfold Native.leafReversed
  split
  · rename_i hm
    have hzero : tw.getD 0 #[] = #[1] :=
      twiddle_zero_eq_one _ (by simpa using htw 0 (by omega)) (hone 0 (by omega))
    let U := fieldLayers tw D.logN (D.logN / 2 - 2) X
    have hUs : U.size = 2 ^ D.logN := by simp only [U, size_fieldLayers, hn]
    rw [Native.leafLayers_encode tw _ _ X (by omega) htw hn hu', getD_map_encode,
      getD_map_encode, getD_map_encode,
      Native.leaf16Blocks_encode _ _ _ _ U (by rw [hUs]; exact hu')
        (by rw [hUs]; exact Nat.div_mul_le_self _ _) (by simpa using htw 3 (by omega))
        (by simpa using htw 2 (by omega)) (by simpa using htw 1 (by omega)) (hone 3 (by omega))
        (hone 2 (by omega)) (hone 1 (by omega)),
      fold_leaf16Stages_eq_radix4 _ _ _ _ U (by rw [hUs]; exact Nat.div_mul_le_self _ _)]
    congr 1
    have hrange : List.range (D.logN / 2) =
        List.range (D.logN / 2 - 2) ++ [D.logN / 2 - 2, D.logN / 2 - 1] := by
      obtain ⟨P, hP⟩ : ∃ P, D.logN / 2 = P + 2 := ⟨D.logN / 2 - 2, by omega⟩
      rw [hP, List.range_succ, List.range_succ, List.append_assoc]
      rfl
    have h3 : D.logN - 1 - D.logN % 2 - 2 * (D.logN / 2 - 2) = 3 := by omega
    have h1 : D.logN - 1 - D.logN % 2 - 2 * (D.logN / 2 - 1) = 1 := by omega
    have hd : 16 ∣ 2 ^ D.logN := by simpa using Nat.pow_dvd_pow 2 (show 4 ≤ D.logN by omega)
    unfold fieldLayers
    rw [hrange, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil]
    simp only [h3, h1, Nat.reduceSub, Nat.reducePow, hzero]
    rw [show 2 ^ D.logN / 4 = 4 * (2 ^ D.logN / 16) by omega]
    rfl
  · exact Native.leafLayers_encode tw _ _ X (le_refl _) htw hn hu'

/-- The sixteen-word product kernel fills its words with the products. -/
theorem Native.fill_mul16 (t a : Array (FastField p)) (i : USize) (N : Nat)
    (hN : 4 * N < USize.size)
    (hi : i.toNat + 16 ≤ N) (h) :
    Native.Fill (fun k ↦ (t.getD k 0 * a.getD k 0).val) (fun k ↦ i.toNat ≤ k ∧ k < i.toNat + 16)
      N (fun b ↦ Native.mul16 p (encode t) (encode a) i b h) := by
  refine (Native.fill_write16U _ N i (fun k ↦ (t.getD (i.toNat + k) 0 * a.getD (i.toNat + k) 0).val)
    hN hi fun _ _ ↦ rfl).congr fun b ↦ ?_
  unfold Native.mul16
  simp only [Native.readUOffset_encode, mul_val, USize.reduceToNat]

/-- The checked product loop fills its `16 * count` words with the products. -/
theorem Native.fill_mul16Loop (t a : Array (FastField p)) (N : Nat) (hN : 4 * N < USize.size) :
    ∀ (count : Nat) (i : USize) (h), i.toNat + 16 * count ≤ N →
    Native.Fill (fun k ↦ (t.getD k 0 * a.getD k 0).val)
      (fun k ↦ i.toNat ≤ k ∧ k < i.toNat + 16 * count) N
      (fun b ↦ Native.mul16Loop p (encode t) (encode a) count i b h) := by
  intro count
  induction count with
  | zero =>
    intro i h _
    exact (Native.Fill.id _ N).mono fun k hk ↦ by omega
  | succ count ih =>
    intro i h hN'
    have ht := h.2.2.1
    have hi : (i + 16).toNat = i.toNat + 16 := Native.usize_add16 i _ (by omega) ht
    have h0 : 4 * (i.toNat + 15) + 3 < (encode t).size ∧ 4 * (i.toNat + 15) + 3 < (encode a).size ∧
        (encode t).size < USize.size ∧ (encode a).size < USize.size := by omega
    have h1 : 4 * ((i + 16).toNat + 16 * count) ≤ (encode t).size ∧
        4 * ((i + 16).toNat + 16 * count) ≤ (encode a).size ∧
        (encode t).size < USize.size ∧ (encode a).size < USize.size := by rw [hi]; omega
    refine (((Native.fill_mul16 t a i N hN (by omega) h0).comp
      (ih (i + 16) h1 (by rw [hi]; omega))).congr fun b ↦ ?_).mono fun k hk ↦ ?_
    · rfl
    · rw [hi] at *
      omega

/-- Products of the first `n` coordinates. -/
theorem Native.mulWords_encode (t a : Array (FastField p)) (n : Nat) (ht : n ≤ t.size)
    (ha : n ≤ a.size)
    (hts : 4 * t.size < USize.size) (has : 4 * a.size < USize.size) :
    Native.mulWords p (encode t) (encode a) n =
      encode (Array.ofFn (n := n) fun i ↦ t.getD i.val 0 * a.getD i.val 0) := by
  let T (k : Nat) : UInt32 := (t.getD k 0 * a.getD k 0).val
  have hN : 4 * n < USize.size := by omega
  have hedge (k : Nat) (hk : k ∈ List.range' (16 * (n / 16)) (n - 16 * (n / 16))) :
      Native.Fill T (· = k) n (fun b ↦
        Native.write b k (mul p (Native.read (encode t) k) (Native.read (encode a) k))) := by
    have hk := List.mem_range'_1.mp hk
    refine Native.fill_write T n k _ hN (by omega) ?_
    rw [Native.read_encode _ _ (by rw [size_encode_fields]; exact hts) (by omega),
      Native.read_encode _ _ (by rw [size_encode_fields]; exact has) (by omega), mul_val]
  have hg : 4 * (16 * (n / 16)) ≤ (encode t).size ∧ 4 * (16 * (n / 16)) ≤ (encode a).size ∧
      (encode t).size < USize.size ∧ (encode a).size < USize.size := by
    simp only [size_encode_fields]
    omega
  have hall := (Native.fill_mul16Loop t a n hN (n / 16) 0
    (by rw [USize.toNat_zero, Nat.zero_add]; exact hg) (by rw [USize.toNat_zero]; omega)).comp
    (Native.Fill.foldl T _ n _ _ hedge)
  unfold Native.mulWords
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, bind_pure,
    Native.zeroWords_eq]
  rw [dite_eq_left_of_eq_true (eq_true hg)]
  refine (hall.eq_ofFn (fun k hk ↦ ?_) _ Array.size_replicate).trans ?_
  · by_cases hk' : k < 16 * (n / 16)
    · exact Or.inl ⟨by rw [USize.toNat_zero]; omega, by rw [USize.toNat_zero]; omega⟩
    · exact Or.inr ⟨k, List.mem_range'_1.mpr (by omega), rfl⟩
  · rw [encode_eq_map_val, Array.map_ofFn]
    rfl

/-- The scaled out-of-place radix-two kernel stores its sixteen sums and sixteen differences. -/
theorem Native.pair16Scaled_eq (w T c : Array (FastField p)) (j i0 i1 : USize) (out : ByteArray)
    (h) :
    Native.pair16Scaled p (encode w) (encode T) (encode c) j i0 i1 out h =
      let x (k : Nat) := T.getD (i0.toNat + k) 0 * c.getD (i0.toNat + k) 0
      let y (k : Nat) := T.getD (i1.toNat + k) 0 * c.getD (i1.toNat + k) 0
      let s (k : Nat) := (x k + y k).val
      let d (k : Nat) := (w.getD (j.toNat + k) 0 * (x k - y k)).val
      Native.write16U (Native.write16U out i0 (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) (s 7)
        (s 8) (s 9) (s 10) (s 11) (s 12) (s 13) (s 14) (s 15)) i1 (d 0) (d 1) (d 2) (d 3) (d 4)
        (d 5) (d 6) (d 7) (d 8) (d 9) (d 10) (d 11) (d 12) (d 13) (d 14) (d 15) := by
  unfold Native.pair16Scaled
  simp only [Native.readUOffset_encode, add_val, sub_val, mul_val, USize.reduceToNat]

/-- The coordinates of the first radix-two DIF layer of `X` with half `h`. -/
theorem getD_firstLayer (w X : Array (FastField p)) (h : Nat) (hX : X.size = 2 * h) (k : Nat) :
    (Plan.butterflyDIFInner w h 0 0 h X).getD k 0 =
      if k < h then X.getD k 0 + X.getD (h + k) 0
      else if k < 2 * h then w.getD (k - h) 0 * (X.getD (k - h) 0 - X.getD k 0)
      else 0 := by
  split_ifs with h1 h2
  · rw [getD_butterflyDIFInner_left w h 0 0 h X (by omega) (by omega) k (by omega),
      Nat.sub_zero]
  · rw [getD_butterflyDIFInner_right w h 0 0 h X (by omega) (by omega) k (by omega)]
    simp only [Nat.zero_add]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
      rw [Plan.size_butterflyDIFInner]; omega), Option.getD_none]

/-- The products `T ⊙ c` of the first `n` coordinates. -/
abbrev scaledCoeffs (T c : Array (FastField p)) (n : Nat) : Array (FastField p) :=
  Array.ofFn (n := n) fun i ↦ T.getD i.val 0 * c.getD i.val 0

theorem getD_scaledCoeffs (T c : Array (FastField p)) (n i : Nat) (hi : i < n) :
    (scaledCoeffs T c n).getD i 0 = T.getD i 0 * c.getD i 0 :=
  getD_ofFn_bounded _ i hi 0

/-- The scaled radix-two kernel at butterfly `j` fills its words of the first layer of `T ⊙ c`. -/
theorem Native.fill_pair16Scaled (w T c : Array (FastField p)) (h N : Nat) (hU j : USize)
    (hhU : hU.toNat = h) (hN : 4 * N < USize.size) (hj : j.toNat + 16 ≤ h) (hNh : 2 * h ≤ N)
    (hb) :
    Native.Fill (fun k ↦ ((Plan.butterflyDIFInner w h 0 0 h (scaledCoeffs T c (2 * h))).getD k
        0).val)
      (fun k ↦ (j.toNat ≤ k ∧ k < j.toNat + 16) ∨ (j.toNat + h ≤ k ∧ k < j.toNat + h + 16)) N
      (fun b ↦ Native.pair16Scaled p (encode w) (encode T) (encode c) j j (j + hU) b hb) := by
  have hjh : (j + hU).toNat = j.toNat + h := by
    rw [Native.usize_add_toNat _ _ (by rw [hhU]; omega), hhU]
  have hX : (scaledCoeffs T c (2 * h)).size = 2 * h := Array.size_ofFn
  let x (k : Nat) := T.getD (j.toNat + k) 0 * c.getD (j.toNat + k) 0
  let y (k : Nat) := T.getD ((j + hU).toNat + k) 0 * c.getD ((j + hU).toNat + k) 0
  refine ((Native.fill_write16U _ N j (fun k ↦ (x k + y k).val) hN (by omega)
    fun t ht ↦ ?_).comp (Native.fill_write16U _ N (j + hU)
      (fun k ↦ (w.getD (j.toNat + k) 0 * (x k - y k)).val) hN (by omega)
    fun t ht ↦ ?_)).congr (fun b ↦ ?_) |>.mono fun k hk ↦ ?_
  · simp only [x, y]
    rw [getD_firstLayer _ _ _ hX, ite_eq_left (by omega), getD_scaledCoeffs _ _ _ _ (by omega),
      getD_scaledCoeffs _ _ _ _ (by omega), hjh, show h + (j.toNat + t) = j.toNat + h + t by omega]
  · simp only [x, y]
    rw [hjh, getD_firstLayer _ _ _ hX, ite_eq_right (by omega), ite_eq_left (by omega),
      getD_scaledCoeffs _ _ _ _ (by omega), getD_scaledCoeffs _ _ _ _ (by omega),
      show j.toNat + h + t - h = j.toNat + t by omega]
  · rw [Native.pair16Scaled_eq]; rfl
  · rw [hjh]; omega

/-- The checked scaled radix-two loop fills its butterflies' words of the first layer of
`T ⊙ c`. -/
theorem Native.fill_pair16ScaledLoop (w T c : Array (FastField p)) (h N : Nat) (hU : USize)
    (hhU : hU.toNat = h) (hN : 4 * N < USize.size) (hNh : 2 * h ≤ N) :
    ∀ (n : Nat) (j : USize) (hb), j.toNat + 16 * n ≤ h →
    Native.Fill (fun k ↦ ((Plan.butterflyDIFInner w h 0 0 h (scaledCoeffs T c (2 * h))).getD k
        0).val)
      (fun k ↦ (j.toNat ≤ k ∧ k < j.toNat + 16 * n) ∨
        (j.toNat + h ≤ k ∧ k < j.toNat + h + 16 * n)) N
      (fun b ↦ Native.pair16ScaledLoop p (encode w) (encode T) (encode c) hU n j b hb) := by
  intro n
  induction n with
  | zero =>
    intro j hb _
    exact (Native.Fill.id _ N).mono fun k hk ↦ by omega
  | succ n ih =>
    intro j hb hjn
    have hj : (j + 16).toNat = j.toNat + 16 := Native.usize_add16 j _ (by omega) hb.2.2.2.1
    have hh : (j + hU).toNat = j.toNat + hU.toNat := Native.usize_add_toNat _ _ (by omega)
    have H0 : 4 * (j.toNat + 15) + 3 < (encode c).size ∧
        4 * ((j + hU).toNat + 15) + 3 < (encode c).size ∧
        4 * (j.toNat + 15) + 3 < (encode T).size ∧
        4 * ((j + hU).toNat + 15) + 3 < (encode T).size ∧
        4 * (j.toNat + 15) + 3 < (encode w).size ∧ (encode c).size < USize.size ∧
        (encode T).size < USize.size ∧ (encode w).size < USize.size := by rw [hh]; omega
    have H1 : 4 * (hU.toNat + (j + 16).toNat + 16 * n) ≤ (encode c).size ∧
        4 * (hU.toNat + (j + 16).toNat + 16 * n) ≤ (encode T).size ∧
        4 * ((j + 16).toNat + 16 * n) ≤ (encode w).size ∧ (encode c).size < USize.size ∧
        (encode T).size < USize.size ∧ (encode w).size < USize.size := by rw [hj]; omega
    refine (((Native.fill_pair16Scaled w T c h N hU j hhU hN (by omega) hNh H0).comp
      (ih (j + 16) H1 (by rw [hj]; omega))).congr fun b ↦ ?_).mono fun k hk ↦ ?_
    · rfl
    · rw [hj] at *
      omega

/-- The scaled out-of-place radix-two pass is the first DIF layer of `T ⊙ c`. -/
theorem Native.pairsScaled_encode (w T c : Array (FastField p)) (h : Nat) (hw : h ≤ w.size)
    (hT : 2 * h ≤ T.size) (hc : 2 * h ≤ c.size) (hws : 4 * w.size < USize.size)
    (hTs : 4 * T.size < USize.size) (hcs : 4 * c.size < USize.size) :
    Native.pairsScaled p (encode w) (encode T) (encode c) h =
      encode (Plan.butterflyDIFInner w h 0 0 h (scaledCoeffs T c (2 * h))) := by
  let Y := Plan.butterflyDIFInner w h 0 0 h (scaledCoeffs T c (2 * h))
  let Tg (k : Nat) : UInt32 := (Y.getD k 0).val
  have hX : (scaledCoeffs T c (2 * h)).size = 2 * h := Array.size_ofFn
  have hY : Y.size = 2 * h := by simp only [Y, Plan.size_butterflyDIFInner, hX]
  have hN : 4 * (2 * h) < USize.size := by omega
  have hrd (a : Array (FastField p)) (ha : 4 * a.size < USize.size) (i : Nat) (hi : i < a.size) :
      Native.read (encode a) i = (a.getD i 0).val :=
    Native.read_encode a i (by rw [size_encode_fields]; exact ha) hi
  have hedge (k : Nat) (hk : k ∈ List.range' (16 * (h / 16)) (h - 16 * (h / 16))) :
      Native.Fill Tg (fun i ↦ i = k ∨ i = h + k) (2 * h) (fun b ↦
        let x := mul p (Native.read (encode T) k) (Native.read (encode c) k)
        let y := mul p (Native.read (encode T) (h + k)) (Native.read (encode c) (h + k))
        Native.write (Native.write b k (add p x y)) (h + k)
          (mul p (Native.read (encode w) k) (sub p x y))) := by
    have hk := List.mem_range'_1.mp hk
    refine ((Native.fill_write Tg (2 * h) k _ hN (by omega) ?_).comp
      (Native.fill_write Tg (2 * h) (h + k) _ hN (by omega) ?_)).congr fun b ↦ rfl
    · rw [hrd T hTs k (by omega), hrd c hcs k (by omega), hrd T hTs (h + k) (by omega),
        hrd c hcs (h + k) (by omega), mul_val, mul_val, add_val]
      simp only [Tg, Y]
      rw [getD_firstLayer _ _ _ hX, ite_eq_left (by omega), getD_scaledCoeffs _ _ _ _ (by omega),
        getD_scaledCoeffs _ _ _ _ (by omega)]
    · rw [hrd T hTs k (by omega), hrd c hcs k (by omega), hrd T hTs (h + k) (by omega),
        hrd c hcs (h + k) (by omega), hrd w hws k (by omega), mul_val, mul_val, sub_val, mul_val]
      simp only [Tg, Y]
      rw [getD_firstLayer _ _ _ hX, ite_eq_right (by omega), ite_eq_left (by omega),
        getD_scaledCoeffs _ _ _ _ (by omega), getD_scaledCoeffs _ _ _ _ (by omega),
        show h + k - h = k by omega]
  have hg : 4 * (h + 16 * (h / 16)) ≤ (encode c).size ∧
      4 * (h + 16 * (h / 16)) ≤ (encode T).size ∧ 4 * (16 * (h / 16)) ≤ (encode w).size ∧
      (encode c).size < USize.size ∧ (encode T).size < USize.size ∧
      (encode w).size < USize.size := by
    simp only [size_encode_fields]
    omega
  have hU : (USize.ofNatLT h (by omega)).toNat = h := USize.toNat_ofNatLT
  have hall := (Native.fill_pair16ScaledLoop w T c h (2 * h) _ hU hN (le_refl _) (h / 16) 0
    (by rw [hU, USize.toNat_zero]; simpa only [size_encode_fields] using
      (show 4 * (h + 0 + 16 * (h / 16)) ≤ 4 * c.size ∧ 4 * (h + 0 + 16 * (h / 16)) ≤ 4 * T.size ∧
        4 * (0 + 16 * (h / 16)) ≤ 4 * w.size ∧ 4 * c.size < USize.size ∧
        4 * T.size < USize.size ∧ 4 * w.size < USize.size by omega))
    (by rw [USize.toNat_zero]; omega)).comp (Native.Fill.foldl Tg _ (2 * h) _ _ hedge)
  unfold Native.pairsScaled
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, bind_pure,
    Native.zeroWords_eq]
  rw [dite_eq_left_of_eq_true (eq_true hg)]
  refine (hall.eq_ofFn (fun k hk ↦ ?_) _ Array.size_replicate).trans ?_
  · by_cases hk' : k < 16 * (h / 16)
    · exact Or.inl (Or.inl ⟨by rw [USize.toNat_zero]; omega, by rw [USize.toNat_zero]; omega⟩)
    · by_cases hk2 : h ≤ k ∧ k < h + 16 * (h / 16)
      · exact Or.inl (Or.inr ⟨by rw [USize.toNat_zero]; omega, by rw [USize.toNat_zero]; omega⟩)
      · by_cases hk3 : k < h
        · exact Or.inr ⟨k, List.mem_range'_1.mpr (by omega), Or.inl rfl⟩
        · exact Or.inr ⟨k - h, List.mem_range'_1.mpr (by omega), Or.inr (by omega)⟩
  · rw [encode_eq_map_val Y]
    congr 1
    apply Array.ext (by rw [Array.size_ofFn, Array.size_map, hY])
    intro k h1 h2
    rw [Array.getElem_ofFn, Array.getElem_map]
    have hk : k < Y.size := by rw [Array.size_map] at h2; exact h2
    simp only [Y, Array.getD_eq_getD_getElem?] at hk ⊢
    rw [Array.getElem?_eq_getElem hk, Option.getD_some]

/-- An odd leaf in DIF order is its radix-two layer, then `leafReversedOdd`. -/
theorem Native.leafReversed_odd (tw : Array ByteArray) (m : Nat) (hm : m % 2 = 1)
    (a : ByteArray) :
    Native.leafReversed p tw m a = Native.leafReversedOdd p tw m
      (Native.pairs p (tw.getD (m - 1) .empty) (2 ^ (m - 1)) 0 0 (2 ^ (m - 1)) a) := by
  unfold Native.leafReversed Native.leafReversedOdd Native.leafLayers
  simp only [hm, ↓reduceIte]
  split <;> rfl

/-! ### Column transforms -/

/-- The subgroup of order `2 ^ logH`, the domain of the input columns. -/
abbrev LdePlan.low (P : LdePlan p) : NTT.Domain (FastField p) := powDomain P.domain P.bits P.bits_le

/-- Packed columns fit machine indices. -/
theorem LdePlan.byte_bound_low (P : LdePlan p) : 4 * P.low.n < USize.size := by
  have := P.byte_bound
  have : P.low.n ≤ P.domain.n := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  omega

/-- Packed columns fit machine indices, stated for the inverse domain. -/
theorem LdePlan.byte_bound_inverse (P : LdePlan p) : 4 * P.low.inverse.n < USize.size := by
  have := P.byte_bound_low
  have e1 : P.low.inverse.n = 2 ^ P.logH := rfl
  have e2 : P.low.n = 2 ^ P.logH := rfl
  omega

/-- A column's coefficients, scaled by `h`, are its unnormalized inverse transform. -/
theorem Native.columnCoefficients_encode (P : LdePlan p) (col : Array (FastField p))
    (hs : col.size = 2 ^ P.logH) :
    Native.columnCoefficients P (encode col) =
      encode (NTT.Forward.forwardSpec P.low.inverse col) := by
  obtain ⟨htw, hone⟩ := twiddleTable_invariants P.low.inverse
  have h := Native.leafNatural_encode P.low.inverse (Plan.twiddleTable P.low.inverse) col 0 false
    htw hone hs P.byte_bound_inverse
    (by have := P.log_bound; change P.domain.logN - P.bits ≤ 32; omega)
  rw [planStages_eq_difSpec _ _ hs, decodedFields_difSpec] at h
  unfold Native.columnCoefficients
  rw [P.inverse_eq]
  exact h

/-- The coset tables have one entry per row. -/
@[simp] theorem size_cosetTable (D : NTT.Domain (FastField p)) (bits : Nat) (shift : FastField p)
    (c : Nat) :
    (cosetTable D bits shift c).size = 2 ^ (D.logN - bits) := by
  simp only [cosetTable, Array.size_map, NTTFast.powers_eq_ofFn, Array.size_ofFn]

/-- Block `t` of a column's extension is the DIF transform of its coefficients, scaled by coset
table `bitrev t`. -/
theorem Native.cosetBlock_encode (P : LdePlan p) (c : Array (FastField p))
    (hc : c.size = 2 ^ P.logH) (t : Nat) :
    Native.cosetBlock P (encode c) t = encode (difSpec P.low (Array.ofFn (n := 2 ^ P.logH) fun i ↦
      (cosetTable P.domain P.bits P.shift (NTT.Transform.bitRevNat P.bits t)).getD i.val 0 *
        c.getD i.val 0)) := by
  obtain ⟨htw, hone⟩ := twiddleTable_invariants P.low
  have hu := P.byte_bound_low
  have hn : P.low.n = 2 ^ P.logH := rfl
  have hX : (Array.ofFn (n := 2 ^ P.logH) fun i ↦
      (cosetTable P.domain P.bits P.shift (NTT.Transform.bitRevNat P.bits t)).getD i.val 0 *
        c.getD i.val 0).size = P.low.n := Array.size_ofFn
  have hkey : Native.cosetBlock P (encode c) t = Native.leafReversed p P.forwardTwiddles P.logH
      (encode (Array.ofFn (n := 2 ^ P.logH) fun i ↦
        (cosetTable P.domain P.bits P.shift (NTT.Transform.bitRevNat P.bits t)).getD i.val 0 *
          c.getD i.val 0)) := by
    unfold Native.cosetBlock
    dsimp only
    rw [P.tables_eq, getD_map_range _ _ _ (NTT.Transform.bitRevNat_lt _ _)]
    split
    · rename_i hm
      have h2 : 2 ^ P.logH = 2 * 2 ^ (P.logH - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      have hu' : 4 * 2 ^ P.logH < USize.size := hu
      have hw : ((Plan.twiddleTable (powDomain P.domain P.bits P.bits_le)).getD (P.logH - 1)
          #[]).size = 2 ^ (P.logH - 1) :=
        htw (P.logH - 1) (by change P.logH - 1 < P.logH; omega)
      have ht : (cosetTable P.domain P.bits P.shift (NTT.Transform.bitRevNat P.bits t)).size =
          2 ^ P.logH := size_cosetTable _ _ _ _
      have hX' : (Array.ofFn (n := 2 ^ P.logH) fun i ↦
          (cosetTable P.domain P.bits P.shift (NTT.Transform.bitRevNat P.bits t)).getD i.val 0 *
            c.getD i.val 0).size = 2 ^ P.logH := Array.size_ofFn
      rw [Native.leafReversed_odd _ _ hm, P.forward_eq, getD_map_encode,
        Native.pairsScaled_encode _ _ _ _ (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega),
        Native.pairs_encode _ _ _ _ _ _ (by rw [size_encode_fields]; omega)
          (by rw [size_encode_fields]; omega) (by omega) (Nat.zero_le _) (by omega) (by omega)]
      congr 3
      rw [h2]
    · rw [Native.mulWords_encode _ _ _ (by rw [size_cosetTable]) (by rw [hc]) (by
        rw [size_cosetTable]; exact hu) (by rw [hc]; exact hu)]
  rw [hkey, P.forward_eq]
  exact (Native.leafReversed_encode P.low _ _ htw hone hX hu).trans
    (congrArg encode (planStages_eq_difSpec _ _ hX))

/-! ### Values on the coset -/

/-- Coset table `c` holds `(1 / h) · (shift · ω ^ c) ^ l`. -/
theorem getD_cosetTable (D : NTT.Domain (FastField p)) (bits : Nat) (shift : FastField p)
    (c l : Nat)
    (hl : l < 2 ^ (D.logN - bits)) :
    (cosetTable D bits shift c).getD l 0 =
      ((2 ^ (D.logN - bits) : Nat) : FastField p)⁻¹ * (shift * D.omega ^ c) ^ l := by
  rw [Array.getD_eq_getD_getElem?, cosetTable, Array.getElem?_map, NTTFast.powers_eq_ofFn,
    Array.getElem?_ofFn, dite_eq_left_of_eq_true (eq_true hl)]
  rfl

/-- Entry `i` of block `t` of a column's extension is the column's interpolant on the subgroup
of order `h` at `shift · ω ^ bitrev (h t + i)`. -/
theorem getD_block (P : LdePlan p) (col : Vector (FastField p) (2 ^ P.logH)) (t i : Nat)
    (hi : i < 2 ^ P.logH) :
    (difSpec P.low (Array.ofFn (n := 2 ^ P.logH) fun l ↦
      (cosetTable P.domain P.bits P.shift (NTT.Transform.bitRevNat P.bits t)).getD l.val 0 *
        (NTT.Forward.forwardSpec P.low.inverse col.toArray).getD l.val 0)).getD i 0 =
      (CPolynomial.CLagrange.interpolatePow (P.domain.omega ^ 2 ^ P.bits) col).eval
        (P.shift * P.domain.omega ^
          NTT.Transform.bitRevNat P.domain.logN (2 ^ P.logH * t + i)) := by
  let h := 2 ^ P.logH
  let c := NTT.Transform.bitRevNat P.bits t
  let b := NTT.Transform.bitRevNat P.logH i
  let ω := P.domain.omega
  let coef := NTT.Forward.forwardSpec P.low.inverse col.toArray
  have hlog : P.domain.logN = P.bits + P.logH := by
    have := P.bits_le; simp only [LdePlan.logH]; omega
  have hrev : NTT.Transform.bitRevNat P.domain.logN (2 ^ P.logH * t + i) = 2 ^ P.bits * b + c := by
    rw [hlog]; exact bitRevNat_concat P.bits P.logH t i hi
  -- The interpolant's coefficients are the normalized inverse transform.
  have hq (x : FastField p) :
      (CPolynomial.CLagrange.interpolatePow (P.domain.omega ^ 2 ^ P.bits) col).eval x =
      CPolynomial.Raw.eval x (NTT.Inverse.inverseSpec P.low col.toArray) := by
    have he := NTT.Inverse.inverseSpec_interpolatePow_eq P.low col.toArray
    have hl : NTT.loadNaturalVector P.low col.toArray = col :=
      NTT.loadNaturalVector_toArray P.low col
    rw [hl] at he
    have he' : CPolynomial.Raw.trim (NTT.Inverse.inverseSpec P.low col.toArray) =
        (CPolynomial.CLagrange.interpolatePow (P.domain.omega ^ 2 ^ P.bits) col).val := he
    rw [CPolynomial.eval_toPoly, ← CPolynomial.Raw.eval_toPoly_eq_eval,
      ← CPolynomial.Raw.toPoly_trim, he']
    rfl
  have hcoef (l : Nat) (hl : l < h) :
      (NTT.Inverse.inverseSpec P.low col.toArray).getD l 0 =
    (h : FastField p)⁻¹ * coef.getD l 0 := by
    rw [← NTT.Inverse.normalize_forwardSpec_inverse_eq_inverseSpec, NTT.Inverse.normalize,
      getD_ofFn_bounded _ _ (show l < P.low.n from hl)]
    rfl
  rw [hq, NTT.Coset.eval_eq_sum_fin _ P.low.n
      (NTT.Coset.natDegree_lt_of_size_le _ (Nat.two_pow_pos _)
        (by rw [NTT.Inverse.size_inverseSpec])),
    getD_difSpec _ _ _ hi, dftValue, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro l _
  have hl : l.val < 2 ^ P.logH := l.isLt
  rw [getD_ofFn_bounded _ _ hl, getD_cosetTable _ _ _ _ _ hl, hcoef l hl, hrev]
  change (h : FastField p)⁻¹ * (P.shift * ω ^ c) ^ l.val * coef.getD l 0 *
      (ω ^ 2 ^ P.bits) ^ (b * l.val) =
    (h : FastField p)⁻¹ * coef.getD l 0 * (P.shift * ω ^ (2 ^ P.bits * b + c)) ^ l.val
  rw [pow_add, pow_mul, pow_mul]
  ring

/-! ### Specification -/

/-- Column `j` of a row-major matrix of width `w` with `h` rows. -/
def column (M : Array (FastField p)) (w h j : Nat) : Vector (FastField p) h :=
  Vector.ofFn fun i ↦ M.getD (i.val * w + j) 0

/-- The low-degree extension of a row-major matrix `M` of width `w` in commitment order: entry
`(r, j)` is column `j`'s interpolant on the subgroup of order `h = 2 ^ logH` at
`shift · ω ^ bitrev r`, where `ω` generates the subgroup of order `2 ^ logN`. -/
def ldeSpec (P : LdePlan p) (w : Nat) (M : Array (FastField p)) : Array (FastField p) :=
  Array.ofFn (n := 2 ^ P.domain.logN * w) fun k ↦
    (CPolynomial.CLagrange.interpolatePow (P.domain.omega ^ 2 ^ P.bits)
      (column M w (2 ^ P.logH) (k.val % w))).eval
        (P.shift * P.domain.omega ^ NTT.Transform.bitRevNat P.domain.logN (k.val / w))

/-! ### Assembly -/

/-- A grid of tasks in row order. -/
theorem flatMap_range_map {α : Type*} (a b : Nat) (f : Nat → Nat → α) :
    (Array.range a).flatMap (fun t ↦ (Array.range b).map (f t)) =
      (Array.range (a * b)).map fun c ↦ f (c / b) (c % b) := by
  apply Array.toList_inj.mp
  simp only [Array.toList_flatMap, Array.toList_range, Array.toList_map]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add, List.map_append,
      List.map_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    congr 1
    apply List.map_congr_left
    intro x hx
    have hx := List.mem_range.mp hx
    simp only [Function.comp_apply]
    rw [(Native.divMod_add a x b hx).1, (Native.divMod_add a x b hx).2]

/-- Joining consecutive ranges of an array packs the array. -/
theorem joinRows_extract (S : Array (FastField p)) (K L : Nat) (hS : S.size = K * L) :
    Native.joinRows ((Array.range K).map fun c ↦ encode (S.extract (c * L) (c * L + L))) =
      encode S := by
  unfold Native.joinRows
  rw [show ByteArray.emptyWithCapacity _ = encode (#[] : Array (FastField p)) from rfl,
    Array.foldl_map,
    ← Array.foldl_toList, Array.toList_range]
  have h (K : Nat) (hK : K * L ≤ S.size) : (List.range K).foldl
      (fun acc c ↦ acc ++ encode (S.extract (c * L) (c * L + L))) (encode (#[] : Array
    (FastField p))) =
      encode (S.extract 0 (K * L)) := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [List.range_succ, List.foldl_append, ih (by rw [Nat.succ_mul] at hK; omega),
        List.foldl_cons, List.foldl_nil, ← PackedRepr.encode_append, Array.extract_append_extract,
        Nat.min_eq_left (Nat.zero_le _), Nat.max_eq_right (by omega), Nat.succ_mul]
  rw [h K (by omega), ← hS, Array.extract_size]

/-- A power of two split into `2 ^ min k a` equal parts. -/
theorem pow_div_mul_pow_min (a k : Nat) : 2 ^ a / 2 ^ min k a * 2 ^ min k a = 2 ^ a :=
  Nat.div_mul_cancel (Nat.pow_dvd_pow 2 (Nat.min_le_right k a))

/-- Column `j` from the transposed row ranges of a packed matrix. -/
theorem Native.gatherColumn_eq_column (M : Array (FastField p)) (w h R rows j : Nat) (hj : j < w)
    (hR : R * rows = h) (hM : M.size = h * w) (hs : 4 * M.size < USize.size) :
    Native.gatherColumn ((Array.range R).map fun k ↦
      Native.transposeRows (encode M) w (k * rows) rows) rows j =
      encode (column M w h j).toArray := by
  rw [encode_eq_map_val M, Native.gatherColumn_transposeRows _ w R rows j hj
    (by rw [hR, Array.size_map, hM]) (by rw [Array.size_map]; exact hs), encode_eq_map_val]
  congr 1
  apply Array.ext (by simp only [Array.size_ofFn, Array.size_map, column, Vector.toArray_ofFn, hR])
  intro i h1 h2
  simp only [Array.getElem_ofFn, Array.getElem_map, column, Vector.toArray_ofFn, getD_map_val]

/-- Entry `i` of a slice is entry `a + i` of the array, inside the slice. -/
theorem getD_extract_map_val (M : Array (FastField p)) (a b i : Nat) (hb : b ≤ M.size)
    (hi : a + i < b) :
    ((M.extract a b).map Subtype.val).getD i 0 = (M.map Subtype.val).getD (a + i) 0 := by
  rw [getD_map_val, getD_map_val]
  have h1 : i < (M.extract a b).size := by rw [Array.size_extract]; omega
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem (show a + i < M.size by omega), Option.getD_some,
    Array.getElem_extract]

/-- The split of `2 ^ k` input chunks into `2 ^ k · q` row ranges of `rows` rows: `2 ^ r` ranges
for `r = max k (min 4 logH)`. -/
theorem rangesPerChunk_spec (logH k : Nat) (hk : k ≤ logH) :
    0 < Native.rangesPerChunk logH (2 ^ k) ∧
      2 ^ k * Native.rangesPerChunk logH (2 ^ k) *
        (2 ^ logH / (2 ^ k * Native.rangesPerChunk logH (2 ^ k))) = 2 ^ logH ∧
      Native.rangesPerChunk logH (2 ^ k) *
        (2 ^ logH / (2 ^ k * Native.rangesPerChunk logH (2 ^ k))) = 2 ^ (logH - k) := by
  unfold Native.rangesPerChunk Native.rangeCount
  by_cases h : k ≤ min 4 logH
  · rw [Nat.pow_div h (by decide), Nat.max_eq_right (Nat.one_le_two_pow), ← Nat.pow_add,
      Nat.add_sub_cancel' h, Nat.pow_div (Nat.min_le_right _ _) (by decide), ← Nat.pow_add,
      ← Nat.pow_add]
    refine ⟨Nat.two_pow_pos _, by congr 1; omega, by congr 1; omega⟩
  · rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega)), Nat.max_eq_left
      (Nat.zero_le _), Nat.mul_one, Nat.one_mul, Nat.pow_div hk (by decide), ← Nat.pow_add]
    exact ⟨Nat.one_pos, by congr 1; omega, rfl⟩

/-- A row range of a chunk transposes as the same rows of the whole matrix. -/
theorem Native.transposeRows_rowChunks (M : Array (FastField p)) (w logH k q rows : Nat)
    (hM : M.size = 2 ^ logH * w) (hk : k ≤ logH) (hq0 : 0 < q)
    (hq : q * rows = 2 ^ (logH - k)) (hs : 4 * M.size < USize.size) (j : Nat)
    (hj : j < 2 ^ k * q) :
    Native.transposeRows ((Native.rowChunks M w logH k).getD (j / q) .empty) w (j % q * rows)
      rows = Native.transposeRows (encode M) w (j * rows) rows := by
  have hc : j / q < 2 ^ k := (Nat.div_lt_iff_lt_mul hq0).mpr hj
  have hkL : 2 ^ k * 2 ^ (logH - k) = 2 ^ logH := by rw [← Nat.pow_add]; congr 1; omega
  have hjq := Nat.div_add_mod j q
  have hsq : j % q < q := Nat.mod_lt _ hq0
  -- Row `j * rows` of the matrix is row `j % q * rows` of chunk `j / q`.
  have e : j * rows = j / q * 2 ^ (logH - k) + j % q * rows := by
    rw [← hq]
    conv_lhs => rw [← hjq]
    ring
  have hsr : j % q * rows + rows ≤ 2 ^ (logH - k) := by
    have := Nat.mul_le_mul_right rows (show j % q + 1 ≤ q by omega)
    rw [Nat.succ_mul, hq] at this; exact this
  have hcL : (j / q + 1) * 2 ^ (logH - k) ≤ 2 ^ logH := by
    rw [← hkL]; exact Nat.mul_le_mul_right _ hc
  have hcLw : j / q * (2 ^ (logH - k) * w) + 2 ^ (logH - k) * w ≤ M.size := by
    rw [hM]
    have := Nat.mul_le_mul_right w hcL
    rw [Nat.succ_mul] at this
    calc _ = (j / q * 2 ^ (logH - k) + 2 ^ (logH - k)) * w := by ring
      _ ≤ _ := this
  have hrowM : (j * rows + rows) * w ≤ M.size := by
    rw [hM, e]
    have := Nat.mul_le_mul_right w (show j / q * 2 ^ (logH - k) + j % q * rows + rows ≤
      2 ^ logH by rw [Nat.succ_mul] at hcL; omega)
    exact this
  have hrow : (j % q * rows + rows) * w ≤ 2 ^ (logH - k) * w := Nat.mul_le_mul_right w hsr
  simp only [Native.rowChunks]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  simp only [hc, ↓reduceIte, Option.map_some, Option.getD_some]
  rw [encode_eq_map_val, encode_eq_map_val M,
    Native.transposeRows_encodeWords _ w _ rows (by
      rw [Array.size_map, Array.size_extract]; omega)
      (by rw [Array.size_map, Array.size_extract]; omega),
    Native.transposeRows_encodeWords _ w _ rows (by rw [Array.size_map]; exact hrowM)
      (by rw [Array.size_map]; exact hs)]
  congr 1
  apply Array.ext (by simp only [Array.size_ofFn])
  intro i h1 _
  simp only [Array.size_ofFn] at h1
  simp only [Array.getElem_ofFn]
  have hrows : 0 < rows := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
  have hw : i / rows < w := (Nat.div_lt_iff_lt_mul hrows).mpr h1
  have hr := Nat.mod_lt i hrows
  have hin : (j % q * rows + i % rows) * w + i / rows < 2 ^ (logH - k) * w := by
    have := Nat.mul_le_mul_right w (show j % q * rows + i % rows + 1 ≤ 2 ^ (logH - k) by
      omega)
    rw [Nat.succ_mul] at this; omega
  rw [getD_extract_map_val M _ _ _ hcLw (by omega), e]
  congr 1
  ring

/-- The extension of a packed row-major matrix `M` of width `w`, given in `2 ^ k` chunks of rows,
is the packed specification, in row chunks: chunk `c` holds rows `c · L, …` with
`L = 2 ^ logH / chunkCount logH`. -/
theorem Native.cosetLde_eq (P : LdePlan p) (w : Nat) (M : Array (FastField p)) (k : Nat)
    (hk : k ≤ P.logH) (hM : M.size = 2 ^ P.logH * w)
    (hu : 4 * (2 ^ P.domain.logN * w) < USize.size) :
    Native.cosetLde P w (Native.rowChunks M w P.logH k) =
      (Array.range (2 ^ P.bits * Native.chunkCount P.logH)).map fun c ↦
        encode ((ldeSpec P w M).extract (c * (2 ^ P.logH / Native.chunkCount P.logH * w))
          (c * (2 ^ P.logH / Native.chunkCount P.logH * w) +
            2 ^ P.logH / Native.chunkCount P.logH * w)) := by
  have hlog : P.domain.logN = P.bits + P.logH := by
    have := P.bits_le; simp only [LdePlan.logH]; omega
  have hHN : 2 ^ P.logH * w ≤ 2 ^ P.domain.logN * w :=
    Nat.mul_le_mul_right w (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  have hHu : 4 * 2 ^ P.logH < USize.size := by
    have := P.byte_bound_low; exact this
  have hMs : 4 * M.size < USize.size := by omega
  let q := Native.rangesPerChunk P.logH (2 ^ k)
  let R := 2 ^ k * q
  let rows := 2 ^ P.logH / R
  obtain ⟨hq0, hR, hq⟩ := rangesPerChunk_spec P.logH k hk
  have hpieces : (Array.range R).map (fun j ↦ Native.transposeRows
      ((Native.rowChunks M w P.logH k).getD (j / q) .empty) w (j % q * rows) rows) =
      (Array.range R).map fun j ↦ Native.transposeRows (encode M) w (j * rows) rows := by
    apply Array.ext (by simp only [Array.size_map])
    intro j h1 _
    simp only [Array.size_map, Array.size_range] at h1
    simp only [Array.getElem_map, Array.getElem_range]
    exact Native.transposeRows_rowChunks M w P.logH k q rows hM hk hq0 hq hMs j h1
  let C := Native.chunkCount P.logH
  let rows' := 2 ^ P.logH / C
  have hC : rows' * C = 2 ^ P.logH := pow_div_mul_pow_min P.logH 3
  have hC0 : 0 < C := Nat.two_pow_pos _
  have hrows' : rows' < 512 ∨ 512 ∣ rows' := by
    have he : rows' = 2 ^ (P.logH - min 3 P.logH) := by
      simp only [rows', C, Native.chunkCount]; rw [Nat.pow_div (Nat.min_le_right _ _) (by decide)]
    rw [he]
    by_cases h9 : 9 ≤ P.logH - min 3 P.logH
    · exact Or.inr (by simpa using Nat.pow_dvd_pow 2 h9)
    · exact Or.inl (by
        have := Nat.pow_lt_pow_right (show 1 < 2 by decide)
          (show P.logH - min 3 P.logH < 9 by omega)
        simpa using this)
  -- Block `t` of column `j`, as field coordinates.
  let B (t j : Nat) : Array (FastField p) := difSpec P.low (Array.ofFn (n := 2 ^ P.logH) fun l ↦
    (cosetTable P.domain P.bits P.shift (NTT.Transform.bitRevNat P.bits t)).getD l.val 0 *
      (NTT.Forward.forwardSpec P.low.inverse (column M w (2 ^ P.logH) j).toArray).getD l.val 0)
  have hB (t j : Nat) : (B t j).size = 2 ^ P.logH := size_difSpec _ _
  have hblock (t : Nat) : (Array.range w).map (fun j ↦ Native.cosetBlock P
      (Native.columnCoefficients P (Native.gatherColumn ((Array.range R).map fun k ↦
        Native.transposeRows (encode M) w (k * rows) rows) rows j)) t) =
      ((Array.range w).map fun j ↦ (B t j).map Subtype.val).map encode := by
    rw [Array.map_map]
    apply Array.ext (by simp only [Array.size_map])
    intro j h1 _
    simp only [Array.size_map, Array.size_range] at h1
    simp only [Array.getElem_map, Array.getElem_range, Function.comp_apply]
    rw [Native.gatherColumn_eq_column M w _ R rows j h1 hR hM hMs,
      Native.columnCoefficients_encode P _ (by simp only [Vector.size_toArray]),
      Native.cosetBlock_encode P _ (by rw [NTT.Forward.forwardSpec, Array.size_ofFn]; rfl),
      encode_eq_map_val]
  unfold Native.cosetLde
  simp only [Array.map_flatMap, Array.map_map, Function.comp_def, Tasks.get_bind, Tasks.get_spawn,
    Tasks.get_join, Tasks.map_get_spawnAll, Native.rowChunks, Array.size_map, Array.size_range]
  rw [← Native.rowChunks, hpieces, flatMap_range_map]
  apply Array.ext (by simp only [Array.size_map])
  intro c h1 _
  simp only [Array.size_map, Array.size_range] at h1
  simp only [Array.getElem_map, Array.getElem_range]
  have hcb : c + 1 ≤ 2 ^ P.bits * C := h1
  have hk : c % C < C := Nat.mod_lt _ hC0
  have hrk : (c % C) * rows' + rows' ≤ 2 ^ P.logH := by
    have := Nat.mul_le_mul_right rows' (show c % C + 1 ≤ C by omega)
    rw [Nat.succ_mul, Nat.mul_comm C] at this; omega
  have hrw : 4 * (rows' * w) < USize.size := by
    have := Nat.mul_le_mul_right w (show rows' ≤ 2 ^ P.logH by
      have := Nat.mul_le_mul_left rows' (show 1 ≤ C by omega); rw [hC] at this; omega)
    omega
  rw [hblock (c / C), Native.rowsOfColumns_encodeWords _ _ _ (fun j hj ↦ by
      simp only [Array.size_map, Array.size_range] at hj
      rw [getD_map_range _ _ _ hj, Array.size_map, hB]
      exact ⟨hrk, hHu⟩) (by simpa only [Array.size_map, Array.size_range] using hrw) hrows',
    encode_eq_map_val]
  congr 1
  have hW : (Array.map (fun j ↦ Array.map Subtype.val (B (c / C) j)) (Array.range w)).size = w := by
    simp only [Array.size_map, Array.size_range]
  have hcC : c * rows' = 2 ^ P.logH * (c / C) + c % C * rows' := by
    have := Nat.div_add_mod c C
    rw [← hC]
    nth_rewrite 1 [← this]
    ring
  have hL : c * (rows' * w) + rows' * w ≤ 2 ^ P.domain.logN * w := by
    have h1 : (c + 1) * rows' ≤ 2 ^ P.bits * C * rows' := Nat.mul_le_mul_right _ hcb
    have h2 : 2 ^ P.bits * C * rows' = 2 ^ P.domain.logN := by
      rw [Nat.mul_assoc, Nat.mul_comm C, hC, hlog, Nat.pow_add]
    have h3 := Nat.mul_le_mul_right w (h1.trans h2.le)
    have e : (c + 1) * rows' * w = c * (rows' * w) + rows' * w := by ring
    omega
  have hL' : c * (2 ^ P.logH / Native.chunkCount P.logH * w) +
      2 ^ P.logH / Native.chunkCount P.logH * w ≤ 2 ^ P.domain.logN * w := hL
  apply Array.ext (by
    simp only [Array.size_ofFn, Array.size_map, Array.size_extract, ldeSpec, hW]
    have : rows' * w = 2 ^ P.logH / Native.chunkCount P.logH * w := rfl
    omega)
  intro idx h1 _
  simp only [Array.size_ofFn, hW] at h1
  have hw0 : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
  have hq : idx / w < rows' := (Nat.div_lt_iff_lt_mul hw0).mpr h1
  have he : c * (rows' * w) + idx = w * (c * rows') + idx := by ring
  have hdiv : (c * (rows' * w) + idx) / w = c * rows' + idx / w := by
    rw [he, Nat.mul_add_div hw0]
  have hmod : (c * (rows' * w) + idx) % w = idx % w := by
    rw [he, Nat.mul_add_mod]
  have hi : c % C * rows' + idx / w < 2 ^ P.logH := by omega
  rw [Array.getElem_ofFn, Array.getElem_map, Array.getElem_extract]
  simp only [hW]
  rw [getD_map_range _ _ _ (Nat.mod_lt _ hw0), getD_map_val, getD_block P _ _ _ hi]
  simp only [ldeSpec, Array.getElem_ofFn]
  rw [hdiv, hmod, hcC, Nat.add_assoc]

/-- **The batched coset LDE is correct.** Joined, the row chunks of the extension of a packed
row-major matrix `M` of width `w` and `2 ^ logH` rows, given in `2 ^ k` chunks of rows, are the
packed specification: row `r` holds
every column's interpolant on the subgroup of order `2 ^ logH`, evaluated at
`shift · ω ^ bitrev r`. -/
theorem Native.joinRows_cosetLde (P : LdePlan p) (w : Nat) (M : Array (FastField p)) (k : Nat)
    (hk : k ≤ P.logH) (hM : M.size = 2 ^ P.logH * w)
    (hu : 4 * (2 ^ P.domain.logN * w) < USize.size) :
    Native.joinRows (Native.cosetLde P w (Native.rowChunks M w P.logH k)) =
      encode (ldeSpec P w M) := by
  rw [Native.cosetLde_eq P w M k hk hM hu]
  apply joinRows_extract
  have hlog : P.domain.logN = P.bits + P.logH := by
    have := P.bits_le; simp only [LdePlan.logH]; omega
  have hC := pow_div_mul_pow_min P.logH 3
  simp only [ldeSpec, Array.size_ofFn, hlog, Nat.pow_add]
  unfold Native.chunkCount
  generalize 2 ^ P.logH / 2 ^ min 3 P.logH = q at hC ⊢
  rw [← hC]
  ring

/-- `Native.joinRows_cosetLde` for the compiled extension. -/
theorem LdePlan.joinRows_cosetLde [PackedCosetLde p] (P : LdePlan p) (w : Nat)
    (M : Array (FastField p)) (k : Nat) (hk : k ≤ P.logH) (hM : M.size = 2 ^ P.logH * w)
    (hu : 4 * (2 ^ P.domain.logN * w) < USize.size) :
    Native.joinRows (P.cosetLde w (Native.rowChunks M w P.logH k)) = encode (ldeSpec P w M) := by
  rw [LdePlan.cosetLde, PackedCosetLde.run_eq]
  exact Native.joinRows_cosetLde P w M k hk hM hu

end CompPoly.CPolynomial.NTTFast.Packed
