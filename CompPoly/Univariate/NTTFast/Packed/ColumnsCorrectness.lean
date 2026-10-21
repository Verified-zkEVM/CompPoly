/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Packed.Columns
public import CompPoly.Univariate.NTTFast.Packed.Columns
public import CompPoly.Univariate.NTTFast.Packed.NativeLastCorrectness
public import CompPoly.Univariate.NTTFast.Packed.DifSpec
public import CompPoly.Univariate.NTTFast.NaturalParallel
import all CompPoly.Univariate.NTTFast.Columns
import Mathlib.Tactic.Ring

/-! # Correctness of the packed column-parallel transform

Every stage of `runColumns` packs a stage of the field-level column transform: column tasks
pack `Columns.columnTask`, a leaf's words pack its block of the top two passes, and a leaf task
packs the natural-order read of that block of the DIF transform. The interleave then packs the
natural-order DFT.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open Montgomery.Native32 (Mont32Field FastField)

variable {p : ℕ} [Mont32Field p]

open CompPoly.PackedRepr (encode)

local notation "F" => FastField p

/-- Appending a range of a packed field array copies its coordinates. -/
theorem copySlice_encode_fields (a o : Array F) (i c : Nat) :
    (encode a).copySlice (4 * i) (encode o) (encode o).size (4 * c) =
      encode (o ++ a.extract i (i + c)) :=
  PackedRepr.copySlice_encode a o i c

/-- A fold of slot-range copies packs the fold of the element ranges. -/
theorem foldl_copySlice_encode {ι : Type*} (f : ι → Array F) (g : ι → Nat) (cs : Nat)
    (L : List ι) (o : Array F) :
    L.foldl (fun out k ↦ (encode (f k)).copySlice (4 * g k) out out.size (4 * cs)) (encode o) =
      encode (L.foldl (fun acc k ↦ acc ++ (f k).extract (g k) (g k + cs)) o) := by
  induction L generalizing o with
  | nil => rfl
  | cons k L ih =>
    simp only [List.foldl_cons]
    rw [copySlice_encode_fields]
    exact ih _

/-- Appended ranges of `cs` entries form a row-major matrix. -/
theorem appendRows_spec (f : Nat → Array F) (g : Nat → Nat) (cs r : Nat)
    (h : ∀ k < r, g k + cs ≤ (f k).size) :
    ((List.range r).foldl (fun acc k ↦ acc ++ (f k).extract (g k) (g k + cs)) #[]).size =
        r * cs ∧
      ∀ k < r, ∀ c < cs,
        ((List.range r).foldl (fun acc k ↦ acc ++ (f k).extract (g k) (g k + cs)) #[]).getD
          (k * cs + c) 0 = (f k).getD (g k + c) 0 := by
  induction r with
  | zero => simp only [List.range_zero, List.foldl_nil, Array.size_empty, Nat.zero_mul,
      Nat.not_lt_zero, false_imp_iff, implies_true, and_self]
  | succ r ih =>
    obtain ⟨hs, hv⟩ := ih fun k hk ↦ h k (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have he : (Array.extract (f r) (g r) (g r + cs)).size = cs := by
      have := h r (by omega)
      rw [Array.size_extract]; omega
    refine ⟨by rw [Array.size_append, hs, he, Nat.succ_mul], fun k hk c hc ↦ ?_⟩
    simp only [Array.getD_eq_getD_getElem?]
    by_cases hkr : k < r
    · have hlt : k * cs + c < r * cs := by
        have := Nat.mul_le_mul_right cs (show k + 1 ≤ r by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      rw [Array.getElem?_append_left (by rw [hs]; exact hlt)]
      have := hv k hkr c hc
      simpa only [Array.getD_eq_getD_getElem?] using this
    · have hkr' : k = r := by omega
      subst hkr'
      rw [Array.getElem?_append_right (by rw [hs]; omega), hs,
        show k * cs + c - k * cs = c by omega]
      have := getD_extract (f k) (g k) cs c 0 (h k hk) hc
      simpa only [Array.getD_eq_getD_getElem?] using this

namespace Native

/-- Gathered words pack the gathered rows. -/
theorem gatherWords_encode (src : Array F) (M j0 cs r : Nat)
    (hsrc : ∀ k < r, k * M + j0 + cs ≤ src.size)
    (hu : src.size < USize.size ∧ r * cs < USize.size) :
    gatherWords (encode src) M j0 cs r = encode (Columns.gatherRows src M j0 cs r) := by
  unfold gatherWords
  rw [show ByteArray.emptyWithCapacity (4 * (r * cs)) = encode (#[] : Array F) from rfl,
    foldl_copySlice_encode (fun _ ↦ src) (fun k ↦ k * M + j0) cs _ _]
  obtain ⟨has, hav⟩ := appendRows_spec (fun _ ↦ src) (fun k ↦ k * M + j0) cs r hsrc
  obtain ⟨hgs, hgv⟩ := Columns.gatherRows_spec src M j0 cs r hsrc hu
  congr 1
  apply array_eq_of_getD _ _ 0 (by rw [has, hgs])
  intro i
  by_cases hi : i < r * cs
  · have hcs : 0 < cs := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
    have hk : i / cs < r := by rw [Nat.div_lt_iff_lt_mul hcs]; exact hi
    rw [← Nat.div_add_mod' i cs, hav _ hk _ (Nat.mod_lt _ hcs), hgv _ hk _ (Nat.mod_lt _ hcs),
      Nat.add_assoc]
  · rw [Columns.getD_of_size_le _ _ (by omega), Columns.getD_of_size_le _ _ (by omega)]

/-- A packed column task packs the field-level column task. -/
theorem columnWords_encode (x : Array F) (tw : Array (Array F)) (logN cs j0 : Nat)
    (h4 : 4 ≤ logN) (hx : x.size = 2 ^ logN) (htw : ∀ s < logN, (tw.getD s #[]).size = 2 ^ s)
    (hu : 4 * 2 ^ logN < USize.size) (hj : j0 + cs ≤ 2 ^ (logN - 4)) :
    columnWords p (tw.map encode) logN (2 ^ (logN - 4)) cs j0 (encode x) =
      encode (Columns.columnTask x tw logN (2 ^ (logN - 4)) cs j0) := by
  obtain ⟨m, rfl⟩ : ∃ m, logN = m + 4 := ⟨logN - 4, by omega⟩
  simp only [show m + 4 - 4 = m by omega] at hj ⊢
  have hp (k : Nat) : 2 ^ (m + k) = 2 ^ k * 2 ^ m := by rw [Nat.pow_add, Nat.mul_comm]
  have hM := Nat.two_pow_pos m
  have hx' : x.size = 16 * 2 ^ m := by rw [hx, hp 4]; rfl
  have hu' : 4 * (16 * 2 ^ m) < USize.size := by rw [hp 4] at hu; exact hu
  have hrow (s k : Nat) (hs : s < m + 4) (hk : 2 ^ s = k * 2 ^ m) :
      ∀ r < k, r * 2 ^ m + j0 + cs ≤ (tw.getD s #[]).size := by
    intro r hr
    rw [htw s hs, hk]
    have := Nat.mul_le_mul_right (2 ^ m) (show r + 1 ≤ k by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have hts (s k : Nat) (hs : s < m + 4) (hk : 2 ^ s = k * 2 ^ m) (hk16 : k ≤ 16) :
      (tw.getD s #[]).size = k * 2 ^ m ∧ (tw.getD s #[]).size < USize.size := by
    rw [htw s hs, hk]
    exact ⟨rfl, by have := Nat.mul_le_mul_right (2 ^ m) hk16; omega⟩
  have hcs16 (k : Nat) (hk : k ≤ 16) : 4 * (k * cs) < USize.size := by
    have := Nat.mul_le_mul_right cs hk
    have : 16 * cs ≤ 16 * 2 ^ m := by omega
    omega
  have hg (s k : Nat) (hs : s < m + 4) (hk : 2 ^ s = k * 2 ^ m) (hk16 : k ≤ 16) :=
    gatherWords_encode (tw.getD s #[]) (2 ^ m) j0 cs k (hrow s k hs hk)
      ⟨(hts s k hs hk hk16).2, by have := hcs16 k hk16; omega⟩
  have hgs (s k : Nat) (hs : s < m + 4) (hk : 2 ^ s = k * 2 ^ m) (hk16 : k ≤ 16) :=
    (Columns.gatherRows_spec (tw.getD s #[]) (2 ^ m) j0 cs k (hrow s k hs hk)
      ⟨(hts s k hs hk hk16).2, by have := hcs16 k hk16; omega⟩).1
  have e1 : 2 ^ (m + 4 - 1) = 8 * 2 ^ m := by rw [show m + 4 - 1 = m + 3 by omega, hp]; rfl
  have e2 : 2 ^ (m + 4 - 2) = 4 * 2 ^ m := by rw [show m + 4 - 2 = m + 2 by omega, hp]; rfl
  have e3 : 2 ^ (m + 4 - 3) = 2 * 2 ^ m := by rw [show m + 4 - 3 = m + 1 by omega, hp]; rfl
  have e4 : 2 ^ (m + 4 - 4) = 1 * 2 ^ m := by rw [show m + 4 - 4 = m by omega, Nat.one_mul]
  have hxr : ∀ r < 16, r * 2 ^ m + j0 + cs ≤ x.size := fun r hr ↦ by
    have := Nat.mul_le_mul_right (2 ^ m) (show r + 1 ≤ 16 by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have hxu : x.size < USize.size ∧ 16 * cs < USize.size := ⟨by omega, by have := hcs16 16; omega⟩
  obtain ⟨hxs, -⟩ := Columns.gatherRows_spec x (2 ^ m) j0 cs 16 hxr hxu
  unfold columnWords Columns.columnTask Columns.columnPasses
  simp only [getD_map_encode]
  rw [hg _ 8 (by omega) e1 (by omega), hg _ 4 (by omega) e2 (by omega),
    hg _ 2 (by omega) e3 (by omega), hg _ 1 (by omega) e4 (by omega),
    gatherWords_encode x (2 ^ m) j0 cs 16 hxr hxu]
  have hfs (a : Array F) (ha : a.size = 16 * cs) : (encode a).size < USize.size := by
    rw [size_encode_fields, ha]; exact hcs16 16 (by omega)
  have hrs (s k : Nat) (hs : s < m + 4) (hk : 2 ^ s = k * 2 ^ m) (hk16 : k ≤ 16) :
      (encode (Columns.gatherRows (tw.getD s #[]) (2 ^ m) j0 cs k)).size < USize.size := by
    rw [size_encode_fields, hgs s k hs hk hk16]; exact hcs16 k hk16
  rw [Native.radix4Blocks_encode _ _ _ _ _ (hfs _ hxs) (hrs _ 8 (by omega) e1 (by omega))
      (hrs _ 4 (by omega) e2 (by omega)) (by rw [hgs _ 8 (by omega) e1 (by omega)]; omega)
      (hgs _ 4 (by omega) e2 (by omega)).ge (by rw [hxs]; omega),
    Native.radix4Blocks_encode _ _ _ _ _ (hfs _ (by rw [Plan.size_butterflyDIFRadix4Blocks, hxs]))
      (hrs _ 2 (by omega) e3 (by omega)) (hrs _ 1 (by omega) e4 (by omega))
      (hgs _ 2 (by omega) e3 (by omega)).ge
      (by rw [hgs _ 1 (by omega) e4 (by omega)]; omega)
      (by rw [Plan.size_butterflyDIFRadix4Blocks, hxs]; omega)]
  simp only [Plan.stageBlocksDIF_eq, Plan.checkedBlocks_eq, show 4 * (4 * cs) = 16 * cs by ring]

/-- A leaf's words pack the concatenated row ranges of the column results. -/
theorem leafWords_encode (C : Nat → Array F) (S cs l : Nat) :
    leafWords ((Array.range S).map fun s ↦ encode (C s)) cs l =
      encode ((List.range S).foldl (fun acc s ↦ acc ++ (C s).extract (l * cs) (l * cs + cs))
        #[]) := by
  unfold leafWords
  rw [Array.foldl_map, ← Array.foldl_toList, Array.toList_range, Array.size_map, Array.size_range,
    show ByteArray.emptyWithCapacity (4 * (S * cs)) = encode (#[] : Array F) from rfl]
  exact foldl_copySlice_encode C (fun _ ↦ l * cs) cs _ _

/-- A leaf's DIF stages are the column transform's leaf layers. -/
theorem leafStages_eq_leafPasses (D : NTT.Domain F) (h4 : 4 ≤ D.logN) (tw : Array (Array F))
    (X : Array F) (hX : X.size = 2 ^ (D.logN - 4)) :
    Plan.runStagesDIFRadix4WithTwiddles (powDomain D 4 h4) tw X =
      Columns.leafPasses tw ((Parallel.forwardPasses D).drop 2) (D.logN % 2 == 1) X := by
  let D4 := powDomain D 4 h4
  have hp : Parallel.forwardPasses D4 = (Parallel.forwardPasses D).drop 2 := by
    unfold Parallel.forwardPasses
    apply List.ext_getElem (by
      simp only [D4, powDomain, List.length_map, List.length_range, List.length_drop]; omega)
    intro i _ _
    simp only [D4, powDomain, List.getElem_map, List.getElem_range, List.getElem_drop]
    omega
  have hX4 : X.size = D4.n := hX
  rw [← Plan.checkedStages_eq, ← Parallel.forwardStages_eq D4 tw X hX4]
  unfold Columns.leafPasses
  rw [← hp]
  have hl : D4.logN = D.logN - 4 := rfl
  by_cases ho : D.logN % 2 = 1
  · simp only [hl, show (D.logN - 4) % 2 = 1 by omega, ho, beq_self_eq_true, ↓reduceIte]
    rw [NaturalPlan.lastPair_eq D4 _ _ (by rw [Parallel.size_runPasses, hX4])]
  · simp only [hl, show ¬(D.logN - 4) % 2 = 1 by omega, ho, beq_iff_eq, ↓reduceIte]

/-- The packed column transform packs the natural-order read of the DIF transform. -/
theorem runColumns_encode (D : NTT.Domain F) (S : Nat) (factor : F) (a : Array F)
    (inverse : Bool) (hs : a.size = D.n) (h15 : 15 ≤ D.logN) (h32 : D.logN ≤ 32)
    (hu : 4 * D.n < USize.size) (hS : 0 < S) (hdiv : S ∣ 2 ^ (D.logN - 4)) :
    runColumns p ((Plan.twiddleTable D).map encode) D.logN S factor.val inverse (encode a) =
      encode (decodedFields D.logN (difSpec D a) factor inverse) := by
  let tw := Plan.twiddleTable D
  obtain ⟨htw, hone⟩ := twiddleTable_invariants D
  have hn : a.size = 2 ^ D.logN := hs
  have hu' : 4 * 2 ^ D.logN < USize.size := hu
  let M := 2 ^ (D.logN - 4)
  have hM : 2 ^ D.logN = 16 * M := by
    rw [show D.logN = D.logN - 4 + 4 by omega, Nat.pow_add, Nat.mul_comm]
  have hM2 : M % 2 = 0 := by
    simp only [M]; rw [show D.logN - 4 = D.logN - 5 + 1 by omega, Nat.pow_succ, Nat.mul_mod_left]
  obtain ⟨cs, hcs⟩ := hdiv
  have hcs' : M = S * cs := hcs
  have hcsM : 2 ^ (D.logN - 4) / S = cs := by rw [hcs, Nat.mul_div_cancel_left _ hS]
  let T := Columns.topPasses tw D.logN a
  have hT : T.size = 16 * M := by
    simp only [T, Columns.topPasses, Parallel.size_step, hn, hM]
  let C := fun s ↦ Columns.columnTask a tw D.logN M cs (s * cs)
  have hj (s : Nat) (hsS : s < S) : s * cs + cs ≤ 2 ^ (D.logN - 4) := by
    rw [hcs]
    have := Nat.mul_le_mul_right cs (show s + 1 ≤ S by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    exact this
  have hcol (s : Nat) (hsS : s < S) :=
    Columns.columnTask_col a tw D.logN cs (s * cs) (by omega) hn htw (by omega) (hj s hsS)
  let X := fun l ↦ T.extract (l * M) (l * M + M)
  have hleafIn (l : Nat) (hl : l < 16) :
      leafWords ((Array.range S).map fun s ↦ encode (C s)) cs l = encode (X l) := by
    have hlc : l * cs + cs ≤ 16 * cs := by
      have := Nat.mul_le_mul_right cs (show l + 1 ≤ 16 by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; exact this
    have hC : ∀ s < S, l * cs + cs ≤ (C s).size := fun s hsS ↦ by
      rw [(hcol s hsS).1]; exact hlc
    have hlM : l * M + M ≤ T.size := by
      rw [hT]
      have := Nat.mul_le_mul_right M (show l + 1 ≤ 16 by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; exact this
    obtain ⟨hbs, hbv⟩ := appendRows_spec C (fun _ ↦ l * cs) cs S hC
    rw [leafWords_encode C S cs l]
    congr 1
    apply array_eq_of_getD _ _ 0 (by
      rw [hbs, Array.size_extract, Nat.min_eq_left hlM, ← hcs']; omega)
    intro k
    by_cases hk : k < M
    · have hcs0 : 0 < cs := Nat.pos_of_ne_zero (by rintro rfl; simp only [M] at hk; omega)
      have hks : k / cs < S := by rw [Nat.div_lt_iff_lt_mul hcs0, ← hcs]; exact hk
      rw [← Nat.div_add_mod' k cs, hbv _ hks _ (Nat.mod_lt _ hcs0),
        (hcol _ hks).2 l hl _ (Nat.mod_lt _ hcs0), getD_extract T (l * M) M _ 0 hlM (by
          rw [Nat.div_add_mod' k cs]; exact hk)]
    · rw [Columns.getD_of_size_le _ _ (by rw [hbs, ← hcs]; omega),
        Columns.getD_of_size_le _ _ (by rw [Array.size_extract]; omega)]
  have hX (l : Nat) (hl : l < 16) : (X l).size = 2 ^ (D.logN - 4) := by
    simp only [X, Array.size_extract, hT]
    have := Nat.mul_le_mul_right M (show l + 1 ≤ 16 by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have hleaf (l : Nat) (hl : l < 16) :
      leafNatural p (tw.map encode) (D.logN - 4) factor.val inverse (encode (X l)) =
        encode (decodedFields (D.logN - 4) ((difSpec D a).extract (l * M) ((l + 1) * M))
          factor inverse) := by
    have htw4 : TwiddleSizes (powDomain D 4 (by omega)).logN tw := fun s hs ↦ htw s (by
      simp only [powDomain] at hs; omega)
    have hone4 : TwiddleOnes (powDomain D 4 (by omega)).logN tw := fun s hs ↦ hone s (by
      simp only [powDomain] at hs; omega)
    have hp : 2 ^ (D.logN - 4) ≤ 2 ^ D.logN := Nat.pow_le_pow_right (by omega) (by omega)
    erw [Native.leafNatural_encode (powDomain D 4 (by omega)) tw (X l) factor inverse htw4 hone4
      (hX l hl) (by simp only [powDomain, NTT.Domain.n]; omega)
      (by simp only [powDomain]; omega)]
    rw [leafStages_eq_leafPasses D (by omega) tw (X l) (hX l hl)]
    simp only [X]
    rw [show l * M + M = (l + 1) * M by ring,
      Columns.leafPasses_extract tw _ _ T M 16 l hT hl hM2
        (NaturalPlan.dvd_of_mem_forwardPasses_drop D),
      NaturalPlan.leafPasses_topPasses D tw a hs (by omega), Plan.checkedStages_eq,
      planStages_eq_difSpec D a hs]
    rfl
  have hcols : ((Array.range S).map fun s ↦
      columnWords p (tw.map encode) D.logN M cs (s * cs) (encode a)) =
      (Array.range S).map fun s ↦ encode (C s) := by
    apply Array.ext (by simp only [Array.size_map, Array.size_range])
    intro s h1 _
    simp only [Array.size_map, Array.size_range] at h1
    simp only [Array.getElem_map, Array.getElem_range]
    exact columnWords_encode a tw D.logN cs (s * cs) (by omega) hn htw hu' (hj s h1)
  have hleaves : (Tasks.spawnAfter (Tasks.spawnAll S fun s ↦
      columnWords p (tw.map encode) D.logN M cs (s * cs) (encode a)) 16 fun cols l ↦
        leafNatural p (tw.map encode) (D.logN - 4) factor.val inverse (leafWords cols cs l)).map
        Task.get =
      (Array.range 16).map fun l ↦ encode (decodedFields (D.logN - 4)
        ((difSpec D a).extract (l * M) ((l + 1) * M)) factor inverse) := by
    rw [Tasks.map_get_spawnAfter, Tasks.map_get_spawnAll, hcols]
    apply Array.ext (by simp only [Array.size_map, Array.size_range])
    intro l h1 _
    simp only [Array.size_map, Array.size_range] at h1
    rw [Array.getElem_map, Array.getElem_map, Array.getElem_range, hleafIn l h1, hleaf l h1]
  dsimp only [runColumns]
  rw [hcsM, hleaves, naturalLeaves_encode (difSpec D a) D.logN factor inverse (by omega) h32
    (by rw [size_difSpec]; rfl) hu']

/-- The packed transform computes the DFT, scaled for an inverse transform. -/
theorem run_dft (D : NTT.Domain F) (parallel : Bool) (factor : F) (a : Array F)
    (inverse : Bool) (hs : a.size = D.n) (h32 : D.logN ≤ 32) (hu : 4 * D.n < USize.size) :
    run p ((Plan.twiddleTable D).map encode) D.logN parallel factor.val inverse (encode a) =
      encode (if inverse then (NTT.Forward.forwardSpec D a).map (fun x ↦ factor * x)
        else NTT.Forward.forwardSpec D a) := by
  rw [← decodedFields_difSpec D a factor inverse]
  unfold run
  split
  · rename_i h
    exact runColumns_encode D _ factor a inverse hs h.2 h32 hu (Nat.two_pow_pos _)
      (Nat.pow_dvd_pow 2 (by omega))
  · obtain ⟨htw, hone⟩ := twiddleTable_invariants D
    rw [Native.leafNatural_encode D _ a factor inverse htw hone hs hu h32,
      planStages_eq_difSpec D a hs]

end Native
end CompPoly.CPolynomial.NTTFast.Packed
