/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTT.FastMul
import CompPoly.Univariate.NTTFast.FastMul
import CompPoly.Univariate.NTTFast.Forward
import CompPoly.Univariate.NTTFast.Inverse

/-!
# Basic NTTFast correctness facts

Basic equivalences, cached-plan well-formedness, twiddle-table facts, and shared
proof helpers for `NTTFast` correctness.
-/
namespace CompPoly
namespace CPolynomial
namespace NTTFast

open scoped BigOperators

variable {R : Type*} [Field R]

namespace Transform

/-- `NTTFast` bit reversal agrees with the `NTT` bit-reversal function. -/
theorem bitRevNat_eq_ntt (bits i : Nat) :
    bitRevNat bits i = NTT.Transform.bitRevNat bits i := by
  induction bits generalizing i with
  | zero =>
      rfl
  | succ bits ih =>
      simp [bitRevNat, NTT.Transform.bitRevNat, ih]

/-- `NTTFast` bit-reversal permutation agrees with `NTT.Transform.bitRevPermute`. -/
theorem bitRevPermute_eq_ntt (D : NTT.Domain R) (a : Array R) :
    bitRevPermute D a = NTT.Transform.bitRevPermute D a := by
  simp [bitRevPermute, NTT.Transform.bitRevPermute, bitRevNat_eq_ntt]

/-- One `NTTFast` radix-2 butterfly step agrees with the `NTT` implementation. -/
theorem butterflyInnerStep_eq_ntt
    (blockSize half : Nat) (wm : R) (block j : Nat) (st : Array R × R) :
    butterflyInnerStep blockSize half wm block j st =
      NTT.Transform.butterflyInnerStep blockSize half wm block j st := by
  rfl

/-- One `NTTFast` radix-2 butterfly stage agrees with the `NTT` implementation. -/
theorem butterflyStage_eq_ntt (D : NTT.Domain R) (stage : Nat) (a : Array R) :
    butterflyStage D stage a = NTT.Transform.butterflyStage D stage a := by
  simp [butterflyStage, NTT.Transform.butterflyStage, butterflyInnerStep_eq_ntt]

/-- The full `NTTFast` radix-2 stage loop agrees with `NTT.Transform.runStages`. -/
theorem runStages_eq_ntt (D : NTT.Domain R) (a : Array R) :
    runStages D a = NTT.Transform.runStages D a := by
  simp [runStages, NTT.Transform.runStages, butterflyStage_eq_ntt]

end Transform

/-- `NTTFast` pointwise multiplication agrees with `NTT.FastMul.pointwiseMul`. -/
theorem pointwiseMul_eq_ntt (D : NTT.Domain R) (a b : Array R) :
    pointwiseMul D a b = NTT.FastMul.pointwiseMul D a b := by
  rfl

/-- Pointwise multiplication over a domain returns an array of the domain size. -/
@[simp] theorem size_pointwiseMul (D : NTT.Domain R) (a b : Array R) :
    (pointwiseMul D a b).size = D.n := by
  simp [pointwiseMul]

namespace Forward

/-- The standalone `NTTFast` forward implementation agrees with `NTT.Forward.forwardImpl`. -/
theorem forwardImpl_eq_ntt (D : NTT.Domain R) (p : CPolynomial.Raw R) :
    forwardImpl D p = NTT.Forward.forwardImpl D p := by
  simp [forwardImpl, NTT.Forward.forwardImpl, Transform.runStages_eq_ntt,
    Transform.bitRevPermute_eq_ntt]

/-- The standalone `NTTFast` forward implementation computes the forward NTT spec. -/
theorem forwardImpl_correct (D : NTT.Domain R) (p : CPolynomial.Raw R) :
    forwardImpl D p = NTT.Forward.forwardSpec D p := by
  rw [forwardImpl_eq_ntt, NTT.Forward.forwardImpl_correct]

end Forward

namespace Inverse

/-- The standalone `NTTFast` inverse implementation agrees with `NTT.Inverse.inverseImpl`. -/
theorem inverseImpl_eq_ntt (D : NTT.Domain R) (v : Array R) :
    inverseImpl D v = NTT.Inverse.inverseImpl D v := by
  simp [inverseImpl, NTT.Inverse.inverseImpl, Transform.runStages_eq_ntt,
    Transform.bitRevPermute_eq_ntt]

/-- The standalone `NTTFast` inverse implementation computes the inverse NTT spec. -/
theorem inverseImpl_correct (D : NTT.Domain R) (v : Array R) :
    inverseImpl D v = NTT.Inverse.inverseSpec D v := by
  rw [inverseImpl_eq_ntt, NTT.Inverse.inverseImpl_correct]

end Inverse

namespace Plan

/-- Well-formedness condition for cached plan data. -/
def WellFormed (P : Plan R) : Prop :=
  P.inverseDomain = P.domain.inverse ∧
    P.nInv = P.domain.nInv ∧
    P.twiddles = twiddleTable P.domain ∧
    P.inverseTwiddles = twiddleTable P.domain.inverse

private theorem foldl_push_size (wm : R) :
    ∀ xs : List Nat, ∀ (powers : Array R) (w : R),
      (List.foldl (fun (b : MProd (Array R) R) (_ : Nat) =>
        ⟨b.fst.push b.snd, b.snd * wm⟩) ⟨powers, w⟩ xs).fst.size =
        powers.size + xs.length
  | [], powers, _ => by simp
  | _ :: xs, powers, w => by
      simp [foldl_push_size wm xs (powers.push w) (w * wm), Nat.add_comm,
        Nat.add_left_comm]

private theorem foldl_push_getD (wm : R) :
    ∀ xs : List Nat, ∀ (powers : Array R) (w base : R) (offset : Nat),
      powers.size = offset →
      (∀ i, i < offset → powers.getD i 0 = base * wm ^ i) →
      w = base * wm ^ offset →
      ∀ i, i < offset + xs.length →
        (List.foldl (fun (b : MProd (Array R) R) (_ : Nat) =>
          ⟨b.fst.push b.snd, b.snd * wm⟩) ⟨powers, w⟩ xs).fst.getD i 0 =
          base * wm ^ i
  | [], powers, _w, base, offset, _hsize, hvals, _hw, i, hi => by
      exact hvals i (by simpa using hi)
  | _ :: xs, powers, w, base, offset, hsize, hvals, hw, i, hi => by
      apply foldl_push_getD wm xs (powers.push w) (w * wm) base (offset + 1)
      · simp [hsize]
      · intro k hk
        by_cases hk0 : k < offset
        · have hkSize : k < powers.size := by simpa [hsize] using hk0
          rw [← hvals k hk0]
          simp [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hkSize,
            Array.getElem?_eq_getElem hkSize]
        · have hkEq : k = offset := by omega
          subst hkEq
          rw [Array.getD_eq_getD_getElem?]
          rw [← hsize, Array.getElem?_push_size]
          simpa [hsize] using hw
      · rw [hw]
        rw [pow_succ]
        ring
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

/-- The cached twiddle powers for a stage have exactly one entry per butterfly offset. -/
theorem twiddlePowers_size (D : NTT.Domain R) (stage : Nat) :
    (twiddlePowers D stage).size = 2 ^ stage := by
  unfold twiddlePowers
  simp
  let wm := D.omega ^ (2 ^ D.logN / 2 ^ (stage + 1))
  simpa [wm] using
    foldl_push_size wm (List.range' 0 (2 ^ stage)) (#[] : Array R) (1 : R)

/-- Entries of the cached twiddle powers are the corresponding powers of the stage root. -/
theorem twiddlePowers_getD_eq_pow (D : NTT.Domain R) (stage j : Nat)
    (hj : j < 2 ^ stage) :
    (twiddlePowers D stage).getD j 0 =
      (D.omega ^ (D.n / 2 ^ (stage + 1))) ^ j := by
  unfold twiddlePowers
  simp
  let wm := D.omega ^ (2 ^ D.logN / 2 ^ (stage + 1))
  have h := foldl_push_getD wm (List.range' 0 (2 ^ stage)) (#[] : Array R)
    (1 : R) (1 : R) 0 (by simp) (by intro i hi; omega) (by simp) j
    (by simpa using hj)
  rw [Array.getD_eq_getD_getElem?] at h
  simpa [wm, NTT.Domain.n] using h

/-- Looking up a valid stage in the twiddle table returns that stage's twiddle powers. -/
theorem twiddleTable_getD_eq_twiddlePowers
    (D : NTT.Domain R) (stage : Nat) (hstage : stage < D.logN) :
    (twiddleTable D).getD stage #[] = twiddlePowers D stage := by
  simp [twiddleTable, hstage]

/-- A plan built directly from a domain has well-formed cached data. -/
theorem ofDomain_wellFormed (D : NTT.Domain R) :
    WellFormed (ofDomain D) := by
  simp [WellFormed, ofDomain]

/-- Loading raw coefficients into a domain-sized array is `Array.ofFn` with zero padding. -/
theorem loadNatural_eq (D : NTT.Domain R) (a : Array R) :
    loadNatural D a = Array.ofFn (fun i : D.Idx => a.getD i.1 0) := by
  rfl

theorem foldl_range_eq_rec {α : Type*} (f : Nat → α → α) (x : α) :
    ∀ n : Nat,
      List.foldl (fun acc i => f i acc) x (List.range n) = Nat.rec x (fun i acc => f i acc) n
  | 0 => by simp
  | n + 1 => by
      simp [List.range_succ, List.foldl_append, foldl_range_eq_rec f x n]

theorem foldl_range_eq_rec_fst {α β : Type*}
    (f : Nat → α × β → α × β) (x : α × β) (n : Nat) :
    (List.foldl (fun acc i => f i acc) x (List.range n)).1 =
      (Nat.rec (motive := fun _ => α × β) x (fun i acc => f i acc) n).1 := by
  simpa using congrArg Prod.fst
    (show List.foldl (fun acc i => f i acc) x (List.range n) =
        Nat.rec (motive := fun _ => α × β) x (fun i acc => f i acc) n from
      foldl_range_eq_rec f x n)

theorem foldl_range_congr {α : Type*} (f g : α → Nat → α) :
    ∀ n : Nat,
      (∀ i, i < n → ∀ acc, f acc i = g acc i) →
      ∀ acc, List.foldl f acc (List.range n) = List.foldl g acc (List.range n)
  | 0, _h, acc => by simp
  | n + 1, h, acc => by
      have hprev : ∀ i, i < n → ∀ acc, f acc i = g acc i := by
        intro i hi
        exact h i (Nat.lt_trans hi (Nat.lt_succ_self n))
      simp [List.range_succ, List.foldl_append, foldl_range_congr f g n hprev acc,
        h n (Nat.lt_succ_self n)]

theorem foldl_range_preserve {α : Type*} (p : α → Prop) (f : α → Nat → α) :
    ∀ n : Nat,
      (∀ i, i < n → ∀ acc, p acc → p (f acc i)) →
      ∀ acc, p acc → p (List.foldl f acc (List.range n))
  | 0, _h, acc, hacc => by simpa using hacc
  | n + 1, h, acc, hacc => by
      have hprev : ∀ i, i < n → ∀ acc, p acc → p (f acc i) := by
        intro i hi
        exact h i (Nat.lt_trans hi (Nat.lt_succ_self n))
      simp [List.range_succ, List.foldl_append,
        foldl_range_preserve p f n hprev acc hacc,
        h n (Nat.lt_succ_self n)]

theorem foldl_range_congr_inv {α : Type*} (p : α → Prop) (f g : α → Nat → α) :
    ∀ n : Nat,
      (∀ i, i < n → ∀ acc, p acc → f acc i = g acc i) →
      (∀ i, i < n → ∀ acc, p acc → p (f acc i)) →
      ∀ acc, p acc → List.foldl f acc (List.range n) = List.foldl g acc (List.range n)
  | 0, _hfg, _hpreserve, acc, _hacc => by simp
  | n + 1, hfg, hpreserve, acc, hacc => by
      have hfgPrev : ∀ i, i < n → ∀ acc, p acc → f acc i = g acc i := by
        intro i hi
        exact hfg i (Nat.lt_trans hi (Nat.lt_succ_self n))
      have hpreservePrev : ∀ i, i < n → ∀ acc, p acc → p (f acc i) := by
        intro i hi
        exact hpreserve i (Nat.lt_trans hi (Nat.lt_succ_self n))
      have ih := foldl_range_congr_inv p f g n hfgPrev hpreservePrev acc hacc
      have haccTail : p (List.foldl f acc (List.range n)) :=
        foldl_range_preserve p f n hpreservePrev acc hacc
      simp [List.range_succ, List.foldl_append]
      rw [← ih]
      exact hfg n (Nat.lt_succ_self n) _ haccTail

theorem foldl_range'_succ_shift {α : Type*} (f : Nat → α → α) :
    ∀ n offset (acc : α),
      List.foldl (fun acc t => f (t + 1) acc) acc (List.range' offset n) =
        List.foldl (fun acc t => f t acc) acc (List.range' (offset + 1) n)
  | 0, _offset, _acc => by simp
  | n + 1, offset, acc => by
      have ih := foldl_range'_succ_shift f n (offset + 1) (f (offset + 1) acc)
      simp only [List.range'_succ, List.foldl_cons]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

theorem foldl_range'_eq_range_add {α : Type*} (f : Nat → α → α)
    (n offset : Nat) (acc : α) :
    List.foldl (fun acc t => f t acc) acc (List.range' offset n) =
      List.foldl (fun acc t => f (offset + t) acc) acc (List.range n) := by
  simp [List.range'_eq_map_range, List.foldl_map]

theorem foldl_range'_append_split {α : Type*} (f : α → Nat → α)
    (acc : α) (s m n : Nat) :
    List.foldl f acc (List.range' s (m + n)) =
      List.foldl f (List.foldl f acc (List.range' s m)) (List.range' (s + m) n) := by
  have h : List.range' s m ++ List.range' (s + m) n = List.range' s (m + n) := by
    rw [show s + m = s + 1 * m by omega]
    exact List.range'_append (s := s) (m := m) (n := n) (step := 1)
  rw [← h, List.foldl_append]

theorem three_mul_add_eq_add_two_mul_add (q b : Nat) :
    3 * q + b = q + (2 * q + b) := by
  nlinarith

theorem foldl_commute {α : Type*} (op : α → α) (f : Nat → α → α) :
    ∀ n : Nat,
      (∀ i, i < n → ∀ x, op (f i x) = f i (op x)) →
      ∀ x, op (List.foldl (fun x i => f i x) x (List.range n)) =
        List.foldl (fun x i => f i x) (op x) (List.range n)
  | 0, _h, x => by simp
  | n + 1, h, x => by
      have hprev : ∀ i, i < n → ∀ x, op (f i x) = f i (op x) := by
        intro i hi
        exact h i (Nat.lt_trans hi (Nat.lt_succ_self n))
      simp [List.range_succ, List.foldl_append, foldl_commute op f n hprev x,
        h n (Nat.lt_succ_self n)]

theorem foldl_commute_foldl {α : Type*} (f g : Nat → α → α) (m n : Nat)
    (hcomm : ∀ i j, i < m → j < n → ∀ x, g j (f i x) = f i (g j x)) :
    ∀ x,
      List.foldl (fun x i => f i x) (List.foldl (fun x j => g j x) x (List.range n))
          (List.range m) =
        List.foldl (fun x j => g j x) (List.foldl (fun x i => f i x) x (List.range m))
          (List.range n) := by
  intro x
  apply foldl_commute (fun x => List.foldl (fun x i => f i x) x (List.range m))
    (fun j x => g j x) n
  intro j hj x
  symm
  apply foldl_commute (g j) f m
  intro i hi x
  exact hcomm i j hi hj x

theorem foldl_pair {α : Type*} (f g : Nat → α → α) :
    ∀ n : Nat,
      (∀ i j, i < j → j < n → ∀ x, f j (g i x) = g i (f j x)) →
      ∀ x,
        List.foldl (fun x i => g i (f i x)) x (List.range n) =
          List.foldl (fun x i => g i x)
            (List.foldl (fun x i => f i x) x (List.range n)) (List.range n)
  | 0, _comm, x => by simp
  | n + 1, comm, x => by
      have commPrev : ∀ i j, i < j → j < n → ∀ x, f j (g i x) = g i (f j x) := by
        intro i j hij hj
        exact comm i j hij (Nat.lt_trans hj (Nat.lt_succ_self n))
      have ih := foldl_pair f g n commPrev x
      simp [List.range_succ, List.foldl_append, ih]
      rw [foldl_commute (f n) (fun i x => g i x) n (by
        intro i hi
        exact comm i n hi (Nat.lt_succ_self n))]

theorem foldl_range_pair {α : Type*} (f : Nat → α → α) :
    ∀ n (acc : α),
      List.foldl (fun acc b => f (2 * b + 1) (f (2 * b) acc)) acc (List.range n) =
        List.foldl (fun acc k => f k acc) acc (List.range (2 * n))
  | 0, acc => by simp
  | n + 1, acc => by
      rw [List.range_succ, List.foldl_append]
      rw [foldl_range_pair f n acc]
      have h : List.range (2 * (n + 1)) = List.range (2 * n) ++ [2 * n, 2 * n + 1] := by
        rw [List.range_eq_range', show 2 * (n + 1) = 2 * n + 2 by omega]
        have happ := List.range'_append (s := 0) (m := 2 * n) (n := 2) (step := 1)
        simpa [List.range_eq_range', List.range'_succ, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using happ.symm
      rw [h, List.foldl_append]
      simp [Nat.add_comm]

theorem foldl_quad {α : Type*} (l₁ l₂ h₁ h₂ : Nat → α → α) :
    ∀ n : Nat,
      (∀ i j, i < j → j < n → ∀ x, l₁ j (l₂ i x) = l₂ i (l₁ j x)) →
      (∀ i j, i < j → j < n → ∀ x, l₁ j (h₁ i x) = h₁ i (l₁ j x)) →
      (∀ i j, i < j → j < n → ∀ x, l₁ j (h₂ i x) = h₂ i (l₁ j x)) →
      (∀ i j, i < j → j < n → ∀ x, l₂ j (h₁ i x) = h₁ i (l₂ j x)) →
      (∀ i j, i < j → j < n → ∀ x, l₂ j (h₂ i x) = h₂ i (l₂ j x)) →
      (∀ i j, i < j → j < n → ∀ x, h₁ j (h₂ i x) = h₂ i (h₁ j x)) →
      ∀ x,
        List.foldl (fun x i => h₂ i (h₁ i (l₂ i (l₁ i x)))) x (List.range n) =
          List.foldl (fun x i => h₂ i x)
            (List.foldl (fun x i => h₁ i x)
              (List.foldl (fun x i => l₂ i x)
                (List.foldl (fun x i => l₁ i x) x (List.range n)) (List.range n))
              (List.range n))
            (List.range n)
  | 0, _, _, _, _, _, _, x => by simp
  | n + 1, c₁₂, c₁₃, c₁₄, c₂₃, c₂₄, c₃₄, x => by
      have c₁₂' : ∀ i j, i < j → j < n → ∀ x, l₁ j (l₂ i x) = l₂ i (l₁ j x) := by
        intro i j hij hj
        exact c₁₂ i j hij (Nat.lt_trans hj (Nat.lt_succ_self n))
      have c₁₃' : ∀ i j, i < j → j < n → ∀ x, l₁ j (h₁ i x) = h₁ i (l₁ j x) := by
        intro i j hij hj
        exact c₁₃ i j hij (Nat.lt_trans hj (Nat.lt_succ_self n))
      have c₁₄' : ∀ i j, i < j → j < n → ∀ x, l₁ j (h₂ i x) = h₂ i (l₁ j x) := by
        intro i j hij hj
        exact c₁₄ i j hij (Nat.lt_trans hj (Nat.lt_succ_self n))
      have c₂₃' : ∀ i j, i < j → j < n → ∀ x, l₂ j (h₁ i x) = h₁ i (l₂ j x) := by
        intro i j hij hj
        exact c₂₃ i j hij (Nat.lt_trans hj (Nat.lt_succ_self n))
      have c₂₄' : ∀ i j, i < j → j < n → ∀ x, l₂ j (h₂ i x) = h₂ i (l₂ j x) := by
        intro i j hij hj
        exact c₂₄ i j hij (Nat.lt_trans hj (Nat.lt_succ_self n))
      have c₃₄' : ∀ i j, i < j → j < n → ∀ x, h₁ j (h₂ i x) = h₂ i (h₁ j x) := by
        intro i j hij hj
        exact c₃₄ i j hij (Nat.lt_trans hj (Nat.lt_succ_self n))
      have ih := foldl_quad l₁ l₂ h₁ h₂ n c₁₂' c₁₃' c₁₄' c₂₃' c₂₄' c₃₄' x
      simp [List.range_succ, List.foldl_append, ih]
      rw [foldl_commute (l₁ n) (fun i x => h₂ i x) n (by
        intro i hi
        exact c₁₄ i n hi (Nat.lt_succ_self n))]
      rw [foldl_commute (l₁ n) (fun i x => h₁ i x) n (by
        intro i hi
        exact c₁₃ i n hi (Nat.lt_succ_self n))]
      rw [foldl_commute (l₁ n) (fun i x => l₂ i x) n (by
        intro i hi
        exact c₁₂ i n hi (Nat.lt_succ_self n))]
      rw [foldl_commute (l₂ n) (fun i x => h₂ i x) n (by
        intro i hi
        exact c₂₄ i n hi (Nat.lt_succ_self n))]
      rw [foldl_commute (l₂ n) (fun i x => h₁ i x) n (by
        intro i hi
        exact c₂₃ i n hi (Nat.lt_succ_self n))]
      rw [foldl_commute (h₁ n) (fun i x => h₂ i x) n (by
        intro i hi
        exact c₃₄ i n hi (Nat.lt_succ_self n))]

private theorem butterflyDITInner_eq_foldl
    (twiddles : Array R) (blockSize half : Nat) (wm : R) (block limit : Nat)
    (htwiddles : ∀ j, j < limit → twiddles.getD j 0 = wm ^ j) :
    ∀ n j (acc : Array R),
      limit = j + n →
      butterflyDITInner twiddles limit j (block * blockSize + j)
          (block * blockSize + j + half) acc =
        (List.foldl
          (fun st k => NTT.Transform.butterflyInnerStep blockSize half wm block k st)
          (acc, wm ^ j) (List.range' j n)).1
  | 0, j, acc, hlimit => by
      have hnot : ¬j < limit := by omega
      simp [butterflyDITInner, hnot]
  | n + 1, j, acc, hlimit => by
      have hjlt : j < limit := by omega
      have htail : limit = j + 1 + n := by omega
      have ih := butterflyDITInner_eq_foldl twiddles blockSize half wm block limit htwiddles
        n (j + 1)
          (((acc.set! (block * blockSize + j)
                (acc.getD (block * blockSize + j) 0 +
                  wm ^ j * acc.getD (block * blockSize + j + half) 0)).set!
            (block * blockSize + j + half)
            (acc.getD (block * blockSize + j) 0 -
              wm ^ j * acc.getD (block * blockSize + j + half) 0)))
        htail
      rw [butterflyDITInner]
      simp only [hjlt, ↓reduceIte]
      simpa [List.range'_succ, NTT.Transform.butterflyInnerStep, htwiddles j hjlt, pow_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

private theorem butterflyDITInner_eq_butterflyBlockStep
    (twiddles : Array R) (blockSize half : Nat) (wm : R) (block : Nat) (acc : Array R)
    (htwiddles : ∀ j, j < half → twiddles.getD j 0 = wm ^ j) :
    butterflyDITInner twiddles half 0 (block * blockSize) (block * blockSize + half) acc =
      NTT.Transform.butterflyBlockStep blockSize half wm block acc := by
  change butterflyDITInner twiddles half 0 (block * blockSize + 0)
      (block * blockSize + 0 + half) acc =
    NTT.Transform.butterflyBlockStep blockSize half wm block acc
  rw [butterflyDITInner_eq_foldl twiddles blockSize half wm block half htwiddles
    half 0 acc (by simp)]
  simpa [NTT.Transform.butterflyBlockStep, List.range_eq_range'] using
    foldl_range_eq_rec_fst
      (f := fun j st => NTT.Transform.butterflyInnerStep blockSize half wm block j st)
      (x := (acc, (1 : R))) half

theorem butterflyDITBlocks_eq_foldl
    (twiddles : Array R) (blockSize half : Nat) (wm : R)
    (htwiddles : ∀ j, j < half → twiddles.getD j 0 = wm ^ j) :
    ∀ n blocks block (acc : Array R),
      blocks = block + n →
      butterflyDITBlocks twiddles blockSize half blocks block acc =
        List.foldl (fun acc block => NTT.Transform.butterflyBlockStep blockSize half wm block acc)
          acc (List.range' block n)
  | 0, blocks, block, acc, hblocks => by
      have hnot : ¬block < blocks := by omega
      simp [butterflyDITBlocks, hnot]
  | n + 1, blocks, block, acc, hblocks => by
      have hblock : block < blocks := by omega
      have htail : blocks = block + 1 + n := by omega
      have ih := butterflyDITBlocks_eq_foldl twiddles blockSize half wm htwiddles
        n blocks (block + 1)
          (NTT.Transform.butterflyBlockStep blockSize half wm block acc) htail
      rw [butterflyDITBlocks]
      simp only [hblock, ↓reduceIte]
      rw [butterflyDITInner_eq_butterflyBlockStep twiddles blockSize half wm block acc
        htwiddles]
      simpa [List.range'_succ] using ih

@[simp] private theorem size_butterflyDITInner
    (twiddles : Array R) (limit j i0 i1 : Nat) :
    ∀ acc : Array R, (butterflyDITInner twiddles limit j i0 i1 acc).size = acc.size := by
  intro acc
  induction h : limit - j generalizing j i0 i1 acc with
  | zero =>
      have hnot : ¬j < limit := by omega
      simp [butterflyDITInner, hnot]
  | succ n ih =>
      by_cases hj : j < limit
      · rw [butterflyDITInner]
        simp only [hj, ↓reduceIte]
        rw [ih (j + 1) (i0 + 1) (i1 + 1)]
        · simp [Array.set!, Array.size_setIfInBounds]
        · omega
      · simp [butterflyDITInner, hj]

@[simp] private theorem size_butterflyDITBlocks
    (twiddles : Array R) (blockSize half blocks block : Nat) :
    ∀ acc : Array R,
      (butterflyDITBlocks twiddles blockSize half blocks block acc).size = acc.size := by
  intro acc
  induction h : blocks - block generalizing block acc with
  | zero =>
      have hnot : ¬block < blocks := by omega
      simp [butterflyDITBlocks, hnot]
  | succ n ih =>
      by_cases hblock : block < blocks
      · rw [butterflyDITBlocks]
        simp only [hblock, ↓reduceIte]
        rw [ih (block + 1)]
        · simp
        · omega
      · simp [butterflyDITBlocks, hblock]

@[simp] private theorem size_butterflyStageWithTwiddles
    (D : NTT.Domain R) (stage : Nat) (twiddles a : Array R) :
    (butterflyStageWithTwiddles D stage twiddles a).size = a.size := by
  simp [butterflyStageWithTwiddles]

@[simp] private theorem size_butterflyDITRadix4Inner
    (twiddlesLow twiddlesHigh : Array R) (limit j i0 i1 i2 i3 : Nat) :
    ∀ acc : Array R,
      (butterflyDITRadix4Inner twiddlesLow twiddlesHigh limit j i0 i1 i2 i3 acc).size =
        acc.size := by
  intro acc
  induction h : limit - j generalizing j i0 i1 i2 i3 acc with
  | zero =>
      have hnot : ¬j < limit := by omega
      simp [butterflyDITRadix4Inner, hnot]
  | succ n ih =>
      by_cases hj : j < limit
      · rw [butterflyDITRadix4Inner]
        simp only [hj, ↓reduceIte]
        rw [ih (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1)]
        · simp [Array.set!, Array.size_setIfInBounds]
        · omega
      · simp [butterflyDITRadix4Inner, hj]

@[simp] private theorem size_butterflyDITRadix4Blocks
    (twiddlesLow twiddlesHigh : Array R) (blockSize quarter blocks block : Nat) :
    ∀ acc : Array R,
      (butterflyDITRadix4Blocks twiddlesLow twiddlesHigh blockSize quarter blocks block acc).size =
        acc.size := by
  intro acc
  induction h : blocks - block generalizing block acc with
  | zero =>
      have hnot : ¬block < blocks := by omega
      simp [butterflyDITRadix4Blocks, hnot]
  | succ n ih =>
      by_cases hblock : block < blocks
      · rw [butterflyDITRadix4Blocks]
        simp only [hblock, ↓reduceIte]
        rw [ih (block + 1)]
        · simp
        · omega
      · simp [butterflyDITRadix4Blocks, hblock]

@[simp] private theorem size_butterflyRadix4StageWithTwiddles
    (D : NTT.Domain R) (lowStage : Nat) (twiddlesLow twiddlesHigh a : Array R) :
    (butterflyRadix4StageWithTwiddles D lowStage twiddlesLow twiddlesHigh a).size =
      a.size := by
  simp [butterflyRadix4StageWithTwiddles]

@[simp] private theorem size_butterflyDIFInner
    (twiddles : Array R) (limit j i0 i1 : Nat) :
    ∀ acc : Array R, (butterflyDIFInner twiddles limit j i0 i1 acc).size = acc.size := by
  intro acc
  induction h : limit - j generalizing j i0 i1 acc with
  | zero =>
      have hnot : ¬j < limit := by omega
      simp [butterflyDIFInner, hnot]
  | succ n ih =>
      by_cases hj : j < limit
      · rw [butterflyDIFInner]
        simp only [hj, ↓reduceIte]
        rw [ih (j + 1) (i0 + 1) (i1 + 1)]
        · simp [Array.set!, Array.size_setIfInBounds]
        · omega
      · simp [butterflyDIFInner, hj]

@[simp] private theorem size_butterflyDIFBlocks
    (twiddles : Array R) (blockSize half blocks block : Nat) :
    ∀ acc : Array R,
      (butterflyDIFBlocks twiddles blockSize half blocks block acc).size = acc.size := by
  intro acc
  induction h : blocks - block generalizing block acc with
  | zero =>
      have hnot : ¬block < blocks := by omega
      simp [butterflyDIFBlocks, hnot]
  | succ n ih =>
      by_cases hblock : block < blocks
      · rw [butterflyDIFBlocks]
        simp only [hblock, ↓reduceIte]
        rw [ih (block + 1)]
        · simp
        · omega
      · simp [butterflyDIFBlocks, hblock]

@[simp] private theorem size_butterflyStageDIFWithTwiddles
    (D : NTT.Domain R) (stage : Nat) (twiddles a : Array R) :
    (butterflyStageDIFWithTwiddles D stage twiddles a).size = a.size := by
  simp [butterflyStageDIFWithTwiddles]

@[simp] private theorem size_butterflyDIFRadix4Inner
    (twiddlesHigh twiddlesLow : Array R) (limit j i0 i1 i2 i3 : Nat) :
    ∀ acc : Array R,
      (butterflyDIFRadix4Inner twiddlesHigh twiddlesLow limit j i0 i1 i2 i3 acc).size =
        acc.size := by
  intro acc
  induction h : limit - j generalizing j i0 i1 i2 i3 acc with
  | zero =>
      have hnot : ¬j < limit := by omega
      simp [butterflyDIFRadix4Inner, hnot]
  | succ n ih =>
      by_cases hj : j < limit
      · rw [butterflyDIFRadix4Inner]
        simp only [hj, ↓reduceIte]
        rw [ih (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1)]
        · simp [Array.set!, Array.size_setIfInBounds]
        · omega
      · simp [butterflyDIFRadix4Inner, hj]

@[simp] private theorem size_butterflyDIFRadix4Blocks
    (twiddlesHigh twiddlesLow : Array R) (blockSize quarter blocks block : Nat) :
    ∀ acc : Array R,
      (butterflyDIFRadix4Blocks twiddlesHigh twiddlesLow blockSize quarter blocks block acc).size =
        acc.size := by
  intro acc
  induction h : blocks - block generalizing block acc with
  | zero =>
      have hnot : ¬block < blocks := by omega
      simp [butterflyDIFRadix4Blocks, hnot]
  | succ n ih =>
      by_cases hblock : block < blocks
      · rw [butterflyDIFRadix4Blocks]
        simp only [hblock, ↓reduceIte]
        rw [ih (block + 1)]
        · simp
        · omega
      · simp [butterflyDIFRadix4Blocks, hblock]

@[simp] private theorem size_butterflyRadix4StageDIFWithTwiddles
    (D : NTT.Domain R) (lowStage : Nat) (twiddlesHigh twiddlesLow a : Array R) :
    (butterflyRadix4StageDIFWithTwiddles D lowStage twiddlesHigh twiddlesLow a).size =
      a.size := by
  simp [butterflyRadix4StageDIFWithTwiddles]

end Plan

end NTTFast
end CPolynomial
end CompPoly
