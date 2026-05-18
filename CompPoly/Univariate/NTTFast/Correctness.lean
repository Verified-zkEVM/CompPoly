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
# Correctness proofs for NTTFast multiplication

This file proves that the `NTTFast` transforms and multiplication pipelines agree
with the NTT specifications, and that multiplication agrees with ordinary
polynomial multiplication under the usual domain-fit hypothesis.
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

private theorem foldl_range_eq_rec {α : Type*} (f : Nat → α → α) (x : α) :
    ∀ n : Nat,
      List.foldl (fun acc i => f i acc) x (List.range n) = Nat.rec x (fun i acc => f i acc) n
  | 0 => by simp
  | n + 1 => by
      simp [List.range_succ, List.foldl_append, foldl_range_eq_rec f x n]

private theorem foldl_range_eq_rec_fst {α β : Type*}
    (f : Nat → α × β → α × β) (x : α × β) (n : Nat) :
    (List.foldl (fun acc i => f i acc) x (List.range n)).1 =
      (Nat.rec (motive := fun _ => α × β) x (fun i acc => f i acc) n).1 := by
  simpa using congrArg Prod.fst
    (show List.foldl (fun acc i => f i acc) x (List.range n) =
        Nat.rec (motive := fun _ => α × β) x (fun i acc => f i acc) n from
      foldl_range_eq_rec f x n)

private theorem foldl_range_congr {α : Type*} (f g : α → Nat → α) :
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

private theorem foldl_range_preserve {α : Type*} (p : α → Prop) (f : α → Nat → α) :
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

private theorem foldl_range_congr_inv {α : Type*} (p : α → Prop) (f g : α → Nat → α) :
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

private theorem foldl_range'_succ_shift {α : Type*} (f : Nat → α → α) :
    ∀ n offset (acc : α),
      List.foldl (fun acc t => f (t + 1) acc) acc (List.range' offset n) =
        List.foldl (fun acc t => f t acc) acc (List.range' (offset + 1) n)
  | 0, _offset, _acc => by simp
  | n + 1, offset, acc => by
      have ih := foldl_range'_succ_shift f n (offset + 1) (f (offset + 1) acc)
      simp only [List.range'_succ, List.foldl_cons]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

private theorem foldl_range'_eq_range_add {α : Type*} (f : Nat → α → α)
    (n offset : Nat) (acc : α) :
    List.foldl (fun acc t => f t acc) acc (List.range' offset n) =
      List.foldl (fun acc t => f (offset + t) acc) acc (List.range n) := by
  simp [List.range'_eq_map_range, List.foldl_map]

private theorem foldl_range'_append_split {α : Type*} (f : α → Nat → α)
    (acc : α) (s m n : Nat) :
    List.foldl f acc (List.range' s (m + n)) =
      List.foldl f (List.foldl f acc (List.range' s m)) (List.range' (s + m) n) := by
  have h : List.range' s m ++ List.range' (s + m) n = List.range' s (m + n) := by
    rw [show s + m = s + 1 * m by omega]
    exact List.range'_append (s := s) (m := m) (n := n) (step := 1)
  rw [← h, List.foldl_append]

private theorem three_mul_add_eq_add_two_mul_add (q b : Nat) :
    3 * q + b = q + (2 * q + b) := by
  nlinarith

private theorem foldl_commute {α : Type*} (op : α → α) (f : Nat → α → α) :
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

private theorem foldl_commute_foldl {α : Type*} (f g : Nat → α → α) (m n : Nat)
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

private theorem foldl_pair {α : Type*} (f g : Nat → α → α) :
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

private theorem foldl_range_pair {α : Type*} (f : Nat → α → α) :
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

private theorem foldl_quad {α : Type*} (l₁ l₂ h₁ h₂ : Nat → α → α) :
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

private theorem butterflyDITBlocks_eq_foldl
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

private def difMathValueAt (D : NTT.Domain R) (completed : Nat) (a : Array R)
    (idx : Nat) : R :=
  let blockSize : Nat := 2 ^ (D.logN - completed)
  let block := idx / blockSize
  let offset := idx % blockSize
  ∑ t : Fin (2 ^ completed),
    a.getD (offset + t.1 * blockSize) 0 *
      D.omega ^ (NTT.Transform.bitRevNat completed block * (offset + t.1 * blockSize))

private def difMathStageSpec (D : NTT.Domain R) (completed : Nat) (a : Array R) : Array R :=
  Array.ofFn (fun i : D.Idx => difMathValueAt D completed a i.1)

private def difMathBlocksSpec
    (D : NTT.Domain R) (stage doneBlocks : Nat) (a : Array R) : Array R :=
  let oldCompleted : Nat := D.logN - (stage + 1)
  let newCompleted : Nat := D.logN - stage
  let blockSize : Nat := 2 ^ (stage + 1)
  Array.ofFn (fun i : D.Idx =>
    if i.1 / blockSize < doneBlocks then
      difMathValueAt D newCompleted a i.1
    else
      difMathValueAt D oldCompleted a i.1)

private def difMathPairsSpec
    (D : NTT.Domain R) (stage block donePairs : Nat) (a : Array R) : Array R :=
  let oldCompleted : Nat := D.logN - (stage + 1)
  let newCompleted : Nat := D.logN - stage
  let half : Nat := 2 ^ stage
  let blockSize : Nat := 2 ^ (stage + 1)
  Array.ofFn (fun i : D.Idx =>
    let bigBlock := i.1 / blockSize
    let pair := i.1 % half
    if bigBlock < block then
      difMathValueAt D newCompleted a i.1
    else if bigBlock = block then
      if pair < donePairs then
        difMathValueAt D newCompleted a i.1
      else
        difMathValueAt D oldCompleted a i.1
    else
      difMathValueAt D oldCompleted a i.1)

private theorem difMathStageSpec_zero (D : NTT.Domain R) (a : Array R) :
    difMathStageSpec D 0 a = loadNatural D a := by
  apply Array.ext
  · simp [difMathStageSpec, loadNatural]
  · intro i hi₁ hi₂
    have hi : i < 2 ^ D.logN := by
      simpa [difMathStageSpec, NTT.Domain.n] using hi₁
    have himod : i % 2 ^ D.logN = i := Nat.mod_eq_of_lt hi
    simp [difMathStageSpec, difMathValueAt, loadNatural, NTT.Domain.n, himod,
      NTT.Transform.bitRevNat]

private theorem difMathStageSpec_final (D : NTT.Domain R) (a : Array R) :
    difMathStageSpec D D.logN a =
      NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D a) := by
  apply Array.ext
  · simp [difMathStageSpec, NTT.Transform.bitRevPermute]
  · intro i hi₁ hi₂
    have hbr : NTT.Transform.bitRevNat D.logN i < D.n := by
      simpa [NTT.Domain.n] using NTT.Transform.bitRevNat_lt D.logN i
    rw [show (NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D a))[i] =
        (NTT.Forward.forwardSpec D a).getD (NTT.Transform.bitRevNat D.logN i) 0 by
      simp [NTT.Transform.bitRevPermute]]
    have hbr' : NTT.Transform.bitRevNat D.logN i < (NTT.Forward.forwardSpec D a).size := by
      simpa [NTT.Forward.forwardSpec] using hbr
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hbr']
    simp [difMathStageSpec, difMathValueAt, NTT.Forward.forwardSpec, NTT.Forward.nttAt,
      NTT.Domain.n, Nat.mod_one]
    rfl

private theorem dif_lower_div_block (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j) / 2 ^ (stage + 1) = block := by
  rw [Nat.mul_comm block (2 ^ (stage + 1))]
  rw [Nat.mul_add_div (Nat.two_pow_pos (stage + 1))]
  have hlt : j < 2 ^ (stage + 1) :=
    Nat.lt_trans hj (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self stage))
  rw [Nat.div_eq_of_lt hlt]
  simp

private theorem dif_upper_div_block (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j + 2 ^ stage) / 2 ^ (stage + 1) = block := by
  rw [show block * 2 ^ (stage + 1) + j + 2 ^ stage =
      block * 2 ^ (stage + 1) + (j + 2 ^ stage) by omega]
  rw [Nat.mul_comm block (2 ^ (stage + 1))]
  rw [Nat.mul_add_div (Nat.two_pow_pos (stage + 1))]
  have hlt : j + 2 ^ stage < 2 ^ (stage + 1) := by
    rw [pow_succ]
    omega
  rw [Nat.div_eq_of_lt hlt]
  simp

private theorem dif_lower_mod_half (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j) % 2 ^ stage = j := by
  rw [show block * 2 ^ (stage + 1) + j = (block * 2) * 2 ^ stage + j by
    rw [pow_succ]
    ring]
  rw [Nat.mul_add_mod_self_right]
  exact Nat.mod_eq_of_lt hj

private theorem dif_upper_mod_half (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j + 2 ^ stage) % 2 ^ stage = j := by
  rw [show block * 2 ^ (stage + 1) + j + 2 ^ stage =
      (block * 2 + 1) * 2 ^ stage + j by
    rw [pow_succ]
    ring]
  rw [Nat.mul_add_mod_self_right]
  exact Nat.mod_eq_of_lt hj

private theorem dif_lower_div_half (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j) / 2 ^ stage = block * 2 := by
  rw [show block * 2 ^ (stage + 1) + j = (block * 2) * 2 ^ stage + j by
    rw [pow_succ]
    ring]
  rw [Nat.mul_comm (block * 2) (2 ^ stage)]
  rw [Nat.mul_add_div (Nat.two_pow_pos stage)]
  rw [Nat.div_eq_of_lt hj]
  simp

private theorem dif_upper_div_half (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j + 2 ^ stage) / 2 ^ stage = block * 2 + 1 := by
  rw [show block * 2 ^ (stage + 1) + j + 2 ^ stage =
      (block * 2 + 1) * 2 ^ stage + j by
    rw [pow_succ]
    ring]
  rw [Nat.mul_comm (block * 2 + 1) (2 ^ stage)]
  rw [Nat.mul_add_div (Nat.two_pow_pos stage)]
  rw [Nat.div_eq_of_lt hj]

private theorem dif_lower_mod_blockSize (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j) % 2 ^ (stage + 1) = j := by
  rw [Nat.mul_add_mod_self_right block (2 ^ (stage + 1)) j]
  exact Nat.mod_eq_of_lt
    (Nat.lt_trans hj (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self stage)))

private theorem dif_upper_mod_blockSize (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j + 2 ^ stage) % 2 ^ (stage + 1) =
      j + 2 ^ stage := by
  rw [show block * 2 ^ (stage + 1) + j + 2 ^ stage =
      block * 2 ^ (stage + 1) + (j + 2 ^ stage) by omega]
  rw [Nat.mul_add_mod_self_right block (2 ^ (stage + 1)) (j + 2 ^ stage)]
  exact Nat.mod_eq_of_lt (by
    rw [pow_succ]
    omega)

private theorem omega_pow_domain_mul (D : NTT.Domain R) (k : Nat) :
    D.omega ^ (D.n * k) = 1 := by
  have h : D.omega ^ D.n = 1 := by
    simpa [NTT.Domain.n] using D.primitive.pow_eq_one
  rw [pow_mul, h, one_pow]

private theorem omega_pow_add_domain_mul (D : NTT.Domain R) (e k : Nat) :
    D.omega ^ (e + D.n * k) = D.omega ^ e := by
  rw [pow_add, omega_pow_domain_mul D k]
  simp

private theorem omega_pow_domain_half_eq_neg_one
    (D : NTT.Domain R) (hlog : 0 < D.logN) :
    D.omega ^ (D.n / 2) = -1 := by
  have hdiv : 2 ∣ D.n := by
    simpa [NTT.Domain.n] using Nat.pow_dvd_pow 2 (show 1 ≤ D.logN by omega)
  have hprod : D.n = D.n / 2 * 2 := by
    exact (Nat.div_mul_cancel hdiv).symm
  have hprim2 : IsPrimitiveRoot (D.omega ^ (D.n / 2)) 2 := by
    exact IsPrimitiveRoot.pow D.n_pos D.primitive hprod
  exact IsPrimitiveRoot.eq_neg_one_of_two_right hprim2

private theorem difMathBlocksSpec_zero
    (D : NTT.Domain R) (stage : Nat) (a : Array R) :
    difMathBlocksSpec D stage 0 a = difMathStageSpec D (D.logN - (stage + 1)) a := by
  apply Array.ext
  · simp [difMathBlocksSpec, difMathStageSpec]
  · intro i hi₁ hi₂
    simp [difMathBlocksSpec, difMathStageSpec]

private theorem difMathPairsSpec_zero
    (D : NTT.Domain R) (stage block : Nat) (a : Array R) :
    difMathPairsSpec D stage block 0 a = difMathBlocksSpec D stage block a := by
  apply Array.ext
  · simp [difMathPairsSpec, difMathBlocksSpec]
  · intro i hi₁ hi₂
    simp [difMathPairsSpec, difMathBlocksSpec]

private theorem difMathPairsSpec_half
    (D : NTT.Domain R) (stage block : Nat) (a : Array R) :
    difMathPairsSpec D stage block (2 ^ stage) a =
      difMathBlocksSpec D stage (block + 1) a := by
  apply Array.ext
  · simp [difMathPairsSpec, difMathBlocksSpec]
  · intro i hi₁ hi₂
    let bb : Nat := i / 2 ^ (stage + 1)
    let v1 : R := difMathValueAt D (D.logN - stage) a i
    let v0 : R := difMathValueAt D (D.logN - (stage + 1)) a i
    have hpair : i % 2 ^ stage < 2 ^ stage :=
      Nat.mod_lt _ (Nat.two_pow_pos stage)
    have hcase :
        (if bb < block then
          v1
        else if bb = block then
          if i % 2 ^ stage < 2 ^ stage then v1 else v0
        else
          v0)
          = (if bb < block + 1 then v1 else v0) := by
      by_cases hlt : bb < block
      · have hlt' : bb < block + 1 := Nat.lt_trans hlt (Nat.lt_succ_self _)
        rw [if_pos hlt, if_pos hlt']
      · by_cases hEq : bb = block
        · have hlt' : bb < block + 1 := by simp [hEq]
          rw [if_neg hlt, if_pos hEq, if_pos hpair, if_pos hlt']
        · have hnot : ¬bb < block + 1 := by
            exact not_lt_of_ge
              (Nat.succ_le_of_lt
                (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hEq)))
          rw [if_neg hlt, if_neg hEq, if_neg hnot]
    simpa [difMathPairsSpec, difMathBlocksSpec, bb, v1, v0] using hcase

private theorem difMathBlocksSpec_final
    (D : NTT.Domain R) (stage : Nat) (a : Array R) (hstage : stage < D.logN) :
    difMathBlocksSpec D stage (D.n / 2 ^ (stage + 1)) a =
      difMathStageSpec D (D.logN - stage) a := by
  apply Array.ext
  · simp [difMathBlocksSpec, difMathStageSpec]
  · intro i hi₁ hi₂
    let blockSize : Nat := 2 ^ (stage + 1)
    let bb : Nat := i / blockSize
    let v1 : R := difMathValueAt D (D.logN - stage) a i
    let v0 : R := difMathValueAt D (D.logN - (stage + 1)) a i
    have hi : i < D.n := by
      simpa [difMathStageSpec] using hi₂
    have hdiv : blockSize ∣ D.n := by
      dsimp [blockSize]
      simpa [NTT.Domain.n] using Nat.pow_dvd_pow 2 (Nat.succ_le_of_lt hstage)
    have hmul : blockSize * (D.n / blockSize) = D.n := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hdiv
    have hmul' : blockSize * (2 ^ D.logN / blockSize) = 2 ^ D.logN := by
      simpa [NTT.Domain.n] using hmul
    have hblock : bb < D.n / blockSize := by
      dsimp [bb]
      apply Nat.div_lt_of_lt_mul
      rw [hmul']
      simpa [NTT.Domain.n] using hi
    have hcase : (if bb < D.n / blockSize then v1 else v0) = v1 := by
      rw [if_pos hblock]
    simpa [difMathBlocksSpec, difMathStageSpec, blockSize, bb, v1, v0] using hcase

private theorem eq_lower_or_upper_of_block_pair
    (stage block j i : Nat)
    (hblock : i / 2 ^ (stage + 1) = block) (hpair : i % 2 ^ stage = j) :
    i = block * 2 ^ (stage + 1) + j ∨
      i = block * 2 ^ (stage + 1) + j + 2 ^ stage := by
  let half : Nat := 2 ^ stage
  let r : Nat := i % 2 ^ (stage + 1)
  have hblockSize : 2 ^ (stage + 1) = 2 * half := by
    simp [half, pow_succ, Nat.mul_comm]
  have hi_decomp : i = block * 2 ^ (stage + 1) + r := by
    calc
      i = 2 ^ (stage + 1) * (i / 2 ^ (stage + 1)) + i % 2 ^ (stage + 1) := by
        exact (Nat.div_add_mod i (2 ^ (stage + 1))).symm
      _ = i / 2 ^ (stage + 1) * 2 ^ (stage + 1) + i % 2 ^ (stage + 1) := by
        ring
      _ = block * 2 ^ (stage + 1) + r := by
        simp [hblock, r]
  have hr_lt : r < 2 * half := by
    simpa [r, hblockSize] using Nat.mod_lt i (Nat.two_pow_pos (stage + 1))
  have hhalf_dvd : half ∣ 2 ^ (stage + 1) := by
    rw [hblockSize]
    exact ⟨2, by ring⟩
  have hr_mod : r % half = j := by
    simpa [r, half, hpair] using (Nat.mod_mod_of_dvd i hhalf_dvd)
  have hr_decomp : r = (r / half) * half + j := by
    calc
      r = half * (r / half) + r % half := by
        exact (Nat.div_add_mod r half).symm
      _ = r / half * half + r % half := by
        ring
      _ = r / half * half + j := by rw [hr_mod]
  have hq_lt : r / half < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos stage)]
    simpa [half, Nat.mul_comm] using hr_lt
  interval_cases hq : r / half
  · left
    rw [hi_decomp, hr_decomp]
    simp
  · right
    rw [hi_decomp, hr_decomp]
    simp [half]
    omega

private theorem difMathPairsSpec_get_lower_current
    (D : NTT.Domain R) (stage block j : Nat) (a : Array R) (hj : j < 2 ^ stage)
    (hi : block * 2 ^ (stage + 1) + j < (difMathPairsSpec D stage block j a).size) :
    (difMathPairsSpec D stage block j a)[block * 2 ^ (stage + 1) + j] =
      difMathValueAt D (D.logN - (stage + 1)) a (block * 2 ^ (stage + 1) + j) := by
  simp [difMathPairsSpec, dif_lower_div_block stage block j hj,
    dif_lower_mod_half stage block j hj]

private theorem difMathPairsSpec_get_upper_current
    (D : NTT.Domain R) (stage block j : Nat) (a : Array R) (hj : j < 2 ^ stage)
    (hi : block * 2 ^ (stage + 1) + j + 2 ^ stage <
      (difMathPairsSpec D stage block j a).size) :
    (difMathPairsSpec D stage block j a)[block * 2 ^ (stage + 1) + j + 2 ^ stage] =
      difMathValueAt D (D.logN - (stage + 1)) a
        (block * 2 ^ (stage + 1) + j + 2 ^ stage) := by
  simp [difMathPairsSpec, dif_upper_div_block stage block j hj,
    dif_upper_mod_half stage block j hj]

private theorem difMathPairsSpec_get_lower_next
    (D : NTT.Domain R) (stage block j : Nat) (a : Array R) (hj : j < 2 ^ stage)
    (hi : block * 2 ^ (stage + 1) + j < (difMathPairsSpec D stage block (j + 1) a).size) :
    (difMathPairsSpec D stage block (j + 1) a)[block * 2 ^ (stage + 1) + j] =
      difMathValueAt D (D.logN - stage) a (block * 2 ^ (stage + 1) + j) := by
  simp [difMathPairsSpec, dif_lower_div_block stage block j hj,
    dif_lower_mod_half stage block j hj]

private theorem difMathPairsSpec_get_upper_next
    (D : NTT.Domain R) (stage block j : Nat) (a : Array R) (hj : j < 2 ^ stage)
    (hi : block * 2 ^ (stage + 1) + j + 2 ^ stage <
      (difMathPairsSpec D stage block (j + 1) a).size) :
    (difMathPairsSpec D stage block (j + 1) a)[block * 2 ^ (stage + 1) + j + 2 ^ stage] =
      difMathValueAt D (D.logN - stage) a
        (block * 2 ^ (stage + 1) + j + 2 ^ stage) := by
  simp [difMathPairsSpec, dif_upper_div_block stage block j hj,
    dif_upper_mod_half stage block j hj]

private theorem difMathPairsSpec_get_unchanged
    (D : NTT.Domain R) (stage block j : Nat) (a : Array R)
    {i : Nat}
    (hiOld : i < (difMathPairsSpec D stage block j a).size)
    (hiNew : i < (difMathPairsSpec D stage block (j + 1) a).size)
    (hneLower : block * 2 ^ (stage + 1) + j ≠ i)
    (hneUpper : block * 2 ^ (stage + 1) + j + 2 ^ stage ≠ i) :
    (difMathPairsSpec D stage block j a)[i] =
      (difMathPairsSpec D stage block (j + 1) a)[i] := by
  simp only [difMathPairsSpec, Array.getElem_ofFn]
  by_cases hltBlock : i / 2 ^ (stage + 1) < block
  · rw [if_pos hltBlock, if_pos hltBlock]
  · rw [if_neg hltBlock, if_neg hltBlock]
    by_cases hEqBlock : i / 2 ^ (stage + 1) = block
    · rw [if_pos hEqBlock, if_pos hEqBlock]
      by_cases hltPair : i % 2 ^ stage < j
      · rw [if_pos hltPair, if_pos (Nat.lt_trans hltPair (Nat.lt_succ_self j))]
      · have hgePair : j ≤ i % 2 ^ stage := Nat.le_of_not_lt hltPair
        rw [if_neg hltPair]
        by_cases hltPairNext : i % 2 ^ stage < j + 1
        · have hpair : i % 2 ^ stage = j := by omega
          rcases eq_lower_or_upper_of_block_pair stage block j i hEqBlock hpair with h | h
          · exact (hneLower h.symm).elim
          · exact (hneUpper h.symm).elim
        · rw [if_neg hltPairNext]
    · rw [if_neg hEqBlock, if_neg hEqBlock]

private theorem dif_upper_lt_of_lower_lt_domain
    (D : NTT.Domain R) (stage block j : Nat) (hstage : stage < D.logN) (hj : j < 2 ^ stage)
    (hlower : block * 2 ^ (stage + 1) + j < D.n) :
    block * 2 ^ (stage + 1) + j + 2 ^ stage < D.n := by
  let blocks : Nat := 2 ^ (D.logN - (stage + 1))
  let blockSize : Nat := 2 ^ (stage + 1)
  have hN : D.n = blocks * blockSize := by
    dsimp [NTT.Domain.n, blocks, blockSize]
    rw [← pow_add]
    congr 1
    omega
  have hlower' : block * blockSize + j < blocks * blockSize := by
    rw [← hN]
    simpa [blockSize] using hlower
  have hblock : block < blocks := by
    by_contra hnot
    have hle : blocks ≤ block := Nat.le_of_not_lt hnot
    have hmul : blocks * blockSize ≤ block * blockSize := Nat.mul_le_mul_right blockSize hle
    have hle' : blocks * blockSize ≤ block * blockSize + j :=
      Nat.le_trans hmul (Nat.le_add_right _ _)
    omega
  have hupperBlock :
      block * blockSize + j + 2 ^ stage < (block + 1) * blockSize := by
    calc
      block * blockSize + j + 2 ^ stage < block * blockSize + blockSize := by
        have hjBlock : j + 2 ^ stage < blockSize := by
          dsimp [blockSize]
          rw [pow_succ]
          omega
        omega
      _ = (block + 1) * blockSize := by ring
  have hnext : block + 1 ≤ blocks := Nat.succ_le_of_lt hblock
  have hnextMul : (block + 1) * blockSize ≤ blocks * blockSize :=
    Nat.mul_le_mul_right blockSize hnext
  rw [hN]
  exact Nat.lt_of_lt_of_le hupperBlock hnextMul

private theorem difMathValueAt_succ_lower
    (D : NTT.Domain R) (stage block j : Nat) (a : Array R)
    (hstage : stage < D.logN) (hj : j < 2 ^ stage) :
    difMathValueAt D (D.logN - stage) a (block * 2 ^ (stage + 1) + j) =
      difMathValueAt D (D.logN - (stage + 1)) a (block * 2 ^ (stage + 1) + j) +
        difMathValueAt D (D.logN - (stage + 1)) a
          (block * 2 ^ (stage + 1) + j + 2 ^ stage) := by
  have hsubNew : D.logN - (D.logN - stage) = stage := by omega
  have hsubOld : D.logN - (D.logN - (stage + 1)) = stage + 1 := by omega
  simp [difMathValueAt,
    hsubNew, hsubOld,
    dif_lower_div_half stage block j hj,
    dif_lower_mod_half stage block j hj,
    dif_lower_div_block stage block j hj,
    dif_lower_mod_blockSize stage block j hj,
    dif_upper_div_block stage block j hj,
    dif_upper_mod_blockSize stage block j hj]
  have hbits : D.logN - stage = (D.logN - (stage + 1)) + 1 := by
    omega
  rw [hbits]
  rw [← Fin.sum_univ_odd_even
    (n := D.logN - (stage + 1))
    (f := fun x =>
      a[j + x * 2 ^ stage]?.getD 0 *
        D.omega ^ (NTT.Transform.bitRevNat ((D.logN - (stage + 1)) + 1) (block * 2) *
          (j + x * 2 ^ stage)))]
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    rw [show block * 2 = 2 * block by ring]
    rw [NTT.Transform.bitRevNat_even]
    rw [show j + 2 * ↑x * 2 ^ stage = j + ↑x * 2 ^ (stage + 1) by
      rw [pow_succ]
      ring]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [show block * 2 = 2 * block by ring]
    rw [NTT.Transform.bitRevNat_even]
    rw [show j + (2 * ↑x + 1) * 2 ^ stage = j + 2 ^ stage + ↑x * 2 ^ (stage + 1) by
      rw [pow_succ]
      ring]

private theorem difMathValueAt_succ_upper
    (D : NTT.Domain R) (stage block j : Nat) (a : Array R)
    (hstage : stage < D.logN) (hj : j < 2 ^ stage) :
    difMathValueAt D (D.logN - stage) a
        (block * 2 ^ (stage + 1) + j + 2 ^ stage) =
      (D.omega ^ (D.n / 2 ^ (stage + 1))) ^ j *
        (difMathValueAt D (D.logN - (stage + 1)) a (block * 2 ^ (stage + 1) + j) -
          difMathValueAt D (D.logN - (stage + 1)) a
            (block * 2 ^ (stage + 1) + j + 2 ^ stage)) := by
  have hsubNew : D.logN - (D.logN - stage) = stage := by omega
  have hsubOld : D.logN - (D.logN - (stage + 1)) = stage + 1 := by omega
  simp [difMathValueAt,
    hsubNew, hsubOld,
    dif_upper_div_half stage block j hj,
    dif_upper_mod_half stage block j hj,
    dif_lower_div_block stage block j hj,
    dif_lower_mod_blockSize stage block j hj,
    dif_upper_div_block stage block j hj,
    dif_upper_mod_blockSize stage block j hj]
  have hbits : D.logN - stage = (D.logN - (stage + 1)) + 1 := by
    omega
  have hstride : D.n / 2 ^ (stage + 1) = 2 ^ (D.logN - (stage + 1)) := by
    rw [NTT.Domain.n]
    exact Nat.pow_div (Nat.succ_le_of_lt hstage) (by decide : 0 < 2)
  have hstride' : 2 ^ D.logN / 2 ^ (stage + 1) = 2 ^ (D.logN - (stage + 1)) := by
    simpa [NTT.Domain.n] using hstride
  rw [hstride']
  rw [← pow_mul]
  rw [hbits]
  rw [← Fin.sum_univ_odd_even
    (n := D.logN - (stage + 1))
    (f := fun x =>
      a[j + x * 2 ^ stage]?.getD 0 *
        D.omega ^ (NTT.Transform.bitRevNat ((D.logN - (stage + 1)) + 1) (block * 2 + 1) *
          (j + x * 2 ^ stage)))]
  rw [mul_sub]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [sub_eq_add_neg]
  have hN :
      D.n = 2 ^ (D.logN - (stage + 1)) * 2 ^ (stage + 1) := by
    rw [NTT.Domain.n, ← pow_add]
    congr 1
    omega
  have hHalf :
      D.n / 2 = 2 ^ (D.logN - (stage + 1)) * 2 ^ stage := by
    rw [NTT.Domain.n, Nat.pow_div (show 1 ≤ D.logN by omega) (by decide : 0 < 2)]
    rw [← pow_add]
    congr 1
    omega
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    rw [show block * 2 + 1 = 2 * block + 1 by ring]
    rw [NTT.Transform.bitRevNat_odd]
    rw [show j + 2 * ↑x * 2 ^ stage = j + ↑x * 2 ^ (stage + 1) by
      rw [pow_succ]
      ring]
    rw [show (2 ^ (D.logN - (stage + 1)) +
          NTT.Transform.bitRevNat (D.logN - (stage + 1)) block) *
          (j + ↑x * 2 ^ (stage + 1)) =
        2 ^ (D.logN - (stage + 1)) * j +
          NTT.Transform.bitRevNat (D.logN - (stage + 1)) block *
            (j + ↑x * 2 ^ (stage + 1)) +
          D.n * ↑x by
      rw [hN]
      ring]
    rw [omega_pow_add_domain_mul]
    rw [pow_add]
    ring
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show block * 2 + 1 = 2 * block + 1 by ring]
    rw [NTT.Transform.bitRevNat_odd]
    rw [show j + (2 * ↑x + 1) * 2 ^ stage =
        j + 2 ^ stage + ↑x * 2 ^ (stage + 1) by
      rw [pow_succ]
      ring]
    rw [show (2 ^ (D.logN - (stage + 1)) +
          NTT.Transform.bitRevNat (D.logN - (stage + 1)) block) *
          (j + 2 ^ stage + ↑x * 2 ^ (stage + 1)) =
        (D.n / 2 +
          (2 ^ (D.logN - (stage + 1)) * j +
            NTT.Transform.bitRevNat (D.logN - (stage + 1)) block *
              (j + 2 ^ stage + ↑x * 2 ^ (stage + 1)))) +
          D.n * ↑x by
      rw [hHalf, hN]
      ring]
    rw [omega_pow_add_domain_mul]
    rw [show D.omega ^ (D.n / 2 +
          (2 ^ (D.logN - (stage + 1)) * j +
            NTT.Transform.bitRevNat (D.logN - (stage + 1)) block *
              (j + 2 ^ stage + ↑x * 2 ^ (stage + 1)))) =
        -D.omega ^
          (2 ^ (D.logN - (stage + 1)) * j +
            NTT.Transform.bitRevNat (D.logN - (stage + 1)) block *
              (j + 2 ^ stage + ↑x * 2 ^ (stage + 1))) by
      rw [pow_add, omega_pow_domain_half_eq_neg_one D (by omega)]
      ring]
    rw [pow_add]
    ring

private theorem butterflyDIFPairStep_difMathPairsSpec_succ
    (D : NTT.Domain R) (stage block j : Nat) (twiddles : Array R) (a : Array R)
    (hstage : stage < D.logN) (hj : j < 2 ^ stage)
    (htw : twiddles.getD j 0 = (D.omega ^ (D.n / 2 ^ (stage + 1))) ^ j) :
    let lower := block * 2 ^ (stage + 1) + j
    let upper := lower + 2 ^ stage
    let acc := difMathPairsSpec D stage block j a
    let u := acc.getD lower 0
    let v := acc.getD upper 0
    (acc.set! lower (u + v)).set! upper (twiddles.getD j 0 * (u - v)) =
      difMathPairsSpec D stage block (j + 1) a := by
  dsimp only
  apply Array.ext
  · simp [difMathPairsSpec, Array.set!, Array.size_setIfInBounds]
  · intro i hi₁ hi₂
    simp only [Array.set!, Array.size_setIfInBounds] at hi₁
    simp [Array.set!, Array.getElem_setIfInBounds, hi₁]
    by_cases hUpper : block * 2 ^ (stage + 1) + j + 2 ^ stage = i
    · rw [if_pos hUpper]
      subst i
      have hUpperOld :
          block * 2 ^ (stage + 1) + j + 2 ^ stage <
            (difMathPairsSpec D stage block j a).size := by
        simpa [difMathPairsSpec] using hi₁
      have hLowerOld :
          block * 2 ^ (stage + 1) + j <
            (difMathPairsSpec D stage block j a).size := by
        simpa [difMathPairsSpec] using (show
          block * 2 ^ (stage + 1) + j < D.n by
            have h : block * 2 ^ (stage + 1) + j + 2 ^ stage < D.n := by
              simpa [difMathPairsSpec] using hi₁
            omega)
      rw [Array.getElem?_eq_getElem hLowerOld]
      rw [Array.getElem?_eq_getElem hUpperOld]
      simp only [Option.getD_some]
      rw [difMathPairsSpec_get_lower_current D stage block j a hj hLowerOld]
      rw [difMathPairsSpec_get_upper_current D stage block j a hj hUpperOld]
      rw [difMathPairsSpec_get_upper_next D stage block j a hj hi₂]
      rw [← (Array.getD_eq_getD_getElem? (xs := twiddles) (i := j) (d := 0)), htw]
      exact (difMathValueAt_succ_upper D stage block j a hstage hj).symm
    · rw [if_neg hUpper]
      by_cases hLower : block * 2 ^ (stage + 1) + j = i
      · rw [if_pos hLower]
        subst i
        have hLowerDomain : block * 2 ^ (stage + 1) + j < D.n := by
          simpa [difMathPairsSpec] using hi₁
        have hUpperDomain :
            block * 2 ^ (stage + 1) + j + 2 ^ stage < D.n :=
          dif_upper_lt_of_lower_lt_domain D stage block j hstage hj hLowerDomain
        have hUpperOld :
            block * 2 ^ (stage + 1) + j + 2 ^ stage <
              (difMathPairsSpec D stage block j a).size := by
          simpa [difMathPairsSpec] using hUpperDomain
        rw [Array.getElem?_eq_getElem hi₁]
        rw [Array.getElem?_eq_getElem hUpperOld]
        simp only [Option.getD_some]
        rw [difMathPairsSpec_get_lower_current D stage block j a hj hi₁]
        rw [difMathPairsSpec_get_upper_current D stage block j a hj hUpperOld]
        rw [difMathPairsSpec_get_lower_next D stage block j a hj hi₂]
        exact (difMathValueAt_succ_lower D stage block j a hstage hj).symm
      · rw [if_neg hLower]
        exact difMathPairsSpec_get_unchanged D stage block j a hi₁ hi₂ hLower hUpper

private theorem butterflyDIFInner_difMathPairsSpec_final
    (D : NTT.Domain R) (stage block : Nat) (twiddles : Array R) (a : Array R)
    (hstage : stage < D.logN)
    (htw : ∀ j, j < 2 ^ stage →
      twiddles.getD j 0 = (D.omega ^ (D.n / 2 ^ (stage + 1))) ^ j) :
    ∀ n j,
      2 ^ stage = j + n →
        butterflyDIFInner twiddles (2 ^ stage) j
            (block * 2 ^ (stage + 1) + j)
            (block * 2 ^ (stage + 1) + j + 2 ^ stage)
            (difMathPairsSpec D stage block j a) =
          difMathPairsSpec D stage block (2 ^ stage) a
  | 0, j, hlimit => by
      simp [butterflyDIFInner, hlimit]
  | n + 1, j, hlimit => by
      have hj : j < 2 ^ stage := by omega
      have htail : 2 ^ stage = j + 1 + n := by omega
      have hstep := butterflyDIFPairStep_difMathPairsSpec_succ
        D stage block j twiddles a hstage hj (htw j hj)
      rw [butterflyDIFInner]
      simp only [hj, ↓reduceIte]
      rw [show block * 2 ^ (stage + 1) + j + 1 =
          block * 2 ^ (stage + 1) + (j + 1) by omega]
      rw [show block * 2 ^ (stage + 1) + j + 2 ^ stage + 1 =
          block * 2 ^ (stage + 1) + (j + 1) + 2 ^ stage by omega]
      rw [hstep]
      exact butterflyDIFInner_difMathPairsSpec_final D stage block twiddles a hstage htw
        n (j + 1) htail

private theorem butterflyDIFBlocks_difMathBlocksSpec_final
    (D : NTT.Domain R) (stage : Nat) (twiddles : Array R) (a : Array R)
    (hstage : stage < D.logN)
    (htw : ∀ j, j < 2 ^ stage →
      twiddles.getD j 0 = (D.omega ^ (D.n / 2 ^ (stage + 1))) ^ j) :
    ∀ n blocks block,
      blocks = block + n →
        butterflyDIFBlocks twiddles (2 ^ (stage + 1)) (2 ^ stage) blocks block
            (difMathBlocksSpec D stage block a) =
          difMathBlocksSpec D stage blocks a
  | 0, blocks, block, hblocks => by
      simp [butterflyDIFBlocks, hblocks]
  | n + 1, blocks, block, hblocks => by
      have hblock : block < blocks := by omega
      have htail : blocks = block + 1 + n := by omega
      have hinner := butterflyDIFInner_difMathPairsSpec_final D stage block twiddles a hstage htw
        (2 ^ stage) 0 (by simp)
      rw [butterflyDIFBlocks]
      simp only [hblock, ↓reduceIte]
      rw [show block * 2 ^ (stage + 1) + 2 ^ stage =
          block * 2 ^ (stage + 1) + 0 + 2 ^ stage by omega]
      rw [difMathPairsSpec_zero D stage block a] at hinner
      have hinner' :
          butterflyDIFInner twiddles (2 ^ stage) 0 (block * 2 ^ (stage + 1))
              (block * 2 ^ (stage + 1) + 0 + 2 ^ stage)
              (difMathBlocksSpec D stage block a) =
            difMathPairsSpec D stage block (2 ^ stage) a := by
        simpa using hinner
      rw [hinner']
      rw [difMathPairsSpec_half]
      exact butterflyDIFBlocks_difMathBlocksSpec_final D stage twiddles a hstage htw
        n blocks (block + 1) htail

private theorem butterflyStageDIFWithTwiddles_difMathStageSpec_succ
    (D : NTT.Domain R) (stage : Nat) (twiddles : Array R) (a : Array R)
    (hstage : stage < D.logN)
    (htw : ∀ j, j < 2 ^ stage →
      twiddles.getD j 0 = (D.omega ^ (D.n / 2 ^ (stage + 1))) ^ j) :
    butterflyStageDIFWithTwiddles D stage twiddles
        (difMathStageSpec D (D.logN - (stage + 1)) a) =
      difMathStageSpec D (D.logN - stage) a := by
  calc
    butterflyStageDIFWithTwiddles D stage twiddles
        (difMathStageSpec D (D.logN - (stage + 1)) a) =
        butterflyDIFBlocks twiddles (2 ^ (stage + 1)) (2 ^ stage)
          (D.n / 2 ^ (stage + 1)) 0 (difMathBlocksSpec D stage 0 a) := by
          simp [butterflyStageDIFWithTwiddles, difMathBlocksSpec_zero]
    _ = difMathBlocksSpec D stage (D.n / 2 ^ (stage + 1)) a := by
          exact butterflyDIFBlocks_difMathBlocksSpec_final D stage twiddles a hstage htw
            (D.n / 2 ^ (stage + 1)) (D.n / 2 ^ (stage + 1)) 0 (by simp)
    _ = difMathStageSpec D (D.logN - stage) a := by
          exact difMathBlocksSpec_final D stage a hstage

private theorem runStagesDIFWithTwiddles_eq_difMathStageSpec
    (D : NTT.Domain R) (a : Array R) :
    runStagesDIFWithTwiddles D (twiddleTable D) (loadNatural D a) =
      difMathStageSpec D D.logN a := by
  have hloop :
      ∀ n, n ≤ D.logN →
        List.foldl
          (fun acc pass =>
            butterflyStageDIFWithTwiddles D (D.logN - pass - 1)
              ((twiddleTable D).getD (D.logN - pass - 1) #[]) acc)
          (loadNatural D a) (List.range n) =
            difMathStageSpec D n a := by
    intro n hn
    induction n with
    | zero =>
        rw [difMathStageSpec_zero]
        simp
    | succ n ih =>
        have hnle : n ≤ D.logN := Nat.le_of_succ_le hn
        have hnlt : n < D.logN := Nat.lt_of_succ_le hn
        have hstage : D.logN - n - 1 < D.logN := by omega
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ih hnle]
        convert butterflyStageDIFWithTwiddles_difMathStageSpec_succ D
          (D.logN - n - 1) ((twiddleTable D).getD (D.logN - n - 1) #[]) a
          hstage ?_ using 1
        · rw [show D.logN - (D.logN - n - 1 + 1) = n by omega]
        · rw [show D.logN - (D.logN - n - 1) = n + 1 by omega]
        · intro j hj
          rw [twiddleTable_getD_eq_twiddlePowers D (D.logN - n - 1) hstage]
          exact twiddlePowers_getD_eq_pow D (D.logN - n - 1) j hj
  simpa [runStagesDIFWithTwiddles, List.range_eq_range'] using hloop D.logN le_rfl

private def ditButterfly (w : R) (i0 i1 : Nat) (acc : Array R) : Array R :=
  let u := acc.getD i0 0
  let t := w * acc.getD i1 0
  (acc.set! i0 (u + t)).set! i1 (u - t)

private theorem getD_ditButterfly_of_ne
    (w : R) (i0 i1 k : Nat) (acc : Array R) (hk0 : k ≠ i0) (hk1 : k ≠ i1) :
    (ditButterfly w i0 i1 acc).getD k 0 = acc.getD k 0 := by
  have h0 : i0 ≠ k := fun h => hk0 h.symm
  have h1 : i1 ≠ k := fun h => hk1 h.symm
  unfold ditButterfly
  simp only [Array.set!, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_setIfInBounds]
  simp [h1]
  rw [Array.getElem?_setIfInBounds]
  simp [h0]

private theorem ditButterfly_comm
    (acc : Array R) (w v : R) (i0 i1 j0 j1 : Nat)
    (h00 : i0 ≠ j0) (h01 : i0 ≠ j1) (h10 : i1 ≠ j0) (h11 : i1 ≠ j1) :
    ditButterfly w i0 i1 (ditButterfly v j0 j1 acc) =
      ditButterfly v j0 j1 (ditButterfly w i0 i1 acc) := by
  change
    (let u := (ditButterfly v j0 j1 acc).getD i0 0
     let t := w * (ditButterfly v j0 j1 acc).getD i1 0
     (((ditButterfly v j0 j1 acc).set! i0 (u + t)).set! i1 (u - t))) =
      (let u := (ditButterfly w i0 i1 acc).getD j0 0
       let t := v * (ditButterfly w i0 i1 acc).getD j1 0
       (((ditButterfly w i0 i1 acc).set! j0 (u + t)).set! j1 (u - t)))
  rw [getD_ditButterfly_of_ne v j0 j1 i0 acc h00 h01]
  rw [getD_ditButterfly_of_ne v j0 j1 i1 acc h10 h11]
  rw [getD_ditButterfly_of_ne w i0 i1 j0 acc h00.symm h10.symm]
  rw [getD_ditButterfly_of_ne w i0 i1 j1 acc h01.symm h11.symm]
  unfold ditButterfly
  simp only [Array.set!]
  rw [Array.setIfInBounds_comm _ _ h01.symm]
  rw [Array.setIfInBounds_comm _ _ h00.symm]
  rw [Array.setIfInBounds_comm _ _ h11.symm]
  rw [Array.setIfInBounds_comm _ _ h10.symm]

private theorem butterflyDITInner_eq_foldl_dit (twiddles : Array R) :
    ∀ n j i0 i1 (acc : Array R),
      butterflyDITInner twiddles (j + n) j i0 i1 acc =
        List.foldl
          (fun acc t => ditButterfly (twiddles.getD (j + t) 0) (i0 + t) (i1 + t) acc)
          acc (List.range' 0 n)
  | 0, j, i0, i1, acc => by
      simp [butterflyDITInner]
  | n + 1, j, i0, i1, acc => by
      have hj : j < j + (n + 1) := by omega
      have ih := butterflyDITInner_eq_foldl_dit twiddles n (j + 1) (i0 + 1) (i1 + 1)
        (ditButterfly (twiddles.getD j 0) i0 i1 acc)
      have hshift :
          List.foldl
              (fun acc t =>
                ditButterfly (twiddles.getD (j + 1 + t) 0) (i0 + 1 + t)
                  (i1 + 1 + t) acc)
              (ditButterfly (twiddles.getD j 0) i0 i1 acc) (List.range' 0 n) =
            List.foldl
              (fun acc t => ditButterfly (twiddles.getD (j + t) 0) (i0 + t) (i1 + t) acc)
              (ditButterfly (twiddles.getD j 0) i0 i1 acc) (List.range' 1 n) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (foldl_range'_succ_shift
            (fun t acc => ditButterfly (twiddles.getD (j + t) 0) (i0 + t) (i1 + t) acc)
            n 0 (ditButterfly (twiddles.getD j 0) i0 i1 acc))
      rw [butterflyDITInner]
      simp only [hj, ↓reduceIte]
      simpa [List.range'_succ, ditButterfly, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih.trans hshift

private theorem butterflyDITInner_comm
    (twiddlesA twiddlesB : Array R) (limitA limitB baseA halfA baseB halfB : Nat)
    (hcomm :
      ∀ i, i < limitA → ∀ j, j < limitB →
        baseA + i ≠ baseB + j ∧
        baseA + i ≠ baseB + halfB + j ∧
        baseA + halfA + i ≠ baseB + j ∧
        baseA + halfA + i ≠ baseB + halfB + j) :
    ∀ acc : Array R,
      butterflyDITInner twiddlesA limitA 0 baseA (baseA + halfA)
          (butterflyDITInner twiddlesB limitB 0 baseB (baseB + halfB) acc) =
        butterflyDITInner twiddlesB limitB 0 baseB (baseB + halfB)
          (butterflyDITInner twiddlesA limitA 0 baseA (baseA + halfA) acc) := by
  intro acc
  let foldA : Array R → Array R :=
    fun acc =>
      List.foldl
        (fun acc i => ditButterfly (twiddlesA.getD i 0) (baseA + i)
          (baseA + halfA + i) acc)
        acc (List.range limitA)
  let foldB : Array R → Array R :=
    fun acc =>
      List.foldl
        (fun acc j => ditButterfly (twiddlesB.getD j 0) (baseB + j)
          (baseB + halfB + j) acc)
        acc (List.range limitB)
  have hA (acc' : Array R) :
      butterflyDITInner twiddlesA limitA 0 baseA (baseA + halfA) acc' = foldA acc' := by
    simpa [foldA, List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (butterflyDITInner_eq_foldl_dit twiddlesA limitA 0 baseA (baseA + halfA) acc')
  have hB (acc' : Array R) :
      butterflyDITInner twiddlesB limitB 0 baseB (baseB + halfB) acc' = foldB acc' := by
    simpa [foldB, List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (butterflyDITInner_eq_foldl_dit twiddlesB limitB 0 baseB (baseB + halfB) acc')
  calc
    butterflyDITInner twiddlesA limitA 0 baseA (baseA + halfA)
        (butterflyDITInner twiddlesB limitB 0 baseB (baseB + halfB) acc) =
        foldA (foldB acc) := by
          rw [hB, hA]
    _ = List.foldl
          (fun acc j => ditButterfly (twiddlesB.getD j 0) (baseB + j)
            (baseB + halfB + j) acc)
          (List.foldl
            (fun acc i => ditButterfly (twiddlesA.getD i 0) (baseA + i)
              (baseA + halfA + i) acc)
            acc (List.range limitA))
          (List.range limitB) := by
          apply foldl_commute_foldl
          intro i j hi hj acc
          rcases hcomm i hi j hj with ⟨h00, h01, h10, h11⟩
          exact (ditButterfly_comm acc (twiddlesA.getD i 0) (twiddlesB.getD j 0)
            (baseA + i) (baseA + halfA + i) (baseB + j) (baseB + halfB + j)
            h00 h01 h10 h11).symm
    _ = butterflyDITInner twiddlesB limitB 0 baseB (baseB + halfB)
          (butterflyDITInner twiddlesA limitA 0 baseA (baseA + halfA) acc) := by
          rw [hA, hB]

private theorem butterflyDITBlocks_eq_foldl_inner
    (twiddles : Array R) (blockSize half blocks : Nat) :
    ∀ n block (acc : Array R),
      blocks = block + n →
      butterflyDITBlocks twiddles blockSize half blocks block acc =
        List.foldl
          (fun acc block =>
            butterflyDITInner twiddles half 0 (block * blockSize) (block * blockSize + half)
              acc)
          acc (List.range' block n)
  | 0, block, acc, hblocks => by
      have hnot : ¬block < blocks := by omega
      simp [butterflyDITBlocks, hnot]
  | n + 1, block, acc, hblocks => by
      have hblock : block < blocks := by omega
      have htail : blocks = block + 1 + n := by omega
      have ih := butterflyDITBlocks_eq_foldl_inner twiddles blockSize half blocks
        n (block + 1)
          (butterflyDITInner twiddles half 0 (block * blockSize) (block * blockSize + half)
            acc)
        htail
      rw [butterflyDITBlocks]
      simp only [hblock, ↓reduceIte]
      simpa [List.range'_succ] using ih

private def radix4Cell
    (wLow wHigh0 wHigh1 : R) (i0 i1 i2 i3 : Nat) (acc : Array R) : Array R :=
  let x0 := acc.getD i0 0
  let x1 := acc.getD i1 0
  let x2 := acc.getD i2 0
  let x3 := acc.getD i3 0
  let t1 := wLow * x1
  let t3 := wLow * x3
  let a0 := x0 + t1
  let a1 := x0 - t1
  let a2 := x2 + t3
  let a3 := x2 - t3
  let u2 := wHigh0 * a2
  let u3 := wHigh1 * a3
  (((acc.set! i0 (a0 + u2)).set! i1 (a1 + u3)).set! i2 (a0 - u2)).set! i3 (a1 - u3)

@[simp] private theorem size_radix4Cell
    (wLow wHigh0 wHigh1 : R) (i0 i1 i2 i3 : Nat) (acc : Array R) :
    (radix4Cell wLow wHigh0 wHigh1 i0 i1 i2 i3 acc).size = acc.size := by
  simp [radix4Cell, Array.set!, Array.size_setIfInBounds]

private theorem setIfInBounds_discard_four {α : Type*}
    (acc : Array α) (i0 i1 i2 i3 : Nat) (v0 v1 v2 v3 w0 w1 w2 w3 : α)
    (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h03 : i0 ≠ i3)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3) :
    (((((((acc.setIfInBounds i0 v0).setIfInBounds i1 v1).setIfInBounds i2 v2).setIfInBounds
          i3 v3).setIfInBounds i0 w0).setIfInBounds i2 w1).setIfInBounds i1
        w2).setIfInBounds i3 w3 =
      (((acc.setIfInBounds i0 w0).setIfInBounds i1 w2).setIfInBounds i2 w1).setIfInBounds
        i3 w3 := by
  rw [Array.setIfInBounds_comm v3 w0 h03.symm]
  rw [Array.setIfInBounds_comm v2 w0 h02.symm]
  rw [Array.setIfInBounds_comm v1 w0 h01.symm]
  rw [Array.setIfInBounds_setIfInBounds]
  rw [Array.setIfInBounds_comm v3 w1 h23.symm]
  rw [Array.setIfInBounds_setIfInBounds]
  rw [Array.setIfInBounds_comm v3 w2 h13.symm]
  rw [Array.setIfInBounds_comm w1 w2 h12.symm]
  rw [Array.setIfInBounds_setIfInBounds]
  rw [Array.setIfInBounds_setIfInBounds]

private theorem radix4Cell_eq_two_stage_cells
    (wLow wHigh0 wHigh1 : R) (i0 i1 i2 i3 : Nat) (acc : Array R)
    (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h03 : i0 ≠ i3)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3)
    (hi0 : i0 < acc.size) (hi1 : i1 < acc.size)
    (hi2 : i2 < acc.size) (hi3 : i3 < acc.size) :
    ditButterfly wHigh1 i1 i3
        (ditButterfly wHigh0 i0 i2
          (ditButterfly wLow i2 i3 (ditButterfly wLow i0 i1 acc))) =
      radix4Cell wLow wHigh0 wHigh1 i0 i1 i2 i3 acc := by
  unfold ditButterfly radix4Cell
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
    Array.size_setIfInBounds]
  simp [hi0, hi1, hi2, hi3, h01, h01.symm, h02, h02.symm, h03, h03.symm,
    h12, h12.symm, h13, h13.symm, h23, h23.symm]
  exact setIfInBounds_discard_four acc i0 i1 i2 i3 _ _ _ _ _ _ _ _
    h01 h02 h03 h12 h13 h23

private theorem butterflyDITRadix4Inner_eq_foldl_cell
    (twiddlesLow twiddlesHigh : Array R) :
    ∀ n j i0 i1 i2 i3 (acc : Array R),
      butterflyDITRadix4Inner twiddlesLow twiddlesHigh (j + n) j i0 i1 i2 i3 acc =
        List.foldl
          (fun acc t =>
            radix4Cell (twiddlesLow.getD (j + t) 0) (twiddlesHigh.getD (j + t) 0)
              (twiddlesHigh.getD (j + t + (j + n)) 0) (i0 + t) (i1 + t) (i2 + t)
              (i3 + t) acc)
          acc (List.range' 0 n)
  | 0, j, _i0, _i1, _i2, _i3, _acc => by
      simp [butterflyDITRadix4Inner]
  | n + 1, j, i0, i1, i2, i3, acc => by
      have hj : j < j + (n + 1) := by omega
      have ih := butterflyDITRadix4Inner_eq_foldl_cell twiddlesLow twiddlesHigh n
        (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1)
        (radix4Cell (twiddlesLow.getD j 0) (twiddlesHigh.getD j 0)
          (twiddlesHigh.getD (j + (j + (n + 1))) 0) i0 i1 i2 i3 acc)
      have hshift :
          List.foldl
              (fun acc t =>
                radix4Cell (twiddlesLow.getD (j + 1 + t) 0)
                  (twiddlesHigh.getD (j + 1 + t) 0)
                  (twiddlesHigh.getD (j + 1 + t + (j + 1 + n)) 0) (i0 + 1 + t)
                  (i1 + 1 + t) (i2 + 1 + t) (i3 + 1 + t) acc)
              (radix4Cell (twiddlesLow.getD j 0) (twiddlesHigh.getD j 0)
                (twiddlesHigh.getD (j + (j + (n + 1))) 0) i0 i1 i2 i3 acc)
              (List.range' 0 n) =
            List.foldl
              (fun acc t =>
                radix4Cell (twiddlesLow.getD (j + t) 0) (twiddlesHigh.getD (j + t) 0)
                  (twiddlesHigh.getD (j + t + (j + (n + 1))) 0) (i0 + t) (i1 + t)
                  (i2 + t) (i3 + t) acc)
              (radix4Cell (twiddlesLow.getD j 0) (twiddlesHigh.getD j 0)
                (twiddlesHigh.getD (j + (j + (n + 1))) 0) i0 i1 i2 i3 acc)
              (List.range' 1 n) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (foldl_range'_succ_shift
            (fun t acc =>
              radix4Cell (twiddlesLow.getD (j + t) 0) (twiddlesHigh.getD (j + t) 0)
                (twiddlesHigh.getD (j + t + (j + (n + 1))) 0) (i0 + t) (i1 + t)
                (i2 + t) (i3 + t) acc)
            n 0
            (radix4Cell (twiddlesLow.getD j 0) (twiddlesHigh.getD j 0)
              (twiddlesHigh.getD (j + (j + (n + 1))) 0) i0 i1 i2 i3 acc))
      rw [butterflyDITRadix4Inner]
      simp only [hj, ↓reduceIte]
      simpa [List.range'_succ, radix4Cell, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih.trans hshift

private theorem butterflyDITRadix4Blocks_eq_foldl_inner
    (twiddlesLow twiddlesHigh : Array R) (blockSize quarter blocks : Nat) :
    ∀ n block (acc : Array R),
      blocks = block + n →
      butterflyDITRadix4Blocks twiddlesLow twiddlesHigh blockSize quarter blocks block acc =
        List.foldl
          (fun acc block =>
            butterflyDITRadix4Inner twiddlesLow twiddlesHigh quarter 0 (block * blockSize)
              (block * blockSize + quarter) (block * blockSize + 2 * quarter)
              (block * blockSize + 3 * quarter) acc)
          acc (List.range' block n)
  | 0, block, _acc, hblocks => by
      have hnot : ¬block < blocks := by omega
      simp [butterflyDITRadix4Blocks, hnot]
  | n + 1, block, acc, hblocks => by
      have hblock : block < blocks := by omega
      have htail : blocks = block + 1 + n := by omega
      have ih := butterflyDITRadix4Blocks_eq_foldl_inner twiddlesLow twiddlesHigh blockSize
        quarter blocks n (block + 1)
        (butterflyDITRadix4Inner twiddlesLow twiddlesHigh quarter 0 (block * blockSize)
          (block * blockSize + quarter) (block * blockSize + 2 * quarter)
          (block * blockSize + 3 * quarter) acc)
        htail
      rw [butterflyDITRadix4Blocks]
      simp only [hblock, ↓reduceIte]
      simpa [List.range'_succ] using ih

set_option maxHeartbeats 800000 in
private theorem butterflyDITRadix4Inner_eq_two_dit_inners
    (twiddlesLow twiddlesHigh : Array R) (q base : Nat) (acc : Array R)
    (hq : 0 < q) (hbound : base + 4 * q ≤ acc.size) :
    butterflyDITRadix4Inner twiddlesLow twiddlesHigh q 0 base (base + q) (base + 2 * q)
        (base + 3 * q) acc =
      butterflyDITInner twiddlesHigh (2 * q) 0 base (base + 2 * q)
        (butterflyDITInner twiddlesLow q 0 (base + 2 * q) (base + 3 * q)
          (butterflyDITInner twiddlesLow q 0 base (base + q) acc)) := by
  calc
    butterflyDITRadix4Inner twiddlesLow twiddlesHigh q 0 base (base + q)
        (base + 2 * q) (base + 3 * q) acc =
        List.foldl
          (fun acc j =>
            radix4Cell (twiddlesLow.getD j 0) (twiddlesHigh.getD j 0)
              (twiddlesHigh.getD (j + q) 0) (base + j) (base + q + j)
              (base + 2 * q + j) (base + 3 * q + j) acc)
          acc (List.range q) := by
          simpa [List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (butterflyDITRadix4Inner_eq_foldl_cell twiddlesLow twiddlesHigh q 0 base
              (base + q) (base + 2 * q) (base + 3 * q) acc)
    _ = List.foldl
          (fun acc j =>
            ditButterfly (twiddlesHigh.getD (j + q) 0) (base + q + j)
              (base + 3 * q + j)
              (ditButterfly (twiddlesHigh.getD j 0) (base + j) (base + 2 * q + j)
                (ditButterfly (twiddlesLow.getD j 0) (base + 2 * q + j)
                  (base + 3 * q + j)
                  (ditButterfly (twiddlesLow.getD j 0) (base + j) (base + q + j) acc))))
          acc (List.range q) := by
          apply foldl_range_congr_inv (p := fun b : Array R => b.size = acc.size)
          · intro j hj acc hacc
            exact (radix4Cell_eq_two_stage_cells (twiddlesLow.getD j 0)
                (twiddlesHigh.getD j 0) (twiddlesHigh.getD (j + q) 0) (base + j)
                (base + q + j) (base + 2 * q + j) (base + 3 * q + j) acc
                (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                (by nlinarith [hacc, hbound]) (by nlinarith [hacc, hbound])
                (by nlinarith [hacc, hbound]) (by nlinarith [hacc, hbound])).symm
          · intro j hj acc hacc
            simp [hacc]
          · rfl
    _ = List.foldl
          (fun acc j =>
            ditButterfly (twiddlesHigh.getD (j + q) 0) (base + q + j)
              (base + 3 * q + j) acc)
          (List.foldl
            (fun acc j => ditButterfly (twiddlesHigh.getD j 0) (base + j)
              (base + 2 * q + j) acc)
            (List.foldl
              (fun acc j => ditButterfly (twiddlesLow.getD j 0) (base + 2 * q + j)
                (base + 3 * q + j) acc)
              (List.foldl
                (fun acc j => ditButterfly (twiddlesLow.getD j 0) (base + j)
                  (base + q + j) acc)
                acc (List.range q)) (List.range q))
            (List.range q))
          (List.range q) := by
          apply foldl_quad
          · intro i j hij hj x
            apply ditButterfly_comm <;> omega
          · intro i j hij hj x
            apply ditButterfly_comm <;> omega
          · intro i j hij hj x
            apply ditButterfly_comm <;> omega
          · intro i j hij hj x
            apply ditButterfly_comm <;> omega
          · intro i j hij hj x
            apply ditButterfly_comm <;> omega
          · intro i j hij hj x
            apply ditButterfly_comm <;> omega
    _ = butterflyDITInner twiddlesHigh (2 * q) 0 base (base + 2 * q)
          (butterflyDITInner twiddlesLow q 0 (base + 2 * q) (base + 3 * q)
            (butterflyDITInner twiddlesLow q 0 base (base + q) acc)) := by
          symm
          have hlow₁ :
              butterflyDITInner twiddlesLow q 0 base (base + q) acc =
                List.foldl
                  (fun acc j => ditButterfly (twiddlesLow.getD j 0) (base + j)
                    (base + q + j) acc)
                  acc (List.range q) := by
            simpa [List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using (butterflyDITInner_eq_foldl_dit twiddlesLow q 0 base (base + q) acc)
          have hlow₂ (acc' : Array R) :
              butterflyDITInner twiddlesLow q 0 (base + 2 * q) (base + 3 * q) acc' =
                List.foldl
                  (fun acc j => ditButterfly (twiddlesLow.getD j 0) (base + 2 * q + j)
                    (base + 3 * q + j) acc)
                  acc' (List.range q) := by
            simpa [List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using (butterflyDITInner_eq_foldl_dit twiddlesLow q 0 (base + 2 * q)
                (base + 3 * q) acc')
          have hhigh (acc' : Array R) :
              butterflyDITInner twiddlesHigh (2 * q) 0 base (base + 2 * q) acc' =
                List.foldl
                  (fun acc j => ditButterfly (twiddlesHigh.getD (j + q) 0) (base + q + j)
                    (base + 3 * q + j) acc)
                  (List.foldl
                    (fun acc j => ditButterfly (twiddlesHigh.getD j 0) (base + j)
                      (base + 2 * q + j) acc)
                    acc' (List.range q))
                  (List.range q) := by
            calc
              butterflyDITInner twiddlesHigh (2 * q) 0 base (base + 2 * q) acc' =
                  List.foldl
                    (fun acc j => ditButterfly (twiddlesHigh.getD j 0) (base + j)
                      (base + 2 * q + j) acc)
                    acc' (List.range' 0 (2 * q)) := by
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                      (butterflyDITInner_eq_foldl_dit twiddlesHigh (2 * q) 0 base
                        (base + 2 * q) acc')
              _ = List.foldl
                    (fun acc j => ditButterfly (twiddlesHigh.getD j 0) (base + j)
                      (base + 2 * q + j) acc)
                    (List.foldl
                      (fun acc j => ditButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc)
                      acc' (List.range' 0 q))
                    (List.range' q q) := by
                    simpa [two_mul] using
                      (foldl_range'_append_split
                      (fun acc j => ditButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc) acc' 0 q q)
              _ = List.foldl
                    (fun acc j =>
                      ditButterfly (twiddlesHigh.getD (j + q) 0) (base + q + j)
                        (base + 3 * q + j) acc)
                    (List.foldl
                      (fun acc j => ditButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc)
                      acc' (List.range q))
                    (List.range q) := by
                    rw [foldl_range'_eq_range_add
                      (fun j acc => ditButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc) q q]
                    rw [← List.range_eq_range']
                    apply foldl_range_congr
                    intro j hj acc
                    simp [Nat.add_comm, Nat.add_left_comm, two_mul]
                    congr 1
                    omega
          rw [hhigh, hlow₂, hlow₁]

set_option maxHeartbeats 1200000 in
private theorem butterflyDITRadix4Blocks_eq_two_dit_blocks
    (twiddlesLow twiddlesHigh : Array R) (q blocks : Nat) (acc : Array R)
    (hq : 0 < q) (hbound : blocks * (4 * q) ≤ acc.size) :
    butterflyDITRadix4Blocks twiddlesLow twiddlesHigh (4 * q) q blocks 0 acc =
      butterflyDITBlocks twiddlesHigh (4 * q) (2 * q) blocks 0
        (butterflyDITBlocks twiddlesLow (2 * q) q (2 * blocks) 0 acc) := by
  let lowBlock : Nat → Array R → Array R :=
    fun block acc =>
      butterflyDITInner twiddlesLow q 0 (2 * q + block * (4 * q))
        (2 * q + (block * (4 * q) + q))
        (butterflyDITInner twiddlesLow q 0 (block * (4 * q)) (q + block * (4 * q))
          acc)
  let highBlock : Nat → Array R → Array R :=
    fun block acc =>
      butterflyDITInner twiddlesHigh (2 * q) 0 (block * (4 * q))
        (block * (4 * q) + 2 * q) acc
  let lowStep : Nat → Array R → Array R :=
    fun block acc =>
      butterflyDITInner twiddlesLow q 0 (block * (2 * q)) (block * (2 * q) + q) acc
  calc
    butterflyDITRadix4Blocks twiddlesLow twiddlesHigh (4 * q) q blocks 0 acc =
        List.foldl
          (fun acc block =>
            butterflyDITRadix4Inner twiddlesLow twiddlesHigh q 0 (block * (4 * q))
              (block * (4 * q) + q) (block * (4 * q) + 2 * q)
              (block * (4 * q) + 3 * q) acc)
          acc (List.range blocks) := by
          simpa [List.range_eq_range'] using
            (butterflyDITRadix4Blocks_eq_foldl_inner twiddlesLow twiddlesHigh (4 * q)
              q blocks blocks 0 acc (by simp))
    _ = List.foldl (fun acc block => highBlock block (lowBlock block acc)) acc
          (List.range blocks) := by
          apply foldl_range_congr_inv (p := fun b : Array R => b.size = acc.size)
          · intro block hblock acc hacc
            simpa [lowBlock, highBlock, three_mul_add_eq_add_two_mul_add, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm]
              using (butterflyDITRadix4Inner_eq_two_dit_inners twiddlesLow twiddlesHigh q
                (block * (4 * q)) acc hq (by nlinarith [hblock, hbound, hacc]))
          · intro block hblock acc hacc
            simp [hacc]
          · rfl
    _ = List.foldl (fun acc block => highBlock block acc)
          (List.foldl (fun acc block => lowBlock block acc) acc (List.range blocks))
          (List.range blocks) := by
          apply foldl_pair
          intro i j hij hj x
          have hlow₁ :
              butterflyDITInner twiddlesLow q 0 (j * (4 * q)) (q + j * (4 * q))
                  (highBlock i x) =
                highBlock i
                  (butterflyDITInner twiddlesLow q 0 (j * (4 * q))
                    (q + j * (4 * q)) x) := by
            simpa [highBlock, three_mul_add_eq_add_two_mul_add, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using
              (butterflyDITInner_comm twiddlesLow twiddlesHigh q (2 * q) (j * (4 * q))
                q (i * (4 * q)) (2 * q) (by
                  intro a ha b hb
                  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith) x)
          have hlow₂ (x' : Array R) :
              butterflyDITInner twiddlesLow q 0 (2 * q + j * (4 * q))
                  (2 * q + (j * (4 * q) + q)) (highBlock i x') =
                highBlock i
                  (butterflyDITInner twiddlesLow q 0 (2 * q + j * (4 * q))
                    (2 * q + (j * (4 * q) + q)) x') := by
            simpa [highBlock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (butterflyDITInner_comm twiddlesLow twiddlesHigh q (2 * q)
                (2 * q + j * (4 * q)) q (i * (4 * q)) (2 * q) (by
                  intro a ha b hb
                  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith) x')
          simp only [lowBlock]
          rw [hlow₁]
          exact hlow₂ _
    _ = List.foldl (fun acc block => highBlock block acc)
          (List.foldl (fun acc block => lowStep block acc) acc (List.range (2 * blocks)))
          (List.range blocks) := by
          congr 1
          calc
            List.foldl (fun acc block => lowBlock block acc) acc (List.range blocks) =
                List.foldl (fun acc block => lowStep (2 * block + 1) (lowStep (2 * block) acc))
                  acc (List.range blocks) := by
                  apply foldl_range_congr
                  intro block hblock acc
                  unfold lowBlock lowStep
                  exact congrArg
                    (fun p : Nat × Nat × Nat × Nat =>
                      butterflyDITInner twiddlesLow q 0 p.1 p.2.1
                        (butterflyDITInner twiddlesLow q 0 p.2.2.1 p.2.2.2 acc))
                    (show
                      ((2 * q + block * (4 * q), 2 * q + (block * (4 * q) + q),
                          block * (4 * q), q + block * (4 * q)) : Nat × Nat × Nat × Nat) =
                        (((2 * block + 1) * (2 * q), (2 * block + 1) * (2 * q) + q,
                          2 * block * (2 * q), 2 * block * (2 * q) + q) :
                          Nat × Nat × Nat × Nat) by
                      ext <;> nlinarith)
            _ = List.foldl (fun acc block => lowStep block acc) acc (List.range (2 * blocks)) := by
                  exact foldl_range_pair lowStep blocks acc
    _ = butterflyDITBlocks twiddlesHigh (4 * q) (2 * q) blocks 0
          (butterflyDITBlocks twiddlesLow (2 * q) q (2 * blocks) 0 acc) := by
          have hlow :
              List.foldl (fun acc block => lowStep block acc) acc (List.range (2 * blocks)) =
                butterflyDITBlocks twiddlesLow (2 * q) q (2 * blocks) 0 acc := by
            symm
            simpa [List.range_eq_range', lowStep] using
              (butterflyDITBlocks_eq_foldl_inner twiddlesLow (2 * q) q (2 * blocks)
                (2 * blocks) 0 acc (by simp))
          rw [hlow]
          symm
          simpa [List.range_eq_range', highBlock] using
            (butterflyDITBlocks_eq_foldl_inner twiddlesHigh (4 * q) (2 * q) blocks
              blocks 0 (butterflyDITBlocks twiddlesLow (2 * q) q (2 * blocks) 0 acc)
              (by simp))

private theorem butterflyRadix4StageWithTwiddles_eq_two_stages
    (D : NTT.Domain R) (lowStage : Nat) (twiddlesLow twiddlesHigh a : Array R)
    (ha : a.size = D.n) (hstage : lowStage + 1 < D.logN) :
    butterflyRadix4StageWithTwiddles D lowStage twiddlesLow twiddlesHigh a =
      butterflyStageWithTwiddles D (lowStage + 1) twiddlesHigh
        (butterflyStageWithTwiddles D lowStage twiddlesLow a) := by
  have hq : 0 < 2 ^ lowStage := Nat.pow_pos (by decide)
  have hblockSize : 2 ^ (lowStage + 2) = 4 * 2 ^ lowStage := by
    rw [show lowStage + 2 = lowStage + 1 + 1 by omega, pow_succ, pow_succ]
    ring
  have hhalf : 2 ^ (lowStage + 1) = 2 * 2 ^ lowStage := by
    rw [pow_succ']
  have hblocks :
      2 * (D.n / 2 ^ (lowStage + 2)) = D.n / 2 ^ (lowStage + 1) := by
    rw [NTT.Domain.n]
    rw [Nat.pow_div (show lowStage + 2 ≤ D.logN by omega) (by decide : 0 < 2)]
    rw [Nat.pow_div (show lowStage + 1 ≤ D.logN by omega) (by decide : 0 < 2)]
    have hsub : D.logN - (lowStage + 1) = (D.logN - (lowStage + 2)) + 1 := by
      omega
    rw [hsub, pow_succ']
  have hbound :
      (D.n / 2 ^ (lowStage + 2)) * (4 * 2 ^ lowStage) ≤ a.size := by
    rw [ha, NTT.Domain.n]
    rw [← hblockSize]
    exact Nat.le_of_eq (Nat.div_mul_cancel
      (Nat.pow_dvd_pow 2 (show lowStage + 2 ≤ D.logN by omega)))
  have hblocks' :
      2 * (2 ^ D.logN / (2 ^ lowStage * 4)) = 2 ^ D.logN / (2 * 2 ^ lowStage) := by
    simpa [NTT.Domain.n, hblockSize, hhalf, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using hblocks
  unfold butterflyRadix4StageWithTwiddles butterflyStageWithTwiddles
  simpa [NTT.Domain.n, hblockSize, hhalf, hblocks', Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (butterflyDITRadix4Blocks_eq_two_dit_blocks twiddlesLow twiddlesHigh
      (2 ^ lowStage) (D.n / 2 ^ (lowStage + 2)) a hq hbound)

private def difButterfly (w : R) (i0 i1 : Nat) (acc : Array R) : Array R :=
  let u := acc.getD i0 0
  let v := acc.getD i1 0
  (acc.set! i0 (u + v)).set! i1 (w * (u - v))

private theorem getD_difButterfly_of_ne
    (w : R) (i0 i1 k : Nat) (acc : Array R) (hk0 : k ≠ i0) (hk1 : k ≠ i1) :
    (difButterfly w i0 i1 acc).getD k 0 = acc.getD k 0 := by
  have h0 : i0 ≠ k := fun h => hk0 h.symm
  have h1 : i1 ≠ k := fun h => hk1 h.symm
  unfold difButterfly
  simp only [Array.set!, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_setIfInBounds]
  simp [h1]
  rw [Array.getElem?_setIfInBounds]
  simp [h0]

private theorem difButterfly_comm
    (acc : Array R) (w v : R) (i0 i1 j0 j1 : Nat)
    (h00 : i0 ≠ j0) (h01 : i0 ≠ j1) (h10 : i1 ≠ j0) (h11 : i1 ≠ j1) :
    difButterfly w i0 i1 (difButterfly v j0 j1 acc) =
      difButterfly v j0 j1 (difButterfly w i0 i1 acc) := by
  change
    (let u := (difButterfly v j0 j1 acc).getD i0 0
     let vv := (difButterfly v j0 j1 acc).getD i1 0
     (((difButterfly v j0 j1 acc).set! i0 (u + vv)).set! i1 (w * (u - vv)))) =
      (let u := (difButterfly w i0 i1 acc).getD j0 0
       let vv := (difButterfly w i0 i1 acc).getD j1 0
       (((difButterfly w i0 i1 acc).set! j0 (u + vv)).set! j1 (v * (u - vv))))
  rw [getD_difButterfly_of_ne v j0 j1 i0 acc h00 h01]
  rw [getD_difButterfly_of_ne v j0 j1 i1 acc h10 h11]
  rw [getD_difButterfly_of_ne w i0 i1 j0 acc h00.symm h10.symm]
  rw [getD_difButterfly_of_ne w i0 i1 j1 acc h01.symm h11.symm]
  unfold difButterfly
  simp only [Array.set!]
  rw [Array.setIfInBounds_comm _ _ h01.symm]
  rw [Array.setIfInBounds_comm _ _ h00.symm]
  rw [Array.setIfInBounds_comm _ _ h11.symm]
  rw [Array.setIfInBounds_comm _ _ h10.symm]

private theorem butterflyDIFInner_eq_foldl_dif (twiddles : Array R) :
    ∀ n j i0 i1 (acc : Array R),
      butterflyDIFInner twiddles (j + n) j i0 i1 acc =
        List.foldl
          (fun acc t => difButterfly (twiddles.getD (j + t) 0) (i0 + t) (i1 + t) acc)
          acc (List.range' 0 n)
  | 0, j, i0, i1, acc => by
      simp [butterflyDIFInner]
  | n + 1, j, i0, i1, acc => by
      have hj : j < j + (n + 1) := by omega
      have ih := butterflyDIFInner_eq_foldl_dif twiddles n (j + 1) (i0 + 1) (i1 + 1)
        (difButterfly (twiddles.getD j 0) i0 i1 acc)
      have hshift :
          List.foldl
              (fun acc t =>
                difButterfly (twiddles.getD (j + 1 + t) 0) (i0 + 1 + t)
                  (i1 + 1 + t) acc)
              (difButterfly (twiddles.getD j 0) i0 i1 acc) (List.range' 0 n) =
            List.foldl
              (fun acc t => difButterfly (twiddles.getD (j + t) 0) (i0 + t) (i1 + t) acc)
              (difButterfly (twiddles.getD j 0) i0 i1 acc) (List.range' 1 n) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (foldl_range'_succ_shift
            (fun t acc => difButterfly (twiddles.getD (j + t) 0) (i0 + t) (i1 + t) acc)
            n 0 (difButterfly (twiddles.getD j 0) i0 i1 acc))
      rw [butterflyDIFInner]
      simp only [hj, ↓reduceIte]
      simpa [List.range'_succ, difButterfly, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih.trans hshift

private theorem butterflyDIFInner_comm
    (twiddlesA twiddlesB : Array R) (limitA limitB baseA halfA baseB halfB : Nat)
    (hcomm :
      ∀ i, i < limitA → ∀ j, j < limitB →
        baseA + i ≠ baseB + j ∧
        baseA + i ≠ baseB + halfB + j ∧
        baseA + halfA + i ≠ baseB + j ∧
        baseA + halfA + i ≠ baseB + halfB + j) :
    ∀ acc : Array R,
      butterflyDIFInner twiddlesA limitA 0 baseA (baseA + halfA)
          (butterflyDIFInner twiddlesB limitB 0 baseB (baseB + halfB) acc) =
        butterflyDIFInner twiddlesB limitB 0 baseB (baseB + halfB)
          (butterflyDIFInner twiddlesA limitA 0 baseA (baseA + halfA) acc) := by
  intro acc
  let foldA : Array R → Array R :=
    fun acc =>
      List.foldl
        (fun acc i => difButterfly (twiddlesA.getD i 0) (baseA + i)
          (baseA + halfA + i) acc)
        acc (List.range limitA)
  let foldB : Array R → Array R :=
    fun acc =>
      List.foldl
        (fun acc j => difButterfly (twiddlesB.getD j 0) (baseB + j)
          (baseB + halfB + j) acc)
        acc (List.range limitB)
  have hA (acc' : Array R) :
      butterflyDIFInner twiddlesA limitA 0 baseA (baseA + halfA) acc' = foldA acc' := by
    simpa [foldA, List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (butterflyDIFInner_eq_foldl_dif twiddlesA limitA 0 baseA (baseA + halfA) acc')
  have hB (acc' : Array R) :
      butterflyDIFInner twiddlesB limitB 0 baseB (baseB + halfB) acc' = foldB acc' := by
    simpa [foldB, List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (butterflyDIFInner_eq_foldl_dif twiddlesB limitB 0 baseB (baseB + halfB) acc')
  calc
    butterflyDIFInner twiddlesA limitA 0 baseA (baseA + halfA)
        (butterflyDIFInner twiddlesB limitB 0 baseB (baseB + halfB) acc) =
        foldA (foldB acc) := by
          rw [hB, hA]
    _ = List.foldl
          (fun acc j => difButterfly (twiddlesB.getD j 0) (baseB + j)
            (baseB + halfB + j) acc)
          (List.foldl
            (fun acc i => difButterfly (twiddlesA.getD i 0) (baseA + i)
              (baseA + halfA + i) acc)
            acc (List.range limitA))
          (List.range limitB) := by
          apply foldl_commute_foldl
          intro i j hi hj acc
          rcases hcomm i hi j hj with ⟨h00, h01, h10, h11⟩
          exact (difButterfly_comm acc (twiddlesA.getD i 0) (twiddlesB.getD j 0)
            (baseA + i) (baseA + halfA + i) (baseB + j) (baseB + halfB + j)
            h00 h01 h10 h11).symm
    _ = butterflyDIFInner twiddlesB limitB 0 baseB (baseB + halfB)
          (butterflyDIFInner twiddlesA limitA 0 baseA (baseA + halfA) acc) := by
          rw [hA, hB]

private theorem butterflyDIFBlocks_eq_foldl_inner
    (twiddles : Array R) (blockSize half blocks : Nat) :
    ∀ n block (acc : Array R),
      blocks = block + n →
      butterflyDIFBlocks twiddles blockSize half blocks block acc =
        List.foldl
          (fun acc block =>
            butterflyDIFInner twiddles half 0 (block * blockSize) (block * blockSize + half)
              acc)
          acc (List.range' block n)
  | 0, block, acc, hblocks => by
      have hnot : ¬block < blocks := by omega
      simp [butterflyDIFBlocks, hnot]
  | n + 1, block, acc, hblocks => by
      have hblock : block < blocks := by omega
      have htail : blocks = block + 1 + n := by omega
      have ih := butterflyDIFBlocks_eq_foldl_inner twiddles blockSize half blocks
        n (block + 1)
          (butterflyDIFInner twiddles half 0 (block * blockSize) (block * blockSize + half)
            acc)
        htail
      rw [butterflyDIFBlocks]
      simp only [hblock, ↓reduceIte]
      simpa [List.range'_succ] using ih

private def radix4DIFCell
    (wHigh0 wHigh1 wLow : R) (i0 i1 i2 i3 : Nat) (acc : Array R) : Array R :=
  let x0 := acc.getD i0 0
  let x1 := acc.getD i1 0
  let x2 := acc.getD i2 0
  let x3 := acc.getD i3 0
  let a0 := x0 + x2
  let a2 := wHigh0 * (x0 - x2)
  let a1 := x1 + x3
  let a3 := wHigh1 * (x1 - x3)
  (((acc.set! i0 (a0 + a1)).set! i1 (wLow * (a0 - a1))).set! i2 (a2 + a3)).set! i3
    (wLow * (a2 - a3))

@[simp] private theorem size_radix4DIFCell
    (wHigh0 wHigh1 wLow : R) (i0 i1 i2 i3 : Nat) (acc : Array R) :
    (radix4DIFCell wHigh0 wHigh1 wLow i0 i1 i2 i3 acc).size = acc.size := by
  simp [radix4DIFCell, Array.set!, Array.size_setIfInBounds]

set_option maxHeartbeats 800000 in
private theorem radix4DIFCell_eq_two_stage_cells
    (wHigh0 wHigh1 wLow : R) (i0 i1 i2 i3 : Nat) (acc : Array R)
    (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h03 : i0 ≠ i3)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3)
    (hi0 : i0 < acc.size) (hi1 : i1 < acc.size)
    (hi2 : i2 < acc.size) (hi3 : i3 < acc.size) :
    difButterfly wLow i2 i3
        (difButterfly wLow i0 i1
          (difButterfly wHigh1 i1 i3 (difButterfly wHigh0 i0 i2 acc))) =
      radix4DIFCell wHigh0 wHigh1 wLow i0 i1 i2 i3 acc := by
  unfold difButterfly radix4DIFCell
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
    Array.size_setIfInBounds]
  simp [hi0, hi1, hi2, hi3, h01, h01.symm, h02, h02.symm, h03, h03.symm,
    h12, h12.symm, h13, h13.symm, h23, h23.symm]
  rw [Array.setIfInBounds_comm _ _ h03.symm]
  rw [Array.setIfInBounds_comm _ _ h01.symm]
  rw [Array.setIfInBounds_comm _ _ h02.symm]
  rw [Array.setIfInBounds_setIfInBounds]
  rw [Array.setIfInBounds_comm _ _ h13.symm]
  rw [Array.setIfInBounds_setIfInBounds]
  rw [Array.setIfInBounds_comm _ _ h23.symm]
  rw [Array.setIfInBounds_setIfInBounds]
  rw [Array.setIfInBounds_comm _ _ h12.symm]
  rw [Array.setIfInBounds_setIfInBounds]

private theorem butterflyDIFRadix4Inner_eq_foldl_cell
    (twiddlesHigh twiddlesLow : Array R) :
    ∀ n j i0 i1 i2 i3 (acc : Array R),
      butterflyDIFRadix4Inner twiddlesHigh twiddlesLow (j + n) j i0 i1 i2 i3 acc =
        List.foldl
          (fun acc t =>
            radix4DIFCell (twiddlesHigh.getD (j + t) 0)
              (twiddlesHigh.getD (j + t + (j + n)) 0) (twiddlesLow.getD (j + t) 0)
              (i0 + t) (i1 + t) (i2 + t) (i3 + t) acc)
          acc (List.range' 0 n)
  | 0, j, _i0, _i1, _i2, _i3, _acc => by
      simp [butterflyDIFRadix4Inner]
  | n + 1, j, i0, i1, i2, i3, acc => by
      have hj : j < j + (n + 1) := by omega
      have ih := butterflyDIFRadix4Inner_eq_foldl_cell twiddlesHigh twiddlesLow n
        (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1)
        (radix4DIFCell (twiddlesHigh.getD j 0)
          (twiddlesHigh.getD (j + (j + (n + 1))) 0) (twiddlesLow.getD j 0)
          i0 i1 i2 i3 acc)
      have hshift :
          List.foldl
              (fun acc t =>
                radix4DIFCell (twiddlesHigh.getD (j + 1 + t) 0)
                  (twiddlesHigh.getD (j + 1 + t + (j + 1 + n)) 0)
                  (twiddlesLow.getD (j + 1 + t) 0) (i0 + 1 + t) (i1 + 1 + t)
                  (i2 + 1 + t) (i3 + 1 + t) acc)
              (radix4DIFCell (twiddlesHigh.getD j 0)
                (twiddlesHigh.getD (j + (j + (n + 1))) 0) (twiddlesLow.getD j 0)
                i0 i1 i2 i3 acc)
              (List.range' 0 n) =
            List.foldl
              (fun acc t =>
                radix4DIFCell (twiddlesHigh.getD (j + t) 0)
                  (twiddlesHigh.getD (j + t + (j + (n + 1))) 0)
                  (twiddlesLow.getD (j + t) 0) (i0 + t) (i1 + t) (i2 + t)
                  (i3 + t) acc)
              (radix4DIFCell (twiddlesHigh.getD j 0)
                (twiddlesHigh.getD (j + (j + (n + 1))) 0) (twiddlesLow.getD j 0)
                i0 i1 i2 i3 acc)
              (List.range' 1 n) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (foldl_range'_succ_shift
            (fun t acc =>
              radix4DIFCell (twiddlesHigh.getD (j + t) 0)
                (twiddlesHigh.getD (j + t + (j + (n + 1))) 0)
                (twiddlesLow.getD (j + t) 0) (i0 + t) (i1 + t) (i2 + t) (i3 + t)
                acc)
            n 0
            (radix4DIFCell (twiddlesHigh.getD j 0)
              (twiddlesHigh.getD (j + (j + (n + 1))) 0) (twiddlesLow.getD j 0)
              i0 i1 i2 i3 acc))
      rw [butterflyDIFRadix4Inner]
      simp only [hj, ↓reduceIte]
      simpa [List.range'_succ, radix4DIFCell, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih.trans hshift

private theorem butterflyDIFRadix4Blocks_eq_foldl_inner
    (twiddlesHigh twiddlesLow : Array R) (blockSize quarter blocks : Nat) :
    ∀ n block (acc : Array R),
      blocks = block + n →
      butterflyDIFRadix4Blocks twiddlesHigh twiddlesLow blockSize quarter blocks block acc =
        List.foldl
          (fun acc block =>
            butterflyDIFRadix4Inner twiddlesHigh twiddlesLow quarter 0 (block * blockSize)
              (block * blockSize + quarter) (block * blockSize + 2 * quarter)
              (block * blockSize + 3 * quarter) acc)
          acc (List.range' block n)
  | 0, block, _acc, hblocks => by
      have hnot : ¬block < blocks := by omega
      simp [butterflyDIFRadix4Blocks, hnot]
  | n + 1, block, acc, hblocks => by
      have hblock : block < blocks := by omega
      have htail : blocks = block + 1 + n := by omega
      have ih := butterflyDIFRadix4Blocks_eq_foldl_inner twiddlesHigh twiddlesLow blockSize
        quarter blocks n (block + 1)
        (butterflyDIFRadix4Inner twiddlesHigh twiddlesLow quarter 0 (block * blockSize)
          (block * blockSize + quarter) (block * blockSize + 2 * quarter)
          (block * blockSize + 3 * quarter) acc)
        htail
      rw [butterflyDIFRadix4Blocks]
      simp only [hblock, ↓reduceIte]
      simpa [List.range'_succ] using ih

set_option maxHeartbeats 800000 in
private theorem butterflyDIFRadix4Inner_eq_two_dif_inners
    (twiddlesHigh twiddlesLow : Array R) (q base : Nat) (acc : Array R)
    (hq : 0 < q) (hbound : base + 4 * q ≤ acc.size) :
    butterflyDIFRadix4Inner twiddlesHigh twiddlesLow q 0 base (base + q) (base + 2 * q)
        (base + 3 * q) acc =
      butterflyDIFInner twiddlesLow q 0 (base + 2 * q) (base + 3 * q)
        (butterflyDIFInner twiddlesLow q 0 base (base + q)
          (butterflyDIFInner twiddlesHigh (2 * q) 0 base (base + 2 * q) acc)) := by
  calc
    butterflyDIFRadix4Inner twiddlesHigh twiddlesLow q 0 base (base + q)
        (base + 2 * q) (base + 3 * q) acc =
        List.foldl
          (fun acc j =>
            radix4DIFCell (twiddlesHigh.getD j 0) (twiddlesHigh.getD (j + q) 0)
              (twiddlesLow.getD j 0) (base + j) (base + q + j) (base + 2 * q + j)
              (base + 3 * q + j) acc)
          acc (List.range q) := by
          simpa [List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (butterflyDIFRadix4Inner_eq_foldl_cell twiddlesHigh twiddlesLow q 0 base
              (base + q) (base + 2 * q) (base + 3 * q) acc)
    _ = List.foldl
          (fun acc j =>
            difButterfly (twiddlesLow.getD j 0) (base + 2 * q + j)
              (base + 3 * q + j)
              (difButterfly (twiddlesLow.getD j 0) (base + j) (base + q + j)
                (difButterfly (twiddlesHigh.getD (j + q) 0) (base + q + j)
                  (base + 3 * q + j)
                  (difButterfly (twiddlesHigh.getD j 0) (base + j) (base + 2 * q + j)
                    acc))))
          acc (List.range q) := by
          apply foldl_range_congr_inv (p := fun b : Array R => b.size = acc.size)
          · intro j hj acc hacc
            exact (radix4DIFCell_eq_two_stage_cells (twiddlesHigh.getD j 0)
                (twiddlesHigh.getD (j + q) 0) (twiddlesLow.getD j 0) (base + j)
                (base + q + j) (base + 2 * q + j) (base + 3 * q + j) acc
                (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                (by nlinarith [hacc, hbound]) (by nlinarith [hacc, hbound])
                (by nlinarith [hacc, hbound]) (by nlinarith [hacc, hbound])).symm
          · intro j hj acc hacc
            simp [hacc]
          · rfl
    _ = List.foldl
          (fun acc j => difButterfly (twiddlesLow.getD j 0) (base + 2 * q + j)
            (base + 3 * q + j) acc)
          (List.foldl
            (fun acc j => difButterfly (twiddlesLow.getD j 0) (base + j) (base + q + j) acc)
            (List.foldl
              (fun acc j => difButterfly (twiddlesHigh.getD (j + q) 0) (base + q + j)
                (base + 3 * q + j) acc)
              (List.foldl
                (fun acc j => difButterfly (twiddlesHigh.getD j 0) (base + j)
                  (base + 2 * q + j) acc)
                acc (List.range q)) (List.range q))
            (List.range q))
          (List.range q) := by
          apply foldl_quad
          · intro i j hij hj x
            apply difButterfly_comm <;> omega
          · intro i j hij hj x
            apply difButterfly_comm <;> omega
          · intro i j hij hj x
            apply difButterfly_comm <;> omega
          · intro i j hij hj x
            apply difButterfly_comm <;> omega
          · intro i j hij hj x
            apply difButterfly_comm <;> omega
          · intro i j hij hj x
            apply difButterfly_comm <;> omega
    _ = butterflyDIFInner twiddlesLow q 0 (base + 2 * q) (base + 3 * q)
          (butterflyDIFInner twiddlesLow q 0 base (base + q)
            (butterflyDIFInner twiddlesHigh (2 * q) 0 base (base + 2 * q) acc)) := by
          symm
          have hhigh (acc' : Array R) :
              butterflyDIFInner twiddlesHigh (2 * q) 0 base (base + 2 * q) acc' =
                List.foldl
                  (fun acc j => difButterfly (twiddlesHigh.getD (j + q) 0)
                    (base + q + j) (base + 3 * q + j) acc)
                  (List.foldl
                    (fun acc j => difButterfly (twiddlesHigh.getD j 0) (base + j)
                      (base + 2 * q + j) acc)
                    acc' (List.range q))
                  (List.range q) := by
            calc
              butterflyDIFInner twiddlesHigh (2 * q) 0 base (base + 2 * q) acc' =
                  List.foldl
                    (fun acc j => difButterfly (twiddlesHigh.getD j 0) (base + j)
                      (base + 2 * q + j) acc)
                    acc' (List.range' 0 (2 * q)) := by
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                      (butterflyDIFInner_eq_foldl_dif twiddlesHigh (2 * q) 0 base
                        (base + 2 * q) acc')
              _ = List.foldl
                    (fun acc j => difButterfly (twiddlesHigh.getD j 0) (base + j)
                      (base + 2 * q + j) acc)
                    (List.foldl
                      (fun acc j => difButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc)
                      acc' (List.range' 0 q))
                    (List.range' q q) := by
                    simpa [two_mul] using
                      (foldl_range'_append_split
                      (fun acc j => difButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc) acc' 0 q q)
              _ = List.foldl
                    (fun acc j =>
                      difButterfly (twiddlesHigh.getD (j + q) 0) (base + q + j)
                        (base + 3 * q + j) acc)
                    (List.foldl
                      (fun acc j => difButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc)
                      acc' (List.range q))
                    (List.range q) := by
                    rw [foldl_range'_eq_range_add
                      (fun j acc => difButterfly (twiddlesHigh.getD j 0) (base + j)
                        (base + 2 * q + j) acc) q q]
                    rw [← List.range_eq_range']
                    apply foldl_range_congr
                    intro j hj acc
                    simp [Nat.add_comm, Nat.add_left_comm, two_mul]
                    congr 1
                    omega
          have hlow₁ (acc' : Array R) :
              butterflyDIFInner twiddlesLow q 0 base (base + q) acc' =
                List.foldl
                  (fun acc j => difButterfly (twiddlesLow.getD j 0) (base + j)
                    (base + q + j) acc)
                  acc' (List.range q) := by
            simpa [List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using (butterflyDIFInner_eq_foldl_dif twiddlesLow q 0 base (base + q) acc')
          have hlow₂ (acc' : Array R) :
              butterflyDIFInner twiddlesLow q 0 (base + 2 * q) (base + 3 * q) acc' =
                List.foldl
                  (fun acc j => difButterfly (twiddlesLow.getD j 0) (base + 2 * q + j)
                    (base + 3 * q + j) acc)
                  acc' (List.range q) := by
            simpa [List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using (butterflyDIFInner_eq_foldl_dif twiddlesLow q 0 (base + 2 * q)
                (base + 3 * q) acc')
          rw [hlow₂, hlow₁, hhigh]

set_option maxHeartbeats 1200000 in
private theorem butterflyDIFRadix4Blocks_eq_two_dif_blocks
    (twiddlesHigh twiddlesLow : Array R) (q blocks : Nat) (acc : Array R)
    (hq : 0 < q) (hbound : blocks * (4 * q) ≤ acc.size) :
    butterflyDIFRadix4Blocks twiddlesHigh twiddlesLow (4 * q) q blocks 0 acc =
      butterflyDIFBlocks twiddlesLow (2 * q) q (2 * blocks) 0
        (butterflyDIFBlocks twiddlesHigh (4 * q) (2 * q) blocks 0 acc) := by
  let highBlock : Nat → Array R → Array R :=
    fun block acc =>
      butterflyDIFInner twiddlesHigh (2 * q) 0 (block * (4 * q))
        (block * (4 * q) + 2 * q) acc
  let lowBlock : Nat → Array R → Array R :=
    fun block acc =>
      butterflyDIFInner twiddlesLow q 0 (2 * q + block * (4 * q))
        (2 * q + (block * (4 * q) + q))
        (butterflyDIFInner twiddlesLow q 0 (block * (4 * q)) (q + block * (4 * q))
          acc)
  let lowStep : Nat → Array R → Array R :=
    fun block acc =>
      butterflyDIFInner twiddlesLow q 0 (block * (2 * q)) (block * (2 * q) + q) acc
  calc
    butterflyDIFRadix4Blocks twiddlesHigh twiddlesLow (4 * q) q blocks 0 acc =
        List.foldl
          (fun acc block =>
            butterflyDIFRadix4Inner twiddlesHigh twiddlesLow q 0 (block * (4 * q))
              (block * (4 * q) + q) (block * (4 * q) + 2 * q)
              (block * (4 * q) + 3 * q) acc)
          acc (List.range blocks) := by
          simpa [List.range_eq_range'] using
            (butterflyDIFRadix4Blocks_eq_foldl_inner twiddlesHigh twiddlesLow (4 * q)
              q blocks blocks 0 acc (by simp))
    _ = List.foldl (fun acc block => lowBlock block (highBlock block acc)) acc
          (List.range blocks) := by
          apply foldl_range_congr_inv (p := fun b : Array R => b.size = acc.size)
          · intro block hblock acc hacc
            simpa [lowBlock, highBlock, three_mul_add_eq_add_two_mul_add, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm]
              using (butterflyDIFRadix4Inner_eq_two_dif_inners twiddlesHigh twiddlesLow q
                (block * (4 * q)) acc hq (by nlinarith [hblock, hbound, hacc]))
          · intro block hblock acc hacc
            simp [hacc]
          · rfl
    _ = List.foldl (fun acc block => lowBlock block acc)
          (List.foldl (fun acc block => highBlock block acc) acc (List.range blocks))
          (List.range blocks) := by
          apply foldl_pair
          intro i j hij hj x
          have hlow₁ :
              highBlock j
                (butterflyDIFInner twiddlesLow q 0 (i * (4 * q)) (q + i * (4 * q)) x) =
              butterflyDIFInner twiddlesLow q 0 (i * (4 * q)) (q + i * (4 * q))
                (highBlock j x) := by
            simpa [highBlock, three_mul_add_eq_add_two_mul_add, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using
              (butterflyDIFInner_comm twiddlesHigh twiddlesLow (2 * q) q (j * (4 * q))
                (2 * q) (i * (4 * q)) q (by
                  intro a ha b hb
                  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith) x)
          have hlow₂ (x' : Array R) :
              highBlock j
                (butterflyDIFInner twiddlesLow q 0 (2 * q + i * (4 * q))
                  (2 * q + (i * (4 * q) + q)) x') =
              butterflyDIFInner twiddlesLow q 0 (2 * q + i * (4 * q))
                (2 * q + (i * (4 * q) + q)) (highBlock j x') := by
            simpa [highBlock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (butterflyDIFInner_comm twiddlesHigh twiddlesLow (2 * q) q (j * (4 * q))
                (2 * q) (2 * q + i * (4 * q)) q (by
                  intro a ha b hb
                  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith) x')
          simp only [lowBlock]
          rw [← hlow₁]
          rw [← hlow₂]
    _ = List.foldl (fun acc block => lowStep block acc)
          (List.foldl (fun acc block => highBlock block acc) acc (List.range blocks))
          (List.range (2 * blocks)) := by
          calc
            List.foldl (fun acc block => lowBlock block acc)
                (List.foldl (fun acc block => highBlock block acc) acc (List.range blocks))
                (List.range blocks) =
                List.foldl (fun acc block => lowStep (2 * block + 1) (lowStep (2 * block) acc))
                  (List.foldl (fun acc block => highBlock block acc) acc (List.range blocks))
                  (List.range blocks) := by
                  apply foldl_range_congr
                  intro block hblock acc
                  unfold lowBlock lowStep
                  exact congrArg
                    (fun p : Nat × Nat × Nat × Nat =>
                      butterflyDIFInner twiddlesLow q 0 p.1 p.2.1
                        (butterflyDIFInner twiddlesLow q 0 p.2.2.1 p.2.2.2 acc))
                    (show
                      ((2 * q + block * (4 * q), 2 * q + (block * (4 * q) + q),
                          block * (4 * q), q + block * (4 * q)) : Nat × Nat × Nat × Nat) =
                        (((2 * block + 1) * (2 * q), (2 * block + 1) * (2 * q) + q,
                          2 * block * (2 * q), 2 * block * (2 * q) + q) :
                          Nat × Nat × Nat × Nat) by
                      ext <;> nlinarith)
            _ = List.foldl (fun acc block => lowStep block acc)
                  (List.foldl (fun acc block => highBlock block acc) acc (List.range blocks))
                  (List.range (2 * blocks)) := by
                  exact foldl_range_pair lowStep blocks
                    (List.foldl (fun acc block => highBlock block acc) acc (List.range blocks))
    _ = butterflyDIFBlocks twiddlesLow (2 * q) q (2 * blocks) 0
          (butterflyDIFBlocks twiddlesHigh (4 * q) (2 * q) blocks 0 acc) := by
          have hhigh :
              List.foldl (fun acc block => highBlock block acc) acc (List.range blocks) =
                butterflyDIFBlocks twiddlesHigh (4 * q) (2 * q) blocks 0 acc := by
            symm
            simpa [List.range_eq_range', highBlock] using
              (butterflyDIFBlocks_eq_foldl_inner twiddlesHigh (4 * q) (2 * q) blocks
                blocks 0 acc (by simp))
          rw [hhigh]
          symm
          simpa [List.range_eq_range', lowStep] using
            (butterflyDIFBlocks_eq_foldl_inner twiddlesLow (2 * q) q (2 * blocks)
              (2 * blocks) 0 (butterflyDIFBlocks twiddlesHigh (4 * q) (2 * q) blocks 0 acc)
              (by simp))

private theorem butterflyRadix4StageDIFWithTwiddles_eq_two_stages
    (D : NTT.Domain R) (lowStage : Nat) (twiddlesHigh twiddlesLow a : Array R)
    (ha : a.size = D.n) (hstage : lowStage + 1 < D.logN) :
    butterflyRadix4StageDIFWithTwiddles D lowStage twiddlesHigh twiddlesLow a =
      butterflyStageDIFWithTwiddles D lowStage twiddlesLow
        (butterflyStageDIFWithTwiddles D (lowStage + 1) twiddlesHigh a) := by
  have hq : 0 < 2 ^ lowStage := Nat.pow_pos (by decide)
  have hblockSize : 2 ^ (lowStage + 2) = 4 * 2 ^ lowStage := by
    rw [show lowStage + 2 = lowStage + 1 + 1 by omega, pow_succ, pow_succ]
    ring
  have hhalf : 2 ^ (lowStage + 1) = 2 * 2 ^ lowStage := by
    rw [pow_succ']
  have hblocks :
      2 * (D.n / 2 ^ (lowStage + 2)) = D.n / 2 ^ (lowStage + 1) := by
    rw [NTT.Domain.n]
    rw [Nat.pow_div (show lowStage + 2 ≤ D.logN by omega) (by decide : 0 < 2)]
    rw [Nat.pow_div (show lowStage + 1 ≤ D.logN by omega) (by decide : 0 < 2)]
    have hsub : D.logN - (lowStage + 1) = (D.logN - (lowStage + 2)) + 1 := by
      omega
    rw [hsub, pow_succ']
  have hbound :
      (D.n / 2 ^ (lowStage + 2)) * (4 * 2 ^ lowStage) ≤ a.size := by
    rw [ha, NTT.Domain.n]
    rw [← hblockSize]
    exact Nat.le_of_eq (Nat.div_mul_cancel
      (Nat.pow_dvd_pow 2 (show lowStage + 2 ≤ D.logN by omega)))
  have hblocks' :
      2 * (2 ^ D.logN / (2 ^ lowStage * 4)) = 2 ^ D.logN / (2 * 2 ^ lowStage) := by
    simpa [NTT.Domain.n, hblockSize, hhalf, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using hblocks
  unfold butterflyRadix4StageDIFWithTwiddles butterflyStageDIFWithTwiddles
  simpa [NTT.Domain.n, hblockSize, hhalf, hblocks', Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (butterflyDIFRadix4Blocks_eq_two_dif_blocks twiddlesHigh twiddlesLow
      (2 ^ lowStage) (D.n / 2 ^ (lowStage + 2)) a hq hbound)

/-- A DIT butterfly stage with matching cached twiddles agrees with the `NTT` stage. -/
theorem butterflyStageWithTwiddles_eq_ntt
    (D : NTT.Domain R) (stage : Nat) (twiddles : Array R) (a : Array R)
    (htwiddles :
      ∀ j, j < 2 ^ stage →
        twiddles.getD j 0 = (D.omega ^ (D.n / 2 ^ (stage + 1))) ^ j) :
    butterflyStageWithTwiddles D stage twiddles a =
      NTT.Transform.butterflyStage D stage a := by
  rw [NTT.Transform.butterflyStage_eq_butterflyStageSpec]
  simp [butterflyStageWithTwiddles, NTT.Transform.butterflyStageSpec]
  let wm := D.omega ^ (D.n / 2 ^ (stage + 1))
  have htw : ∀ j, j < 2 ^ stage → twiddles.getD j 0 = wm ^ j := by
    intro j hj
    simpa [wm] using htwiddles j hj
  have hblocks := butterflyDITBlocks_eq_foldl twiddles (2 ^ (stage + 1)) (2 ^ stage) wm htw
    (2 ^ D.logN / 2 ^ (stage + 1)) (2 ^ D.logN / 2 ^ (stage + 1)) 0 a (by simp)
  rw [hblocks]
  simpa [List.range_eq_range', wm, NTT.Domain.n] using
    foldl_range_eq_rec
      (f := fun block acc =>
        NTT.Transform.butterflyBlockStep (2 ^ (stage + 1)) (2 ^ stage)
          (D.omega ^ (2 ^ D.logN / 2 ^ (stage + 1))) block acc)
      (x := a) (2 ^ D.logN / 2 ^ (stage + 1))

/-- The DIT radix-2 stage loop with the full twiddle table agrees with `NTT`. -/
theorem runStagesWithTwiddles_eq_ntt (D : NTT.Domain R) (a : Array R) :
    runStagesWithTwiddles D (twiddleTable D) a = NTT.Transform.runStages D a := by
  simp [runStagesWithTwiddles, NTT.Transform.runStages]
  rw [← List.range_eq_range']
  apply foldl_range_congr
  intro stage hstage acc
  apply butterflyStageWithTwiddles_eq_ntt
  intro j hj
  simpa [twiddleTable, hstage] using twiddlePowers_getD_eq_pow D stage j hj

/--
The mixed radix-4 DIT stage loop agrees with the radix-2 `NTT` stage loop on
domain-sized arrays.
-/
theorem runStagesRadix4WithTwiddles_eq_ntt (D : NTT.Domain R) (a : Array R)
    (ha : a.size = D.n) :
    runStagesRadix4WithTwiddles D (twiddleTable D) a =
      NTT.Transform.runStages D a := by
  rw [← runStagesWithTwiddles_eq_ntt D a]
  let stageStep : Nat → Array R → Array R :=
    fun stage acc => butterflyStageWithTwiddles D stage ((twiddleTable D).getD stage #[]) acc
  let radixStep : Nat → Array R → Array R :=
    fun pass acc =>
      butterflyRadix4StageWithTwiddles D (2 * pass) ((twiddleTable D).getD (2 * pass) #[])
        ((twiddleTable D).getD (2 * pass + 1) #[]) acc
  let pairStep : Nat → Array R → Array R :=
    fun pass acc => stageStep (2 * pass + 1) (stageStep (2 * pass) acc)
  have hpairLoop :
      List.foldl (fun acc pass => radixStep pass acc) a (List.range (D.logN / 2)) =
        List.foldl (fun acc pass => pairStep pass acc) a (List.range (D.logN / 2)) := by
    apply foldl_range_congr_inv (p := fun b : Array R => b.size = D.n)
    · intro pass hpass acc hacc
      exact butterflyRadix4StageWithTwiddles_eq_two_stages D (2 * pass)
        ((twiddleTable D).getD (2 * pass) #[])
        ((twiddleTable D).getD (2 * pass + 1) #[]) acc hacc (by omega)
    · intro pass hpass acc hacc
      simp [radixStep, hacc]
    · exact ha
  have hpairRange :
      List.foldl (fun acc pass => pairStep pass acc) a (List.range (D.logN / 2)) =
        List.foldl (fun acc stage => stageStep stage acc) a
          (List.range (2 * (D.logN / 2))) := by
    simpa [pairStep] using foldl_range_pair stageStep (D.logN / 2) a
  calc
    runStagesRadix4WithTwiddles D (twiddleTable D) a =
        (if D.logN % 2 = 1 then
          stageStep (D.logN - 1)
            (List.foldl (fun acc pass => radixStep pass acc) a (List.range (D.logN / 2)))
        else
          List.foldl (fun acc pass => radixStep pass acc) a (List.range (D.logN / 2))) := by
          by_cases hodd : D.logN % 2 = 1
          · simp [runStagesRadix4WithTwiddles, stageStep, radixStep, List.range_eq_range', hodd]
          · simp [runStagesRadix4WithTwiddles, stageStep, radixStep, List.range_eq_range', hodd]
    _ = (if D.logN % 2 = 1 then
          stageStep (D.logN - 1)
            (List.foldl (fun acc stage => stageStep stage acc) a
              (List.range (2 * (D.logN / 2))))
        else
          List.foldl (fun acc stage => stageStep stage acc) a
            (List.range (2 * (D.logN / 2)))) := by
          rw [hpairLoop, hpairRange]
    _ = List.foldl (fun acc stage => stageStep stage acc) a (List.range D.logN) := by
          by_cases hodd : D.logN % 2 = 1
          · have hlen : D.logN = 2 * (D.logN / 2) + 1 := by omega
            have hlast : D.logN - 1 = 2 * (D.logN / 2) := by omega
            simp only [hodd, ↓reduceIte]
            rw [hlast]
            conv_rhs => rw [hlen]
            simp [List.range_succ, List.foldl_append]
          · have hlen : 2 * (D.logN / 2) = D.logN := by omega
            simp only [hodd, ↓reduceIte]
            rw [hlen]
    _ = runStagesWithTwiddles D (twiddleTable D) a := by
          symm
          simp [runStagesWithTwiddles, stageStep, List.range_eq_range']

/-- The DIF stage loop computes the bit-reversed forward NTT output. -/
theorem runStagesDIFWithTwiddles_correct (D : NTT.Domain R) (a : Array R) :
    runStagesDIFWithTwiddles D (twiddleTable D) (loadNatural D a) =
      NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D a) := by
  rw [runStagesDIFWithTwiddles_eq_difMathStageSpec, difMathStageSpec_final]

private theorem runStagesDIFRadix4WithTwiddles_eq_difMathStageSpec
    (D : NTT.Domain R) (a : Array R) :
    runStagesDIFRadix4WithTwiddles D (twiddleTable D) (loadNatural D a) =
      difMathStageSpec D D.logN a := by
  let radixStep : Nat → Array R → Array R :=
    fun pass acc =>
      let highStage := D.logN - 1 - 2 * pass
      let lowStage := highStage - 1
      butterflyRadix4StageDIFWithTwiddles D lowStage
        ((twiddleTable D).getD highStage #[]) ((twiddleTable D).getD lowStage #[]) acc
  have hloop :
      ∀ n, n ≤ D.logN / 2 →
        List.foldl (fun acc pass => radixStep pass acc) (loadNatural D a) (List.range n) =
          difMathStageSpec D (2 * n) a := by
    intro n hn
    induction n with
    | zero =>
        rw [difMathStageSpec_zero]
        simp
    | succ n ih =>
        have hnle : n ≤ D.logN / 2 := Nat.le_of_succ_le hn
        have hnlt : n < D.logN / 2 := Nat.lt_of_succ_le hn
        let highStage := D.logN - 1 - 2 * n
        let lowStage := highStage - 1
        have hhigh : highStage < D.logN := by
          dsimp [highStage]
          omega
        have hlowPair : lowStage + 1 = highStage := by
          dsimp [lowStage, highStage]
          omega
        have hlowStage : lowStage + 1 < D.logN := by
          rw [hlowPair]
          exact hhigh
        have hprev : D.logN - (highStage + 1) = 2 * n := by
          dsimp [highStage]
          omega
        have hmid : D.logN - (lowStage + 1) = 2 * n + 1 := by
          rw [hlowPair]
          dsimp [highStage]
          omega
        have hfinal : D.logN - lowStage = 2 * (n + 1) := by
          dsimp [lowStage, highStage]
          omega
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ih hnle]
        change radixStep n (difMathStageSpec D (2 * n) a) =
          difMathStageSpec D (2 * (n + 1)) a
        simp only [radixStep]
        change butterflyRadix4StageDIFWithTwiddles D lowStage
            ((twiddleTable D).getD highStage #[]) ((twiddleTable D).getD lowStage #[])
            (difMathStageSpec D (2 * n) a) =
          difMathStageSpec D (2 * (n + 1)) a
        rw [butterflyRadix4StageDIFWithTwiddles_eq_two_stages D lowStage
          ((twiddleTable D).getD highStage #[]) ((twiddleTable D).getD lowStage #[])
          (difMathStageSpec D (2 * n) a) (by simp [difMathStageSpec]) hlowStage]
        have hhighStep :
            butterflyStageDIFWithTwiddles D highStage ((twiddleTable D).getD highStage #[])
                (difMathStageSpec D (2 * n) a) =
              difMathStageSpec D (2 * n + 1) a := by
          convert butterflyStageDIFWithTwiddles_difMathStageSpec_succ D highStage
            ((twiddleTable D).getD highStage #[]) a hhigh ?_ using 1
          · rw [hprev]
          · rw [show D.logN - highStage = 2 * n + 1 by
              dsimp [highStage]
              omega]
          · intro j hj
            rw [twiddleTable_getD_eq_twiddlePowers D highStage hhigh]
            exact twiddlePowers_getD_eq_pow D highStage j hj
        rw [hlowPair]
        rw [hhighStep]
        have hlow : lowStage < D.logN := by omega
        have hlowStep :
            butterflyStageDIFWithTwiddles D lowStage ((twiddleTable D).getD lowStage #[])
                (difMathStageSpec D (2 * n + 1) a) =
              difMathStageSpec D (2 * (n + 1)) a := by
          convert butterflyStageDIFWithTwiddles_difMathStageSpec_succ D lowStage
            ((twiddleTable D).getD lowStage #[]) a hlow ?_ using 1
          · rw [hmid]
          · rw [hfinal]
          · intro j hj
            rw [twiddleTable_getD_eq_twiddlePowers D lowStage hlow]
            exact twiddlePowers_getD_eq_pow D lowStage j hj
        exact hlowStep
  have hpairs := hloop (D.logN / 2) le_rfl
  let stageZero : Array R → Array R :=
    fun acc => butterflyStageDIFWithTwiddles D 0 ((twiddleTable D).getD 0 #[]) acc
  calc
    runStagesDIFRadix4WithTwiddles D (twiddleTable D) (loadNatural D a) =
        (if D.logN % 2 = 1 then
          stageZero (List.foldl (fun acc pass => radixStep pass acc) (loadNatural D a)
            (List.range (D.logN / 2)))
        else
          List.foldl (fun acc pass => radixStep pass acc) (loadNatural D a)
            (List.range (D.logN / 2))) := by
          by_cases hodd : D.logN % 2 = 1
          · simp [runStagesDIFRadix4WithTwiddles, radixStep, stageZero, List.range_eq_range',
              hodd]
          · simp [runStagesDIFRadix4WithTwiddles, radixStep, stageZero, List.range_eq_range',
              hodd]
    _ = (if D.logN % 2 = 1 then
          stageZero (difMathStageSpec D (2 * (D.logN / 2)) a)
        else
          difMathStageSpec D (2 * (D.logN / 2)) a) := by
          rw [hpairs]
    _ = difMathStageSpec D D.logN a := by
          by_cases hodd : D.logN % 2 = 1
          · have hcompleted : 2 * (D.logN / 2) = D.logN - 1 := by omega
            have hlog : 0 < D.logN := by omega
            simp only [hodd, ↓reduceIte]
            rw [hcompleted]
            dsimp [stageZero]
            apply butterflyStageDIFWithTwiddles_difMathStageSpec_succ
            · exact hlog
            · intro j hj
              rw [twiddleTable_getD_eq_twiddlePowers D 0 hlog]
              exact twiddlePowers_getD_eq_pow D 0 j hj
          · have hcompleted : 2 * (D.logN / 2) = D.logN := by omega
            simp [hodd, hcompleted]

/-- The mixed radix-4 DIF stage loop computes the bit-reversed forward NTT output. -/
theorem runStagesDIFRadix4WithTwiddles_correct (D : NTT.Domain R) (a : Array R) :
    runStagesDIFRadix4WithTwiddles D (twiddleTable D) (loadNatural D a) =
      NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D a) := by
  rw [runStagesDIFRadix4WithTwiddles_eq_difMathStageSpec, difMathStageSpec_final]

set_option maxHeartbeats 800000 in
private theorem butterflyDIFPairInner_eq_pair
    (twiddles : Array R) :
    ∀ n limit j i0 i1 (accA accB : Array R),
      limit = j + n →
        butterflyDIFPairInner twiddles limit j i0 i1 accA accB =
          (butterflyDIFInner twiddles limit j i0 i1 accA,
            butterflyDIFInner twiddles limit j i0 i1 accB)
  | 0, limit, j, i0, i1, accA, accB, hlimit => by
      have hj : ¬ j < limit := by omega
      simp [butterflyDIFPairInner, butterflyDIFInner, hj]
  | n + 1, limit, j, i0, i1, accA, accB, hlimit => by
      have hj : j < limit := by omega
      have htail : limit = j + 1 + n := by omega
      let nextA :=
        ((accA.set! i0 (accA.getD i0 0 + accA.getD i1 0)).set! i1
          (twiddles.getD j 0 * (accA.getD i0 0 - accA.getD i1 0)))
      let nextB :=
        ((accB.set! i0 (accB.getD i0 0 + accB.getD i1 0)).set! i1
          (twiddles.getD j 0 * (accB.getD i0 0 - accB.getD i1 0)))
      have ih := butterflyDIFPairInner_eq_pair twiddles n limit (j + 1) (i0 + 1)
        (i1 + 1) nextA nextB htail
      rw [butterflyDIFPairInner]
      nth_rewrite 1 [butterflyDIFInner]
      nth_rewrite 2 [butterflyDIFInner]
      simp only [hj, ↓reduceIte]
      change butterflyDIFPairInner twiddles limit (j + 1) (i0 + 1) (i1 + 1) nextA
          nextB =
        (butterflyDIFInner twiddles limit (j + 1) (i0 + 1) (i1 + 1) nextA,
          butterflyDIFInner twiddles limit (j + 1) (i0 + 1) (i1 + 1) nextB)
      exact ih

set_option maxHeartbeats 800000 in
private theorem butterflyDIFPairBlocks_eq_pair
    (twiddles : Array R) (blockSize half : Nat) :
    ∀ n blocks block (accA accB : Array R),
      blocks = block + n →
        butterflyDIFPairBlocks twiddles blockSize half blocks block accA accB =
          (butterflyDIFBlocks twiddles blockSize half blocks block accA,
            butterflyDIFBlocks twiddles blockSize half blocks block accB)
  | 0, blocks, block, accA, accB, hblocks => by
      have hblock : ¬ block < blocks := by omega
      simp [butterflyDIFPairBlocks, butterflyDIFBlocks, hblock]
  | n + 1, blocks, block, accA, accB, hblocks => by
      have hblock : block < blocks := by omega
      have htail : blocks = block + 1 + n := by omega
      let base := block * blockSize
      have hinner := butterflyDIFPairInner_eq_pair twiddles half half 0 base
        (base + half) accA accB (by simp)
      have ih := butterflyDIFPairBlocks_eq_pair twiddles blockSize half n blocks
        (block + 1)
        (butterflyDIFInner twiddles half 0 base (base + half) accA)
        (butterflyDIFInner twiddles half 0 base (base + half) accB) htail
      rw [butterflyDIFPairBlocks]
      nth_rewrite 1 [butterflyDIFBlocks]
      nth_rewrite 2 [butterflyDIFBlocks]
      simp only [hblock, ↓reduceIte]
      rw [hinner]
      exact ih

private theorem butterflyStageDIFPairWithTwiddles_eq_pair
    (D : NTT.Domain R) (stage : Nat) (twiddles : Array R) (a b : Array R) :
    butterflyStageDIFPairWithTwiddles D stage twiddles a b =
      (butterflyStageDIFWithTwiddles D stage twiddles a,
        butterflyStageDIFWithTwiddles D stage twiddles b) := by
  unfold butterflyStageDIFPairWithTwiddles butterflyStageDIFWithTwiddles
  exact butterflyDIFPairBlocks_eq_pair twiddles (2 ^ (stage + 1)) (2 ^ stage)
    (D.n / 2 ^ (stage + 1)) (D.n / 2 ^ (stage + 1)) 0 a b (by simp)

set_option maxHeartbeats 800000 in
private theorem butterflyDIFRadix4PairInner_eq_pair
    (twiddlesHigh twiddlesLow : Array R) :
    ∀ n limit j i0 i1 i2 i3 (accA accB : Array R),
      limit = j + n →
        butterflyDIFRadix4PairInner twiddlesHigh twiddlesLow limit j i0 i1 i2 i3
            accA accB =
          (butterflyDIFRadix4Inner twiddlesHigh twiddlesLow limit j i0 i1 i2 i3 accA,
            butterflyDIFRadix4Inner twiddlesHigh twiddlesLow limit j i0 i1 i2 i3 accB)
  | 0, limit, j, i0, i1, i2, i3, accA, accB, hlimit => by
      have hj : ¬ j < limit := by omega
      simp [butterflyDIFRadix4PairInner, butterflyDIFRadix4Inner, hj]
  | n + 1, limit, j, i0, i1, i2, i3, accA, accB, hlimit => by
      have hj : j < limit := by omega
      have htail : limit = j + 1 + n := by omega
      let wHigh0 := twiddlesHigh.getD j 0
      let wHigh1 := twiddlesHigh.getD (j + limit) 0
      let wLow := twiddlesLow.getD j 0
      let x0A := accA.getD i0 0
      let x1A := accA.getD i1 0
      let x2A := accA.getD i2 0
      let x3A := accA.getD i3 0
      let a0A := x0A + x2A
      let a2A := wHigh0 * (x0A - x2A)
      let a1A := x1A + x3A
      let a3A := wHigh1 * (x1A - x3A)
      let nextA := (((accA.set! i0 (a0A + a1A)).set! i1 (wLow * (a0A - a1A))).set!
        i2 (a2A + a3A)).set! i3 (wLow * (a2A - a3A))
      let x0B := accB.getD i0 0
      let x1B := accB.getD i1 0
      let x2B := accB.getD i2 0
      let x3B := accB.getD i3 0
      let a0B := x0B + x2B
      let a2B := wHigh0 * (x0B - x2B)
      let a1B := x1B + x3B
      let a3B := wHigh1 * (x1B - x3B)
      let nextB := (((accB.set! i0 (a0B + a1B)).set! i1 (wLow * (a0B - a1B))).set!
        i2 (a2B + a3B)).set! i3 (wLow * (a2B - a3B))
      have ih := butterflyDIFRadix4PairInner_eq_pair twiddlesHigh twiddlesLow n
        limit (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1) nextA nextB htail
      rw [butterflyDIFRadix4PairInner]
      nth_rewrite 1 [butterflyDIFRadix4Inner]
      nth_rewrite 2 [butterflyDIFRadix4Inner]
      simp only [hj, ↓reduceIte]
      change
        butterflyDIFRadix4PairInner twiddlesHigh twiddlesLow limit (j + 1) (i0 + 1)
            (i1 + 1) (i2 + 1) (i3 + 1) nextA nextB =
          (butterflyDIFRadix4Inner twiddlesHigh twiddlesLow limit (j + 1) (i0 + 1)
              (i1 + 1) (i2 + 1) (i3 + 1) nextA,
            butterflyDIFRadix4Inner twiddlesHigh twiddlesLow limit (j + 1) (i0 + 1)
              (i1 + 1) (i2 + 1) (i3 + 1) nextB)
      exact ih

set_option maxHeartbeats 800000 in
private theorem butterflyDIFRadix4PairBlocks_eq_pair
    (twiddlesHigh twiddlesLow : Array R) (blockSize quarter : Nat) :
    ∀ n blocks block (accA accB : Array R),
      blocks = block + n →
        butterflyDIFRadix4PairBlocks twiddlesHigh twiddlesLow blockSize quarter blocks block
            accA accB =
          (butterflyDIFRadix4Blocks twiddlesHigh twiddlesLow blockSize quarter blocks block accA,
            butterflyDIFRadix4Blocks twiddlesHigh twiddlesLow blockSize quarter blocks block accB)
  | 0, blocks, block, accA, accB, hblocks => by
      have hblock : ¬ block < blocks := by omega
      simp [butterflyDIFRadix4PairBlocks, butterflyDIFRadix4Blocks, hblock]
  | n + 1, blocks, block, accA, accB, hblocks => by
      have hblock : block < blocks := by omega
      have htail : blocks = block + 1 + n := by omega
      let base := block * blockSize
      have hinner := butterflyDIFRadix4PairInner_eq_pair twiddlesHigh twiddlesLow
        quarter quarter 0 base (base + quarter) (base + 2 * quarter)
        (base + 3 * quarter) accA accB (by simp)
      have ih := butterflyDIFRadix4PairBlocks_eq_pair twiddlesHigh twiddlesLow
        blockSize quarter n blocks (block + 1)
        (butterflyDIFRadix4Inner twiddlesHigh twiddlesLow quarter 0 base
          (base + quarter) (base + 2 * quarter) (base + 3 * quarter) accA)
        (butterflyDIFRadix4Inner twiddlesHigh twiddlesLow quarter 0 base
          (base + quarter) (base + 2 * quarter) (base + 3 * quarter) accB) htail
      rw [butterflyDIFRadix4PairBlocks]
      nth_rewrite 1 [butterflyDIFRadix4Blocks]
      nth_rewrite 2 [butterflyDIFRadix4Blocks]
      simp only [hblock, ↓reduceIte]
      rw [hinner]
      exact ih

private theorem butterflyRadix4StageDIFPairWithTwiddles_eq_pair
    (D : NTT.Domain R) (lowStage : Nat) (twiddlesHigh twiddlesLow : Array R)
    (a b : Array R) :
    butterflyRadix4StageDIFPairWithTwiddles D lowStage twiddlesHigh twiddlesLow a b =
      (butterflyRadix4StageDIFWithTwiddles D lowStage twiddlesHigh twiddlesLow a,
        butterflyRadix4StageDIFWithTwiddles D lowStage twiddlesHigh twiddlesLow b) := by
  unfold butterflyRadix4StageDIFPairWithTwiddles butterflyRadix4StageDIFWithTwiddles
  exact butterflyDIFRadix4PairBlocks_eq_pair twiddlesHigh twiddlesLow
    (2 ^ (lowStage + 2)) (2 ^ lowStage) (D.n / 2 ^ (lowStage + 2))
    (D.n / 2 ^ (lowStage + 2)) 0 a b (by simp)

/-- The paired radix-4 DIF stage loop is extensionally two independent stage loops. -/
theorem runStagesDIFRadix4PairWithTwiddles_eq_pair
    (D : NTT.Domain R) (a b : Array R) :
    runStagesDIFRadix4PairWithTwiddles D (twiddleTable D)
        (loadNatural D a) (loadNatural D b) =
      (runStagesDIFRadix4WithTwiddles D (twiddleTable D) (loadNatural D a),
        runStagesDIFRadix4WithTwiddles D (twiddleTable D) (loadNatural D b)) := by
  have hfoldFst :
      ∀ xs (accA accB : Array R),
        (List.foldl
            (fun (acc : MProd (Array R) (Array R)) pass =>
              ⟨(butterflyRadix4StageDIFPairWithTwiddles D
                    (D.logN - 1 - 2 * pass - 1)
                    ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                    ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[])
                    acc.fst acc.snd).1,
                (butterflyRadix4StageDIFPairWithTwiddles D
                    (D.logN - 1 - 2 * pass - 1)
                    ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                    ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[])
                    acc.fst acc.snd).2⟩)
            (⟨accA, accB⟩ : MProd (Array R) (Array R)) xs).fst =
          List.foldl
            (fun acc pass =>
              butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) acc)
            accA xs := by
    intro xs
    induction xs with
    | nil =>
        intro accA accB
        simp
    | cons pass rest ih =>
        intro accA accB
        simp only [List.foldl_cons]
        rw [show
            (⟨(butterflyRadix4StageDIFPairWithTwiddles D
                (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA accB).1,
              (butterflyRadix4StageDIFPairWithTwiddles D
                (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA accB).2⟩ :
                MProd (Array R) (Array R)) =
            ⟨butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA,
              butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accB⟩ by
          simp [butterflyRadix4StageDIFPairWithTwiddles_eq_pair]]
        exact ih
          (butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
            ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
            ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA)
          (butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
            ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
            ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accB)
  have hfoldSnd :
      ∀ xs (accA accB : Array R),
        (List.foldl
            (fun (acc : MProd (Array R) (Array R)) pass =>
              ⟨(butterflyRadix4StageDIFPairWithTwiddles D
                    (D.logN - 1 - 2 * pass - 1)
                    ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                    ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[])
                    acc.fst acc.snd).1,
                (butterflyRadix4StageDIFPairWithTwiddles D
                    (D.logN - 1 - 2 * pass - 1)
                    ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                    ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[])
                    acc.fst acc.snd).2⟩)
            (⟨accA, accB⟩ : MProd (Array R) (Array R)) xs).snd =
          List.foldl
            (fun acc pass =>
              butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) acc)
            accB xs := by
    intro xs
    induction xs with
    | nil =>
        intro accA accB
        simp
    | cons pass rest ih =>
        intro accA accB
        simp only [List.foldl_cons]
        rw [show
            (⟨(butterflyRadix4StageDIFPairWithTwiddles D
                (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA accB).1,
              (butterflyRadix4StageDIFPairWithTwiddles D
                (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA accB).2⟩ :
                MProd (Array R) (Array R)) =
            ⟨butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA,
              butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
                ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
                ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accB⟩ by
          simp [butterflyRadix4StageDIFPairWithTwiddles_eq_pair]]
        exact ih
          (butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
            ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
            ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accA)
          (butterflyRadix4StageDIFWithTwiddles D (D.logN - 1 - 2 * pass - 1)
            ((twiddleTable D)[D.logN - 1 - 2 * pass]?.getD #[])
            ((twiddleTable D)[D.logN - 1 - 2 * pass - 1]?.getD #[]) accB)
  by_cases hodd : D.logN % 2 = 1
  · simp [runStagesDIFRadix4PairWithTwiddles, runStagesDIFRadix4WithTwiddles,
      hodd, butterflyStageDIFPairWithTwiddles_eq_pair]
    constructor
    · congr 1
      simpa only [Prod.fst, Prod.snd] using
        hfoldFst (List.range' 0 (D.logN / 2)) (loadNatural D a)
        (loadNatural D b)
    · congr 1
      simpa only [Prod.fst, Prod.snd] using
        hfoldSnd (List.range' 0 (D.logN / 2)) (loadNatural D a)
        (loadNatural D b)
  · simp [runStagesDIFRadix4PairWithTwiddles, runStagesDIFRadix4WithTwiddles, hodd]
    constructor
    · simpa only [Prod.fst, Prod.snd] using
        hfoldFst (List.range' 0 (D.logN / 2)) (loadNatural D a)
        (loadNatural D b)
    · simpa only [Prod.fst, Prod.snd] using
        hfoldSnd (List.range' 0 (D.logN / 2)) (loadNatural D a)
        (loadNatural D b)

/-- A well-formed plan's forward transform computes the bit-reversed forward NTT. -/
theorem forwardImpl_correct (P : Plan R) (hP : WellFormed P) (p : CPolynomial.Raw R) :
    forwardImpl P p =
      NTT.Transform.bitRevPermute P.domain (NTT.Forward.forwardSpec P.domain p) := by
  rcases hP with ⟨_, _, htwiddles, _⟩
  simp [forwardImpl, htwiddles, runStagesDIFRadix4WithTwiddles_correct]

/-- A plan built from a domain has a correct forward transform. -/
theorem forwardImpl_ofDomain_correct (D : NTT.Domain R) (p : CPolynomial.Raw R) :
    forwardImpl (ofDomain D) p =
      NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D p) := by
  simpa using forwardImpl_correct (P := ofDomain D) (ofDomain_wellFormed D) p

/-- The paired forward transform equals the pair of individual forward transforms. -/
theorem forwardPairImpl_eq_pair
    (P : Plan R) (hP : WellFormed P) (p q : CPolynomial.Raw R) :
    forwardPairImpl P p q = (forwardImpl P p, forwardImpl P q) := by
  rcases hP with ⟨_, _, htwiddles, _⟩
  simp [forwardPairImpl, forwardImpl, htwiddles,
    runStagesDIFRadix4PairWithTwiddles_eq_pair]

/-- The paired forward transform computes the two bit-reversed forward NTT outputs. -/
theorem forwardPairImpl_correct
    (P : Plan R) (hP : WellFormed P) (p q : CPolynomial.Raw R) :
    forwardPairImpl P p q =
      (NTT.Transform.bitRevPermute P.domain (NTT.Forward.forwardSpec P.domain p),
        NTT.Transform.bitRevPermute P.domain (NTT.Forward.forwardSpec P.domain q)) := by
  rw [forwardPairImpl_eq_pair P hP p q]
  simp [forwardImpl_correct P hP]

/-- Plan normalization agrees with `NTT.Inverse.normalize` for the same domain. -/
theorem normalize_eq_ntt_normalize (P : Plan R) (hP : WellFormed P) (a : Array R) :
    normalize P a = NTT.Inverse.normalize P.domain a := by
  rcases hP with ⟨_, hnInv, _⟩
  simp [normalize, NTT.Inverse.normalize, hnInv]

/-- A well-formed plan's inverse transform computes the inverse NTT spec. -/
theorem inverseImpl_correct (P : Plan R) (hP : WellFormed P) (v : Array R) :
    inverseImpl P (NTT.Transform.bitRevPermute P.domain v) =
      NTT.Inverse.inverseSpec P.domain v := by
  rcases hP with ⟨hinverseDomain, hnInv, htwiddles, hinverseTwiddles⟩
  rw [inverseImpl, hinverseDomain, hinverseTwiddles]
  rw [runStagesRadix4WithTwiddles_eq_ntt _ _ (by simp [NTT.Transform.bitRevPermute,
    NTT.Domain.inverse])]
  have hbit :
      NTT.Transform.bitRevPermute P.domain v =
        NTT.Transform.bitRevPermute P.domain.inverse v := by
    apply Array.ext
    · simp [NTT.Transform.bitRevPermute, NTT.Domain.inverse]
    · intro i hi₁ hi₂
      simp [NTT.Transform.bitRevPermute, NTT.Domain.inverse]
  rw [hbit]
  rw [normalize_eq_ntt_normalize P ⟨hinverseDomain, hnInv, htwiddles, hinverseTwiddles⟩]
  exact NTT.Inverse.inverseImpl_correct P.domain v

/-- Pointwise multiplication commutes with applying the bit-reversal permutation. -/
theorem pointwiseMul_bitRevPermute_forwardSpec_eq
    (D : NTT.Domain R) (p q : CPolynomial.Raw R) :
    pointwiseMul D
        (NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D p))
        (NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D q)) =
      NTT.Transform.bitRevPermute D
        (NTT.FastMul.pointwiseMul D
          (NTT.Forward.forwardSpec D p) (NTT.Forward.forwardSpec D q)) := by
  apply Array.ext
  · simp [pointwiseMul, NTT.FastMul.pointwiseMul, NTT.Transform.bitRevPermute]
  · intro i hiLeft hiRight
    have hrev : NTT.Transform.bitRevNat D.logN i < D.n := by
      simpa [NTT.Domain.n] using NTT.Transform.bitRevNat_lt D.logN i
    have hrevPow : NTT.Transform.bitRevNat D.logN i < 2 ^ D.logN := by
      simpa [NTT.Domain.n] using hrev
    simp [pointwiseMul, NTT.FastMul.pointwiseMul, NTT.Transform.bitRevPermute,
      Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hrevPow]

namespace Raw

/-- The planned raw multiplication implementation computes the raw NTT multiplication spec. -/
theorem fastMulImpl_correct [BEq R] [LawfulBEq R]
    (P : Plan R) (hP : WellFormed P) (p q : CPolynomial.Raw R) :
    fastMulImpl P p q = NTT.FastMul.Raw.fastMulSpec P.domain p q := by
  rw [fastMulImpl, NTT.FastMul.Raw.fastMulSpec]
  rw [forwardPairImpl_correct P hP p q]
  simp only
  rw [pointwiseMul_bitRevPermute_forwardSpec_eq]
  rw [inverseImpl_correct P hP]

/-- The planned raw multiplication implementation trims to ordinary multiplication. -/
theorem fastMulImpl_trim_eq_mul [BEq R] [LawfulBEq R]
    (P : Plan R) (hP : WellFormed P) (p q : CPolynomial.Raw R)
    (hfit : NTT.Domain.fits P.domain p q) :
    (fastMulImpl P p q).trim = p * q := by
  rw [fastMulImpl_correct P hP p q]
  exact NTT.FastMul.Raw.fastMulSpec_trim_eq_mul P.domain p q hfit

end Raw

/-- The planned multiplication implementation computes the NTT multiplication spec. -/
theorem fastMulImpl_correct [BEq R] [LawfulBEq R]
    (P : Plan R) (hP : WellFormed P) (p q : CPolynomial R) :
    fastMulImpl P p q = NTT.FastMul.fastMulSpec P.domain p q := by
  apply CPolynomial.ext
  simp [fastMulImpl, NTT.FastMul.fastMulSpec, Raw.fastMulImpl_correct P hP]

/-- The planned multiplication implementation agrees with ordinary multiplication. -/
theorem fastMulImpl_eq_mul [BEq R] [LawfulBEq R]
    (P : Plan R) (hP : WellFormed P) (p q : CPolynomial R)
    (hfit : NTT.Domain.fits P.domain p.val q.val) :
    fastMulImpl P p q = p * q := by
  rw [fastMulImpl_correct P hP p q]
  exact NTT.FastMul.fastMulSpec_eq_mul P.domain p q hfit

end Plan

namespace Raw

/-- The one-shot raw multiplication implementation computes the raw NTT multiplication spec. -/
theorem fastMulImpl_correct [BEq R] [LawfulBEq R]
    (D : NTT.Domain R) (p q : CPolynomial.Raw R) :
    fastMulImpl D p q = NTT.FastMul.Raw.fastMulSpec D p q := by
  simpa [fastMulImpl] using
    Plan.Raw.fastMulImpl_correct (P := Plan.ofDomain D) (Plan.ofDomain_wellFormed D) p q

/-- The one-shot raw multiplication implementation trims to ordinary multiplication. -/
theorem fastMulImpl_trim_eq_mul [BEq R] [LawfulBEq R]
    (D : NTT.Domain R) (p q : CPolynomial.Raw R)
    (hfit : NTT.Domain.fits D p q) :
    (fastMulImpl D p q).trim = p * q := by
  rw [fastMulImpl_correct D p q]
  exact NTT.FastMul.Raw.fastMulSpec_trim_eq_mul D p q hfit

end Raw

/-- The one-shot multiplication implementation computes the NTT multiplication spec. -/
theorem fastMulImpl_correct [BEq R] [LawfulBEq R]
    (D : NTT.Domain R) (p q : CPolynomial R) :
    fastMulImpl D p q = NTT.FastMul.fastMulSpec D p q := by
  simpa [fastMulImpl] using
    Plan.fastMulImpl_correct (P := Plan.ofDomain D) (Plan.ofDomain_wellFormed D) p q

/-- The one-shot multiplication implementation agrees with ordinary multiplication. -/
theorem fastMulImpl_eq_mul [BEq R] [LawfulBEq R]
    (D : NTT.Domain R) (p q : CPolynomial R)
    (hfit : NTT.Domain.fits D p.val q.val) :
    fastMulImpl D p q = p * q := by
  rw [fastMulImpl_correct D p q]
  exact NTT.FastMul.fastMulSpec_eq_mul D p q hfit

/-- The safe one-shot wrapper agrees with ordinary multiplication. -/
theorem safeFastMul_eq_mul [BEq R] [LawfulBEq R]
    (D : NTT.Domain R) (p q : CPolynomial R)
    (hfit : NTT.Domain.fits D p.val q.val) :
    safeFastMul D p q hfit = p * q := by
  exact fastMulImpl_eq_mul D p q hfit

end NTTFast
end CPolynomial
end CompPoly
