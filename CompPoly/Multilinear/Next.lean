/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin
-/
import CompPoly.Multilinear.Semantics

/-!
# The next kernel and shift identity

This file defines the multilinear `nextHat` kernel on the Boolean hypercube
and proves the shift identity `CompPoly.Multilinear.shift_eq_sum`.
-/

open scoped BigOperators

namespace CompPoly.Multilinear

open CompPoly

variable {R : Type*} {n : Nat}

/-- The terminal-successor map on hypercube indices. `nextIndex n i` is `i + 1`
when that is still a valid index and is the terminal self-loop `i` at the
all-ones point `i = 2^n - 1`. -/
def nextIndex (n : Nat) (i : Fin (2 ^ n)) : Fin (2 ^ n) :=
  if h : i.val + 1 < 2 ^ n then ⟨i.val + 1, h⟩ else i

/-- The all-ones index, where `nextIndex` has its terminal self-loop. -/
private def terminalIndex (n : ℕ) : Fin (2 ^ n) :=
  ⟨2 ^ n - 1, by have := Nat.two_pow_pos n; omega⟩

private theorem not_succ_lt_iff_eq_terminal (i : Fin (2 ^ n)) :
    ¬ i.val + 1 < 2 ^ n ↔ i = terminalIndex n := by
  constructor
  · intro h
    apply Fin.ext
    simp only [terminalIndex]
    omega
  · rintro rfl
    simp only [terminalIndex]
    omega

/-- Embed a prefix index with a zero low bit. -/
private def evenIndex (i : Fin (2 ^ n)) : Fin (2 ^ (n + 1)) :=
  ⟨2 * i.val, by
    rw [pow_succ]
    omega⟩

/-- Embed a prefix index with a one low bit. -/
private def oddIndex (i : Fin (2 ^ n)) : Fin (2 ^ (n + 1)) :=
  ⟨2 * i.val + 1, by
    rw [pow_succ, mul_comm]
    omega⟩

private theorem nextIndex_evenIndex (i : Fin (2 ^ n)) :
    nextIndex (n + 1) (evenIndex i) = oddIndex i := by
  unfold nextIndex
  split
  · apply Fin.ext
    simp [evenIndex, oddIndex]
  · rename_i h
    exfalso
    apply h
    simpa [evenIndex, oddIndex] using (oddIndex i).isLt

private theorem nextIndex_oddIndex (i : Fin (2 ^ n)) :
    nextIndex (n + 1) (oddIndex i) =
      if h : i.val + 1 < 2 ^ n then evenIndex ⟨i.val + 1, h⟩ else oddIndex i := by
  unfold nextIndex
  by_cases h : i.val + 1 < 2 ^ n
  · rw [dif_pos h]
    have hglobal : 2 * i.val + 1 + 1 < 2 ^ (n + 1) := by
      rw [pow_succ, mul_comm]
      omega
    split
    · apply Fin.ext
      simp [oddIndex, evenIndex]
      omega
    · rename_i hg
      exact (hg (by simpa [oddIndex] using hglobal)).elim
  · rw [dif_neg h]
    have hglobal : ¬2 * i.val + 1 + 1 < 2 ^ (n + 1) := by
      rw [pow_succ, mul_comm]
      omega
    split
    · rename_i hg
      exact (hglobal (by simpa [oddIndex] using hg)).elim
    · rfl

private theorem cubePoint_terminal [CommRing R] :
    cubePoint (R := R) n (terminalIndex n) = Vector.replicate n 1 := by
  apply Vector.ext
  intro k hk
  have hlt : n - 1 - k < n := by omega
  simp [cubePoint, terminalIndex, Nat.testBit_two_pow_sub_one, hlt]

private theorem eqHat_cubePoint_terminal [CommRing R] (x : Vector R n) :
    eqHat x (cubePoint n (terminalIndex n)) = ∏ j : Fin n, x[j] := by
  rw [cubePoint_terminal]
  unfold eqHat
  simp

private theorem cubePoint_evenIndex [CommRing R] (i : Fin (2 ^ n)) :
    cubePoint (R := R) (n + 1) (evenIndex i) = (cubePoint n i).push 0 := by
  apply Vector.ext
  intro k hk
  by_cases hkn : k < n
  · have hexp : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
    have hbit : (2 * i.val).testBit (n + 1 - 1 - k) =
        i.val.testBit (n - 1 - k) := by
      rw [hexp, ← Nat.bit_false_apply i.val, Nat.testBit_bit_succ]
    simp only [cubePoint, Vector.getElem_ofFn, evenIndex]
    rw [Vector.getElem_push_lt hkn]
    rw [hbit]
    simp only [Vector.getElem_ofFn]
  · have hk : k = n := by omega
    subst k
    have hbit : (2 * i.val).testBit 0 = false := by
      rw [← Nat.bit_false_apply i.val, Nat.testBit_bit_zero]
    simp [cubePoint, evenIndex, hbit]

private theorem cubePoint_oddIndex [CommRing R] (i : Fin (2 ^ n)) :
    cubePoint (R := R) (n + 1) (oddIndex i) = (cubePoint n i).push 1 := by
  apply Vector.ext
  intro k hk
  by_cases hkn : k < n
  · have hexp : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
    have hbit : (2 * i.val + 1).testBit (n + 1 - 1 - k) =
        i.val.testBit (n - 1 - k) := by
      rw [hexp, ← Nat.bit_true_apply i.val, Nat.testBit_bit_succ]
    simp only [cubePoint, Vector.getElem_ofFn, oddIndex]
    rw [Vector.getElem_push_lt hkn]
    rw [hbit]
    simp only [Vector.getElem_ofFn]
  · have hk : k = n := by omega
    subst k
    have hbit : (2 * i.val + 1).testBit 0 = true := by
      rw [← Nat.bit_true_apply i.val, Nat.testBit_bit_zero]
    simp [cubePoint, oddIndex, hbit]

/-- Split a `2^(n+1)`-term sum according to its low bit. -/
private theorem sum_even_odd {S : Type*} [AddCommMonoid S]
    (term : Fin (2 ^ (n + 1)) → S) :
    (∑ i : Fin (2 ^ (n + 1)), term i) =
      (∑ i : Fin (2 ^ n), term (evenIndex i)) +
        ∑ i : Fin (2 ^ n), term (oddIndex i) := by
  let f : ℕ → S := fun k ↦ if h : k < 2 ^ (n + 1) then term ⟨k, h⟩ else 0
  symm
  calc
    (∑ i : Fin (2 ^ n), term (evenIndex i)) +
          ∑ i : Fin (2 ^ n), term (oddIndex i) =
        (∑ i : Fin (2 ^ n), f (2 * i.val)) +
          ∑ i : Fin (2 ^ n), f (2 * i.val + 1) := by
      congr 1
      · exact Finset.sum_congr rfl fun i _ ↦ by
          have hb : 2 * i.val < 2 ^ (n + 1) := (evenIndex i).isLt
          dsimp only [f]
          rw [dif_pos hb]
          congr
      · exact Finset.sum_congr rfl fun i _ ↦ by
          have hb : 2 * i.val + 1 < 2 ^ (n + 1) := (oddIndex i).isLt
          dsimp only [f]
          rw [dif_pos hb]
          congr
    _ = ∑ i : Fin (2 ^ (n + 1)), f i.val := Fin.sum_univ_pow_two_even_add_odd f
    _ = ∑ i : Fin (2 ^ (n + 1)), term i := by
      exact Finset.sum_congr rfl fun i _ ↦ by
        dsimp only [f]
        rw [dif_pos i.isLt]

private theorem eqHat_push [CommRing R] (x y : Vector R n) (a b : R) :
    eqHat (x.push a) (y.push b) =
      eqHat x y * (a * b + (1 - a) * (1 - b)) := by
  unfold eqHat
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.getElem_fin, Fin.val_castSucc, Fin.is_lt, Vector.getElem_push_lt,
    Fin.val_last, Vector.getElem_push_eq]

/-- Summing products of equality-kernel weights over the Boolean cube composes
the two kernels. -/
private theorem sum_eqHat_cubePoint_mul_eqHat_cubePoint [CommRing R]
    (x y : Vector R n) :
    (∑ i : Fin (2 ^ n), eqHat x (cubePoint n i) * eqHat y (cubePoint n i)) =
      eqHat x y := by
  induction n with
  | zero =>
      have hx : x = #v[] := Vector.eq_empty_of_size_eq_zero rfl
      have hy : y = #v[] := Vector.eq_empty_of_size_eq_zero rfl
      subst x
      subst y
      simp [eqHat, cubePoint]
  | succ n ih =>
      obtain ⟨x', a, hx⟩ : ∃ (x' : Vector R n) (a : R), x = x'.push a :=
        Vector.exists_push
      obtain ⟨y', b, hy⟩ : ∃ (y' : Vector R n) (b : R), y = y'.push b :=
        Vector.exists_push
      rw [hx, hy]
      let term : Fin (2 ^ (n + 1)) → R := fun i ↦
        eqHat (x'.push a) (cubePoint (n + 1) i) *
          eqHat (y'.push b) (cubePoint (n + 1) i)
      change (∑ i : Fin (2 ^ (n + 1)), term i) = _
      rw [sum_even_odd]
      dsimp only [term]
      simp_rw [cubePoint_evenIndex, cubePoint_oddIndex, eqHat_push]
      simp only [mul_zero, add_zero, zero_add, sub_zero, sub_self, mul_one]
      have heven : ∀ i : Fin (2 ^ n),
          eqHat x' (cubePoint n i) * (1 - a) *
              (eqHat y' (cubePoint n i) * (1 - b)) =
            (1 - a) * (1 - b) *
              (eqHat x' (cubePoint n i) * eqHat y' (cubePoint n i)) :=
        fun i ↦ by ring
      have hodd : ∀ i : Fin (2 ^ n),
          eqHat x' (cubePoint n i) * a * (eqHat y' (cubePoint n i) * b) =
            a * b * (eqHat x' (cubePoint n i) * eqHat y' (cubePoint n i)) :=
        fun i ↦ by ring
      have hevenSum :
          (∑ i : Fin (2 ^ n),
            eqHat x' (cubePoint n i) * (1 - a) *
              (eqHat y' (cubePoint n i) * (1 - b))) =
            ∑ i : Fin (2 ^ n),
              (1 - a) * (1 - b) *
                (eqHat x' (cubePoint n i) * eqHat y' (cubePoint n i)) :=
        Finset.sum_congr rfl fun i _ ↦ heven i
      have hoddSum :
          (∑ i : Fin (2 ^ n),
            eqHat x' (cubePoint n i) * a * (eqHat y' (cubePoint n i) * b)) =
            ∑ i : Fin (2 ^ n),
              a * b * (eqHat x' (cubePoint n i) * eqHat y' (cubePoint n i)) :=
        Finset.sum_congr rfl fun i _ ↦ hodd i
      rw [hevenSum, hoddSum]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ih x' y']
      ring

/-- The multilinear "next" kernel in canonical interpolation form.

`nextHat x y` is the `2n`-variable multilinear polynomial whose value on Boolean
cube points is `1` exactly when the `y`-index is the terminal successor of the
`x`-index, and `0` otherwise. -/
def nextHat [CommRing R] (x y : Vector R n) : R :=
  ∑ i : Fin (2 ^ n),
    eqHat x (cubePoint n i) * eqHat y (cubePoint n (nextIndex n i))

/-- With the right input fixed, `nextHat` is represented by a canonical
`n`-variable multilinear-evaluation table in its left input. -/
theorem nextHat_left_mle [CommRing R] (y : Vector R n) :
    ∃ v : CMlPolynomialEval R n, ∀ x, nextHat x y = mleEval v x := by
  let v : CMlPolynomialEval R n :=
    Vector.ofFn fun i ↦ eqHat y (cubePoint n (nextIndex n i))
  have hv (i : Fin (2 ^ n)) : v[i] = eqHat y (cubePoint n (nextIndex n i)) := by
    change (Vector.ofFn fun i ↦ eqHat y (cubePoint n (nextIndex n i)))[i.val] = _
    simp
  refine ⟨v, fun x ↦ ?_⟩
  unfold nextHat mleEval
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hv]

/-- With the left input fixed, `nextHat` is represented by a canonical
`n`-variable multilinear-evaluation table in its right input. Together with
`nextHat_left_mle`, this records the kernel's degree-at-most-one property in
each of its `2n` variables. -/
theorem nextHat_right_mle [CommRing R] (x : Vector R n) :
    ∃ v : CMlPolynomialEval R n, ∀ y, nextHat x y = mleEval v y := by
  let v : CMlPolynomialEval R n := Vector.ofFn fun j ↦
    ∑ i : Fin (2 ^ n),
      if nextIndex n i = j then eqHat x (cubePoint n i) else 0
  have hv (j : Fin (2 ^ n)) :
      v[j] = ∑ i : Fin (2 ^ n),
        if nextIndex n i = j then eqHat x (cubePoint n i) else 0 := by
    change (Vector.ofFn fun j ↦
      ∑ i : Fin (2 ^ n),
        if nextIndex n i = j then eqHat x (cubePoint n i) else 0)[j.val] = _
    simp
  refine ⟨v, fun y ↦ ?_⟩
  symm
  calc
    mleEval v y =
        ∑ j : Fin (2 ^ n), ∑ i : Fin (2 ^ n),
          eqHat y (cubePoint n j) *
            (if nextIndex n i = j then eqHat x (cubePoint n i) else 0) := by
      unfold mleEval
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hv, Finset.mul_sum]
    _ = ∑ i : Fin (2 ^ n), ∑ j : Fin (2 ^ n),
          eqHat y (cubePoint n j) *
            (if nextIndex n i = j then eqHat x (cubePoint n i) else 0) :=
      Finset.sum_comm
    _ = ∑ i : Fin (2 ^ n),
          eqHat x (cubePoint n i) * eqHat y (cubePoint n (nextIndex n i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single (nextIndex n i)]
      · simp only [if_pos, mul_comm]
      · intro j _ hji
        rw [if_neg (Ne.symm hji), mul_zero]
      · simp
    _ = nextHat x y := rfl

/-- Recurrence for the interpolation definition after appending the low bit. -/
private theorem nextHat_push [CommRing R] (x y : Vector R n) (a b : R) :
    nextHat (x.push a) (y.push b) =
      a * b *
          (eqHat x (cubePoint n (terminalIndex n)) *
            eqHat y (cubePoint n (terminalIndex n))) +
        (1 - a) * b * eqHat x y +
        a * (1 - b) *
          (nextHat x y -
            eqHat x (cubePoint n (terminalIndex n)) *
              eqHat y (cubePoint n (terminalIndex n))) := by
  let prefixTerm : Fin (2 ^ n) → R := fun i ↦
    eqHat x (cubePoint n i) * eqHat y (cubePoint n (nextIndex n i))
  let terminalWeight : R :=
    eqHat x (cubePoint n (terminalIndex n)) *
      eqHat y (cubePoint n (terminalIndex n))
  let globalTerm : Fin (2 ^ (n + 1)) → R := fun i ↦
    eqHat (x.push a) (cubePoint (n + 1) i) *
      eqHat (y.push b) (cubePoint (n + 1) (nextIndex (n + 1) i))
  change (∑ i : Fin (2 ^ (n + 1)), globalTerm i) = _
  rw [sum_even_odd]
  have heven : ∀ i : Fin (2 ^ n),
      globalTerm (evenIndex i) =
        (1 - a) * b *
          (eqHat x (cubePoint n i) * eqHat y (cubePoint n i)) := by
    intro i
    dsimp only [globalTerm]
    rw [nextIndex_evenIndex, cubePoint_evenIndex, cubePoint_oddIndex,
      eqHat_push, eqHat_push]
    ring
  have hevenSum :
      (∑ i : Fin (2 ^ n), globalTerm (evenIndex i)) = (1 - a) * b * eqHat x y := by
    calc
      (∑ i : Fin (2 ^ n), globalTerm (evenIndex i)) =
          ∑ i : Fin (2 ^ n),
            (1 - a) * b *
              (eqHat x (cubePoint n i) * eqHat y (cubePoint n i)) :=
        Finset.sum_congr rfl fun i _ ↦ heven i
      _ = (1 - a) * b *
          ∑ i : Fin (2 ^ n),
            eqHat x (cubePoint n i) * eqHat y (cubePoint n i) := by
        rw [Finset.mul_sum]
      _ = (1 - a) * b * eqHat x y := by
        rw [sum_eqHat_cubePoint_mul_eqHat_cubePoint]
  have hodd : ∀ i : Fin (2 ^ n),
      globalTerm (oddIndex i) =
        a * (1 - b) * prefixTerm i +
          if i = terminalIndex n then
            a * (b - (1 - b)) * terminalWeight
          else 0 := by
    intro i
    by_cases h : i.val + 1 < 2 ^ n
    · have hne : i ≠ terminalIndex n := by
        intro hi
        exact (not_succ_lt_iff_eq_terminal i).2 hi h
      dsimp only [globalTerm, prefixTerm]
      rw [nextIndex_oddIndex, dif_pos h, cubePoint_oddIndex, cubePoint_evenIndex,
        eqHat_push, eqHat_push, if_neg hne]
      unfold nextIndex
      rw [dif_pos h]
      ring
    · have hi : i = terminalIndex n := (not_succ_lt_iff_eq_terminal i).1 h
      subst i
      have hterminal :
          ¬(terminalIndex n).val + 1 < 2 ^ n :=
        (not_succ_lt_iff_eq_terminal (terminalIndex n)).2 rfl
      have hnext : nextIndex n (terminalIndex n) = terminalIndex n := by
        unfold nextIndex
        rw [dif_neg hterminal]
      dsimp only [globalTerm, prefixTerm, terminalWeight]
      rw [nextIndex_oddIndex, dif_neg hterminal, cubePoint_oddIndex,
        eqHat_push, eqHat_push, if_pos rfl, hnext]
      ring
  have hoddSum :
      (∑ i : Fin (2 ^ n), globalTerm (oddIndex i)) =
        a * (1 - b) * nextHat x y + a * (b - (1 - b)) * terminalWeight := by
    calc
      (∑ i : Fin (2 ^ n), globalTerm (oddIndex i)) =
          ∑ i : Fin (2 ^ n),
            (a * (1 - b) * prefixTerm i +
              if i = terminalIndex n then
                a * (b - (1 - b)) * terminalWeight
              else 0) :=
        Finset.sum_congr rfl fun i _ ↦ hodd i
      _ = (∑ i : Fin (2 ^ n), a * (1 - b) * prefixTerm i) +
          ∑ i : Fin (2 ^ n),
            if i = terminalIndex n then a * (b - (1 - b)) * terminalWeight else 0 := by
        rw [Finset.sum_add_distrib]
      _ = a * (1 - b) * (∑ i : Fin (2 ^ n), prefixTerm i) +
          a * (b - (1 - b)) * terminalWeight := by
        rw [Finset.mul_sum]
        simp
      _ = a * (1 - b) * nextHat x y + a * (b - (1 - b)) * terminalWeight := by
        rfl
  rw [hevenSum, hoddSum]
  dsimp only [terminalWeight]
  ring

/-- Equality factors strictly above carry-stop coordinate `k`. -/
def carryPrefix [CommRing R] (x y : Vector R n) (k : Fin n) : R :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ j < k),
    (x[j] * y[j] + (1 - x[j]) * (1 - y[j]))

/-- One-to-zero factors strictly below carry-stop coordinate `k`. -/
def carrySuffix [CommRing R] (x y : Vector R n) (k : Fin n) : R :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ k < j),
    x[j] * (1 - y[j])

/-- The closed carry-chain expression. The leading product is
the all-ones self-loop. In summand `k`, high bits `j < k` agree, bit `k`
changes from zero to one, and low bits `j > k` change from one to zero. -/
def nextHatCarry [CommRing R] (x y : Vector R n) : R :=
  (∏ j : Fin n, x[j] * y[j]) +
    ∑ k : Fin n, carryPrefix x y k * ((1 - x[k]) * y[k]) * carrySuffix x y k

private theorem carryPrefix_push_castSucc [CommRing R]
    (x y : Vector R n) (a b : R) (k : Fin n) :
    carryPrefix (x.push a) (y.push b) k.castSucc = carryPrefix x y k := by
  have hlast : ¬Fin.last n < k.castSucc := not_lt_of_ge (Fin.le_last _)
  simp [carryPrefix, Finset.prod_filter, Fin.prod_univ_castSucc, hlast]

private theorem carryPrefix_push_last [CommRing R] (x y : Vector R n) (a b : R) :
    carryPrefix (x.push a) (y.push b) (Fin.last n) = eqHat x y := by
  simp [carryPrefix, eqHat, Finset.prod_filter, Fin.prod_univ_castSucc]

private theorem carrySuffix_push_castSucc [CommRing R]
    (x y : Vector R n) (a b : R) (k : Fin n) :
    carrySuffix (x.push a) (y.push b) k.castSucc =
      carrySuffix x y k * (a * (1 - b)) := by
  simp [carrySuffix, Finset.prod_filter, Fin.prod_univ_castSucc]

private theorem carrySuffix_push_last [CommRing R] (x y : Vector R n) (a b : R) :
    carrySuffix (x.push a) (y.push b) (Fin.last n) = 1 := by
  have hnone : ∀ k : Fin n, ¬Fin.last n < k.castSucc := by
    intro k
    exact not_lt_of_ge (Fin.le_last _)
  simp [carrySuffix, Finset.prod_filter, Fin.prod_univ_castSucc, hnone]

/-- Recurrence for the carry-chain expression after appending the low bit. -/
private theorem nextHatCarry_push [CommRing R] (x y : Vector R n) (a b : R) :
    nextHatCarry (x.push a) (y.push b) =
      a * b * (∏ j : Fin n, x[j] * y[j]) +
        (1 - a) * b * eqHat x y +
        a * (1 - b) * (nextHatCarry x y - ∏ j : Fin n, x[j] * y[j]) := by
  rw [nextHatCarry, Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [carryPrefix_push_castSucc, carryPrefix_push_last,
    carrySuffix_push_castSucc, carrySuffix_push_last, mul_one]
  simp only [Fin.getElem_fin, Fin.val_castSucc, Fin.is_lt, Vector.getElem_push_lt,
    Fin.val_last, Vector.getElem_push_eq]
  have hfactor :
      (∑ k : Fin n,
        carryPrefix x y k * ((1 - x[k]) * y[k]) *
          (carrySuffix x y k * (a * (1 - b)))) =
        a * (1 - b) *
          ∑ k : Fin n, carryPrefix x y k * ((1 - x[k]) * y[k]) * carrySuffix x y k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  simp only [Fin.getElem_fin] at hfactor
  rw [hfactor]
  rw [nextHatCarry]
  simp only [Fin.getElem_fin]
  ring

/-- The interpolation definition of `nextHat` equals the closed
carry-chain expression at every field point, not only on the Boolean cube. -/
theorem nextHat_eq_carry [CommRing R] (x y : Vector R n) :
    nextHat x y = nextHatCarry x y := by
  induction n with
  | zero =>
      have hx : x = #v[] := Vector.eq_empty_of_size_eq_zero rfl
      have hy : y = #v[] := Vector.eq_empty_of_size_eq_zero rfl
      subst x
      subst y
      simp [nextHat, nextHatCarry, eqHat, cubePoint, nextIndex]
  | succ n ih =>
      obtain ⟨x', a, hx⟩ : ∃ (x' : Vector R n) (a : R), x = x'.push a :=
        Vector.exists_push
      obtain ⟨y', b, hy⟩ : ∃ (y' : Vector R n) (b : R), y = y'.push b :=
        Vector.exists_push
      rw [hx, hy, nextHat_push, nextHatCarry_push, ih x' y',
        eqHat_cubePoint_terminal, eqHat_cubePoint_terminal]
      rw [← Finset.prod_mul_distrib]

/-- The shifted column of a hypercube-evaluation table: the entry at index `i`
is the original entry at the terminal-successor index `nextIndex i`. -/
def shiftColumn (v : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  Vector.ofFn (fun i : Fin (2 ^ n) ↦ v[nextIndex n i])

/-- On Boolean points, `nextHat` is the indicator of the successor relation,
including the all-ones self-loop. -/
theorem nextHat_cubePoint [CommRing R] (i j : Fin (2 ^ n)) :
    nextHat (cubePoint n i) (cubePoint n j) =
      if nextIndex n i = j then (1 : R) else 0 := by
  classical
  unfold nextHat
  rw [Finset.sum_eq_single i]
  · simp only [eqHat_cubePoint_delta, if_pos, one_mul, eq_comm]
  · intro b _ hbi
    have hib : i ≠ b := fun h ↦ hbi h.symm
    simp [eqHat_cubePoint_delta, hib]
  · simp

/-- The shift identity. Evaluating the multilinear extension of the shifted
column `shiftColumn v` at a point `x` equals the finite sum over the original
column values weighted by `nextHat x (cubePoint n i)`. -/
theorem shift_eq_sum [CommRing R] (v : CMlPolynomialEval R n) (x : Vector R n) :
    mleEval (shiftColumn v) x =
      ∑ i : Fin (2 ^ n), nextHat x (cubePoint n i) * v[i] := by
  convert eqHat_interpolation (shiftColumn v) x using 1
  simp +decide only [nextHat, eqHat_cubePoint_delta, shiftColumn]
  simp +decide [Finset.sum_mul, Vector.getElem_ofFn]
  rw [Finset.sum_comm, Finset.sum_congr rfl]
  intro i _
  rw [Finset.sum_eq_single (nextIndex n i)]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

end CompPoly.Multilinear
