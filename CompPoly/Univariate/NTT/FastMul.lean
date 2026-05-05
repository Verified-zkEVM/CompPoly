/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu
-/
import CompPoly.Univariate.NTT.Domain
import CompPoly.Univariate.NTT.Forward
import CompPoly.Univariate.NTT.Inverse
import CompPoly.Univariate.Raw
import CompPoly.Univariate.ToPoly.Equiv
import Mathlib.Algebra.Field.GeomSum

/-!
# Fast Multiplication via NTT

This file wires forward NTT, pointwise multiplication, and inverse NTT into a
spec/implementation pipeline.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace FastMul

variable {R : Type*} [Field R]

/-- Pointwise multiplication in evaluation form. -/
@[inline] def pointwiseMul (D : Domain R) (a b : Array R) : Array R :=
  Array.ofFn (fun i : D.Idx => a.getD i.1 0 * b.getD i.1 0)

@[simp] theorem size_pointwiseMul (D : Domain R) (a b : Array R) :
    (pointwiseMul D a b).size = D.n := by
  simp [pointwiseMul]

private theorem omegaInv_pow_mul_eq (D : Domain R) {i : Nat} (hi : i < D.n) (k : Nat) :
    D.omegaInv ^ (i * k) = D.omega ^ ((D.n - i) * k) := by
  rw [show D.omegaInv ^ (i * k) = (D.omegaInv ^ i) ^ k by rw [pow_mul]]
  rw [show D.omega ^ ((D.n - i) * k) = (D.omega ^ (D.n - i)) ^ k by rw [pow_mul]]
  congr 1
  rw [Domain.omegaInv, inv_pow]
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_add]
  have hle : i ≤ D.n := Nat.le_of_lt hi
  rw [Nat.sub_add_cancel hle]
  simpa [Domain.n] using D.primitive.pow_eq_one

private theorem kernel_term_eq (D : Domain R) {i : Nat} (hi : i < D.n) (j k : Nat) :
    D.omega ^ (k * j) * D.omegaInv ^ (i * k) =
      D.omega ^ ((j + (D.n - i)) * k) := by
  rw [omegaInv_pow_mul_eq D hi k]
  rw [← pow_add]
  congr 1
  ring

private theorem omega_sum_pow_mul_eq_if_dvd (D : Domain R) (m : Nat) :
    (∑ k : D.Idx, D.omega ^ (m * (k : Nat))) = if D.n ∣ m then (D.n : R) else 0 := by
  by_cases hdiv : D.n ∣ m
  · rw [if_pos hdiv]
    rcases hdiv with ⟨t, rfl⟩
    trans ∑ _k : D.Idx, (1 : R)
    · apply Finset.sum_congr rfl
      intro k _hk
      rw [show D.n * t * (k : Nat) = D.n * (t * (k : Nat)) by ring]
      rw [pow_mul]
      simp [Domain.n, D.primitive.pow_eq_one]
    · simp
  · rw [if_neg hdiv]
    have hne : D.omega ^ m ≠ 1 := by
      intro h
      exact hdiv ((D.primitive.pow_eq_one_iff_dvd m).mp h)
    have hpow : (D.omega ^ m) ^ D.n = 1 := by
      rw [← pow_mul]
      rw [Nat.mul_comm]
      rw [pow_mul]
      simp [Domain.n, D.primitive.pow_eq_one]
    calc
      (∑ k : D.Idx, D.omega ^ (m * (k : Nat))) =
          ∑ k : D.Idx, (D.omega ^ m) ^ (k : Nat) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [pow_mul]
      _ = (∑ k ∈ Finset.range D.n, (D.omega ^ m) ^ k) := by
            rw [Fin.sum_univ_eq_sum_range]
      _ = 0 := by
            rw [geom_sum_eq hne]
            rw [hpow]
            simp

private theorem dvd_add_sub_iff_fin_eq (D : Domain R) (i j : D.Idx) :
    D.n ∣ (j.1 + (D.n - i.1)) ↔ j = i := by
  constructor
  · intro h
    rcases h with ⟨t, ht⟩
    have hlt : j.1 + (D.n - i.1) < 2 * D.n := by omega
    have hpos : 0 < j.1 + (D.n - i.1) := by
      have : 0 < D.n - i.1 := by omega
      omega
    have htlt : t < 2 := by
      rw [ht] at hlt
      nlinarith [D.n_pos]
    have htpos : 0 < t := by
      rw [ht] at hpos
      nlinarith [D.n_pos]
    interval_cases t
    apply Fin.ext
    omega
  · intro h
    subst h
    use 1
    omega

private theorem kernel_sum_eq_if (D : Domain R) (i j : D.Idx) :
    (∑ k : D.Idx, D.omega ^ ((k : Nat) * (j : Nat)) *
        D.omegaInv ^ ((i : Nat) * (k : Nat))) =
      if j = i then (D.n : R) else 0 := by
  calc
    (∑ k : D.Idx, D.omega ^ ((k : Nat) * (j : Nat)) *
        D.omegaInv ^ ((i : Nat) * (k : Nat))) =
        ∑ k : D.Idx, D.omega ^ (((j : Nat) + (D.n - (i : Nat))) * (k : Nat)) := by
          apply Finset.sum_congr rfl
          intro k _
          exact kernel_term_eq D i.is_lt (j : Nat) (k : Nat)
    _ = if D.n ∣ ((j : Nat) + (D.n - (i : Nat))) then (D.n : R) else 0 := by
          exact omega_sum_pow_mul_eq_if_dvd D ((j : Nat) + (D.n - (i : Nat)))
    _ = if j = i then (D.n : R) else 0 := by
          by_cases h : j = i
          · rw [if_pos h, if_pos ((dvd_add_sub_iff_fin_eq D i j).mpr h)]
          · rw [if_neg h, if_neg (mt (dvd_add_sub_iff_fin_eq D i j).mp h)]

private theorem inverse_forwardSpec_coeff_of_lt (D : Domain R) (a : CPolynomial.Raw R)
    {i : Nat} (hi : i < D.n) :
    CPolynomial.Raw.coeff (Inverse.inverseSpec D (Forward.forwardSpec D a)) i = a.coeff i := by
  have hsize : i < (Inverse.inverseSpec D (Forward.forwardSpec D a)).size := by
    simpa [Inverse.inverseSpec] using hi
  rw [CPolynomial.Raw.coeff]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsize]
  simp [Inverse.inverseSpec, Inverse.inttAt, Forward.forwardSpec, Forward.nttAt,
    CPolynomial.Raw.coeff]
  let ii : D.Idx := ⟨i, hi⟩
  calc
    D.nInv * (∑ x : D.Idx,
      (∑ x_1 : D.Idx, a[x_1.1]?.getD 0 * D.omega ^ (x.1 * x_1.1)) *
        D.omegaInv ^ (i * x.1))
      = D.nInv * (∑ x : D.Idx, ∑ x_1 : D.Idx,
          a[x_1.1]?.getD 0 *
            (D.omega ^ (x.1 * x_1.1) * D.omegaInv ^ (i * x.1))) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x_1 _
          ring
    _ = D.nInv * (∑ x_1 : D.Idx, ∑ x : D.Idx,
          a[x_1.1]?.getD 0 *
            (D.omega ^ (x.1 * x_1.1) * D.omegaInv ^ (i * x.1))) := by
          rw [Finset.sum_comm]
    _ = D.nInv * (∑ x_1 : D.Idx,
          a[x_1.1]?.getD 0 * (∑ x : D.Idx,
            D.omega ^ (x.1 * x_1.1) * D.omegaInv ^ (i * x.1))) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x_1 _
          rw [Finset.mul_sum]
    _ = D.nInv * (∑ x_1 : D.Idx,
          a[x_1.1]?.getD 0 * (if x_1 = ii then (D.n : R) else 0)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x_1 _
          rw [kernel_sum_eq_if D ii x_1]
    _ = a[i]?.getD 0 := by
          rw [Finset.sum_eq_single ii]
          · have hn : ((D.n : Nat) : R) ≠ 0 := by
              simpa [Domain.n] using D.natCast_ne_zero
            simp [ii]
            rw [Domain.nInv]
            rw [show (2 : R) ^ D.logN = ((D.n : Nat) : R) by simp [Domain.n]]
            rw [_root_.mul_comm (a[i]?.getD 0) (((D.n : Nat) : R))]
            rw [← _root_.mul_assoc]
            rw [inv_mul_cancel₀ hn]
            simp
          · intro b _hb hb
            simp [hb]
          · intro hii
            exact (hii (Finset.mem_univ ii)).elim

section RawMul

variable [BEq R] [LawfulBEq R]

private theorem coeff_zero_of_trim_size_le
    (a : CPolynomial.Raw R) {i : Nat} (hi : a.trim.size ≤ i) : a.coeff i = 0 := by
  rw [← CPolynomial.Raw.Trim.coeff_eq_coeff a i]
  simp [CPolynomial.Raw.coeff, hi]

omit [BEq R] [LawfulBEq R] in
private theorem coeff_truncate (m : Nat) (a : CPolynomial.Raw R) (i : Nat) :
    (Domain.truncate m a).coeff i = if i < m then a.coeff i else 0 := by
  simp [Domain.truncate, CPolynomial.Raw.coeff, Array.getElem?_extract]
  by_cases hi : i < m
  · simp [hi]
    by_cases ha : i < a.size
    · simp [ha]
    · simp [ha]
  · simp [hi]

private theorem mul_coeff_eq_zero_of_requiredLength_le
    (p q : CPolynomial.Raw R) {i : Nat} (hi : Domain.requiredLength p q ≤ i) :
    (p * q).coeff i = 0 := by
  rw [CPolynomial.Raw.mul_coeff]
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hpx : p.trim.size ≤ x
  · have hp0 : p.coeff x = 0 := coeff_zero_of_trim_size_le p hpx
    simp [hp0]
  · have hxlt : x < p.trim.size := Nat.lt_of_not_ge hpx
    have hqle : q.trim.size ≤ i - x := by
      simp [Domain.requiredLength] at hi
      omega
    have hq0 : q.coeff (i - x) = 0 := coeff_zero_of_trim_size_le q hqle
    simp [hq0]

private theorem mul_coeff_eq_zero_of_left_trim_size_zero
    (p q : CPolynomial.Raw R) (hp : p.trim.size = 0) (i : Nat) :
    (p * q).coeff i = 0 := by
  rw [CPolynomial.Raw.mul_coeff]
  apply Finset.sum_eq_zero
  intro x hx
  have hp0 : p.coeff x = 0 := coeff_zero_of_trim_size_le p (by omega)
  simp [hp0]

private theorem mul_coeff_eq_zero_of_right_trim_size_zero
    (p q : CPolynomial.Raw R) (hq : q.trim.size = 0) (i : Nat) :
    (p * q).coeff i = 0 := by
  rw [CPolynomial.Raw.mul_coeff]
  apply Finset.sum_eq_zero
  intro x hx
  have hq0 : q.coeff (i - x) = 0 := coeff_zero_of_trim_size_le q (by omega)
  simp [hq0]

private theorem natDegree_toPoly_lt_of_trim_size_le
    (D : Domain R) (a : CPolynomial.Raw R) (ha : a.trim.size ≤ D.n) :
    a.toPoly.natDegree < D.n := by
  by_cases hzero : a.toPoly = 0
  · rw [hzero]
    exact D.n_pos
  · have hround := CPolynomial.Raw.toImpl_toPoly (R := R) a
    have hsize : a.toPoly.toImpl.size = a.trim.size := congrArg Array.size hround
    rcases CPolynomial.Raw.toImpl_elim a.toPoly with ⟨hz, _himpl⟩ | ⟨_hnz, himpl⟩
    · exact (hzero hz).elim
    · have himpl_size : a.toPoly.toImpl.size = a.toPoly.natDegree + 1 := by
        simp [himpl]
      omega

private theorem natDegree_toPoly_lt_trim_size_of_pos
    (a : CPolynomial.Raw R) (ha : 0 < a.trim.size) :
    a.toPoly.natDegree < a.trim.size := by
  have hround := CPolynomial.Raw.toImpl_toPoly (R := R) a
  have hsize : a.toPoly.toImpl.size = a.trim.size := congrArg Array.size hround
  rcases CPolynomial.Raw.toImpl_elim a.toPoly with ⟨hz, himpl⟩ | ⟨_hnz, himpl⟩
  · have : a.trim.size = 0 := by
      rw [← hsize, himpl]
      simp
    omega
  · have himpl_size : a.toPoly.toImpl.size = a.toPoly.natDegree + 1 := by
      simp [himpl]
    omega

omit [BEq R] [LawfulBEq R] in
private theorem forwardSpec_get_eq_eval_of_natDegree_lt
    (D : Domain R) (a : CPolynomial.Raw R) (hdeg : a.toPoly.natDegree < D.n)
    (k : D.Idx) :
    (Forward.forwardSpec D a)[k.1] = a.eval (D.node k) := by
  calc
    (Forward.forwardSpec D a)[k.1]
        = ∑ j : D.Idx, a.coeff j.1 * (D.node k) ^ (j : Nat) := by
            simp [Forward.forwardSpec, Forward.nttAt, Domain.node, CPolynomial.Raw.coeff, pow_mul]
    _ = ∑ j ∈ Finset.range D.n, a.toPoly.coeff j * (D.node k) ^ j := by
            change (∑ j : Fin D.n,
                (fun j : Nat => a.coeff j * (D.node k) ^ j) j) =
              ∑ j ∈ Finset.range D.n, a.toPoly.coeff j * (D.node k) ^ j
            rw [Fin.sum_univ_eq_sum_range
              (f := fun j : Nat => a.coeff j * (D.node k) ^ j) (n := D.n)]
            apply Finset.sum_congr rfl
            intro j _
            rw [CPolynomial.Raw.coeff_toPoly]
    _ = a.toPoly.eval (D.node k) := by
            rw [Polynomial.eval_eq_sum_range' hdeg]
    _ = a.eval (D.node k) := by
            exact CPolynomial.Raw.eval_toPoly_eq_eval (D.node k) a

private theorem raw_eval_mul (x : R) (p q : CPolynomial.Raw R) :
    (p * q).eval x = p.eval x * q.eval x := by
  rw [← CPolynomial.Raw.eval_toPoly_eq_eval x (p * q)]
  rw [← CPolynomial.Raw.eval_toPoly_eq_eval x p]
  rw [← CPolynomial.Raw.eval_toPoly_eq_eval x q]
  have hpoly : (p * q).toPoly = p.toPoly * q.toPoly := by
    ext i
    exact CPolynomial.Raw.toPoly_mul_coeff p q i
  rw [hpoly]
  simp

private theorem pointwise_forwardSpec_eq_forwardSpec_mul_of_natDegree_lt
    (D : Domain R) (p q : CPolynomial.Raw R)
    (hpdeg : p.toPoly.natDegree < D.n) (hqdeg : q.toPoly.natDegree < D.n)
    (hpqdeg : (p * q).toPoly.natDegree < D.n) :
    pointwiseMul D (Forward.forwardSpec D p) (Forward.forwardSpec D q) =
      Forward.forwardSpec D (p * q) := by
  apply Array.ext
  · simp [pointwiseMul, Forward.forwardSpec]
  · intro i hi₁ hi₂
    have hiD : i < D.n := by simpa [pointwiseMul] using hi₁
    let k : D.Idx := ⟨i, hiD⟩
    have hpsize : i < (Forward.forwardSpec D p).size := by simpa [Forward.forwardSpec] using hiD
    have hqsize : i < (Forward.forwardSpec D q).size := by simpa [Forward.forwardSpec] using hiD
    have hpqsize : i < (Forward.forwardSpec D (p * q)).size := by simpa [Forward.forwardSpec] using hiD
    have hpget : (Forward.forwardSpec D p)[i]'hpsize = p.eval (D.node k) := by
      simpa [k] using forwardSpec_get_eq_eval_of_natDegree_lt D p hpdeg k
    have hqget : (Forward.forwardSpec D q)[i]'hqsize = q.eval (D.node k) := by
      simpa [k] using forwardSpec_get_eq_eval_of_natDegree_lt D q hqdeg k
    have hpqget : (Forward.forwardSpec D (p * q))[i]'hpqsize = (p * q).eval (D.node k) := by
      simpa [k] using forwardSpec_get_eq_eval_of_natDegree_lt D (p * q) hpqdeg k
    simp [pointwiseMul]
    rw [hpget, hqget, hpqget, raw_eval_mul]

private theorem forwardSpec_getD_eq_zero_of_trim_size_zero
    (D : Domain R) (p : CPolynomial.Raw R) (hp : p.trim.size = 0) (i : Nat) :
    (Forward.forwardSpec D p).getD i 0 = 0 := by
  by_cases hi : i < (Forward.forwardSpec D p).size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    simp only [Option.getD_some]
    have hiD : i < D.n := by simpa [Forward.forwardSpec] using hi
    let k : D.Idx := ⟨i, hiD⟩
    change (Forward.forwardSpec D p)[k.1] = 0
    simp [Forward.forwardSpec, Forward.nttAt]
    apply Finset.sum_eq_zero
    intro j _
    have hp0 : p.coeff j.1 = 0 := coeff_zero_of_trim_size_le p (by omega)
    simp [CPolynomial.Raw.coeff] at hp0
    simp [hp0]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hi)]
    simp

omit [BEq R] [LawfulBEq R] in
private theorem inverseSpec_getD_eq_zero_of_getD_zero
    (D : Domain R) (a : Array R) (ha : ∀ i : Nat, a.getD i 0 = 0) (i : Nat) :
    (Inverse.inverseSpec D a).getD i 0 = 0 := by
  by_cases hi : i < (Inverse.inverseSpec D a).size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    simp only [Option.getD_some]
    simp only [Inverse.inverseSpec, Inverse.inttAt, Array.getElem_ofFn]
    have hsum : (∑ j : D.Idx, a.getD j.1 0 * D.omegaInv ^ (i * j.1)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp [ha j.1]
    rw [hsum]
    simp
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hi)]
    simp

private theorem pointwise_getD_eq_zero_of_left_trim_size_zero
    (D : Domain R) (p q : CPolynomial.Raw R) (hp : p.trim.size = 0) (i : Nat) :
    (pointwiseMul D (Forward.forwardSpec D p) (Forward.forwardSpec D q)).getD i 0 = 0 := by
  by_cases hi : i < (pointwiseMul D (Forward.forwardSpec D p) (Forward.forwardSpec D q)).size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    simp [pointwiseMul]
    left
    have hpsize : i < (Forward.forwardSpec D p).size := by
      simpa [Forward.forwardSpec, pointwiseMul] using hi
    have hpget := forwardSpec_getD_eq_zero_of_trim_size_zero D p hp i
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hpsize] at hpget
    simpa using hpget
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hi)]
    simp

private theorem pointwise_getD_eq_zero_of_right_trim_size_zero
    (D : Domain R) (p q : CPolynomial.Raw R) (hq : q.trim.size = 0) (i : Nat) :
    (pointwiseMul D (Forward.forwardSpec D p) (Forward.forwardSpec D q)).getD i 0 = 0 := by
  by_cases hi : i < (pointwiseMul D (Forward.forwardSpec D p) (Forward.forwardSpec D q)).size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    simp [pointwiseMul]
    right
    have hqsize : i < (Forward.forwardSpec D q).size := by
      simpa [Forward.forwardSpec, pointwiseMul] using hi
    have hqget := forwardSpec_getD_eq_zero_of_trim_size_zero D q hq i
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hqsize] at hqget
    simpa using hqget
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hi)]
    simp

/-- Spec pipeline for NTT-based multiplication. -/
@[inline] def fastMulSpec (D : Domain R) (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  let pHat := Forward.forwardSpec D p
  let qHat := Forward.forwardSpec D q
  let cHat := pointwiseMul D pHat qHat
  let c := Inverse.inverseSpec D cHat
  (Domain.truncate (Domain.requiredLength p q) c).trim

private theorem fastMulSpec_coeff_eq_zero_of_left_trim_size_zero
    (D : Domain R) (p q : CPolynomial.Raw R) (hp : p.trim.size = 0) (i : Nat) :
    (fastMulSpec D p q).coeff i = 0 := by
  rw [fastMulSpec]
  rw [CPolynomial.Raw.Trim.coeff_eq_coeff]
  rw [coeff_truncate]
  by_cases hi : i < Domain.requiredLength p q
  · rw [if_pos hi]
    rw [CPolynomial.Raw.coeff]
    exact inverseSpec_getD_eq_zero_of_getD_zero D
      (pointwiseMul D (Forward.forwardSpec D p) (Forward.forwardSpec D q))
      (pointwise_getD_eq_zero_of_left_trim_size_zero D p q hp) i
  · rw [if_neg hi]

private theorem fastMulSpec_coeff_eq_zero_of_right_trim_size_zero
    (D : Domain R) (p q : CPolynomial.Raw R) (hq : q.trim.size = 0) (i : Nat) :
    (fastMulSpec D p q).coeff i = 0 := by
  rw [fastMulSpec]
  rw [CPolynomial.Raw.Trim.coeff_eq_coeff]
  rw [coeff_truncate]
  by_cases hi : i < Domain.requiredLength p q
  · rw [if_pos hi]
    rw [CPolynomial.Raw.coeff]
    exact inverseSpec_getD_eq_zero_of_getD_zero D
      (pointwiseMul D (Forward.forwardSpec D p) (Forward.forwardSpec D q))
      (pointwise_getD_eq_zero_of_right_trim_size_zero D p q hq) i
  · rw [if_neg hi]

/-- Implementation pipeline for NTT-based multiplication. -/
@[inline] def fastMulImpl (D : Domain R) (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  let pHat := Forward.forwardImpl D p
  let qHat := Forward.forwardImpl D q
  let cHat := pointwiseMul D pHat qHat
  let c := Inverse.inverseImpl D cHat
  (Domain.truncate (Domain.requiredLength p q) c).trim

omit [LawfulBEq R] in
theorem fastMulImpl_correct (D : Domain R) (p q : CPolynomial.Raw R) :
    fastMulImpl D p q = fastMulSpec D p q := by
  simp [fastMulImpl, fastMulSpec, Forward.forwardImpl_correct, Inverse.inverseImpl_correct]

theorem fastMulSpec_coeff (D : Domain R) (p q : CPolynomial.Raw R)
    (hfit : Domain.fits D p q) (i : Nat) :
    (fastMulSpec D p q).coeff i = (p * q).coeff i := by
  by_cases hpzero : p.trim.size = 0
  · rw [fastMulSpec_coeff_eq_zero_of_left_trim_size_zero D p q hpzero i]
    exact (mul_coeff_eq_zero_of_left_trim_size_zero p q hpzero i).symm
  · by_cases hqzero : q.trim.size = 0
    · rw [fastMulSpec_coeff_eq_zero_of_right_trim_size_zero D p q hqzero i]
      exact (mul_coeff_eq_zero_of_right_trim_size_zero p q hqzero i).symm
    · have hppos : 0 < p.trim.size := Nat.pos_of_ne_zero hpzero
      have hqpos : 0 < q.trim.size := Nat.pos_of_ne_zero hqzero
      have hfit' : Domain.requiredLength p q ≤ D.n := by
        simpa [Domain.fits] using hfit
      have hfitLen : p.trim.size + q.trim.size - 1 ≤ D.n := by
        simpa [Domain.requiredLength] using hfit'
      have hpdeg_lt_trim := natDegree_toPoly_lt_trim_size_of_pos p hppos
      have hqdeg_lt_trim := natDegree_toPoly_lt_trim_size_of_pos q hqpos
      have hpdeg : p.toPoly.natDegree < D.n := by
        omega
      have hqdeg : q.toPoly.natDegree < D.n := by
        omega
      have hpqdeg : (p * q).toPoly.natDegree < D.n := by
        have hpoly : (p * q).toPoly = p.toPoly * q.toPoly := by
          ext j
          exact CPolynomial.Raw.toPoly_mul_coeff p q j
        rw [hpoly]
        refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
        omega
      rw [fastMulSpec]
      rw [CPolynomial.Raw.Trim.coeff_eq_coeff]
      rw [coeff_truncate]
      by_cases hi : i < Domain.requiredLength p q
      · rw [if_pos hi]
        have hiD : i < D.n := Nat.lt_of_lt_of_le hi hfit'
        rw [CPolynomial.Raw.coeff]
        have hpoint :=
          pointwise_forwardSpec_eq_forwardSpec_mul_of_natDegree_lt D p q hpdeg hqdeg hpqdeg
        rw [hpoint]
        exact inverse_forwardSpec_coeff_of_lt D (p * q) hiD
      · rw [if_neg hi]
        exact (mul_coeff_eq_zero_of_requiredLength_le p q (Nat.le_of_not_lt hi)).symm

theorem fastMulSpec_eq_mul (D : Domain R) (p q : CPolynomial.Raw R)
    (hfit : Domain.fits D p q) : fastMulSpec D p q = p * q := by
  have hp : (fastMulSpec D p q).trim = fastMulSpec D p q := by
    simp [fastMulSpec, CPolynomial.Raw.Trim.trim_twice]
  have hq : (p * q).trim = p * q := by
    simpa using (CPolynomial.Raw.mul_is_trimmed (p := p) (q := q))
  refine CPolynomial.Raw.Trim.canonical_ext (p := fastMulSpec D p q) (q := p * q) hp hq ?_
  intro i
  exact fastMulSpec_coeff D p q hfit i

theorem fastMulImpl_eq_mul (D : Domain R) (p q : CPolynomial.Raw R)
    (hfit : Domain.fits D p q) : fastMulImpl D p q = p * q := by
  rw[fastMulImpl_correct]
  rw[fastMulSpec_eq_mul]
  exact hfit

end RawMul

end FastMul
end NTT
end CPolynomial
end CompPoly
