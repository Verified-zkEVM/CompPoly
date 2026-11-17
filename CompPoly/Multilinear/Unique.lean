/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import CompPoly.Multilinear.Equiv
public import CompPoly.Multilinear.TransformEquiv
public import CompPoly.ToMathlib.MvPolynomial.Nullstellensatz

/-!
  # Multilinear extensions on the Boolean hypercube

  - evaluation: a hypercube table evaluates to its entries at the Boolean vertices.
  - bridge: a coefficient form and its `MvPolynomial` image evaluate alike at every point.
  - uniqueness: no other polynomial of degree at most one per variable has those vertex values.

  So the multilinear extension computed by CompPoly is the multilinear extension.

  The reference is Thaler, "Proofs, Arguments, and Zero-Knowledge", Lemma 3.6.
-/

@[expose] public section

open MvPolynomial Finset

variable {R : Type*} {n : ℕ}

namespace CompPoly

namespace CMlPolynomialEval

/-- The Boolean vertex with index `i`, in little-endian order: coordinate `j` is bit `j` of `i`. -/
def vertex [Zero R] [One R] (i : Fin (2 ^ n)) : Vector R n :=
  Vector.ofFn fun j => if (BitVec.ofFin i).getLsb j then 1 else 0

/-- Every point with coordinates in `{0, 1}` is a Boolean vertex. -/
theorem exists_vertex_get_eq [Zero R] [One R] {x : Fin n → R}
    (hx : ∀ j, x j = 0 ∨ x j = 1) : ∃ i : Fin (2 ^ n), (vertex i).get = x := by
  classical
  refine ⟨Nat.binaryFinMapToNat (fun j => if x j = 1 then 1 else 0) fun j => ?_,
    funext fun j => ?_⟩
  · split <;> omega
  · have hbit := Nat.getBit_of_binaryFinMapToNat (fun j => if x j = 1 then 1 else 0)
      (fun j => by split <;> omega) j
    simp only [j.isLt, dite_true, Fin.eta, Nat.getBit_eq_testBit] at hbit
    simp only [vertex, Vector.get_ofFn, BitVec.getLsb, BitVec.toNat_ofFin]
    split_ifs at hbit ⊢
    · exact (‹x j = 1›).symm
    · exact ((hx j).resolve_right ‹¬x j = 1›).symm

/-- Two indices below `2 ^ n` are equal when their first `n` bits agree. -/
private lemma eq_of_bits {i k : Fin (2 ^ n)}
    (h : ∀ j : Fin n, (i : ℕ).testBit j = (k : ℕ).testBit j) : i = k := by
  refine Fin.ext (Nat.eq_of_testBit_eq fun j => ?_)
  by_cases hj : j < n
  · exact h ⟨j, hj⟩
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right two_pos (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le k.isLt (Nat.pow_le_pow_right two_pos (by omega)))]

variable [CommRing R]

/-- At a Boolean vertex the Lagrange basis is the indicator of that vertex. -/
theorem lagrangeBasis_vertex (i k : Fin (2 ^ n)) :
    (lagrangeBasis (vertex (R := R) i))[(k : ℕ)] = if i = k then 1 else 0 := by
  rw [← Fin.getElem_fin, lagrangeBasis_getElem]
  have hfac : ∀ j : Fin n, (if (BitVec.ofFin k).getLsb j then (vertex (R := R) i)[j]
      else 1 - (vertex (R := R) i)[j]) =
      if (i : ℕ).testBit j = (k : ℕ).testBit j then (1 : R) else 0 := fun j => by
    simp only [vertex, Vector.getElem_ofFn, BitVec.getLsb_eq_getElem, Fin.getElem_fin,
      BitVec.getElem_ofFin]
    by_cases hi : (i : ℕ).testBit j <;> by_cases hk : (k : ℕ).testBit j <;>
      simp only [hi, hk, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, sub_self, sub_zero]
  simp only [hfac, prod_ite_zero, prod_const_one]
  congr 1
  exact propext ⟨fun h => eq_of_bits fun j => h j (mem_univ j), fun h j _ => by rw [h]⟩

/-- A hypercube table evaluates to its entry `i` at the vertex `i`. -/
theorem eval_vertex (p : CMlPolynomialEval R n) (i : Fin (2 ^ n)) :
    eval p (vertex i) = p[i] := by
  rw [eval, Vector.dotProduct_eq_root_dotProduct, _root_.dotProduct,
    sum_eq_single i (fun k _ hk => by
      simp only [Vector.get_eq_getElem, lagrangeBasis_vertex, Ne.symm hk, ite_false, mul_zero])
      fun h => absurd (mem_univ i) h]
  simp only [Vector.get_eq_getElem, lagrangeBasis_vertex, ite_true, mul_one, Fin.getElem_fin]

/-- Hypercube tables with the same values at every vertex are equal. -/
theorem ext_of_eval_vertex {p q : CMlPolynomialEval R n}
    (h : ∀ i : Fin (2 ^ n), eval p (vertex i) = eval q (vertex i)) : p = q :=
  Vector.ext fun k hk => by simpa only [eval_vertex, Fin.getElem_fin] using h ⟨k, hk⟩

end CMlPolynomialEval

namespace CMlPolynomial

open CMlPolynomialEval (vertex exists_vertex_get_eq)

/-- At a Boolean vertex the monomial basis indicates the bitwise subsets of that vertex. -/
theorem monomialBasis_vertex [CommSemiring R] (i k : Fin (2 ^ n)) :
    (monomialBasis (vertex (R := R) i))[(k : ℕ)] = if (i : ℕ) &&& k = k then 1 else 0 := by
  rw [← Fin.getElem_fin, monomialBasis_getElem]
  have hfac : ∀ j : Fin n, (if (BitVec.ofFin k).getLsb j then (vertex (R := R) i)[j] else 1) =
      if (k : ℕ).testBit j → (i : ℕ).testBit j then (1 : R) else 0 := fun j => by
    simp only [vertex, Fin.getElem_fin, Vector.getElem_ofFn, BitVec.getLsb, BitVec.toNat_ofFin]
    by_cases hi : (i : ℕ).testBit j <;> by_cases hk : (k : ℕ).testBit j <;>
      simp only [hi, hk, Bool.false_eq_true, ↓reduceIte, imp_self, implies_true, imp_false,
        not_true_eq_false]
  simp only [hfac, prod_ite_zero, prod_const_one]
  congr 1
  refine propext ⟨fun h => Nat.eq_of_testBit_eq fun j => ?_, fun h j _ hk => ?_⟩
  · rw [Nat.testBit_and]
    by_cases hj : j < n
    · cases hk : (k : ℕ).testBit j
      · exact Bool.and_false _
      · rw [h ⟨j, hj⟩ (mem_univ _) hk, Bool.true_and]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le k.isLt (Nat.pow_le_pow_right two_pos (by omega))),
        Bool.and_false]
  · rw [← h, Nat.testBit_and, Bool.and_eq_true] at hk
    exact hk.1

/-- A coefficient form evaluates at the vertex `i` to entry `i` of its hypercube table. -/
theorem eval_vertex [CommRing R] (p : CMlPolynomial R n) (i : Fin (2 ^ n)) :
    eval p (vertex i) = (monoToLagrange n p)[i] := by
  rw [monoToLagrange_eq_monoToLagrangeSpec, monoToLagrangeSpec, eval,
    Vector.dotProduct_eq_root_dotProduct, _root_.dotProduct]
  simp only [Vector.get_eq_getElem, monomialBasis_vertex, mul_ite, mul_one, mul_zero,
    Fin.getElem_fin, Vector.getElem_ofFn]

/-- The coefficient form of a hypercube table evaluates to the table entries at the vertices. -/
theorem eval_lagrangeToMono_vertex [CommRing R] (f : CMlPolynomialEval R n) (i : Fin (2 ^ n)) :
    eval (lagrangeToMono n f) (vertex i) = f[i] := by
  rw [eval_vertex]
  exact congrArg (·[i]) (equivMonomialLagrangeRepr.right_inv f)

/-- Coefficient forms with the same values at every vertex are equal. -/
theorem ext_of_eval_vertex [CommRing R] {p q : CMlPolynomial R n}
    (h : ∀ i : Fin (2 ^ n), eval p (vertex i) = eval q (vertex i)) : p = q :=
  equivMonomialLagrangeRepr.injective <| Vector.ext fun k hk => by
    simpa only [equivMonomialLagrangeRepr, Equiv.coe_fn_mk, eval_vertex, Fin.getElem_fin]
      using h ⟨k, hk⟩

/-- The `MvPolynomial` image of a coefficient form evaluates like it at every point. -/
theorem eval_toMvPolynomial [CommSemiring R] (p : CMlPolynomial R n) (x : Vector R n) :
    MvPolynomial.eval x.get (toMvPolynomial p) = eval p x := by
  rw [toMvPolynomial, map_sum, eval, Vector.dotProduct_eq_root_dotProduct, _root_.dotProduct]
  refine sum_congr rfl fun i _ => ?_
  rw [eval_monomial, Finsupp.prod_fintype _ _ fun j => pow_zero _]
  simp only [Vector.get_eq_getElem, monomialBasis, Vector.getElem_ofFn, Fin.getElem_fin,
    monomialOfNat, Finsupp.onFinset_apply, Nat.getBit_eq_testBit, pow_ite, pow_one, pow_zero,
    BitVec.getLsb, BitVec.toNat_ofFin]

/-- The `MvPolynomial` image of a coefficient form has degree at most one in each variable. -/
theorem degreeOf_toMvPolynomial_le_one [CommSemiring R] (p : CMlPolynomial R n) (j : Fin n) :
    (toMvPolynomial p).degreeOf j ≤ 1 :=
  degreeOf_le_iff.2 fun m hm =>
    (mem_restrictDegree _ _ _).1 (toMvPolynomial_is_multilinear p) m hm j

/-- The `MvPolynomial` image of a coefficient form is fixed by its vertex values.

Any polynomial of degree at most one per variable that matches the form on the vertices equals it.
-/
theorem toMvPolynomial_eq_of_eval_vertex [CommRing R] [IsDomain R] {p : CMlPolynomial R n}
    {q : MvPolynomial (Fin n) R} (hq : ∀ j, q.degreeOf j ≤ 1)
    (h : ∀ i : Fin (2 ^ n), MvPolynomial.eval (vertex i).get q = eval p (vertex i)) :
    toMvPolynomial p = q :=
  eq_of_degreeOf_le_one_of_eval_zeroOne (degreeOf_toMvPolynomial_le_one p) hq fun x hx => by
    obtain ⟨i, rfl⟩ := exists_vertex_get_eq hx
    rw [eval_toMvPolynomial, h]

end CMlPolynomial

namespace CMlPolynomialEval

variable [CommRing R]

/-- The `MvPolynomial` image of a hypercube table evaluates to entry `i` at the vertex `i`. -/
theorem eval_toMvPolynomial_vertex (f : CMlPolynomialEval R n) (i : Fin (2 ^ n)) :
    MvPolynomial.eval (vertex i).get (toMvPolynomial f) = f[i] := by
  rw [toMvPolynomial, CMlPolynomial.eval_toMvPolynomial, CMlPolynomial.eval_lagrangeToMono_vertex]

/-- The `MvPolynomial` image of a hypercube table is its unique multilinear extension.

Any polynomial of degree at most one per variable taking the table values on the vertices equals it.
-/
theorem toMvPolynomial_eq_of_eval_vertex [IsDomain R] {f : CMlPolynomialEval R n}
    {q : MvPolynomial (Fin n) R} (hq : ∀ j, q.degreeOf j ≤ 1)
    (h : ∀ i : Fin (2 ^ n), MvPolynomial.eval (vertex i).get q = f[i]) :
    toMvPolynomial f = q :=
  CMlPolynomial.toMvPolynomial_eq_of_eval_vertex hq fun i => by
    rw [h, CMlPolynomial.eval_lagrangeToMono_vertex]

end CMlPolynomialEval

end CompPoly
