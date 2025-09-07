import CompPoly.Lawful
import CompPoly.Wheels
import CompPoly.Unlawful
-- import Mathlib

namespace CPoly

open Std

abbrev CMvPolynomial (n : ℕ) R [Zero R] : Type := Lawful n R

variable {R : Type}

namespace CMvPolynomial

def coeff {R : Type} {n : ℕ} [Zero R] (m : CMvMonomial n) (p : CMvPolynomial n R) : R :=
  p.1[m]?.getD 0

attribute [grind=] coeff.eq_def

@[ext, grind ext]
theorem ext {n : ℕ} [Zero R] (p q : CMvPolynomial n R)
  (h : ∀ m, coeff m p = coeff m q) : p = q := by
  unfold coeff at h
  rcases p with ⟨p, hp⟩; rcases q with ⟨q, hq⟩
  congr
  apply ExtTreeMap.ext_getElem?
  grind

attribute [grind=] Option.some_inj

@[simp, grind=]
lemma fromUnlawful_zero {n : ℕ} {R : Type} [Zero R] [BEq R] [LawfulBEq R] :
  Lawful.fromUnlawful 0 = (0 : Lawful n R) := by
  unfold Lawful.fromUnlawful
  grind

lemma add_getD? [CommSemiring R] [BEq R] [LawfulBEq R]
  {m : CMvMonomial n}
  {p q : CMvPolynomial n R}  :
  (p + q).val[m]?.getD 0 = p.val[m]?.getD 0 + q.val[m]?.getD 0
:= by
  rw [HAdd.hAdd, instHAdd, Add.add, Lawful.instAdd]; dsimp
  simp only [Lawful.add, Lawful.fromUnlawful];
  rw [HAdd.hAdd, instHAdd, Add.add, Unlawful.instAdd]; dsimp
  rw [Unlawful.filter_get]
  apply Unlawful.add_getD?

lemma coeff_add [CommSemiring R] [BEq R] [LawfulBEq R]
  {m : CMvMonomial n}
  {p q : CMvPolynomial n R} :
  coeff m (p + q) = coeff m p + coeff m q
:= by
  simp only [coeff, add_getD?]

lemma fromUnlawful_fold_eq_fold_fromUnlawful₀ [CommSemiring R] [BEq R] [LawfulBEq R]
  {t : List (CMvMonomial n × R)}
  {f : CMvMonomial n → R → Unlawful n R} :
  ∀ init : Unlawful n R,
  Lawful.fromUnlawful (List.foldl (fun u term => (f term.1 term.2) + u) init t) =
    List.foldl (fun l term => (Lawful.fromUnlawful (f term.1 term.2)) + l) (Lawful.fromUnlawful init) t
:= by
  induction' t with head tail ih
  · simp
  · intro init
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    generalize f head.1 head.2 = x
    ext m
    simp [coeff_add]
    unfold coeff Lawful.fromUnlawful
    simp [Unlawful.filter_get]
    apply Unlawful.add_getD?

lemma fromUnlawful_fold_eq_fold_fromUnlawful [CommSemiring R] [BEq R] [LawfulBEq R]
  {t : Unlawful n R}
  {f : CMvMonomial n → R → Unlawful n R} :
  Lawful.fromUnlawful (ExtTreeMap.foldl (fun u m c => (f m c) + u) 0 t) =
    ExtTreeMap.foldl (fun l m c => (Lawful.fromUnlawful (f m c)) + l) 0 t
:= by
  simp [ExtTreeMap.foldl_eq_foldl_toList]
  generalize list_def : ExtTreeMap.toList t = list
  rw [fromUnlawful_fold_eq_fold_fromUnlawful₀ 0]
  simp

def eval₂ {R S : Type} {n : ℕ} [Semiring R] [CommSemiring S] : (R →+* S) → (Fin n → S) → CMvPolynomial n R → S :=
  fun f vs p => ExtTreeMap.foldl (fun s m c => (f c * MonoR.evalMonomial vs m) + s) 0 p.1

def eval {R : Type} {n : ℕ} [CommSemiring R] : (Fin n → R) → CMvPolynomial n R → R := eval₂ (RingHom.id _)

def totalDegree {R : Type} {n : ℕ} [inst : CommSemiring R] : CMvPolynomial n R → ℕ :=
  fun p => p.1.foldl (fun cm m _ => max cm (CMvMonomial.totalDegree m)) 0

def degreeOf {R : Type} {n : ℕ} [CommSemiring R] (i : Fin n) : CMvPolynomial n R → ℕ :=
  fun p => p.1.foldl (fun cm m _ => max cm (CMvMonomial.degreeOf m i)) 0

end CMvPolynomial

end CPoly
