/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Fields.Binary.Tower.Equiv

/-!
# Binary tower basis transport tests

The existing tower equivalence preserves multilinear basis indices, coefficient readback,
and reconstruction with the chosen scalar actions. Self and skipped endpoints remain usable,
and a swapped-index control distinguishes the two successor generators.
-/

namespace CompPolyTests.BinaryTowerBasisTransport

open ConcreteBinaryTower BinaryTower

example (i : ℕ) (h : i ≤ i) (q : Fin (2 ^ (i - i))) :
    (towerEquiv i).ringEquiv (ConcreteBinaryTower.multilinearBasis i i h q) =
      BinaryTower.multilinearBasis i i h q :=
  towerEquiv_multilinearBasis h q

example (i : ℕ) (q : Fin (2 ^ (i + 2 - i))) :
    (towerEquiv (i + 2)).ringEquiv
        (ConcreteBinaryTower.multilinearBasis i (i + 2) (by omega) q) =
      BinaryTower.multilinearBasis i (i + 2) (by omega) q :=
  towerEquiv_multilinearBasis (by omega) q

-- At self endpoints, select the modules induced by the chosen tower algebras.
example (i : ℕ) (x : ConcreteBTField i) (q : Fin (2 ^ (i - i))) :
    let := ConcreteBTFieldAlgebra (show i ≤ i from le_rfl)
    let := binaryAlgebraTower (show i ≤ i from le_rfl)
    let : Module (ConcreteBTField i) (ConcreteBTField i) := Algebra.toModule
    let : Module (BTField i) (BTField i) := Algebra.toModule
    (BinaryTower.multilinearBasis i i le_rfl).repr ((towerEquiv i).ringEquiv x) q =
      (towerEquiv i).ringEquiv ((ConcreteBinaryTower.multilinearBasis i i le_rfl).repr x q) :=
  multilinearBasis_repr_towerEquiv le_rfl x q

example {i j : ℕ} (h : i ≤ j) (x : ConcreteBTField j) :
    let := ConcreteBTFieldAlgebra h
    let := binaryAlgebraTower h
    ∑ q, (towerEquiv i).ringEquiv
        ((ConcreteBinaryTower.multilinearBasis i j h).repr x q) •
      BinaryTower.multilinearBasis i j h q = (towerEquiv j).ringEquiv x := by
  let := ConcreteBTFieldAlgebra h
  let := binaryAlgebraTower h
  simp_rw [← multilinearBasis_repr_towerEquiv h x]
  exact (BinaryTower.multilinearBasis i j h).sum_repr _

-- Interchanging the two generator indices is incompatible with the fixed tower equivalence.
example : (towerEquiv 3).ringEquiv
      (ConcreteBinaryTower.multilinearBasis 1 3 (by decide) 1) ≠
    BinaryTower.multilinearBasis 1 3 (by decide) 2 := by
  let := binaryAlgebraTower (show 1 ≤ 3 by decide)
  rw [towerEquiv_multilinearBasis]
  exact (BinaryTower.multilinearBasis 1 3 (by decide)).injective.ne (by decide)

end CompPolyTests.BinaryTowerBasisTransport
