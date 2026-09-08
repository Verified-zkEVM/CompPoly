/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Fields.Binary.Tower.Abstract.Algebra
import CompPoly.Fields.Binary.Tower.Concrete.Algebra

/-!
# Binary tower algebra regression tests

Both tower instances satisfy the generic self-map law at symbolic levels. Adjacent maps
remain the existing canonical embeddings, and skipping a level agrees with composition.
All checks quantify over arbitrary field elements rather than testing only zero and one.
-/

namespace CompPolyTests.BinaryTowerAlgebra

open BinaryTower ConcreteBinaryTower

example (k : ℕ) (h : k ≤ k) (x : BTField k) :
    AlgebraTower.algebraMap (AT := BTField) k k h x = x := by
  simp only [AlgebraTower.algebraMap_self_apply]

example (k : ℕ) (h : k ≤ k) (x : ConcreteBTField k) :
    AlgebraTower.algebraMap (AT := ConcreteBTField) k k h x = x := by
  simp only [AlgebraTower.algebraMap_self_apply]

example (k : ℕ) (x : BTField k) :
    AlgebraTower.algebraMap (AT := BTField) k (k + 1) (by omega) x =
      canonicalEmbedding k x := by
  change towerAlgebraMap k (k + 1) _ x = _
  rw [towerAlgebraMap_succ_1]

example (k : ℕ) (x : ConcreteBTField k) :
    AlgebraTower.algebraMap (AT := ConcreteBTField) k (k + 1) (by omega) x =
      canonicalAlgMap k x := by
  change concreteTowerAlgebraMap k (k + 1) _ x = _
  rw [concreteTowerAlgebraMap_succ_1]

example (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (x : BTField i) :
    AlgebraTower.algebraMap (AT := BTField) i k (hij.trans hjk) x =
      AlgebraTower.algebraMap (AT := BTField) j k hjk
        (AlgebraTower.algebraMap (AT := BTField) i j hij x) := by
  rw [AlgebraTower.coherence', RingHom.comp_apply]

example (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (x : ConcreteBTField i) :
    AlgebraTower.algebraMap (AT := ConcreteBTField) i k (hij.trans hjk) x =
      AlgebraTower.algebraMap (AT := ConcreteBTField) j k hjk
        (AlgebraTower.algebraMap (AT := ConcreteBTField) i j hij x) := by
  rw [AlgebraTower.coherence', RingHom.comp_apply]

example (k : ℕ) (x : BTField k) :
    AlgebraTower.algebraMap (AT := BTField) k (k + 2) (by omega) x =
      canonicalEmbedding (k + 1) (canonicalEmbedding k x) := by
  change towerAlgebraMap k (k + 2) _ x = _
  rw [towerAlgebraMap_assoc (k + 2) (k + 1) k (by omega) (by omega)]
  rw [towerAlgebraMap_succ_1, towerAlgebraMap_succ_1, RingHom.comp_apply]

example (k : ℕ) (x : ConcreteBTField k) :
    AlgebraTower.algebraMap (AT := ConcreteBTField) k (k + 2) (by omega) x =
      canonicalAlgMap (k + 1) (canonicalAlgMap k x) := by
  change concreteTowerAlgebraMap k (k + 2) _ x = _
  rw [concreteTowerAlgebraMap_assoc (k + 2) (k + 1) k (by omega) (by omega)]
  rw [concreteTowerAlgebraMap_succ_1, concreteTowerAlgebraMap_succ_1, RingHom.comp_apply]

end CompPolyTests.BinaryTowerAlgebra
