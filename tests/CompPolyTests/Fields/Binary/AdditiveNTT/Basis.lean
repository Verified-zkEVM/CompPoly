/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Fields.Binary.AdditiveNTT.Impl

/-!
# Executable tower basis regressions

The basis used by the additive NTT reconstructs arbitrary concrete tower elements and
recovers arbitrary coefficient vectors at every level, including level zero.
-/

open scoped BigOperators
open ConcreteBinaryTower AdditiveNTT

namespace CompPolyTests.AdditiveNTTBasis

example (k : ℕ) (x : ConcreteBTField k) :
    letI := ConcreteBTFieldAlgebra (l := 0) (r := k) (h_le := by omega)
    ∑ i, (multilinearBasis 0 k (by omega)).repr x i • computableBasisExplicit k i = x := by
  let := ConcreteBTFieldAlgebra (l := 0) (r := k) (h_le := by omega)
  simp_rw [computableBasisExplicit_eq_multilinearBasis]
  exact (multilinearBasis 0 k (by omega)).sum_repr x

example (k : ℕ) (c : Fin (2 ^ k) → ConcreteBTField 0) (i : Fin (2 ^ k)) :
    letI := ConcreteBTFieldAlgebra (l := 0) (r := k) (h_le := by omega)
    (multilinearBasis 0 k (by omega)).repr (∑ j, c j • computableBasisExplicit k j) i = c i := by
  let := ConcreteBTFieldAlgebra (l := 0) (r := k) (h_le := by omega)
  simp_rw [computableBasisExplicit_eq_multilinearBasis]
  exact congrFun ((multilinearBasis 0 k (by omega)).repr_sum_self c) i

end CompPolyTests.AdditiveNTTBasis
