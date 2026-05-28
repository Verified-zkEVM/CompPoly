/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Basic

/-!
# Root Extraction Helpers

Candidate extraction, validation, and deduplication helpers for univariate root
finding.
-/

namespace CompPoly

namespace CPolynomial

/-- Extract the root of a represented nonconstant linear factor. -/
def linearRootOfFactor? {F : Type*} [Field F] [BEq F]
    (factor : CPolynomial F) : Option F :=
  if factor.val.size ≤ 2 && !(factor.coeff 1 == 0) then
    some (-(factor.coeff 0) / factor.coeff 1)
  else
    none

/-- Keep only candidates that are actual roots of the original polynomial. -/
def validateRootCandidates {F : Type*} [Field F] [BEq F]
    (p : CPolynomial F) (candidates : Array F) : Array F :=
  candidates.filter fun a => CPolynomial.evalHorner a p == 0

/-- Extract, validate, and deduplicate roots from a list of linear factors. -/
def rootsFromLinearFactors {F : Type*} [Field F] [BEq F]
    (p : CPolynomial F) (factors : Array (CPolynomial F)) : Array F :=
  let candidates := (factors.toList.filterMap linearRootOfFactor?).toArray
  (validateRootCandidates p candidates).eraseDups

end CPolynomial

end CompPoly
