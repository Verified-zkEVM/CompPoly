/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Data.Polynomial.Rabin
public import Mathlib.Tactic.NormNum.Prime

/-!
# Rabin's test: the numeral-parameterized statements

`Polynomial.irreducible_of_rabin` and its two companions state Rabin's conditions at a
caller-supplied numeral `q` with `hcard : Fintype.card F = q`. Two things are checked here.

* **The `Fintype.card F` statement is still available.** Passing `rfl` for `hcard` has to give
  back the `Fintype.card F` form *verbatim*, so parameterizing by `q` costs an abstract caller
  nothing, and a later edit cannot silently add a hypothesis or shift an exponent. This mirrors
  `CompPolyTests.RabinCertificate.CardRflInstance`.
* **A concrete caller needs no cast.** Over `ZMod 5` the conditions are stated at the literal `5`
  and discharged by `exact`, with no `rw [hcard]` transport in the resulting proof term — which is
  what the numeral parameter exists for.
-/

@[expose] public section

namespace CompPolyTests.Rabin

open Polynomial

/-! ### `rfl` recovers the `Fintype.card F` statements -/

namespace CardRflInstance

variable {F : Type*} [Field F] [Fintype F]

/-- At `hcard := rfl`, `irreducible_of_rabin` is Rabin soundness at `Fintype.card F`. -/
theorem soundness_recovered {f : F[X]} {d : ℕ}
    (h_deg : f.natDegree = d) (h_pos : 0 < d)
    (h_trace : f ∣ X ^ (Fintype.card F ^ d) - X)
    (h_coprime : ∀ ℓ ∈ d.primeFactors, IsCoprime f (X ^ (Fintype.card F ^ (d / ℓ)) - X)) :
    Irreducible f :=
  irreducible_of_rabin rfl h_deg h_pos h_trace h_coprime

/-- At `hcard := rfl`, `rabin_of_irreducible` is Rabin completeness at `Fintype.card F`. -/
theorem completeness_recovered {f : F[X]} {d : ℕ}
    (h_deg : f.natDegree = d) (h_pos : 0 < d) (h_irr : Irreducible f) :
    f ∣ X ^ (Fintype.card F ^ d) - X ∧
      ∀ ℓ ∈ d.primeFactors, IsCoprime f (X ^ (Fintype.card F ^ (d / ℓ)) - X) :=
  rabin_of_irreducible rfl h_deg h_pos h_irr

/-- At `hcard := rfl`, `irreducible_iff_rabin` is the characterization at `Fintype.card F`. -/
theorem iff_recovered {f : F[X]} {d : ℕ} (h_deg : f.natDegree = d) (h_pos : 0 < d) :
    Irreducible f ↔
      (f ∣ X ^ (Fintype.card F ^ d) - X ∧
        ∀ ℓ ∈ d.primeFactors, IsCoprime f (X ^ (Fintype.card F ^ (d / ℓ)) - X)) :=
  irreducible_iff_rabin rfl h_deg h_pos

end CardRflInstance

/-! ### A concrete caller states its conditions at the numeral -/

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Over `ZMod 5` the two Rabin conditions for a quadratic read `f ∣ X^(5^2) - X` and
`IsCoprime f (X^5 - X)` — literal exponents, applied without a cardinality rewrite. -/
theorem irreducible_of_rabin_zmod5_quadratic {f : (ZMod 5)[X]} (h_deg : f.natDegree = 2)
    (h_trace : f ∣ X ^ (5 ^ 2) - X) (h_cop : IsCoprime f (X ^ 5 - X)) :
    Irreducible f := by
  refine irreducible_of_rabin (ZMod.card 5) h_deg (by norm_num) h_trace fun ℓ hℓ => ?_
  rw [Nat.Prime.primeFactors Nat.prime_two, Finset.mem_singleton] at hℓ
  subst hℓ
  exact h_cop

end CompPolyTests.Rabin
