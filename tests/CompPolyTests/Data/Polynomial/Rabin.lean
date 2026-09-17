/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Data.Polynomial.Rabin
public import Mathlib.Tactic.NormNum.Prime

/-!
# Rabin's test: the explicit-cardinality forms

`Polynomial.irreducible_of_rabin_of_card` and its two companions state Rabin's conditions at a
caller-supplied numeral `q` with `hcard : Fintype.card F = q`, which is the shape every concrete
field in the library uses. Two things are checked here.

* **Nothing is weakened.** Instantiating each `_of_card` form at `q := Fintype.card F` with `rfl`
  recovers the plain statement *verbatim*, so a later edit cannot silently add a hypothesis or
  shift an exponent. The opposite direction is each wrapper's own proof body, checked whenever the
  library builds. This mirrors `CompPolyTests.RabinCertificate.OfCardRoundTrip`.
* **The caller needs no cast.** Over `ZMod 5` the conditions are stated at the literal `5` and
  discharged by `exact`, with no `rw [hcard]` transport in the resulting proof term — the point of
  the `_of_card` forms.
-/

@[expose] public section

namespace CompPolyTests.Rabin

open Polynomial

/-! ### The `_of_card` forms are equivalent to the plain ones -/

namespace OfCardRoundTrip

variable {F : Type*} [Field F] [Fintype F]

/-- `irreducible_of_rabin_of_card` recovers `irreducible_of_rabin`. -/
theorem soundness_recovered {f : F[X]} {d : ℕ}
    (h_deg : f.natDegree = d) (h_pos : 0 < d)
    (h_trace : f ∣ X ^ (Fintype.card F ^ d) - X)
    (h_coprime : ∀ ℓ ∈ d.primeFactors, IsCoprime f (X ^ (Fintype.card F ^ (d / ℓ)) - X)) :
    Irreducible f :=
  irreducible_of_rabin_of_card rfl h_deg h_pos h_trace h_coprime

/-- `rabin_of_irreducible_of_card` recovers `rabin_of_irreducible`. -/
theorem completeness_recovered {f : F[X]} {d : ℕ}
    (h_deg : f.natDegree = d) (h_pos : 0 < d) (h_irr : Irreducible f) :
    f ∣ X ^ (Fintype.card F ^ d) - X ∧
      ∀ ℓ ∈ d.primeFactors, IsCoprime f (X ^ (Fintype.card F ^ (d / ℓ)) - X) :=
  rabin_of_irreducible_of_card rfl h_deg h_pos h_irr

/-- `irreducible_iff_rabin_of_card` recovers `irreducible_iff_rabin`. -/
theorem iff_recovered {f : F[X]} {d : ℕ} (h_deg : f.natDegree = d) (h_pos : 0 < d) :
    Irreducible f ↔
      (f ∣ X ^ (Fintype.card F ^ d) - X ∧
        ∀ ℓ ∈ d.primeFactors, IsCoprime f (X ^ (Fintype.card F ^ (d / ℓ)) - X)) :=
  irreducible_iff_rabin_of_card rfl h_deg h_pos

end OfCardRoundTrip

/-! ### A concrete caller states its conditions at the numeral -/

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Over `ZMod 5` the two Rabin conditions for a quadratic read `f ∣ X^(5^2) - X` and
`IsCoprime f (X^5 - X)` — literal exponents, applied without a cardinality rewrite. -/
theorem irreducible_of_rabin_zmod5_quadratic {f : (ZMod 5)[X]} (h_deg : f.natDegree = 2)
    (h_trace : f ∣ X ^ (5 ^ 2) - X) (h_cop : IsCoprime f (X ^ 5 - X)) :
    Irreducible f := by
  refine irreducible_of_rabin_of_card (ZMod.card 5) h_deg (by norm_num) h_trace fun ℓ hℓ => ?_
  rw [Nat.Prime.primeFactors Nat.prime_two, Finset.mem_singleton] at hℓ
  subst hℓ
  exact h_cop

end CompPolyTests.Rabin
