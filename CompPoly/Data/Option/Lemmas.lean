/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa
-/
module

public import Mathlib.Data.Option.Basic

/-!
# Auxiliary lemmas for `Option`
-/

@[expose] public section

namespace Option

/-- `Option.filter` leaves its argument alone exactly when the predicate holds of the contained
value. The `Option` analogue of `List.filter_eq_self` and `Array.filter_eq_self`. -/
theorem filter_eq_self {α : Type*} {o : Option α} {p : α → Bool} :
    o.filter p = o ↔ ∀ a ∈ o, p a := by
  cases o <;> simp

end Option
