/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Extension.Defs

/-!
# Base change of extension parameters

`ExtensionParams.map e P` maps the coefficients of `P`'s modulus along a ring homomorphism
`e : F →+* G`, and `ExtensionParams.map_poly` shows that its polynomial is `P.poly.map e`. Along a
ring isomorphism irreducibility transfers (`irreducible_map_ringEquiv`), so an irreducibility
certificate proved over one presentation of a field, such as `ZMod p`, serves every isomorphic
one, such as a Montgomery carrier.
-/

@[expose] public section

namespace CompPoly.Extension

open Polynomial

variable {F G : Type*} [Field F] [Field G]

/-- Irreducibility transfers along a ring isomorphism of the coefficients. -/
theorem irreducible_map_ringEquiv (e : F ≃+* G) {f : F[X]} (h : Irreducible f) :
    Irreducible (f.map (e : F →+* G)) :=
  h.map (mapEquiv e)

namespace ExtensionParams

/-- The parameters with the modulus' coefficients mapped along `e`. -/
def map (e : F →+* G) (P : ExtensionParams F) : ExtensionParams G where
  d := P.d
  two_le := P.two_le
  lower := P.lower.map e
  q := P.q

@[simp] theorem map_d (e : F →+* G) (P : ExtensionParams F) : (P.map e).d = P.d := rfl
@[simp] theorem map_q (e : F →+* G) (P : ExtensionParams F) : (P.map e).q = P.q := rfl

theorem map_poly (e : F →+* G) (P : ExtensionParams F) : (P.map e).poly = P.poly.map e := by
  simp only [poly, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum,
    Polynomial.map_mul, map_C]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by
    simp only [lowerCoeff, map, Vector.getElem_map]

theorem irreducible_map_poly (e : F ≃+* G) (P : ExtensionParams F) (h : Irreducible P.poly) :
    Irreducible (P.map (e : F →+* G)).poly := by
  rw [map_poly]; exact irreducible_map_ringEquiv e h

end ExtensionParams

end CompPoly.Extension
