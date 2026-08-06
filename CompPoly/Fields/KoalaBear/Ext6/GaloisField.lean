/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.KoalaBear.Ext6
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# `Ext6` as a computable model of `GaloisField KoalaBear.fieldSize 6`

Mathlib's `GaloisField p n` is the abstract field of order `p^n`, defined as a splitting field and
therefore noncomputable. Downstream developments that only need "the field of order `p^6`" state
things in those terms — ArkLib's `KoalaSextic := GaloisField KoalaBear.fieldSize 6` is exactly
this, used for the KoalaBear-sextic parameter point of the Proximity Prize open problems
([ABF26], ePrint 2026/680).

`ext6AlgEquivGaloisField` identifies `KoalaBear.Ext6` with that field, so the computable
arithmetic here is usable as a model for statements phrased over `GaloisField`.

Two things worth noting about *why* this is unconditional:

* `GaloisField p n` commits to no defining polynomial, so this is not a coincidence of
  presentation. Any two finite fields of the same cardinality are isomorphic, and the isomorphism
  follows from `card_ext6` alone — the choice of `X^6 + X^3 + 1` is irrelevant to it.
* The isomorphism is *noncanonical*, as Mathlib's own docstring says. There is no distinguished
  map, so nothing here pins down where `ext6Gen` lands. Consumers that need a specific element
  (a domain generator, a high-order element) should construct it on whichever side they compute.

This lives in its own module so that the `Mathlib.FieldTheory.Finite.GaloisField` import is
opt-in: users of `Ext6` who do not need the bridge do not pay for it.

The same one-liner works for any `Ext P` with a cardinality lemma in hand; `card_ext` in
`CompPoly/Fields/Extension/Field.lean` supplies it generically.
-/

@[expose] public section

namespace KoalaBear

/--
**`Ext6` is a computable model of `GaloisField KoalaBear.fieldSize 6`**, the abstract field of
order `p^6 ≈ 2^186`.

Noncomputable because the isomorphism is obtained by a splitting-field argument, not because
either side's arithmetic is: `Ext6` itself computes.
-/
noncomputable def ext6AlgEquivGaloisField :
    Ext6 ≃ₐ[Field] GaloisField fieldSize 6 :=
  GaloisField.algEquivGaloisFieldOfFintype fieldSize 6 card_ext6

end KoalaBear
