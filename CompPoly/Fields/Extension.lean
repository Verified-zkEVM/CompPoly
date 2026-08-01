/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Extension.Binomial
public import CompPoly.Fields.Extension.Bridge
public import CompPoly.Fields.Extension.Defs
public import CompPoly.Fields.Extension.Field

/-!
# Computable field extensions

Facade for the binomial field-extension stack. See the individual modules for details:

* `CompPoly/Fields/Extension/Binomial.lean` — irreducibility of `X^d - W` over a finite field,
  via Rabin's test collapsed to two base-field exponentiations.
* `CompPoly/Fields/Extension/Defs.lean` — `BinomialParams` and the coefficient-vector carrier
  `Ext P` with its ring operations.
* `CompPoly/Fields/Extension/Bridge.lean` — `toQuot : Ext P → AdjoinRoot P.poly` and the
  `CommRing` structure.
* `CompPoly/Fields/Extension/Field.lean` — bijectivity, cardinality, and the `Field` structure.
-/

@[expose] public section
