/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.BF64.Basic
public import CompPoly.Fields.Binary.BF64.Reduce
public import CompPoly.Fields.Binary.BF64.Impl
public import CompPoly.Fields.Binary.BF64.Ext3

/-!
# `GF(2^64)` in a polynomial basis, and its cubic extension

Facade module. It re-exports the specification-side quotient model from
`CompPoly.Fields.Binary.BF64.Basic`, the reduction from `...Reduce`, the computable
`BitVec 64` carrier from `...Impl`, and the degree-three extension from `...Ext3`.
-/

@[expose] public section
