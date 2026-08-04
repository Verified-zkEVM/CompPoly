/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import CompPoly.Data.ExtTreeMap.DTreeMap
public import Std.Data.ExtDTreeMap.Lemmas

/-!
# Auxiliary lemmas for `Std.ExtDTreeMap`

Bridge lemma lifting `DTreeMap.get?_filter_with_getKey_pfilter` to
`Std.ExtDTreeMap`, used in turn by the `Std.ExtTreeMap` layer.

Vendored from
[`Verified-zkEVM/ExtTreeMapLemmas`](https://github.com/Verified-zkEVM/ExtTreeMapLemmas)
(tag `v4.29.1`, commit `3fee686227f18dca03bb7fc42ca5a9275d6cfda6`).
-/

@[expose] public section

namespace Std

attribute [local instance low] beqOfOrd

theorem ExtDTreeMap.get?_filter_with_getKey_pfilter {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtDTreeMap α (fun _ => β) cmp) (f : α → β → Bool) (k : α) :
    Const.get? (m.filter f) k =
    (Const.get? m k).pfilter (fun v h' =>
      f (m.getKey k
          (Const.contains_eq_isSome_get?.trans (Option.isSome_of_eq_some h'))) v) :=
  Const.get?_filter

end Std
