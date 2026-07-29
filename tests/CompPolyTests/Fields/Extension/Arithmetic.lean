/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Fields.BabyBear.Ext4
import CompPoly.Fields.Hachi.Ext4
import CompPoly.Fields.KoalaBear.Ext4

/-!
# Extension-field arithmetic tests

Executable regressions for `CompPoly/Fields/Extension/`. These check that the *compiled*
arithmetic works, not merely that the instances elaborate: a `Field` instance built by the
`Function.Injective.field` transport would be `noncomputable` and every `#guard` below would
fail to build.

Each field is exercised for:

* the defining relation `gen ^ d = W`, which pins down the wrap-around factor in `Ext.mul`;
* ring identities, which cross-check `mul` against `add`/`sub`;
* `x * x⁻¹ = 1` and `0⁻¹ = 0`, which exercise Fermat inversion;
* agreement of binary `^` with repeated multiplication.
-/

namespace CompPolyTests.Fields.Extension

open CompPoly.Extension

/-! ### KoalaBear, `X^4 - 3` -/

section KoalaBear
open KoalaBear

private def kbX : Ext4 := Ext.ofFn fun i => ((i : ℕ) + 1 : ℕ)
private def kbY : Ext4 := Ext.ofFn fun i => (2 * (i : ℕ) + 5 : ℕ)

-- The defining relation.
#guard (ext4Gen ^ 4) == (3 : Ext4)

-- Hand-computed product: with `kbX = (1,2,3,4)`, `kbY = (5,7,9,11)` and `W = 3`, the schoolbook
-- convolution is `(5,17,38,70,77,69,44)` and folding gives `c_k + 3 * c_{k+4}`.
#guard (kbX * kbY).coeffs.toArray.map (·.val) == #[236, 224, 170, 70]

-- Ring identities.
#guard (kbX + kbY) * (kbX - kbY) == kbX * kbX - kbY * kbY
#guard (kbX + kbY) ^ 2 == kbX * kbX + 2 * kbX * kbY + kbY * kbY
#guard kbX ^ 5 == kbX * kbX * kbX * kbX * kbX
#guard (3 : Ext4) * kbX == kbX + kbX + kbX

-- Inversion.
#guard kbX * kbX⁻¹ == 1
#guard kbY * kbY⁻¹ == 1
#guard ext4Gen * ext4Gen⁻¹ == 1
#guard (0 : Ext4)⁻¹ == 0
#guard (kbX / kbY) * kbY == kbX

-- The base field embeds as the constant coefficient.
#guard Ext.coeff (7 : Ext4) ⟨0, by norm_num⟩ == (7 : KoalaBear.Field)

end KoalaBear

/-! ### BabyBear, `X^4 - 11` -/

section BabyBear
open BabyBear

private def bbX : Ext4 := Ext.ofFn fun i => (7 * (i : ℕ) + 3 : ℕ)
private def bbY : Ext4 := Ext.ofFn fun i => ((i : ℕ) * (i : ℕ) + 2 : ℕ)

#guard (ext4Gen ^ 4) == (11 : Ext4)
#guard (bbX + bbY) * (bbX - bbY) == bbX * bbX - bbY * bbY
#guard bbX ^ 6 == (bbX * bbX * bbX) ^ 2
#guard bbX * bbX⁻¹ == 1
#guard bbY * bbY⁻¹ == 1
#guard (0 : Ext4)⁻¹ == 0

end BabyBear

/-! ### Hachi, `X^4 - 2` -/

section Hachi
open Hachi

private def haX : Ext4 := Ext.ofFn fun i => (7 * (i : ℕ) + 3 : ℕ)
private def haY : Ext4 := Ext.ofFn fun i => (3 * (i : ℕ) + 1 : ℕ)

#guard (ext4Gen ^ 4) == (2 : Ext4)
#guard (haX + haY) * (haX - haY) == haX * haX - haY * haY
#guard haX ^ 7 == haX * haX * haX * haX * haX * haX * haX
#guard haX * haX⁻¹ == 1
#guard haY * haY⁻¹ == 1
#guard (0 : Ext4)⁻¹ == 0
#guard (haX / haY) * haY == haX

end Hachi

end CompPolyTests.Fields.Extension
