/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Fields.BabyBear.Ext4
public meta import CompPoly.Fields.Hachi.Ext4
public meta import CompPoly.Fields.KoalaBear.Ext4
public meta import CompPoly.Fields.KoalaBear.Ext5
-- The `#guard`s below run at elaboration time and so need the `meta` imports above; the
-- `example`s at the end are ordinary declarations and need this plain import as well.
public import CompPoly.Fields.Extension.Bridge
public import CompPoly.Fields.KoalaBear.Ext4
public import CompPoly.Fields.KoalaBear.Ext5

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

public meta section

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

-- Hand-computed product, as for KoalaBear: with `bbX = (3,10,17,24)`, `bbY = (2,3,6,11)` and
-- `W = 11`, the schoolbook convolution is `(6,29,82,192,284,331,264)` and folding the high half
-- back gives `c_k + 11 * c_{k+4}`.
#guard (bbX * bbY).coeffs.toArray.map (·.val) == #[3130, 3670, 2986, 192]

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

/-! ### KoalaBear, `X^5 + X^2 - 1` (non-binomial)

The quintic exercises the *general* monic-modulus path of `Ext.mul` (`monomialMod`), where the
reduction relation `X^5 = 1 - X^2` cascades instead of being a scalar fold.
-/

section KoalaBearQuintic
open KoalaBear

private def q5X : Ext5 := Ext.ofFn fun i => ((i : ℕ) + 1 : ℕ)
private def q5Y : Ext5 := Ext.ofFn fun i => (2 * (i : ℕ) + 5 : ℕ)

-- The defining relation `g^5 = 1 - g^2`.
#guard ext5Gen ^ 5 == (1 : Ext5) - ext5Gen ^ 2
#guard ext5Gen ^ 5 + ext5Gen ^ 2 == (1 : Ext5)

-- Hand-computed product: with `q5X = (1,2,3,4,5)` and `q5Y = (5,7,9,11,13)`, the schoolbook
-- convolution is `(5,17,38,70,115,130,128,107,65)`; reducing `X^5 = 1 - X^2` (so
-- `X^6 = X - X^3`, `X^7 = X^2 - X^4`, `X^8 = X^2 + X^3 - 1`) gives the result below.
#guard (q5X * q5Y).coeffs.toArray.map (·.val) == #[70, 145, 80, 7, 8]

-- Ring identities.
#guard (q5X + q5Y) * (q5X - q5Y) == q5X * q5X - q5Y * q5Y
#guard (q5X + q5Y) ^ 2 == q5X * q5X + 2 * q5X * q5Y + q5Y * q5Y
#guard q5X ^ 5 == q5X * q5X * q5X * q5X * q5X
#guard (3 : Ext5) * q5X == q5X + q5X + q5X

-- Inversion.
#guard q5X * q5X⁻¹ == 1
#guard q5Y * q5Y⁻¹ == 1
#guard ext5Gen * ext5Gen⁻¹ == 1
#guard (0 : Ext5)⁻¹ == 0
#guard (q5X / q5Y) * q5Y == q5X

-- The base field embeds as the constant coefficient.
#guard Ext.coeff (7 : Ext5) ⟨0, by norm_num⟩ == (7 : KoalaBear.Field)

-- The instances Mathlib consumers need actually resolve for the general modulus too.
example : Module KoalaBear.Field Ext5 := inferInstance
example : Algebra KoalaBear.Field Ext5 := inferInstance

end KoalaBearQuintic

/-! ### The `Algebra` surface

`Algebra F (Ext P)` introduces a second `SMul F (Ext P)` path (`Algebra.toSMul`) on top of the
one in `Extension/Defs.lean`. These guards confirm the new layer is computable and that the two
scalar actions agree — the same class of regression as the `Monoid.toNatPow` / `Ext.instPow`
shadowing that a `noncomputable` instance would cause.
-/

section Algebra
open KoalaBear

private def c : KoalaBear.Field := 5

#guard (Ext.ofBase c : Ext4).coeffs.toArray.map (·.val) == #[5, 0, 0, 0]
#guard (algebraMap KoalaBear.Field Ext4 c).coeffs.toArray.map (·.val) == #[5, 0, 0, 0]
#guard (Ext.gen : Ext4).coeffs.toArray.map (·.val) == #[0, 1, 0, 0]

-- `Algebra.smul_def` holds computationally, not just propositionally.
#guard c • kbX == algebraMap KoalaBear.Field Ext4 c * kbX

-- `ofBase` agrees with the numeral casts, so scalars and literals cannot diverge.
#guard (Ext.ofBase (3 : KoalaBear.Field) : Ext4) == (3 : Ext4)

-- The defining relation, as an executable check next to the `ext4Gen_pow_four` theorem.
#guard (Ext.gen : Ext4) ^ 4 == Ext.ofBase (3 : KoalaBear.Field)

-- The instances Mathlib consumers need actually resolve.
example : Module KoalaBear.Field Ext4 := inferInstance
example : Algebra KoalaBear.Field Ext4 := inferInstance
example : IsScalarTower KoalaBear.Field Ext4 Ext4 := inferInstance

end Algebra

end CompPolyTests.Fields.Extension
