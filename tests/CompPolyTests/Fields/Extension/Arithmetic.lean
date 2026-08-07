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
public meta import CompPoly.Fields.KoalaBear.Ext6
-- The `#guard`s below run at elaboration time and so need the `meta` imports above; the
-- `example`s at the end are ordinary declarations and need this plain import as well.
public import CompPoly.Fields.Extension.Bridge
public import CompPoly.Fields.KoalaBear.Ext4
public import CompPoly.Fields.KoalaBear.Ext5
public import CompPoly.Fields.KoalaBear.Ext6

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

/-! ### KoalaBear, `X^6 + X^3 + 1` (`Φ₉`)

The first *composite*-degree general modulus, so this section also pins down that the degree-6
Rabin packaging produced a genuine field: if `X^6 + X^3 + 1` were reducible, `Ext6` would not be
a field and the inversion guards below would fail.
-/

section KoalaBearSextic
open KoalaBear

private def s6X : Ext6 := Ext.ofFn fun i => ((i : ℕ) + 1 : ℕ)
private def s6Y : Ext6 := Ext.ofFn fun i => (2 * (i : ℕ) + 5 : ℕ)

-- The defining relation `θ^6 = -θ^3 - 1`.
#guard ext6Gen ^ 6 == -(ext6Gen ^ 3) - (1 : Ext6)
#guard ext6Gen ^ 6 + ext6Gen ^ 3 + 1 == (0 : Ext6)

-- `θ` is a primitive 9th root of unity, and `θ^3` a primitive cube root of unity.
#guard ext6Gen ^ 9 == (1 : Ext6)
#guard (ext6Gen ^ 3) ^ 3 == (1 : Ext6)
#guard (ext6Gen ^ 3) ^ 2 + ext6Gen ^ 3 + 1 == (0 : Ext6)
-- ...and `θ^3 ≠ 1`, so the order really is 9 and not 3.
#guard ext6Gen ^ 3 != (1 : Ext6)

-- Hand-computed product: with `s6X = (1,2,3,4,5,6)` and `s6Y = (5,7,9,11,13,15)`, the schoolbook
-- convolution is `(5,17,38,70,115,175,200,206,191,153,90)`. Reducing with `X^6 = -X^3 - 1`,
-- `X^7 = -X^4 - X`, `X^8 = -X^5 - X^2`, `X^9 = 1`, `X^10 = X` folds the top five terms down:
--   `c0 = 5 - 200 + 153 = -42`     `c3 = 70 - 200 = -130`
--   `c1 = 17 - 206 + 90 = -99`     `c4 = 115 - 206 = -91`
--   `c2 = 38 - 191 = -153`         `c5 = 175 - 191 = -16`
-- Note every fold is a plain add or subtract — no coefficient multiplications, which is the
-- arithmetic reason `Φ₉` was chosen over the other irreducible sextics.
#guard (s6X * s6Y).coeffs.toArray.map (·.val)
  == #[2130706391, 2130706334, 2130706280, 2130706303, 2130706342, 2130706417]

-- Ring identities.
#guard (s6X + s6Y) * (s6X - s6Y) == s6X * s6X - s6Y * s6Y
#guard (s6X + s6Y) ^ 2 == s6X * s6X + 2 * s6X * s6Y + s6Y * s6Y
#guard s6X ^ 5 == s6X * s6X * s6X * s6X * s6X
#guard (3 : Ext6) * s6X == s6X + s6X + s6X

-- Inversion.
#guard s6X * s6X⁻¹ == 1
#guard s6Y * s6Y⁻¹ == 1
#guard ext6Gen * ext6Gen⁻¹ == 1
#guard (0 : Ext6)⁻¹ == 0
#guard (s6X / s6Y) * s6Y == s6X

-- `θ⁻¹ = θ^8` follows from `θ^9 = 1`, and is a cheap independent check on Fermat inversion.
#guard ext6Gen⁻¹ == ext6Gen ^ 8

-- The base field embeds as the constant coefficient.
#guard Ext.coeff (7 : Ext6) ⟨0, by norm_num⟩ == (7 : KoalaBear.Field)

-- The instances Mathlib consumers need resolve at composite degree too.
example : Module KoalaBear.Field Ext6 := inferInstance
example : Algebra KoalaBear.Field Ext6 := inferInstance

end KoalaBearSextic

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
