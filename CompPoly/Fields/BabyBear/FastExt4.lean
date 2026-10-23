/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Extension.Map
public import CompPoly.Fields.BabyBear.Ext4
public import CompPoly.Fields.BabyBear.Fast
public import CompPoly.Fields.Montgomery.Native32Ext4

/-!
# The degree-4 extension of BabyBear over the fast carrier

`BabyBear.Fast.Ext4` is `Montgomery.Native32.Ext4` for BabyBear and the binomial `X^4 - 11`, the
same field as Plonky3's `BinomialExtensionField<BabyBear, 4>`. Irreducibility is the spec
certificate `BabyBear.ext4Params_poly_irreducible`, transferred from `BabyBear.Field` to the fast
carrier along `ringEquiv`.
-/

@[expose] public section

namespace BabyBear.Fast

open CompPoly.Extension Montgomery.Native32 Polynomial

/-- `X^4 - 11` is irreducible over the fast carrier. -/
theorem irreducible_X_pow_four_sub_eleven : Irreducible (X ^ 4 - C 11 : Field[X]) := by
  have h := irreducible_map_ringEquiv ringEquiv.symm ext4Params_poly_irreducible
  rwa [BinomialParams.poly, ext4Params_d, ext4Params_W, Polynomial.map_sub, Polynomial.map_pow,
    map_X, map_C, map_ofNat] at h

/-- BabyBear's quartic extension is `X^4 - 11`. Inlined, so that specialized code multiplies by
`W` directly. -/
@[inline] instance instBinomial4 : Binomial4 BabyBear.fieldSize where
  W := 11
  irreducible := irreducible_X_pow_four_sub_eleven

/-- The degree-4 extension of BabyBear with fast coefficients. -/
abbrev Ext4 : Type := Montgomery.Native32.Ext4 BabyBear.fieldSize

end BabyBear.Fast
