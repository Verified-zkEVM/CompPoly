/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Extension.Map
public import CompPoly.Fields.KoalaBear.Ext4
public import CompPoly.Fields.KoalaBear.Fast
public import CompPoly.Fields.Montgomery.Native32Ext4

/-!
# The degree-4 extension of KoalaBear over the fast carrier

`KoalaBear.Fast.Ext4` is `Montgomery.Native32.Ext4` for KoalaBear and the binomial `X^4 - 3`, the
same field as Plonky3's `BinomialExtensionField<KoalaBear, 4>`. Multiplication by `W = 3` is
`x + x + x`. Irreducibility is the spec certificate `KoalaBear.ext4Params_poly_irreducible`,
transferred from `KoalaBear.Field` to the fast carrier along `ringEquiv`.
-/

@[expose] public section

namespace KoalaBear.Fast

open CompPoly.Extension Montgomery.Native32 Polynomial

/-- `X^4 - 3` is irreducible over the fast carrier. -/
theorem irreducible_X_pow_four_sub_three : Irreducible (X ^ 4 - C 3 : Field[X]) := by
  have h := irreducible_map_ringEquiv ringEquiv.symm ext4Params_poly_irreducible
  rwa [BinomialParams.poly, ext4Params_d, ext4Params_W, Polynomial.map_sub, Polynomial.map_pow,
    map_X, map_C, map_ofNat] at h

/-- KoalaBear's quartic extension is `X^4 - 3`. -/
instance instBinomial4 : Binomial4 KoalaBear.fieldSize where
  W := 3
  mulW x := x + x + x
  mulW_eq x := by ring
  irreducible := irreducible_X_pow_four_sub_three

/-- The degree-4 extension of KoalaBear with fast coefficients. -/
abbrev Ext4 : Type := Montgomery.Native32.Ext4 KoalaBear.fieldSize

end KoalaBear.Fast
