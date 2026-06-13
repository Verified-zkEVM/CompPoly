/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Extension.Primitive
import CompPoly.Fields.Binary.GF2_32.Impl
import Mathlib.Tactic.NormNum

/-!
# GF2^32 Primitive-Power Certificates

Generated structural power-chain certificates for the polynomial-basis
root. These certify the nontrivial prime-divisor powers used to prove
that the root has full multiplicative order.
-/

namespace GF2_32

set_option maxRecDepth 50000

/-- Structural power chain for `root ^ ((fieldSize - 1) / 3)`. -/
def rootPowDiv3Chain : List (Nat × Nat) :=
  [(0, 1),
    (1, 2),
    (2, 4),
    (5, 32),
    (10, 1024),
    (21, 2097152),
    (42, 4201479),
    (85, 10543122),
    (170, 1346493811),
    (341, 3323544796),
    (682, 4027602832),
    (1365, 1556035943),
    (2730, 1739416994),
    (5461, 3493923718),
    (10922, 4066962303),
    (21845, 4104604283),
    (43690, 3995013102),
    (87381, 3546564175),
    (174762, 3055722894),
    (349525, 2490840567),
    (699050, 2186346002),
    (1398101, 674290231),
    (2796202, 499347406),
    (5592405, 130325264),
    (11184810, 275753947),
    (22369621, 2794060042),
    (44739242, 3445344052),
    (89478485, 3252423199),
    (178956970, 2972626249),
    (357913941, 478257971),
    (715827882, 1135962393),
    (1431655765, 1754248962)]

/-- Residue of `root ^ ((fieldSize - 1) / 3)`. -/
def rootPowDiv3Residue : Nat :=
  1754248962

/-- Kernel check for `root ^ ((fieldSize - 1) / 3)`. -/
theorem root_pow_div_3_check :
    BinaryField.Extension.Concrete.checkPowNatChain Concrete.params 2
      ((fieldSize - 1) / 3) rootPowDiv3Chain rootPowDiv3Residue = true := by
  rfl

private theorem root_pow_div_3_certified :
    ConcreteField.root ^ ((fieldSize - 1) / 3) =
        ConcreteField.ofNat rootPowDiv3Residue ∧
      rootPowDiv3Residue < 2 ^ extensionDegree := by
  simpa [ConcreteField.root, ConcreteField.ofNat, BinaryField.Extension.Concrete.root,
    Concrete.params] using
    (BinaryField.Extension.Concrete.pow_eq_of_checkPowNatChain
      Concrete.params (a := 2) (target := (fieldSize - 1) / 3)
      (cert := rootPowDiv3Chain) (expected := rootPowDiv3Residue)
      (by unfold Concrete.params extensionDegree; norm_num)
      (by unfold Concrete.params extensionDegree; norm_num)
      root_pow_div_3_check)

/-- Certified residue of `root ^ ((fieldSize - 1) / 3)`. -/
theorem root_pow_div_3_eq :
    ConcreteField.root ^ ((fieldSize - 1) / 3) =
      ConcreteField.ofNat rootPowDiv3Residue :=
  root_pow_div_3_certified.1

/-- The `3`-prime divisor power of the root is nontrivial. -/
theorem root_pow_div_3_ne_one :
    ConcreteField.root ^ ((fieldSize - 1) / 3) ≠ (1 : ConcreteField) := by
  rw [root_pow_div_3_eq]
  change BinaryField.Extension.Concrete.ofNat Concrete.params
      rootPowDiv3Residue ≠ BinaryField.Extension.Concrete.one Concrete.params
  exact BinaryField.Extension.Concrete.ofNat_ne_one_of_lt Concrete.params
    (by unfold Concrete.params extensionDegree; norm_num)
    (by simpa [rootPowDiv3Residue] using root_pow_div_3_certified.2)
    (by unfold rootPowDiv3Residue; norm_num)

/-- Structural power chain for `root ^ ((fieldSize - 1) / 5)`. -/
def rootPowDiv5Chain : List (Nat × Nat) :=
  [(0, 1),
    (1, 2),
    (3, 8),
    (6, 64),
    (12, 4096),
    (25, 33554432),
    (51, 2151157248),
    (102, 2422474439),
    (204, 3324370958),
    (409, 3233822785),
    (819, 3759896285),
    (1638, 3091156298),
    (3276, 2330437444),
    (6553, 2301734431),
    (13107, 2844192533),
    (26214, 2313465105),
    (52428, 2510799046),
    (104857, 80649081),
    (209715, 2733207820),
    (419430, 2355869500),
    (838860, 2509576331),
    (1677721, 617516525),
    (3355443, 3100635308),
    (6710886, 2331465787),
    (13421772, 3522020697),
    (26843545, 1152699485),
    (53687091, 1081844386),
    (107374182, 605563332),
    (214748364, 1484147479),
    (429496729, 3484531228),
    (858993459, 1137006577)]

/-- Residue of `root ^ ((fieldSize - 1) / 5)`. -/
def rootPowDiv5Residue : Nat :=
  1137006577

/-- Kernel check for `root ^ ((fieldSize - 1) / 5)`. -/
theorem root_pow_div_5_check :
    BinaryField.Extension.Concrete.checkPowNatChain Concrete.params 2
      ((fieldSize - 1) / 5) rootPowDiv5Chain rootPowDiv5Residue = true := by
  rfl

private theorem root_pow_div_5_certified :
    ConcreteField.root ^ ((fieldSize - 1) / 5) =
        ConcreteField.ofNat rootPowDiv5Residue ∧
      rootPowDiv5Residue < 2 ^ extensionDegree := by
  simpa [ConcreteField.root, ConcreteField.ofNat, BinaryField.Extension.Concrete.root,
    Concrete.params] using
    (BinaryField.Extension.Concrete.pow_eq_of_checkPowNatChain
      Concrete.params (a := 2) (target := (fieldSize - 1) / 5)
      (cert := rootPowDiv5Chain) (expected := rootPowDiv5Residue)
      (by unfold Concrete.params extensionDegree; norm_num)
      (by unfold Concrete.params extensionDegree; norm_num)
      root_pow_div_5_check)

/-- Certified residue of `root ^ ((fieldSize - 1) / 5)`. -/
theorem root_pow_div_5_eq :
    ConcreteField.root ^ ((fieldSize - 1) / 5) =
      ConcreteField.ofNat rootPowDiv5Residue :=
  root_pow_div_5_certified.1

/-- The `5`-prime divisor power of the root is nontrivial. -/
theorem root_pow_div_5_ne_one :
    ConcreteField.root ^ ((fieldSize - 1) / 5) ≠ (1 : ConcreteField) := by
  rw [root_pow_div_5_eq]
  change BinaryField.Extension.Concrete.ofNat Concrete.params
      rootPowDiv5Residue ≠ BinaryField.Extension.Concrete.one Concrete.params
  exact BinaryField.Extension.Concrete.ofNat_ne_one_of_lt Concrete.params
    (by unfold Concrete.params extensionDegree; norm_num)
    (by simpa [rootPowDiv5Residue] using root_pow_div_5_certified.2)
    (by unfold rootPowDiv5Residue; norm_num)

/-- Structural power chain for `root ^ ((fieldSize - 1) / 17)`. -/
def rootPowDiv17Chain : List (Nat × Nat) :=
  [(0, 1),
    (1, 2),
    (3, 8),
    (7, 128),
    (15, 32768),
    (30, 1073741824),
    (60, 807143168),
    (120, 1528022784),
    (240, 1922283191),
    (481, 4272326556),
    (963, 4259600839),
    (1927, 4286224077),
    (3855, 2112558589),
    (7710, 989680522),
    (15420, 266230836),
    (30840, 297457931),
    (61680, 386276190),
    (123361, 2933888798),
    (246723, 1004503703),
    (493447, 2670756220),
    (986895, 670527999),
    (1973790, 153937234),
    (3947580, 1352039791),
    (7895160, 1733104697),
    (15790320, 2019584237),
    (31580641, 1437933004),
    (63161283, 3304367054),
    (126322567, 3933337751),
    (252645135, 1370394541)]

/-- Residue of `root ^ ((fieldSize - 1) / 17)`. -/
def rootPowDiv17Residue : Nat :=
  1370394541

/-- Kernel check for `root ^ ((fieldSize - 1) / 17)`. -/
theorem root_pow_div_17_check :
    BinaryField.Extension.Concrete.checkPowNatChain Concrete.params 2
      ((fieldSize - 1) / 17) rootPowDiv17Chain rootPowDiv17Residue = true := by
  rfl

private theorem root_pow_div_17_certified :
    ConcreteField.root ^ ((fieldSize - 1) / 17) =
        ConcreteField.ofNat rootPowDiv17Residue ∧
      rootPowDiv17Residue < 2 ^ extensionDegree := by
  simpa [ConcreteField.root, ConcreteField.ofNat, BinaryField.Extension.Concrete.root,
    Concrete.params] using
    (BinaryField.Extension.Concrete.pow_eq_of_checkPowNatChain
      Concrete.params (a := 2) (target := (fieldSize - 1) / 17)
      (cert := rootPowDiv17Chain) (expected := rootPowDiv17Residue)
      (by unfold Concrete.params extensionDegree; norm_num)
      (by unfold Concrete.params extensionDegree; norm_num)
      root_pow_div_17_check)

/-- Certified residue of `root ^ ((fieldSize - 1) / 17)`. -/
theorem root_pow_div_17_eq :
    ConcreteField.root ^ ((fieldSize - 1) / 17) =
      ConcreteField.ofNat rootPowDiv17Residue :=
  root_pow_div_17_certified.1

/-- The `17`-prime divisor power of the root is nontrivial. -/
theorem root_pow_div_17_ne_one :
    ConcreteField.root ^ ((fieldSize - 1) / 17) ≠ (1 : ConcreteField) := by
  rw [root_pow_div_17_eq]
  change BinaryField.Extension.Concrete.ofNat Concrete.params
      rootPowDiv17Residue ≠ BinaryField.Extension.Concrete.one Concrete.params
  exact BinaryField.Extension.Concrete.ofNat_ne_one_of_lt Concrete.params
    (by unfold Concrete.params extensionDegree; norm_num)
    (by simpa [rootPowDiv17Residue] using root_pow_div_17_certified.2)
    (by unfold rootPowDiv17Residue; norm_num)

/-- Structural power chain for `root ^ ((fieldSize - 1) / 257)`. -/
def rootPowDiv257Chain : List (Nat × Nat) :=
  [(0, 1),
    (1, 2),
    (3, 8),
    (7, 128),
    (15, 32768),
    (31, 2147483648),
    (63, 2157983751),
    (127, 2191753411),
    (255, 2325425877),
    (510, 3518626982),
    (1020, 3795534868),
    (2040, 4251387404),
    (4080, 3951680331),
    (8160, 3920936430),
    (16320, 3921470543),
    (32640, 3908936078),
    (65280, 3920330836),
    (130561, 1931169607),
    (261123, 1546235260),
    (522247, 3480831990),
    (1044495, 3278150689),
    (2088991, 3364809555),
    (4177983, 1804695437),
    (8355967, 2066345588),
    (16711935, 1462464888)]

/-- Residue of `root ^ ((fieldSize - 1) / 257)`. -/
def rootPowDiv257Residue : Nat :=
  1462464888

/-- Kernel check for `root ^ ((fieldSize - 1) / 257)`. -/
theorem root_pow_div_257_check :
    BinaryField.Extension.Concrete.checkPowNatChain Concrete.params 2
      ((fieldSize - 1) / 257) rootPowDiv257Chain rootPowDiv257Residue = true := by
  rfl

private theorem root_pow_div_257_certified :
    ConcreteField.root ^ ((fieldSize - 1) / 257) =
        ConcreteField.ofNat rootPowDiv257Residue ∧
      rootPowDiv257Residue < 2 ^ extensionDegree := by
  simpa [ConcreteField.root, ConcreteField.ofNat, BinaryField.Extension.Concrete.root,
    Concrete.params] using
    (BinaryField.Extension.Concrete.pow_eq_of_checkPowNatChain
      Concrete.params (a := 2) (target := (fieldSize - 1) / 257)
      (cert := rootPowDiv257Chain) (expected := rootPowDiv257Residue)
      (by unfold Concrete.params extensionDegree; norm_num)
      (by unfold Concrete.params extensionDegree; norm_num)
      root_pow_div_257_check)

/-- Certified residue of `root ^ ((fieldSize - 1) / 257)`. -/
theorem root_pow_div_257_eq :
    ConcreteField.root ^ ((fieldSize - 1) / 257) =
      ConcreteField.ofNat rootPowDiv257Residue :=
  root_pow_div_257_certified.1

/-- The `257`-prime divisor power of the root is nontrivial. -/
theorem root_pow_div_257_ne_one :
    ConcreteField.root ^ ((fieldSize - 1) / 257) ≠ (1 : ConcreteField) := by
  rw [root_pow_div_257_eq]
  change BinaryField.Extension.Concrete.ofNat Concrete.params
      rootPowDiv257Residue ≠ BinaryField.Extension.Concrete.one Concrete.params
  exact BinaryField.Extension.Concrete.ofNat_ne_one_of_lt Concrete.params
    (by unfold Concrete.params extensionDegree; norm_num)
    (by simpa [rootPowDiv257Residue] using root_pow_div_257_certified.2)
    (by unfold rootPowDiv257Residue; norm_num)

/-- Structural power chain for `root ^ ((fieldSize - 1) / 65537)`. -/
def rootPowDiv65537Chain : List (Nat × Nat) :=
  [(0, 1),
    (1, 2),
    (3, 8),
    (7, 128),
    (15, 32768),
    (31, 2147483648),
    (63, 2157983751),
    (127, 2191753411),
    (255, 2325425877),
    (511, 2738092363),
    (1023, 270147765),
    (2047, 2885879674),
    (4095, 2615462159),
    (8191, 2232683971),
    (16383, 678210915),
    (32767, 3148615908),
    (65535, 496518513)]

/-- Residue of `root ^ ((fieldSize - 1) / 65537)`. -/
def rootPowDiv65537Residue : Nat :=
  496518513

/-- Kernel check for `root ^ ((fieldSize - 1) / 65537)`. -/
theorem root_pow_div_65537_check :
    BinaryField.Extension.Concrete.checkPowNatChain Concrete.params 2
      ((fieldSize - 1) / 65537) rootPowDiv65537Chain rootPowDiv65537Residue = true := by
  rfl

private theorem root_pow_div_65537_certified :
    ConcreteField.root ^ ((fieldSize - 1) / 65537) =
        ConcreteField.ofNat rootPowDiv65537Residue ∧
      rootPowDiv65537Residue < 2 ^ extensionDegree := by
  simpa [ConcreteField.root, ConcreteField.ofNat, BinaryField.Extension.Concrete.root,
    Concrete.params] using
    (BinaryField.Extension.Concrete.pow_eq_of_checkPowNatChain
      Concrete.params (a := 2) (target := (fieldSize - 1) / 65537)
      (cert := rootPowDiv65537Chain) (expected := rootPowDiv65537Residue)
      (by unfold Concrete.params extensionDegree; norm_num)
      (by unfold Concrete.params extensionDegree; norm_num)
      root_pow_div_65537_check)

/-- Certified residue of `root ^ ((fieldSize - 1) / 65537)`. -/
theorem root_pow_div_65537_eq :
    ConcreteField.root ^ ((fieldSize - 1) / 65537) =
      ConcreteField.ofNat rootPowDiv65537Residue :=
  root_pow_div_65537_certified.1

/-- The `65537`-prime divisor power of the root is nontrivial. -/
theorem root_pow_div_65537_ne_one :
    ConcreteField.root ^ ((fieldSize - 1) / 65537) ≠ (1 : ConcreteField) := by
  rw [root_pow_div_65537_eq]
  change BinaryField.Extension.Concrete.ofNat Concrete.params
      rootPowDiv65537Residue ≠ BinaryField.Extension.Concrete.one Concrete.params
  exact BinaryField.Extension.Concrete.ofNat_ne_one_of_lt Concrete.params
    (by unfold Concrete.params extensionDegree; norm_num)
    (by simpa [rootPowDiv65537Residue] using root_pow_div_65537_certified.2)
    (by unfold rootPowDiv65537Residue; norm_num)

end GF2_32
