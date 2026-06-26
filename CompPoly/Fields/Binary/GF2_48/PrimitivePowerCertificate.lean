/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Extension.Primitive
import CompPoly.Fields.Binary.GF2_48.Impl
import Mathlib.Tactic.NormNum

/-!
# GF2^48 Primitive-Power Certificates

Generated structural power-chain certificates for the polynomial-basis
root. These certify the nontrivial prime-divisor powers used to prove
that the root has full multiplicative order.
-/

namespace GF2_48

set_option maxRecDepth 50000

/-- Structural power chain for `root ^ ((fieldSize - 1) / 3)`. -/
def rootPowDiv3Chain : List (Nat × Nat) :=
  [(0, 1), (1, 2), (2, 4), (5, 32), (10, 1024), (21, 2097152), (42, 4398046511104),
    (85, 90297392431104), (170, 153168264577307), (341, 239113957168115), (682, 126119346275310),
    (1365, 68118054016467), (2730, 85786808640717), (5461, 15575669117153),
    (10922, 143347404838421), (21845, 172606321685184), (43690, 80831776680898),
    (87381, 86622958655337), (174762, 232881539791740), (349525, 202935929788109),
    (699050, 54870390925357), (1398101, 183260923738027), (2796202, 61567496953679),
    (5592405, 79173554647435), (11184810, 269385973704121), (22369621, 137576615846835),
    (44739242, 100924215630453), (89478485, 99039778605076), (178956970, 138550707487263),
    (357913941, 15427885231210), (715827882, 217981134220997), (1431655765, 251730884502424),
    (2863311530, 114970032252646), (5726623061, 80698868357301), (11453246122, 179165345868221),
    (22906492245, 207849359609366), (45812984490, 34723303299245), (91625968981, 36041016527950),
    (183251937962, 19641450941483), (366503875925, 189237286047101),
    (733007751850, 154233819647710), (1466015503701, 169815596898641),
    (2932031007402, 121176297650067), (5864062014805, 191984876758421),
    (11728124029610, 166796011300363), (23456248059221, 247199318462005),
    (46912496118442, 94075238128051), (93824992236885, 101580418639119)]

/-- Residue of `root ^ ((fieldSize - 1) / 3)`. -/
def rootPowDiv3Residue : Nat :=
  101580418639119

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
  [(0, 1), (1, 2), (3, 8), (6, 64), (12, 4096), (25, 33554432), (51, 5256), (102, 17842240),
    (204, 1099780067985), (409, 5643621474306), (819, 96430950192256), (1638, 246469869353227),
    (3276, 22053167914995), (6553, 134703828887893), (13107, 129640253166786),
    (26214, 258761870046052), (52428, 186911430657782), (104857, 118792979732263),
    (209715, 158518644506271), (419430, 215911181407254), (838860, 115629506514696),
    (1677721, 120078505330877), (3355443, 70065354013493), (6710886, 18039512702409),
    (13421772, 233607316320823), (26843545, 231901518996583), (53687091, 34110304840399),
    (107374182, 94288478391335), (214748364, 204543569237387), (429496729, 235893740838106),
    (858993459, 85630304092143), (1717986918, 226512346234361), (3435973836, 144315422935369),
    (6871947673, 19628631989960), (13743895347, 191550654281559), (27487790694, 217758663924747),
    (54975581388, 38489827985485), (109951162777, 28046756068182), (219902325555, 217987274961484),
    (439804651110, 125796626944665), (879609302220, 245615824766069),
    (1759218604441, 39497553457270), (3518437208883, 18166515285246),
    (7036874417766, 233801619693878), (14073748835532, 279203897055231),
    (28147497671065, 24213435108770), (56294995342131, 121637617569279)]

/-- Residue of `root ^ ((fieldSize - 1) / 5)`. -/
def rootPowDiv5Residue : Nat :=
  121637617569279

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

/-- Structural power chain for `root ^ ((fieldSize - 1) / 7)`. -/
def rootPowDiv7Chain : List (Nat × Nat) :=
  [(0, 1), (1, 2), (2, 4), (4, 16), (9, 512), (18, 262144), (36, 68719476736), (73, 22045261824),
    (146, 730549828), (292, 70665371580549), (585, 3276481702480), (1170, 82275195641793),
    (2340, 262641432909245), (4681, 8367384970623), (9362, 36727545386192), (18724, 95619477462522),
    (37449, 262800110579727), (74898, 163644114730423), (149796, 256850855091730),
    (299593, 226941206178685), (599186, 143431298912077), (1198372, 12304234700128),
    (2396745, 239388755334419), (4793490, 37643018696235), (9586980, 33316286093995),
    (19173961, 4782933384524), (38347922, 45622856404625), (76695844, 253868309161983),
    (153391689, 78805978789580), (306783378, 35453015546669), (613566756, 88068370847915),
    (1227133513, 184884603787655), (2454267026, 180656635747994), (4908534052, 119266248636254),
    (9817068105, 170333197127607), (19634136210, 64401606288898), (39268272420, 47225849691784),
    (78536544841, 140374837168207), (157073089682, 88509217214948), (314146179364, 162882359309643),
    (628292358729, 273487679720629), (1256584717458, 37297901438020),
    (2513169434916, 72923599746298), (5026338869833, 22914149051736),
    (10052677739666, 278776472013475), (20105355479332, 82952670984256),
    (40210710958665, 92122832017475)]

/-- Residue of `root ^ ((fieldSize - 1) / 7)`. -/
def rootPowDiv7Residue : Nat :=
  92122832017475

/-- Kernel check for `root ^ ((fieldSize - 1) / 7)`. -/
theorem root_pow_div_7_check :
    BinaryField.Extension.Concrete.checkPowNatChain Concrete.params 2
      ((fieldSize - 1) / 7) rootPowDiv7Chain rootPowDiv7Residue = true := by
  rfl

private theorem root_pow_div_7_certified :
    ConcreteField.root ^ ((fieldSize - 1) / 7) =
        ConcreteField.ofNat rootPowDiv7Residue ∧
      rootPowDiv7Residue < 2 ^ extensionDegree := by
  simpa [ConcreteField.root, ConcreteField.ofNat, BinaryField.Extension.Concrete.root,
    Concrete.params] using
    (BinaryField.Extension.Concrete.pow_eq_of_checkPowNatChain
      Concrete.params (a := 2) (target := (fieldSize - 1) / 7)
      (cert := rootPowDiv7Chain) (expected := rootPowDiv7Residue)
      (by unfold Concrete.params extensionDegree; norm_num)
      (by unfold Concrete.params extensionDegree; norm_num)
      root_pow_div_7_check)

/-- Certified residue of `root ^ ((fieldSize - 1) / 7)`. -/
theorem root_pow_div_7_eq :
    ConcreteField.root ^ ((fieldSize - 1) / 7) =
      ConcreteField.ofNat rootPowDiv7Residue :=
  root_pow_div_7_certified.1

/-- The `7`-prime divisor power of the root is nontrivial. -/
theorem root_pow_div_7_ne_one :
    ConcreteField.root ^ ((fieldSize - 1) / 7) ≠ (1 : ConcreteField) := by
  rw [root_pow_div_7_eq]
  change BinaryField.Extension.Concrete.ofNat Concrete.params
      rootPowDiv7Residue ≠ BinaryField.Extension.Concrete.one Concrete.params
  exact BinaryField.Extension.Concrete.ofNat_ne_one_of_lt Concrete.params
    (by unfold Concrete.params extensionDegree; norm_num)
    (by simpa [rootPowDiv7Residue] using root_pow_div_7_certified.2)
    (by unfold rootPowDiv7Residue; norm_num)

/-- Structural power chain for `root ^ ((fieldSize - 1) / 13)`. -/
def rootPowDiv13Chain : List (Nat × Nat) :=
  [(0, 1), (1, 2), (2, 4), (4, 16), (9, 512), (19, 524288), (39, 549755813888), (78, 705448378368),
    (157, 1496166047744), (315, 52209907031560), (630, 163485128753386), (1260, 273404014519891),
    (2520, 41415108901841), (5041, 137266615548278), (10082, 28152253055264),
    (20164, 60690029723555), (40329, 106760880792193), (80659, 146399995613956),
    (161319, 102926423345762), (322638, 99450172705871), (645277, 92776042313788),
    (1290555, 88975207756077), (2581110, 217238579388559), (5162220, 116972852988376),
    (10324440, 258823563135506), (20648881, 265965013271647), (41297762, 144119733978644),
    (82595524, 9379569031989), (165191049, 248261459756817), (330382099, 51201868472556),
    (660764199, 158111427237095), (1321528398, 228804162913652), (2643056797, 35789625632615),
    (5286113595, 37287086094932), (10572227190, 6629939730799), (21144454380, 42131216019856),
    (42288908760, 109107314005418), (84577817521, 56867250300166), (169155635042, 225921276629404),
    (338311270084, 223064276232716), (676622540169, 95717651322115),
    (1353245080339, 214409264398509), (2706490160679, 194761820552120),
    (5412980321358, 162290903296685), (10825960642717, 64626218883221),
    (21651921285435, 93528367818650)]

/-- Residue of `root ^ ((fieldSize - 1) / 13)`. -/
def rootPowDiv13Residue : Nat :=
  93528367818650

/-- Kernel check for `root ^ ((fieldSize - 1) / 13)`. -/
theorem root_pow_div_13_check :
    BinaryField.Extension.Concrete.checkPowNatChain Concrete.params 2
      ((fieldSize - 1) / 13) rootPowDiv13Chain rootPowDiv13Residue = true := by
  rfl

private theorem root_pow_div_13_certified :
    ConcreteField.root ^ ((fieldSize - 1) / 13) =
        ConcreteField.ofNat rootPowDiv13Residue ∧
      rootPowDiv13Residue < 2 ^ extensionDegree := by
  simpa [ConcreteField.root, ConcreteField.ofNat, BinaryField.Extension.Concrete.root,
    Concrete.params] using
    (BinaryField.Extension.Concrete.pow_eq_of_checkPowNatChain
      Concrete.params (a := 2) (target := (fieldSize - 1) / 13)
      (cert := rootPowDiv13Chain) (expected := rootPowDiv13Residue)
      (by unfold Concrete.params extensionDegree; norm_num)
      (by unfold Concrete.params extensionDegree; norm_num)
      root_pow_div_13_check)

/-- Certified residue of `root ^ ((fieldSize - 1) / 13)`. -/
theorem root_pow_div_13_eq :
    ConcreteField.root ^ ((fieldSize - 1) / 13) =
      ConcreteField.ofNat rootPowDiv13Residue :=
  root_pow_div_13_certified.1

/-- The `13`-prime divisor power of the root is nontrivial. -/
theorem root_pow_div_13_ne_one :
    ConcreteField.root ^ ((fieldSize - 1) / 13) ≠ (1 : ConcreteField) := by
  rw [root_pow_div_13_eq]
  change BinaryField.Extension.Concrete.ofNat Concrete.params
      rootPowDiv13Residue ≠ BinaryField.Extension.Concrete.one Concrete.params
  exact BinaryField.Extension.Concrete.ofNat_ne_one_of_lt Concrete.params
    (by unfold Concrete.params extensionDegree; norm_num)
    (by simpa [rootPowDiv13Residue] using root_pow_div_13_certified.2)
    (by unfold rootPowDiv13Residue; norm_num)

/-- Structural power chain for `root ^ ((fieldSize - 1) / 17)`. -/
def rootPowDiv17Chain : List (Nat × Nat) :=
  [(0, 1), (1, 2), (3, 8), (7, 128), (15, 32768), (30, 1073741824), (60, 2691072),
    (120, 4677236162560), (240, 45325101367953), (481, 78825126860111), (963, 257808250225490),
    (1927, 137346191716309), (3855, 65446122679784), (7710, 49620820364440),
    (15420, 240373327265903), (30840, 70245636929278), (61680, 93810842067848),
    (123361, 279128825875845), (246723, 163375128126624), (493447, 241780583993789),
    (986895, 132134602612446), (1973790, 106771955911093), (3947580, 24817350337730),
    (7895160, 179991599648743), (15790320, 32064567349470), (31580641, 59052695360878),
    (63161283, 93404791989633), (126322567, 135391122981295), (252645135, 127225952834146),
    (505290270, 149778248921956), (1010580540, 269708456730673), (2021161080, 280005451069508),
    (4042322160, 26107615066004), (8084644321, 108268330336639), (16169288643, 174145398047366),
    (32338577287, 50872759621420), (64677154575, 42169890118085), (129354309150, 130271431394858),
    (258708618300, 266516302632929), (517417236600, 227745986508421),
    (1034834473200, 163664482617048), (2069668946401, 232808671277239),
    (4139337892803, 170263705038701), (8278675785607, 131489751431172),
    (16557351571215, 105996826927705)]

/-- Residue of `root ^ ((fieldSize - 1) / 17)`. -/
def rootPowDiv17Residue : Nat :=
  105996826927705

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

/-- Structural power chain for `root ^ ((fieldSize - 1) / 97)`. -/
def rootPowDiv97Chain : List (Nat × Nat) :=
  [(0, 1), (1, 2), (2, 4), (5, 32), (10, 1024), (21, 2097152), (42, 4398046511104),
    (84, 45148696215552), (168, 249398298677674), (337, 67721180456260), (675, 31771632970544),
    (1351, 160034639044804), (2702, 144450920964371), (5405, 56951288155232),
    (10810, 225436609020441), (21620, 246022787930717), (43240, 17631167540670),
    (86480, 145430587562403), (172960, 45343731141541), (345921, 122123457612135),
    (691843, 144745062986911), (1383687, 158728924284874), (2767375, 187418305352855),
    (5534751, 233377707517317), (11069503, 267157925589607), (22139006, 175653402286977),
    (44278013, 35399789981606), (88556026, 17905099681915), (177112053, 36118051354997),
    (354224106, 6439006591086), (708448213, 241991237211680), (1416896427, 19996957273180),
    (2833792855, 200236385714687), (5667585710, 266382709865277), (11335171420, 245364872495632),
    (22670342840, 76483442030251), (45340685681, 103813662583544), (90681371362, 21384588760155),
    (181362742725, 160441147996927), (362725485451, 50738510970421), (725450970903, 51251138592239),
    (1450901941807, 52656619740269), (2901803883615, 141451938052813)]

/-- Residue of `root ^ ((fieldSize - 1) / 97)`. -/
def rootPowDiv97Residue : Nat :=
  141451938052813

/-- Kernel check for `root ^ ((fieldSize - 1) / 97)`. -/
theorem root_pow_div_97_check :
    BinaryField.Extension.Concrete.checkPowNatChain Concrete.params 2
      ((fieldSize - 1) / 97) rootPowDiv97Chain rootPowDiv97Residue = true := by
  rfl

private theorem root_pow_div_97_certified :
    ConcreteField.root ^ ((fieldSize - 1) / 97) =
        ConcreteField.ofNat rootPowDiv97Residue ∧
      rootPowDiv97Residue < 2 ^ extensionDegree := by
  simpa [ConcreteField.root, ConcreteField.ofNat, BinaryField.Extension.Concrete.root,
    Concrete.params] using
    (BinaryField.Extension.Concrete.pow_eq_of_checkPowNatChain
      Concrete.params (a := 2) (target := (fieldSize - 1) / 97)
      (cert := rootPowDiv97Chain) (expected := rootPowDiv97Residue)
      (by unfold Concrete.params extensionDegree; norm_num)
      (by unfold Concrete.params extensionDegree; norm_num)
      root_pow_div_97_check)

/-- Certified residue of `root ^ ((fieldSize - 1) / 97)`. -/
theorem root_pow_div_97_eq :
    ConcreteField.root ^ ((fieldSize - 1) / 97) =
      ConcreteField.ofNat rootPowDiv97Residue :=
  root_pow_div_97_certified.1

/-- The `97`-prime divisor power of the root is nontrivial. -/
theorem root_pow_div_97_ne_one :
    ConcreteField.root ^ ((fieldSize - 1) / 97) ≠ (1 : ConcreteField) := by
  rw [root_pow_div_97_eq]
  change BinaryField.Extension.Concrete.ofNat Concrete.params
      rootPowDiv97Residue ≠ BinaryField.Extension.Concrete.one Concrete.params
  exact BinaryField.Extension.Concrete.ofNat_ne_one_of_lt Concrete.params
    (by unfold Concrete.params extensionDegree; norm_num)
    (by simpa [rootPowDiv97Residue] using root_pow_div_97_certified.2)
    (by unfold rootPowDiv97Residue; norm_num)

/-- Structural power chain for `root ^ ((fieldSize - 1) / 241)`. -/
def rootPowDiv241Chain : List (Nat × Nat) :=
  [(0, 1), (1, 2), (2, 4), (4, 16), (8, 256), (16, 65536), (33, 8589934592), (67, 344457216),
    (135, 141287244525600), (271, 142295118784968), (543, 146707456578880), (1087, 129085588640842),
    (2175, 94304222573403), (4350, 262066767323791), (8701, 180830601058933),
    (17403, 229528675566388), (34807, 153633219510341), (69615, 267116754424953),
    (139230, 175672023904721), (278460, 23193596112087), (556920, 205434478303011),
    (1113840, 64663449552888), (2227680, 51168180848473), (4455360, 218686688357226),
    (8910720, 114156637382349), (17821441, 79814377066022), (35642882, 270426720254392),
    (71285764, 263081917350165), (142571528, 163729440612390), (285143056, 277656597194823),
    (570286113, 197263269948456), (1140572227, 57102817894851), (2281144455, 195743861958185),
    (4562288911, 30798870074337), (9124577823, 196274495017836), (18249155647, 210428564687715),
    (36498311295, 144923404912984), (72996622590, 80648881724916), (145993245181, 219886962402121),
    (291986490363, 213308358474648), (583972980727, 30932552665530),
    (1167945961455, 170101039684070)]

/-- Residue of `root ^ ((fieldSize - 1) / 241)`. -/
def rootPowDiv241Residue : Nat :=
  170101039684070

/-- Kernel check for `root ^ ((fieldSize - 1) / 241)`. -/
theorem root_pow_div_241_check :
    BinaryField.Extension.Concrete.checkPowNatChain Concrete.params 2
      ((fieldSize - 1) / 241) rootPowDiv241Chain rootPowDiv241Residue = true := by
  rfl

private theorem root_pow_div_241_certified :
    ConcreteField.root ^ ((fieldSize - 1) / 241) =
        ConcreteField.ofNat rootPowDiv241Residue ∧
      rootPowDiv241Residue < 2 ^ extensionDegree := by
  simpa [ConcreteField.root, ConcreteField.ofNat, BinaryField.Extension.Concrete.root,
    Concrete.params] using
    (BinaryField.Extension.Concrete.pow_eq_of_checkPowNatChain
      Concrete.params (a := 2) (target := (fieldSize - 1) / 241)
      (cert := rootPowDiv241Chain) (expected := rootPowDiv241Residue)
      (by unfold Concrete.params extensionDegree; norm_num)
      (by unfold Concrete.params extensionDegree; norm_num)
      root_pow_div_241_check)

/-- Certified residue of `root ^ ((fieldSize - 1) / 241)`. -/
theorem root_pow_div_241_eq :
    ConcreteField.root ^ ((fieldSize - 1) / 241) =
      ConcreteField.ofNat rootPowDiv241Residue :=
  root_pow_div_241_certified.1

/-- The `241`-prime divisor power of the root is nontrivial. -/
theorem root_pow_div_241_ne_one :
    ConcreteField.root ^ ((fieldSize - 1) / 241) ≠ (1 : ConcreteField) := by
  rw [root_pow_div_241_eq]
  change BinaryField.Extension.Concrete.ofNat Concrete.params
      rootPowDiv241Residue ≠ BinaryField.Extension.Concrete.one Concrete.params
  exact BinaryField.Extension.Concrete.ofNat_ne_one_of_lt Concrete.params
    (by unfold Concrete.params extensionDegree; norm_num)
    (by simpa [rootPowDiv241Residue] using root_pow_div_241_certified.2)
    (by unfold rootPowDiv241Residue; norm_num)

/-- Structural power chain for `root ^ ((fieldSize - 1) / 257)`. -/
def rootPowDiv257Chain : List (Nat × Nat) :=
  [(0, 1), (1, 2), (3, 8), (7, 128), (15, 32768), (31, 2147483648), (63, 21528576),
    (127, 35736275387682), (255, 150944501902172), (510, 266893304808229), (1020, 224197440815428),
    (2040, 190300878332045), (4080, 171265265718559), (8160, 118873039358802),
    (16320, 221080466616902), (32640, 196274878469085), (65280, 153519777481257),
    (130561, 132854211039473), (261123, 214645074412512), (522247, 168471309130256),
    (1044495, 122255799173388), (2088991, 151258196137493), (4177983, 224639745914961),
    (8355967, 170362051025673), (16711935, 140203517980204), (33423870, 22149350809009),
    (66847740, 207048542309747), (133695480, 80787359482749), (267390960, 254680610974441),
    (534781920, 39762856893667), (1069563840, 61623038660587), (2139127680, 105899874875736),
    (4278255360, 70899523738755), (8556510721, 150499693688920), (17113021443, 116155302349785),
    (34226042887, 110485280299679), (68452085775, 90615530287782), (136904171551, 66416804183559),
    (273808343103, 194359622149394), (547616686207, 37084812156993),
    (1095233372415, 154835689853052)]

/-- Residue of `root ^ ((fieldSize - 1) / 257)`. -/
def rootPowDiv257Residue : Nat :=
  154835689853052

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

/-- Structural power chain for `root ^ ((fieldSize - 1) / 673)`. -/
def rootPowDiv673Chain : List (Nat × Nat) :=
  [(0, 1), (1, 2), (3, 8), (6, 64), (12, 4096), (24, 16777216), (48, 657), (97, 557570),
    (194, 275951910916), (389, 490168524832), (779, 37708044730368), (1558, 16758898680830),
    (3116, 141321843072260), (6232, 88673711331296), (12464, 141486659320730),
    (24928, 72223204541108), (49857, 15897856632058), (99715, 14205409967249),
    (199431, 56244673534131), (398863, 29948425826977), (797727, 100857033517028),
    (1595455, 231279147536700), (3190911, 209417934873285), (6381823, 183359765335384),
    (12763647, 218871802943262), (25527294, 124003223520393), (51054588, 216161968472304),
    (102109177, 230815027203736), (204218355, 13252978378981), (408436711, 27091015536921),
    (816873423, 80636314690798), (1633746846, 249498523823977), (3267493693, 164442984598724),
    (6534987386, 209395057117975), (13069974772, 78481257136120), (26139949545, 81114814604152),
    (52279899091, 253550418637257), (104559798183, 255002750420036), (209119596367, 79230113247982),
    (418239192735, 220465521204419)]

/-- Residue of `root ^ ((fieldSize - 1) / 673)`. -/
def rootPowDiv673Residue : Nat :=
  220465521204419

/-- Kernel check for `root ^ ((fieldSize - 1) / 673)`. -/
theorem root_pow_div_673_check :
    BinaryField.Extension.Concrete.checkPowNatChain Concrete.params 2
      ((fieldSize - 1) / 673) rootPowDiv673Chain rootPowDiv673Residue = true := by
  rfl

private theorem root_pow_div_673_certified :
    ConcreteField.root ^ ((fieldSize - 1) / 673) =
        ConcreteField.ofNat rootPowDiv673Residue ∧
      rootPowDiv673Residue < 2 ^ extensionDegree := by
  simpa [ConcreteField.root, ConcreteField.ofNat, BinaryField.Extension.Concrete.root,
    Concrete.params] using
    (BinaryField.Extension.Concrete.pow_eq_of_checkPowNatChain
      Concrete.params (a := 2) (target := (fieldSize - 1) / 673)
      (cert := rootPowDiv673Chain) (expected := rootPowDiv673Residue)
      (by unfold Concrete.params extensionDegree; norm_num)
      (by unfold Concrete.params extensionDegree; norm_num)
      root_pow_div_673_check)

/-- Certified residue of `root ^ ((fieldSize - 1) / 673)`. -/
theorem root_pow_div_673_eq :
    ConcreteField.root ^ ((fieldSize - 1) / 673) =
      ConcreteField.ofNat rootPowDiv673Residue :=
  root_pow_div_673_certified.1

/-- The `673`-prime divisor power of the root is nontrivial. -/
theorem root_pow_div_673_ne_one :
    ConcreteField.root ^ ((fieldSize - 1) / 673) ≠ (1 : ConcreteField) := by
  rw [root_pow_div_673_eq]
  change BinaryField.Extension.Concrete.ofNat Concrete.params
      rootPowDiv673Residue ≠ BinaryField.Extension.Concrete.one Concrete.params
  exact BinaryField.Extension.Concrete.ofNat_ne_one_of_lt Concrete.params
    (by unfold Concrete.params extensionDegree; norm_num)
    (by simpa [rootPowDiv673Residue] using root_pow_div_673_certified.2)
    (by unfold rootPowDiv673Residue; norm_num)

end GF2_48
