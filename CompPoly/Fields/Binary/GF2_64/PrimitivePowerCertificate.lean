/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Extension.Primitive
import CompPoly.Fields.Binary.GF2_64.Impl
import Mathlib.Tactic.NormNum

/-!
# GF2^64 Primitive-Power Certificates

Generated structural power-chain certificates for the polynomial-basis
root. These certify the nontrivial prime-divisor powers used to prove
that the root has full multiplicative order.
-/

namespace GF2_64

set_option maxRecDepth 50000

/-- Structural power chain for `root ^ ((fieldSize - 1) / 3)`. -/
def rootPowDiv3Chain : List (Nat × Nat) :=
  [(0, 1),
    (1, 2),
    (2, 4),
    (5, 32),
    (10, 1024),
    (21, 2097152),
    (42, 4398046511104),
    (85, 56623104),
    (170, 1429365116108800),
    (341, 3668797554688),
    (682, 365095035034053340),
    (1365, 240410548471636640),
    (2730, 4983231460161116188),
    (5461, 4744244927560792685),
    (10922, 12977174872011159626),
    (21845, 5577735636430933375),
    (43690, 11978056309670548770),
    (87381, 8870512220009982119),
    (174762, 9580854867404007525),
    (349525, 283172313511053403),
    (699050, 27333090561073285),
    (1398101, 144458462052347636),
    (2796202, 5001551169862247328),
    (5592405, 7743719202701829493),
    (11184810, 16134095663629651926),
    (22369621, 14990400136725602578),
    (44739242, 9084907874049376581),
    (89478485, 2502479396378613473),
    (178956970, 3278310103988839425),
    (357913941, 6079615500721804652),
    (715827882, 12660948147669634711),
    (1431655765, 8980538088000184925),
    (2863311530, 15308770099851454029),
    (5726623061, 9025546545411214670),
    (11453246122, 15365971086693523512),
    (22906492245, 18436822897148651354),
    (45812984490, 73602847640625433),
    (91625968981, 2888497718686628154),
    (183251937962, 7674217092863469891),
    (366503875925, 10770255747030896017),
    (733007751850, 10284975553068631936),
    (1466015503701, 2636129607266100217),
    (2932031007402, 7539747033546575770),
    (5864062014805, 1523899303434289661),
    (11728124029610, 6845236036137451414),
    (23456248059221, 8661698266377926533),
    (46912496118442, 15318281316170197782),
    (93824992236885, 6153913113235778674),
    (187649984473770, 12590900751084468504),
    (375299968947541, 6241392359340867991),
    (750599937895082, 13537483124624848846),
    (1501199875790165, 4738027310139864785),
    (3002399751580330, 11532633803407155562),
    (6004799503160661, 8250739964050374057),
    (12009599006321322, 15163568353485845146),
    (24019198012642645, 8429364114987332836),
    (48038396025285290, 15269178436121023499),
    (96076792050570581, 17609702562285369574),
    (192153584101141162, 193879326829526857),
    (384307168202282325, 3095595981615055618),
    (768614336404564650, 4520231837250186676),
    (1537228672809129301, 16733099453633052576),
    (3074457345618258602, 1986500647487271729),
    (6148914691236517205, 1858076378458151938)]

/-- Residue of `root ^ ((fieldSize - 1) / 3)`. -/
def rootPowDiv3Residue : Nat :=
  1858076378458151938

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
    (51, 2251799813685248),
    (102, 7421703487488),
    (204, 31158272),
    (409, 741664247250944),
    (819, 614742265454497112),
    (1638, 1695209234734939115),
    (3276, 775130197547892574),
    (6553, 12537001131179822224),
    (13107, 17615980313972881911),
    (26214, 572385715309389091),
    (52428, 4739272290175120857),
    (104857, 13842492915490533145),
    (209715, 13871847693897305998),
    (419430, 8455439506674631074),
    (838860, 9493498753804115715),
    (1677721, 12169678962202302099),
    (3355443, 17847407213643894547),
    (6710886, 542118931229881903),
    (13421772, 4954123332599001826),
    (26843545, 4849497804619816645),
    (53687091, 7658167510715674113),
    (107374182, 11523011428416975302),
    (214748364, 11029696507194194569),
    (429496729, 13383781749761052059),
    (858993459, 4736030129335515051),
    (1717986918, 11825872944594744153),
    (3435973836, 13303924860188256192),
    (6871947673, 4721276808310060623),
    (13743895347, 7501028808047771839),
    (27487790694, 14970345159955071973),
    (54975581388, 7349999157695252967),
    (109951162777, 3538319141024286047),
    (219902325555, 17194375590543073860),
    (439804651110, 5645975784458735702),
    (879609302220, 16291961861482157576),
    (1759218604441, 13470997692184657978),
    (3518437208883, 4717150064516401577),
    (7036874417766, 17680995585741177905),
    (14073748835532, 4823281833483465308),
    (28147497671065, 14039441887863849435),
    (56294995342131, 13861647657052316390),
    (112589990684262, 8160990201683069433),
    (225179981368524, 9736465841236211841),
    (450359962737049, 650412515276143405),
    (900719925474099, 10357861010334771266),
    (1801439850948198, 10610728455063578357),
    (3602879701896396, 9972857463710343756),
    (7205759403792793, 12671927713076749239),
    (14411518807585587, 17736012934613873235),
    (28823037615171174, 1340234834950776819),
    (57646075230342348, 827128078216238258),
    (115292150460684697, 12632352266407194960),
    (230584300921369395, 6245875499889307641),
    (461168601842738790, 18149135383924833834),
    (922337203685477580, 339314029946848734),
    (1844674407370955161, 12233269549184699558),
    (3689348814741910323, 6753221685647269129)]

/-- Residue of `root ^ ((fieldSize - 1) / 5)`. -/
def rootPowDiv5Residue : Nat :=
  6753221685647269129

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
    (60, 1152921504606846976),
    (120, 1945555039024054272),
    (240, 2141180147837960192),
    (481, 4096988742676381696),
    (963, 16397284557568314936),
    (1927, 12883440346528595156),
    (3855, 5502357835101356655),
    (7710, 11971056134035252030),
    (15420, 17999049644792178958),
    (30840, 6110368521546413774),
    (61680, 18133241910698190584),
    (123361, 9358888601177629748),
    (246723, 2889815726003302671),
    (493447, 6172354125460813092),
    (986895, 18265286746424954883),
    (1973790, 5002322587161575919),
    (3947580, 17649500154884868153),
    (7895160, 284318660805990683),
    (15790320, 5773639088123718213),
    (31580641, 6097997731130832313),
    (63161283, 16127198964082528943),
    (126322567, 14997240368184985798),
    (252645135, 8944283063646812964),
    (505290270, 9598693700748772119),
    (1010580540, 9276046253884316239),
    (2021161080, 10467175751356451512),
    (4042322160, 14937230767959529837),
    (8084644321, 17054372478629103640),
    (16169288643, 1605532020783822772),
    (32338577287, 10742001702566384374),
    (64677154575, 3881597435267773023),
    (129354309150, 7397277944650245694),
    (258708618300, 15699530505333446804),
    (517417236600, 3208881070711777873),
    (1034834473200, 7652414838927637418),
    (2069668946401, 11491186187456768165),
    (4139337892803, 11144026633947481581),
    (8278675785607, 13357662386041159221),
    (16557351571215, 7140415565801644003),
    (33114703142430, 15593444141465942046),
    (66229406284860, 7534953760740305829),
    (132458812569720, 15763600732378596822),
    (264917625139440, 4372767040240876693),
    (529835250278881, 6973635062753595202),
    (1059670500557763, 10965820371697859397),
    (2119341001115527, 11070541345736729347),
    (4238682002231055, 13335704236759936587),
    (8477364004462110, 12811155757958806980),
    (16954728008924220, 13121633050386294417),
    (33909456017848440, 16329222712584433963),
    (67818912035696880, 6641557631996314280),
    (135637824071393761, 8856607681970768885),
    (271275648142787523, 10087666430596238049),
    (542551296285575047, 10187180005000642125),
    (1085102592571150095, 934417933708345563)]

/-- Residue of `root ^ ((fieldSize - 1) / 17)`. -/
def rootPowDiv17Residue : Nat :=
  934417933708345563

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
    (63, 9223372036854775808),
    (127, 9223372036854775983),
    (255, 9223372036854810629),
    (510, 13835058056360099915),
    (1020, 6917546619827130372),
    (2040, 15852670688780353547),
    (4080, 7868914448923099140),
    (8160, 15810861415100579851),
    (16320, 7905746674450609924),
    (32640, 10050318714223441623),
    (65280, 14048561813064617288),
    (130561, 14003573154494000564),
    (261123, 16199998851856285484),
    (522247, 11143697931309953068),
    (1044495, 13510782506780650327),
    (2088991, 4712324870270884331),
    (4177983, 16725579547643685031),
    (8355967, 13054416880880094150),
    (16711935, 14230917241974333543),
    (33423870, 8426113191624343295),
    (66847740, 10589962743355204133),
    (133695480, 10033763316657226832),
    (267390960, 15489626251543104045),
    (534781920, 7755012294843499644),
    (1069563840, 16043379140506339467),
    (2139127680, 2909041589022223219),
    (4278255360, 3158690311495552990),
    (8556510721, 17816484055161149936),
    (17113021443, 550917475208425946),
    (34226042887, 2381130819332677936),
    (68452085775, 17923778717675082454),
    (136904171551, 9441773188340007204),
    (273808343103, 598593371972789903),
    (547616686207, 1126265079727325354),
    (1095233372415, 2595017038785196166),
    (2190466744830, 8783238042965782547),
    (4380933489660, 10780590433868302274),
    (8761866979320, 11455074362790071365),
    (17523733958640, 9892809175183578955),
    (35047467917280, 10848035612234666456),
    (70094935834560, 10348927729312353217),
    (140189871669120, 15426110064449967963),
    (280379743338240, 9141563848451407107),
    (560759486676481, 2458669077384804607),
    (1121518973352963, 8852555409678609060),
    (2243037946705927, 9473033605397112885),
    (4486075893411855, 785751923792335491),
    (8972151786823711, 422266354773421490),
    (17944303573647423, 862573781629307622),
    (35888607147294847, 12486372504028562856),
    (71777214294589695, 6259950186334376129)]

/-- Residue of `root ^ ((fieldSize - 1) / 257)`. -/
def rootPowDiv257Residue : Nat :=
  6259950186334376129

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

/-- Structural power chain for `root ^ ((fieldSize - 1) / 641)`. -/
def rootPowDiv641Chain : List (Nat × Nat) :=
  [(0, 1),
    (1, 2),
    (3, 8),
    (6, 64),
    (12, 4096),
    (25, 33554432),
    (51, 2251799813685248),
    (102, 7421703487488),
    (204, 31158272),
    (408, 370832123625472),
    (817, 153685566363624278),
    (1635, 2517744163555561342),
    (3271, 15012202378562382320),
    (6543, 18170756862725007674),
    (13086, 28199878090168517),
    (26173, 11539237407358712012),
    (52347, 18023503466788146575),
    (104694, 48757091473971919),
    (209388, 6149641648998841173),
    (418776, 13739051797956841741),
    (837552, 11551731855768840976),
    (1675104, 13566235451271814125),
    (3350208, 12781674114376263099),
    (6700416, 13190719059879418216),
    (13400833, 14343415190391100335),
    (26801667, 5263586565831700496),
    (53603335, 7860653167533373869),
    (107206671, 3914786640680795407),
    (214413343, 14968100261656620540),
    (428826687, 16432308167853118202),
    (857653375, 1252147369269413764),
    (1715306751, 11429910066283625334),
    (3430613503, 3476658674257064401),
    (6861227006, 2526626407823178929),
    (13722454012, 4333324053496131505),
    (27444908025, 6945386695125100898),
    (54889816051, 3470921799577998237),
    (109779632102, 3694476400150069537),
    (219559264204, 8242345632324104925),
    (439118528409, 3338064937220306103),
    (878237056819, 9086958808615604772),
    (1756474113639, 11536026967193564013),
    (3512948227278, 17961562390662465996),
    (7025896454556, 1503820422458456737),
    (14051792909112, 5666422559142507185),
    (28103585818224, 17535602372484461485),
    (56207171636449, 307779687151503054),
    (112414343272898, 5039797362426662984),
    (224828686545796, 16265052519128305756),
    (449657373091593, 4184382385916090284),
    (899314746183187, 16823370750287228992),
    (1798629492366375, 4584384662368261762),
    (3597258984732751, 7641397096994770438),
    (7194517969465503, 3841587427645904613),
    (14389035938931007, 14266695536909557140),
    (28778071877862015, 7779978215417873058)]

/-- Residue of `root ^ ((fieldSize - 1) / 641)`. -/
def rootPowDiv641Residue : Nat :=
  7779978215417873058

/-- Kernel check for `root ^ ((fieldSize - 1) / 641)`. -/
theorem root_pow_div_641_check :
    BinaryField.Extension.Concrete.checkPowNatChain Concrete.params 2
      ((fieldSize - 1) / 641) rootPowDiv641Chain rootPowDiv641Residue = true := by
  rfl

private theorem root_pow_div_641_certified :
    ConcreteField.root ^ ((fieldSize - 1) / 641) =
        ConcreteField.ofNat rootPowDiv641Residue ∧
      rootPowDiv641Residue < 2 ^ extensionDegree := by
  simpa [ConcreteField.root, ConcreteField.ofNat, BinaryField.Extension.Concrete.root,
    Concrete.params] using
    (BinaryField.Extension.Concrete.pow_eq_of_checkPowNatChain
      Concrete.params (a := 2) (target := (fieldSize - 1) / 641)
      (cert := rootPowDiv641Chain) (expected := rootPowDiv641Residue)
      (by unfold Concrete.params extensionDegree; norm_num)
      (by unfold Concrete.params extensionDegree; norm_num)
      root_pow_div_641_check)

/-- Certified residue of `root ^ ((fieldSize - 1) / 641)`. -/
theorem root_pow_div_641_eq :
    ConcreteField.root ^ ((fieldSize - 1) / 641) =
      ConcreteField.ofNat rootPowDiv641Residue :=
  root_pow_div_641_certified.1

/-- The `641`-prime divisor power of the root is nontrivial. -/
theorem root_pow_div_641_ne_one :
    ConcreteField.root ^ ((fieldSize - 1) / 641) ≠ (1 : ConcreteField) := by
  rw [root_pow_div_641_eq]
  change BinaryField.Extension.Concrete.ofNat Concrete.params
      rootPowDiv641Residue ≠ BinaryField.Extension.Concrete.one Concrete.params
  exact BinaryField.Extension.Concrete.ofNat_ne_one_of_lt Concrete.params
    (by unfold Concrete.params extensionDegree; norm_num)
    (by simpa [rootPowDiv641Residue] using root_pow_div_641_certified.2)
    (by unfold rootPowDiv641Residue; norm_num)

/-- Structural power chain for `root ^ ((fieldSize - 1) / 65537)`. -/
def rootPowDiv65537Chain : List (Nat × Nat) :=
  [(0, 1),
    (1, 2),
    (3, 8),
    (7, 128),
    (15, 32768),
    (31, 2147483648),
    (63, 9223372036854775808),
    (127, 9223372036854775983),
    (255, 9223372036854810629),
    (511, 9223372039010648205),
    (1023, 140737488388109),
    (2047, 55834575010),
    (4095, 34526),
    (8191, 2150146728),
    (16383, 9223381384985872512),
    (32767, 36029349141217455),
    (65535, 9272771591053052074),
    (131070, 13836935268454033522),
    (262140, 2305862589952212549),
    (524280, 4131020304175097613),
    (1048560, 6957704021784009441),
    (2097120, 11048036110380782337),
    (4194240, 11014396488249292615),
    (8388480, 10143929262081728584),
    (16776960, 15521217246677174957),
    (33553920, 4312069708791884235),
    (67107840, 2424478959916259118),
    (134215680, 4330396582168917476),
    (268431360, 3490387098519200791),
    (536862720, 3626688616775211641),
    (1073725440, 2462619771810090993),
    (2147450880, 3182121027457317229),
    (4294901760, 7742038277098398358),
    (8589803521, 13819056402066206571),
    (17179607043, 13871343205798092101),
    (34359214087, 5334375927601494808),
    (68718428175, 16677394170408557005),
    (137436856351, 3676534277026740430),
    (274873712703, 16638137442702143088),
    (549747425407, 10454565298279346484),
    (1099494850815, 3896800843627850369),
    (2198989701631, 8005321385189303170),
    (4397979403263, 1597716869343557885),
    (8795958806527, 4015086932901931308),
    (17591917613055, 4972478849236428280),
    (35183835226111, 7166537877424996291),
    (70367670452223, 1787838675202753407),
    (140735340904447, 1235365684474725500),
    (281470681808895, 2026190363967203278)]

/-- Residue of `root ^ ((fieldSize - 1) / 65537)`. -/
def rootPowDiv65537Residue : Nat :=
  2026190363967203278

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

/-- Structural power chain for `root ^ ((fieldSize - 1) / 6700417)`. -/
def rootPowDiv6700417Chain : List (Nat × Nat) :=
  [(0, 1),
    (1, 2),
    (2, 4),
    (5, 32),
    (10, 1024),
    (20, 1048576),
    (40, 1099511627776),
    (80, 1769472),
    (160, 1395864371200),
    (320, 1749419),
    (640, 1392727114821),
    (1281, 2315413167550055234),
    (2563, 14988220327703224528),
    (5127, 15996786455491289562),
    (10255, 8805137778939470258),
    (20511, 277233553980940197),
    (41023, 11736513695949326074),
    (82047, 6554630823350282655),
    (164095, 15806666150837387953),
    (328191, 8351919345915834966),
    (656383, 10252510146753435987),
    (1312767, 1060966642988709669),
    (2625535, 2753893685143373178),
    (5251071, 18129492098565621510),
    (10502143, 3152972240194895986),
    (21004287, 15558470632917411048),
    (42008575, 6848318466046628716),
    (84017151, 8082878837150412909),
    (168034303, 9550010875068132311),
    (336068607, 2985619513454219229),
    (672137215, 15390803841133607572),
    (1344274431, 6769929685099678786),
    (2688548863, 6543875676375545373),
    (5377097726, 16783560468053995857),
    (10754195453, 13235724490548147288),
    (21508390906, 12074620434524055146),
    (43016781813, 15249642109578593833),
    (86033563627, 8377108833218422510),
    (172067127255, 1144969938178970419),
    (344134254511, 9694755075876601732),
    (688268509023, 12375203333100091535),
    (1376537018047, 9026313549350721747),
    (2753074036095, 69034349764540817)]

/-- Residue of `root ^ ((fieldSize - 1) / 6700417)`. -/
def rootPowDiv6700417Residue : Nat :=
  69034349764540817

/-- Kernel check for `root ^ ((fieldSize - 1) / 6700417)`. -/
theorem root_pow_div_6700417_check :
    BinaryField.Extension.Concrete.checkPowNatChain Concrete.params 2
      ((fieldSize - 1) / 6700417) rootPowDiv6700417Chain rootPowDiv6700417Residue = true := by
  rfl

private theorem root_pow_div_6700417_certified :
    ConcreteField.root ^ ((fieldSize - 1) / 6700417) =
        ConcreteField.ofNat rootPowDiv6700417Residue ∧
      rootPowDiv6700417Residue < 2 ^ extensionDegree := by
  simpa [ConcreteField.root, ConcreteField.ofNat, BinaryField.Extension.Concrete.root,
    Concrete.params] using
    (BinaryField.Extension.Concrete.pow_eq_of_checkPowNatChain
      Concrete.params (a := 2) (target := (fieldSize - 1) / 6700417)
      (cert := rootPowDiv6700417Chain) (expected := rootPowDiv6700417Residue)
      (by unfold Concrete.params extensionDegree; norm_num)
      (by unfold Concrete.params extensionDegree; norm_num)
      root_pow_div_6700417_check)

/-- Certified residue of `root ^ ((fieldSize - 1) / 6700417)`. -/
theorem root_pow_div_6700417_eq :
    ConcreteField.root ^ ((fieldSize - 1) / 6700417) =
      ConcreteField.ofNat rootPowDiv6700417Residue :=
  root_pow_div_6700417_certified.1

/-- The `6700417`-prime divisor power of the root is nontrivial. -/
theorem root_pow_div_6700417_ne_one :
    ConcreteField.root ^ ((fieldSize - 1) / 6700417) ≠ (1 : ConcreteField) := by
  rw [root_pow_div_6700417_eq]
  change BinaryField.Extension.Concrete.ofNat Concrete.params
      rootPowDiv6700417Residue ≠ BinaryField.Extension.Concrete.one Concrete.params
  exact BinaryField.Extension.Concrete.ofNat_ne_one_of_lt Concrete.params
    (by unfold Concrete.params extensionDegree; norm_num)
    (by simpa [rootPowDiv6700417Residue] using root_pow_div_6700417_certified.2)
    (by unfold rootPowDiv6700417Residue; norm_num)

end GF2_64
