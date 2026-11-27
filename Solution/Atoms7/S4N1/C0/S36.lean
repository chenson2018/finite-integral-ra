/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S36

open RACert RACert.Problem

theorem cover6006 : P.CoversSplit 24 10 6006 0xffffffffaaaaa0a0ffffffffaaaaa0a0f5f5f5f505050000f5f5f5f505050000cc00cc0080008000cc00cc0080008000c400c40000000000c400c40000000000ffffffffaaaaa0a0ffffffffaaaaa0a0f5f5f5f500000000f5f5f5f5000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 860, 867, 916, 1202, 1209, 1217, 1258, 1601]) (by decide +kernel)

theorem c6006_0 : P.sumLeaves 24 6150144 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6006) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover6006 (by decide)
  decide +kernel

theorem contract6006_1 : P.leaf 30 96100 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 468), (8, 0, 1272), (5, 1, 622), (14, 1, 1266), (9, 1, 629), (21, 1, 629), (20, 1, 678)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6006_1 : P.sumLeaves 24 6150400 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96100) rows (by decide) (by decide)).symm.trans contract6006_1

theorem contract6006_2 : P.leaf 30 96101 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 468), (8, 0, 1272), (5, 1, 622), (14, 1, 1266), (9, 1, 629), (21, 1, 629), (20, 1, 678)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6006_2 : P.sumLeaves 24 6150464 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96101) rows (by decide) (by decide)).symm.trans contract6006_2

theorem c6006_3 : P.sumLeaves 24 6150528 239 = 4350456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6006) (lo := 384) (len := 239) (W := 4350456) check rows elimOK (by decide) (by decide) cover6006 (by decide)
  decide +kernel

theorem c6006_4 : P.sumLeaves 24 6150767 309 = 7127615 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6006) (lo := 623) (len := 309) (W := 7127615) check rows elimOK (by decide) (by decide) cover6006 (by decide)
  decide +kernel

theorem c6006_5 : P.sumLeaves 24 6151076 92 = 18489430 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6006) (lo := 932) (len := 92) (W := 18489430) check rows elimOK (by decide) (by decide) cover6006 (by decide)
  decide +kernel

theorem h6006 : P.leaf 34 6006 = 29967501 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (239, 4350456), (309, 7127615), (92, 18489430)]) (.cons c6006_0 (.cons c6006_1 (.cons c6006_2 (.cons c6006_3 (.cons c6006_4 (.cons c6006_5 (.nil))))))) (by decide) (by decide))

theorem cover6007 : P.CoversSplit 24 10 6007 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffffffffaaaaa0a0ffffffffaaaaa0a0cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc0080008000ffffffffaaaaa0a0ffffffffaaaaa0a0ffffffff00000000ffffffff000000000000000000000000cc00cc0080008000cc00cc0000000000cc00cc0000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 860, 916, 1202, 1209, 1258, 1601, 1609]) (ps := [(8, [1217], [1272]), (14, [958], [1272])]) (by decide +kernel)

theorem contract6007_0 : P.leaf 30 96112 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 475), (6, 1, 480), (4, 1, 578), (10, 1, 872), (11, 1, 921), (27, 1, 1258), (8, 0, 1272), (5, 0, 622), (22, 1, 426), (14, 1, 433), (31, 1, 531), (30, 1, 566), (29, 1, 572), (25, 1, 573)]) (q := 580) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6007_0 : P.sumLeaves 24 6151168 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96112) rows (by decide) (by decide)).symm.trans contract6007_0

theorem contract6007_1 : P.leaf 30 96113 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 475), (6, 1, 480), (4, 1, 578), (10, 1, 872), (11, 1, 921), (8, 0, 1272), (5, 0, 622), (22, 1, 426), (14, 1, 433), (31, 1, 531)]) (q := 580) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6007_1 : P.sumLeaves 24 6151232 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96113) rows (by decide) (by decide)).symm.trans contract6007_1

theorem contract6007_2 : P.leaf 30 96114 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 475), (6, 1, 480), (4, 1, 578), (10, 1, 872), (11, 1, 921), (27, 1, 1258), (29, 1, 1601), (8, 0, 1609), (5, 1, 580)]) (q := 622) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6007_2 : P.sumLeaves 24 6151296 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96114) rows (by decide) (by decide)).symm.trans contract6007_2

theorem c6007_3 : P.sumLeaves 24 6151360 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6007) (lo := 192) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover6007 (by decide)
  decide +kernel

theorem contract6007_4 : P.leaf 30 96116 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1272), (5, 1, 622), (14, 1, 1266), (9, 1, 629), (21, 1, 629), (20, 1, 678)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6007_4 : P.sumLeaves 24 6151424 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96116) rows (by decide) (by decide)).symm.trans contract6007_4

theorem contract6007_5 : P.leaf 30 96117 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1272), (5, 1, 622), (14, 1, 1266), (9, 1, 629), (21, 1, 629), (20, 1, 678)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6007_5 : P.sumLeaves 24 6151488 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96117) rows (by decide) (by decide)).symm.trans contract6007_5

theorem c6007_6 : P.sumLeaves 24 6151552 190 = 11160072 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6007) (lo := 384) (len := 190) (W := 11160072) check rows elimOK (by decide) (by decide) cover6007 (by decide)
  decide +kernel

theorem c6007_7 : P.sumLeaves 24 6151742 298 = 15355301 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6007) (lo := 574) (len := 298) (W := 15355301) check rows elimOK (by decide) (by decide) cover6007 (by decide)
  decide +kernel

theorem c6007_8 : P.sumLeaves 24 6152040 136 = 45470962 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6007) (lo := 872) (len := 136) (W := 45470962) check rows elimOK (by decide) (by decide) cover6007 (by decide)
  decide +kernel

theorem c6007_9 : P.sumLeaves 24 6152176 16 = 14164098 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6007) (lo := 1008) (len := 16) (W := 14164098) check rows elimOK (by decide) (by decide) cover6007 (by decide)
  decide +kernel

theorem h6007 : P.leaf 34 6007 = 86150433 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (64, 0), (64, 0), (64, 0), (64, 0), (190, 11160072), (298, 15355301), (136, 45470962), (16, 14164098)]) (.cons c6007_0 (.cons c6007_1 (.cons c6007_2 (.cons c6007_3 (.cons c6007_4 (.cons c6007_5 (.cons c6007_6 (.cons c6007_7 (.cons c6007_8 (.cons c6007_9 (.nil))))))))))) (by decide) (by decide))

theorem cover6008 : P.CoversSplit 24 10 6008 0xffffffffa0a0a0a0ffffffffa0a0a0a0f0f0f0f000000000f0f0f0f000000000cc00cc0080008000cc00cc0080008000c000c00000000000c000c00000000000cc00cc0080008000cc00cc0080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 572, 860, 916, 1202, 1209, 1258, 1601]) (ps := [(2, [465], [466]), (5, [565], [572]), (6, [474], [466]), (8, [586, 1217], [572, 1272, 1609]), (12, [867, 909], [860, 867, 909]), (14, [558], [860, 916, 1272])]) (by decide +kernel)

theorem c6008_0 : P.sumLeaves 24 6152192 512 = 173192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6008) (lo := 0) (len := 512) (W := 173192) check rows elimOK (by decide) (by decide) cover6008 (by decide)
  decide +kernel

theorem contract6008_1 : P.leaf 30 96136 = 22064 := by
  apply (leaf_contract (k := 30) (b := 18) (H := 96136) (ss := [(15, 1, 487), (2, 1, 486), (14, 1, 558), (5, 1, 572), (27, 1, 572), (19, 1, 578), (12, 1, 867), (16, 1, 874), (31, 1, 909), (28, 1, 860), (18, 1, 879), (29, 1, 916)]) (ids := [1, 2, 4, 5, 6, 7, 8, 9, 11, 15, 18, 19, 20, 21, 22, 23, 24, 28]) (cs := [1, 2, 3, 1, 4, 5, 6, 7, 8, 9, 1, 10, 1, 1, 1, 11, 1, 1, 12, 13, 14, 15, 16, 17, 18, 1, 1, 1, 19, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c6008_1 : P.sumLeaves 24 6152704 64 = 22064 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96136) rows (by decide) (by decide)).symm.trans contract6008_1

theorem c6008_2 : P.sumLeaves 24 6152768 389 = 1659652 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6008) (lo := 576) (len := 389) (W := 1659652) check rows elimOK (by decide) (by decide) cover6008 (by decide)
  decide +kernel

theorem c6008_3 : P.sumLeaves 24 6153157 59 = 1425568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6008) (lo := 965) (len := 59) (W := 1425568) check rows elimOK (by decide) (by decide) cover6008 (by decide)
  decide +kernel

theorem h6008 : P.leaf 34 6008 = 3280476 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(512, 173192), (64, 22064), (389, 1659652), (59, 1425568)]) (.cons c6008_0 (.cons c6008_1 (.cons c6008_2 (.cons c6008_3 (.nil))))) (by decide) (by decide))

theorem cover6009 : P.CoversSplit 24 10 6009 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffff00000000ffffffff00000000cc00cc0080008000cc00cc0080008000cc00cc0000000000cc00cc0000000000cc00cc0080008000cc00cc0080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 572, 860, 916, 1202, 1258, 1601]) (ps := [(5, [523], [572]), (8, [586], [572, 1609]), (12, [860, 867], [909, 916]), (14, [558], [916, 1272])]) (by decide +kernel)

theorem c6009_0 : P.sumLeaves 24 6153216 872 = 2624714 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6009) (lo := 0) (len := 872) (W := 2624714) check rows elimOK (by decide) (by decide) cover6009 (by decide)
  decide +kernel

theorem c6009_1 : P.sumLeaves 24 6154088 144 = 5608400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6009) (lo := 872) (len := 144) (W := 5608400) check rows elimOK (by decide) (by decide) cover6009 (by decide)
  decide +kernel

theorem c6009_2 : P.sumLeaves 24 6154232 8 = 1327624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6009) (lo := 1016) (len := 8) (W := 1327624) check rows elimOK (by decide) (by decide) cover6009 (by decide)
  decide +kernel

theorem h6009 : P.leaf 34 6009 = 9560738 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(872, 2624714), (144, 5608400), (8, 1327624)]) (.cons c6009_0 (.cons c6009_1 (.cons c6009_2 (.nil)))) (by decide) (by decide))

theorem cover6010 : P.CoversSplit 24 10 6010 0xffffffffa0a0a0a0ffffffffa0a0a0a0f0f0f0f00f0f0000f0f0f0f00f0f0000cc00cc0080008000cc00cc0080008000c000c00000000000c000c00000000000ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffff00000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 860, 916, 1202, 1209, 1217, 1258, 1601, 1609]) (ps := [(8, [586, 1217], [1272, 1609]), (12, [867, 909], [860, 867]), (14, [874], [860])]) (by decide +kernel)

theorem c6010_0 : P.sumLeaves 24 6154240 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6010) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover6010 (by decide)
  decide +kernel

theorem contract6010_1 : P.leaf 30 96164 = 0 := by
  exact leaf_contract_zero (ss := [(12, 1, 867), (8, 0, 1272), (14, 0, 586), (5, 1, 433), (20, 1, 482), (15, 2, 486), (21, 0, 488), (28, 2, 509), (31, 1, 1217)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6010_1 : P.sumLeaves 24 6154496 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96164) rows (by decide) (by decide)).symm.trans contract6010_1

theorem contract6010_2 : P.leaf 30 96165 = 0 := by
  exact leaf_contract_zero (ss := [(12, 1, 867), (8, 0, 1272), (14, 0, 586), (5, 1, 433), (20, 1, 482), (15, 2, 486), (21, 0, 488), (28, 2, 509), (31, 1, 1217)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6010_2 : P.sumLeaves 24 6154560 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96165) rows (by decide) (by decide)).symm.trans contract6010_2

theorem c6010_3 : P.sumLeaves 24 6154624 318 = 1164958 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6010) (lo := 384) (len := 318) (W := 1164958) check rows elimOK (by decide) (by decide) cover6010 (by decide)
  decide +kernel

theorem c6010_4 : P.sumLeaves 24 6154942 254 = 3130343 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6010) (lo := 702) (len := 254) (W := 3130343) check rows elimOK (by decide) (by decide) cover6010 (by decide)
  decide +kernel

theorem c6010_5 : P.sumLeaves 24 6155196 68 = 4207540 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6010) (lo := 956) (len := 68) (W := 4207540) check rows elimOK (by decide) (by decide) cover6010 (by decide)
  decide +kernel

theorem h6010 : P.leaf 34 6010 = 8502841 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (318, 1164958), (254, 3130343), (68, 4207540)]) (.cons c6010_0 (.cons c6010_1 (.cons c6010_2 (.cons c6010_3 (.cons c6010_4 (.cons c6010_5 (.nil))))))) (by decide) (by decide))

theorem cover6011 : P.CoversSplit 24 10 6011 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc0080008000ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a000000000000000000000000000000000cc00cc0080008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 860, 916, 1202, 1258, 1601, 1609]) (ps := [(8, [586], [1609])]) (by decide +kernel)

theorem contract6011_0 : P.leaf 30 96176 = 0 := by
  exact leaf_contract_zero (ss := [(6, 1, 474), (5, 1, 572), (27, 1, 572), (4, 1, 578), (12, 1, 803), (2, 1, 487), (10, 1, 872), (29, 1, 916), (11, 1, 921), (8, 0, 1272), (14, 0, 586), (20, 1, 482), (21, 0, 488), (31, 1, 1217)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6011_0 : P.sumLeaves 24 6155264 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96176) rows (by decide) (by decide)).symm.trans contract6011_0

theorem contract6011_1 : P.leaf 30 96177 = 0 := by
  exact leaf_contract_zero (ss := [(6, 1, 474), (4, 1, 578), (12, 1, 803), (2, 1, 487), (10, 1, 872), (29, 1, 916), (11, 1, 921), (8, 0, 1272), (14, 0, 586), (5, 1, 433), (20, 1, 482), (21, 0, 488), (31, 1, 1217)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6011_1 : P.sumLeaves 24 6155328 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96177) rows (by decide) (by decide)).symm.trans contract6011_1

theorem c6011_2 : P.sumLeaves 24 6155392 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6011) (lo := 128) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover6011 (by decide)
  decide +kernel

theorem contract6011_3 : P.leaf 30 96180 = 0 := by
  exact leaf_contract_zero (ss := [(12, 1, 867), (8, 0, 1272), (14, 0, 586), (5, 1, 433), (20, 1, 482), (21, 0, 488), (31, 1, 1217)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6011_3 : P.sumLeaves 24 6155520 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96180) rows (by decide) (by decide)).symm.trans contract6011_3

theorem contract6011_4 : P.leaf 30 96181 = 0 := by
  exact leaf_contract_zero (ss := [(12, 1, 867), (8, 0, 1272), (14, 0, 586), (5, 1, 433), (20, 1, 482), (21, 0, 488), (31, 1, 1217)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6011_4 : P.sumLeaves 24 6155584 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96181) rows (by decide) (by decide)).symm.trans contract6011_4

theorem c6011_5 : P.sumLeaves 24 6155648 250 = 3158925 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6011) (lo := 384) (len := 250) (W := 3158925) check rows elimOK (by decide) (by decide) cover6011 (by decide)
  decide +kernel

theorem c6011_6 : P.sumLeaves 24 6155898 254 = 6927215 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6011) (lo := 634) (len := 254) (W := 6927215) check rows elimOK (by decide) (by decide) cover6011 (by decide)
  decide +kernel

theorem c6011_7 : P.sumLeaves 24 6156152 136 = 15884659 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6011) (lo := 888) (len := 136) (W := 15884659) check rows elimOK (by decide) (by decide) cover6011 (by decide)
  decide +kernel

theorem h6011 : P.leaf 34 6011 = 25970799 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (128, 0), (64, 0), (64, 0), (250, 3158925), (254, 6927215), (136, 15884659)]) (.cons c6011_0 (.cons c6011_1 (.cons c6011_2 (.cons c6011_3 (.cons c6011_4 (.cons c6011_5 (.cons c6011_6 (.cons c6011_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(6006, 48), (6007, 48), (6008, 48), (6009, 48), (6010, 48), (6011, 48)]

theorem segOK : checkSeg 16 perms 6006 6012 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6006 6012 288 7844773824 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 7844773824)
    (SegSum.cons (w := 48) h6006 (SegSum.cons (w := 48) h6007 (SegSum.cons (w := 48) h6008 (SegSum.cons (w := 48) h6009 (SegSum.cons (w := 48) h6010 (SegSum.cons (w := 48) h6011 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S36
