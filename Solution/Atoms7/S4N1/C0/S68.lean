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

namespace RACert.S4N1.C0.S68

open RACert RACert.Problem

theorem cover27373 : P.CoversSplit 24 10 27373 0xcc00cc0088008000cc00cc0088008000cc00000000000800cc00000000000800cc00cc0080008000cc00cc0080008000cc00000008000800cc00000008000800cc00cc0088008000cc00000088000000cc000c0000000800cc000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 859, 1202, 1210, 1259, 1264, 1601]) (by decide +kernel)

theorem c27373_0 : P.sumLeaves 24 28029952 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 27373) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover27373 (by decide)
  decide +kernel

theorem contract27373_1 : P.leaf 30 437973 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 473), (29, 1, 473), (4, 1, 536), (14, 0, 1266), (31, 12, 908), (20, 1, 923), (21, 1, 929), (12, 1, 965)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c27373_1 : P.sumLeaves 24 28030272 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 437973) rows (by decide) (by decide)).symm.trans contract27373_1

theorem c27373_2 : P.sumLeaves 24 28030336 640 = 17426752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 27373) (lo := 384) (len := 640) (W := 17426752) check rows elimOK (by decide) (by decide) cover27373 (by decide)
  decide +kernel

theorem h27373 : P.leaf 34 27373 = 17426752 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (640, 17426752)]) (.cons c27373_0 (.cons c27373_1 (.cons c27373_2 (.nil)))) (by decide) (by decide))

theorem h22446 : P.leaf 34 22446 = 17426752 :=
  orient24 (v := 27373) (by decide) (by decide +kernel) h27373

theorem cover22447 : P.CoversSplit 24 10 22447 0xfffffffffafa0000fffffffffafa0000aaaaafaf00000000aaaa000000000000cccccccc88880000cccccccc8888000088888c8c000000008888000000000000fffffffffafa00000000000000000000aaaaafaf0000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 860, 916, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem c22447_0 : P.sumLeaves 24 22985728 698 = 17201184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22447) (lo := 0) (len := 698) (W := 17201184) check rows elimOK (by decide) (by decide) cover22447 (by decide)
  decide +kernel

theorem c22447_1 : P.sumLeaves 24 22986426 279 = 35190731 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22447) (lo := 698) (len := 279) (W := 35190731) check rows elimOK (by decide) (by decide) cover22447 (by decide)
  decide +kernel

theorem c22447_2 : P.sumLeaves 24 22986705 47 = 40333688 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22447) (lo := 977) (len := 47) (W := 40333688) check rows elimOK (by decide) (by decide) cover22447 (by decide)
  decide +kernel

theorem h22447 : P.leaf 34 22447 = 92725603 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(698, 17201184), (279, 35190731), (47, 40333688)]) (.cons c22447_0 (.cons c22447_1 (.cons c22447_2 (.nil)))) (by decide) (by decide))

theorem cover23526 : P.CoversSplit 24 10 23526 0xffffffffaaaaa0a0ffffffffaaaaa0a0f0f0000000000000f0f0000000000000cccccccc88888080cccccccc88888080c0c0000000000000c0c0000000000000ffffffffaaaaa0a00000000000000000f0f055550000000030300000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 859, 879, 1202, 1210, 1259, 1601]) (ps := [(17, [871, 1251], [1259])]) (by decide +kernel)

theorem c23526_0 : P.sumLeaves 24 24090624 723 = 10944768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23526) (lo := 0) (len := 723) (W := 10944768) check rows elimOK (by decide) (by decide) cover23526 (by decide)
  decide +kernel

theorem c23526_1 : P.sumLeaves 24 24091347 273 = 17381656 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23526) (lo := 723) (len := 273) (W := 17381656) check rows elimOK (by decide) (by decide) cover23526 (by decide)
  decide +kernel

theorem c23526_2 : P.sumLeaves 24 24091620 28 = 18944396 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23526) (lo := 996) (len := 28) (W := 18944396) check rows elimOK (by decide) (by decide) cover23526 (by decide)
  decide +kernel

theorem h23526 : P.leaf 34 23526 = 47270820 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(723, 10944768), (273, 17381656), (28, 18944396)]) (.cons c23526_0 (.cons c23526_1 (.cons c23526_2 (.nil)))) (by decide) (by decide))

theorem h22460 : P.leaf 34 22460 = 47270820 :=
  orient4 (v := 23526) (by decide) (by decide +kernel) h23526

theorem cover23527 : P.CoversSplit 24 10 23527 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffff000000000000ffff000000000000cccccccc88888080cccccccc88888080cccc000000000000cccc000000000000ffffffffaaaaa0a00000000000000000ffff55550000000033330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 859, 1202, 1210, 1259, 1601]) (ps := [(17, [1251], [1259])]) (by decide +kernel)

theorem c23527_0 : P.sumLeaves 24 24091648 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23527) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover23527 (by decide)
  decide +kernel

theorem contract23527_1 : P.leaf 30 376436 = 0 := by
  exact leaf_contract_zero (ss := [(17, 0, 1259), (4, 1, 565), (8, 0, 880), (21, 0, 880), (6, 1, 482), (14, 1, 482)]) (q := 629) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c23527_1 : P.sumLeaves 24 24091904 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 376436) rows (by decide) (by decide)).symm.trans contract23527_1

theorem c23527_2 : P.sumLeaves 24 24091968 366 = 24232542 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23527) (lo := 320) (len := 366) (W := 24232542) check rows elimOK (by decide) (by decide) cover23527 (by decide)
  decide +kernel

theorem c23527_3 : P.sumLeaves 24 24092334 262 = 30018425 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23527) (lo := 686) (len := 262) (W := 30018425) check rows elimOK (by decide) (by decide) cover23527 (by decide)
  decide +kernel

theorem c23527_4 : P.sumLeaves 24 24092596 76 = 58346818 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23527) (lo := 948) (len := 76) (W := 58346818) check rows elimOK (by decide) (by decide) cover23527 (by decide)
  decide +kernel

theorem h23527 : P.leaf 34 23527 = 112597785 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (366, 24232542), (262, 30018425), (76, 58346818)]) (.cons c23527_0 (.cons c23527_1 (.cons c23527_2 (.cons c23527_3 (.cons c23527_4 (.nil)))))) (by decide) (by decide))

theorem h22461 : P.leaf 34 22461 = 112597785 :=
  orient4 (v := 23527) (by decide) (by decide +kernel) h23527

theorem cover27375 : P.CoversSplit 24 10 27375 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffff000000000a0affff000000000a0aff00ff0080008000cc00cc0080008000ff00000008000800cc00000008000800ffffffffaaaaa0a0ffff0000aaaa0000ffff0f0f00000a0affff0000000000000000000000000000cc00000080000000ff00000000000000cc00000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 859, 915, 1202, 1210, 1259, 1264, 1601, 1609]) (ps := [(8, [1217], [1609])]) (by decide +kernel)

theorem c27375_0 : P.sumLeaves 24 28032000 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 27375) (lo := 0) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover27375 (by decide)
  decide +kernel

theorem contract27375_1 : P.leaf 30 438001 = 0 := by
  exact leaf_contract_zero (ss := [(4, 1, 536), (10, 1, 879), (11, 1, 921), (30, 1, 1264), (14, 0, 1266), (12, 1, 908), (21, 0, 1266), (8, 1, 580), (20, 1, 1272), (29, 1, 1601), (27, 0, 1609), (31, 1, 1259)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c27375_1 : P.sumLeaves 24 28032064 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 438001) rows (by decide) (by decide)).symm.trans contract27375_1

theorem c27375_2 : P.sumLeaves 24 28032128 128 = 21552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 27375) (lo := 128) (len := 128) (W := 21552) check rows elimOK (by decide) (by decide) cover27375 (by decide)
  decide +kernel

theorem contract27375_3 : P.leaf 30 438004 = 0 := by
  exact leaf_contract_zero (ss := [(4, 1, 536), (30, 1, 1264), (31, 1, 1210), (14, 0, 1266), (12, 1, 908), (21, 0, 1266), (8, 1, 580), (20, 1, 1272)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c27375_3 : P.sumLeaves 24 28032256 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 438004) rows (by decide) (by decide)).symm.trans contract27375_3

theorem contract27375_4 : P.leaf 30 438005 = 0 := by
  exact leaf_contract_zero (ss := [(4, 1, 536), (14, 0, 1266), (12, 1, 908), (21, 0, 1266), (8, 1, 580), (20, 1, 1272)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c27375_4 : P.sumLeaves 24 28032320 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 438005) rows (by decide) (by decide)).symm.trans contract27375_4

theorem c27375_5 : P.sumLeaves 24 28032384 360 = 26160420 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 27375) (lo := 384) (len := 360) (W := 26160420) check rows elimOK (by decide) (by decide) cover27375 (by decide)
  decide +kernel

theorem c27375_6 : P.sumLeaves 24 28032744 212 = 38286894 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 27375) (lo := 744) (len := 212) (W := 38286894) check rows elimOK (by decide) (by decide) cover27375 (by decide)
  decide +kernel

theorem c27375_7 : P.sumLeaves 24 28032956 68 = 41138814 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 27375) (lo := 956) (len := 68) (W := 41138814) check rows elimOK (by decide) (by decide) cover27375 (by decide)
  decide +kernel

theorem h27375 : P.leaf 34 27375 = 105607680 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (128, 21552), (64, 0), (64, 0), (360, 26160420), (212, 38286894), (68, 41138814)]) (.cons c27375_0 (.cons c27375_1 (.cons c27375_2 (.cons c27375_3 (.cons c27375_4 (.cons c27375_5 (.cons c27375_6 (.cons c27375_7 (.nil))))))))) (by decide) (by decide))

theorem h22462 : P.leaf 34 22462 = 105607680 :=
  orient24 (v := 27375) (by decide) (by decide +kernel) h27375

theorem cover22463 : P.CoversSplit 24 10 22463 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff000000000000cccccccc88880000cccccccc88880000cccccccc00000000cccc000000000000fffffffffafa0000fffffffffafa0000fffffffffa000000ffff000000000000cccccccc88880000cccccccc8888000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 860, 909, 916, 1202, 1210, 1217, 1251, 1308, 1601]) (by decide +kernel)

theorem c22463_0 : P.sumLeaves 24 23002112 404 = 12130926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22463) (lo := 0) (len := 404) (W := 12130926) check rows elimOK (by decide) (by decide) cover22463 (by decide)
  decide +kernel

theorem c22463_1 : P.sumLeaves 24 23002516 210 = 53730647 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22463) (lo := 404) (len := 210) (W := 53730647) check rows elimOK (by decide) (by decide) cover22463 (by decide)
  decide +kernel

theorem c22463_2 : P.sumLeaves 24 23002726 276 = 55546600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22463) (lo := 614) (len := 276) (W := 55546600) check rows elimOK (by decide) (by decide) cover22463 (by decide)
  decide +kernel

theorem c22463_3 : P.sumLeaves 24 23003002 134 = 133462388 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22463) (lo := 890) (len := 134) (W := 133462388) check rows elimOK (by decide) (by decide) cover22463 (by decide)
  decide +kernel

theorem h22463 : P.leaf 34 22463 = 254870561 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(404, 12130926), (210, 53730647), (276, 55546600), (134, 133462388)]) (.cons c22463_0 (.cons c22463_1 (.cons c22463_2 (.cons c22463_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(22446, 48), (22447, 48), (22460, 48), (22461, 48), (22462, 48), (22463, 48)]

theorem segOK : checkSeg 16 perms 22446 22508 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22446 22508 288 30263961648 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 30263961648)
    (SegSum.cons (w := 48) h22446 (SegSum.cons (w := 48) h22447 (SegSum.cons (w := 48) h22460 (SegSum.cons (w := 48) h22461 (SegSum.cons (w := 48) h22462 (SegSum.cons (w := 48) h22463 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S68
