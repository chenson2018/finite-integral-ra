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

namespace RACert.S4N1.C0.S62

open RACert RACert.Problem

theorem cover21932 : P.CoversSplit 24 10 21932 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [508]) (by decide +kernel)

theorem h21932 : P.leaf 34 21932 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21932) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21932) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover21932 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover26876 : P.CoversSplit 24 10 26876 0xc000c00080008000000000000000000000000000000000000000000000000000f000f00080008000c000c0008000800000000000000000000000000000000000c000c000800080000000000000000000000000000000000000000000000000000000000000000000003000300020002000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 473, 573, 859, 865, 908, 915, 1202, 1259, 1601]) (by decide +kernel)

theorem c26876_0 : P.sumLeaves 24 27521024 1024 = 2566997 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26876) (lo := 0) (len := 1024) (W := 2566997) check rows elimOK (by decide) (by decide) cover26876 (by decide)
  decide +kernel

theorem h26876 : P.leaf 34 26876 = 2566997 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2566997)]) (.cons c26876_0 (.nil)) (by decide) (by decide))

theorem h21933 : P.leaf 34 21933 = 2566997 :=
  orient24 (v := 26876) (by decide) (by decide +kernel) h26876

theorem cover40297 : P.CoversSplit 24 10 40297 0xcc000000c80000000000000000000000cc000000000000000000000000000000cc000000c00000000000000000000000cc000000080000000000000000000000cc000000c80000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 572, 858, 865, 1202, 1209, 1258]) (by decide +kernel)

theorem c40297_0 : P.sumLeaves 24 41264128 1024 = 1514160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 40297) (lo := 0) (len := 1024) (W := 1514160) check rows elimOK (by decide) (by decide) cover40297 (by decide)
  decide +kernel

theorem h40297 : P.leaf 34 40297 = 1514160 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1514160)]) (.cons c40297_0 (.nil)) (by decide) (by decide))

theorem h21934 : P.leaf 34 21934 = 1514160 :=
  orient25 (v := 40297) (by decide) (by decide +kernel) h40297

theorem cover26877 : P.CoversSplit 24 10 26877 0xcc00cc0088008000000000000000000000000000000000000000000000000000cc00cc0080008000000000000000000000000000000000000000000000000000cc00cc00880080000000000000000000000000000000000000000000000000000000000000000000003300330020002000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 573, 858, 859, 865, 908, 1202, 1210, 1259]) (by decide +kernel)

theorem c26877_0 : P.sumLeaves 24 27522048 1024 = 5598256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26877) (lo := 0) (len := 1024) (W := 5598256) check rows elimOK (by decide) (by decide) cover26877 (by decide)
  decide +kernel

theorem h26877 : P.leaf 34 26877 = 5598256 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5598256)]) (.cons c26877_0 (.nil)) (by decide) (by decide))

theorem h21935 : P.leaf 34 21935 = 5598256 :=
  orient24 (v := 26877) (by decide) (by decide +kernel) h26877

theorem cover21948 : P.CoversSplit 24 10 21948 0xf0000000f0000000f0000000f0000000f000000000000000f000000000000000c000000080000000c000000080000000c000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 858, 860, 867, 1202, 1210, 1217, 1601]) (by decide +kernel)

theorem c21948_0 : P.sumLeaves 24 22474752 1024 = 3592640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21948) (lo := 0) (len := 1024) (W := 3592640) check rows elimOK (by decide) (by decide) cover21948 (by decide)
  decide +kernel

theorem h21948 : P.leaf 34 21948 = 3592640 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3592640)]) (.cons c21948_0 (.nil)) (by decide) (by decide))

theorem cover23015 : P.CoversSplit 24 10 23015 0xffffffffaaaaa0a0ffff0000aaaa0000ffff000000000000ffff000000000000cccccccc88888080cccc000088880000cccc000000000000cccc000000000000ffffffffaaaaa0a00000000000000000ffff55550000000033330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 522, 858, 859, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c23015_0 : P.sumLeaves 24 23567360 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23015) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover23015 (by decide)
  decide +kernel

theorem contract23015_1 : P.leaf 30 368244 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (13, 1, 866), (14, 1, 908), (31, 1, 1210), (17, 0, 1259), (4, 1, 565), (8, 0, 880), (9, 1, 629), (21, 1, 629)]) (q := 880) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c23015_1 : P.sumLeaves 24 23567616 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 368244) rows (by decide) (by decide)).symm.trans contract23015_1

theorem c23015_2 : P.sumLeaves 24 23567680 391 = 11189880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23015) (lo := 320) (len := 391) (W := 11189880) check rows elimOK (by decide) (by decide) cover23015 (by decide)
  decide +kernel

theorem c23015_3 : P.sumLeaves 24 23568071 287 = 18345870 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23015) (lo := 711) (len := 287) (W := 18345870) check rows elimOK (by decide) (by decide) cover23015 (by decide)
  decide +kernel

theorem c23015_4 : P.sumLeaves 24 23568358 26 = 15808096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23015) (lo := 998) (len := 26) (W := 15808096) check rows elimOK (by decide) (by decide) cover23015 (by decide)
  decide +kernel

theorem h23015 : P.leaf 34 23015 = 45343846 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (391, 11189880), (287, 18345870), (26, 15808096)]) (.cons c23015_0 (.cons c23015_1 (.cons c23015_2 (.cons c23015_3 (.cons c23015_4 (.nil)))))) (by decide) (by decide))

theorem h21949 : P.leaf 34 21949 = 45343846 :=
  orient4 (v := 23015) (by decide) (by decide +kernel) h23015

theorem cover21950 : P.CoversSplit 24 10 21950 0xf0f00000f0f00000f0f00000f0f00000f000000000000000f000000000000000c0c0000080800000c000000080000000c000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 860, 865, 867, 909, 916, 1202, 1210, 1217, 1601]) (by decide +kernel)

theorem c21950_0 : P.sumLeaves 24 22476800 1024 = 9210732 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21950) (lo := 0) (len := 1024) (W := 9210732) check rows elimOK (by decide) (by decide) cover21950 (by decide)
  decide +kernel

theorem h21950 : P.leaf 34 21950 = 9210732 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9210732)]) (.cons c21950_0 (.nil)) (by decide) (by decide))

theorem cover21951 : P.CoversSplit 24 10 21951 0xfffffffffafa0000fffffffffafa0000f500f50000000000f500000000000000cccccccc88880000cccccccc88880000c400c40000000000c400000000000000fffffffffafa0000fffffffffafa0000f500f50050000000f500000000000000cccccccc88880000cccccccc8888000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 858, 860, 865, 909, 916, 1202, 1210, 1217, 1251, 1308, 1601]) (by decide +kernel)

theorem c21951_0 : P.sumLeaves 24 22477824 440 = 14387031 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21951) (lo := 0) (len := 440) (W := 14387031) check rows elimOK (by decide) (by decide) cover21951 (by decide)
  decide +kernel

theorem c21951_1 : P.sumLeaves 24 22478264 319 = 37954008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21951) (lo := 440) (len := 319) (W := 37954008) check rows elimOK (by decide) (by decide) cover21951 (by decide)
  decide +kernel

theorem c21951_2 : P.sumLeaves 24 22478583 250 = 63517443 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21951) (lo := 759) (len := 250) (W := 63517443) check rows elimOK (by decide) (by decide) cover21951 (by decide)
  decide +kernel

theorem c21951_3 : P.sumLeaves 24 22478833 15 = 17520882 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21951) (lo := 1009) (len := 15) (W := 17520882) check rows elimOK (by decide) (by decide) cover21951 (by decide)
  decide +kernel

theorem h21951 : P.leaf 34 21951 = 133379364 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(440, 14387031), (319, 37954008), (250, 63517443), (15, 17520882)]) (.cons c21951_0 (.cons c21951_1 (.cons c21951_2 (.cons c21951_3 (.nil))))) (by decide) (by decide))

theorem cover23020 : P.CoversSplit 24 10 23020 0xffffffffaaa0a0a0ffffffffaaa0a0a000000000000000000000000000000000ccc0ccc088808080cc00cc00880080000000000000000000000000000000000000000000000000000000000000000000f00055000000000030301111000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 858, 859, 865, 879, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f23020 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (23572480 + i)

theorem c23020_0 : rowSum f23020 0 1024 = 4713312 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23020) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23020 (by decide)
  decide +kernel

theorem sum23020 : rowSum f23020 0 1024 = 4713312 :=
  c23020_0

theorem h23020 : P.leaf 34 23020 = 4713312 :=
  leaf_weighted (k := 24) (d := 10) (H := 23020) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 23020) (by decide) (by decide +kernel)) sum23020

theorem h21996 : P.leaf 34 21996 = 4713312 :=
  orient4 (v := 23020) (by decide) (by decide +kernel) h23020

theorem cover27132 : P.CoversSplit 24 10 27132 0xff00ff00aa00a000000000000000000000000000000000000000000000000000ff0cff0c88008000cccccccc8880808000000000000000000000000000000000f000f000a000a0000000000000000000000000000000000000000000000000003000300000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 859, 865, 866, 908, 915, 1202, 1259]) (by decide +kernel)

theorem c27132_0 : P.sumLeaves 24 27783168 1024 = 11060042 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 27132) (lo := 0) (len := 1024) (W := 11060042) check rows elimOK (by decide) (by decide) cover27132 (by decide)
  decide +kernel

theorem h27132 : P.leaf 34 27132 = 11060042 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11060042)]) (.cons c27132_0 (.nil)) (by decide) (by decide))

theorem h21997 : P.leaf 34 21997 = 11060042 :=
  orient24 (v := 27132) (by decide) (by decide +kernel) h27132

theorem cover23036 : P.CoversSplit 24 10 23036 0xffffffffaaa0a0a0ffffffffaaa0a0a000000000000000000000000000000000ccc0ccc088808080cc00cc00880080000000000000000000000000000000000000000000000000000000000000000000f000f50000000000f030f531000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 859, 865, 879, 916, 1202, 1259, 1601]) (by decide +kernel)

noncomputable def f23036 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (23588864 + i)

theorem c23036_0 : rowSum f23036 0 1024 = 12641150 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23036) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23036 (by decide)
  decide +kernel

theorem sum23036 : rowSum f23036 0 1024 = 12641150 :=
  c23036_0

theorem h23036 : P.leaf 34 23036 = 12641150 :=
  leaf_weighted (k := 24) (d := 10) (H := 23036) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 23036) (by decide) (by decide +kernel)) sum23036

theorem h21998 : P.leaf 34 21998 = 12641150 :=
  orient4 (v := 23036) (by decide) (by decide +kernel) h23036

theorem cover27133 : P.CoversSplit 24 10 27133 0xff00ff00aa00a000000000000000000000000000000000000000000000000000ff00ff0088008000000000000000000000000000000000000000000000000000ff00ff00aa00a0000000000000000000000000000000000000000000000000003300330000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 858, 859, 865, 908, 915, 1202, 1259, 1601]) (by decide +kernel)

theorem c27133_0 : P.sumLeaves 24 27784192 1024 = 30021186 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 27133) (lo := 0) (len := 1024) (W := 30021186) check rows elimOK (by decide) (by decide) cover27133 (by decide)
  decide +kernel

theorem h27133 : P.leaf 34 27133 = 30021186 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 30021186)]) (.cons c27133_0 (.nil)) (by decide) (by decide))

theorem h21999 : P.leaf 34 21999 = 30021186 :=
  orient24 (v := 27133) (by decide) (by decide +kernel) h27133

theorem cover23023 : P.CoversSplit 24 10 23023 0xffffffffaaaaaaaaffffffffaaaaaaaaffff000000000000ffff000000000000cccccccc88888888cccccccc88888888cccc000000000000cccc000000000000ffffffffaaaaaaaa0000000000000000ffff55550000000033331111000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f23023 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (23575552 + i)

theorem c23023_0 : rowSum f23023 0 739 = 60859144 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23023) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23023 (by decide)
  decide +kernel

theorem c23023_1 : rowSum f23023 739 285 = 73608768 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23023) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23023 (by decide)
  decide +kernel

theorem sum23023 : rowSum f23023 0 1024 = 134467912 :=
  rowSum_append (F := f23023) (lo := 0) (n := 739) (m := 285) (A := 60859144) (B := 73608768) c23023_0 (c23023_1)

theorem h23023 : P.leaf 34 23023 = 134467912 :=
  leaf_weighted (k := 24) (d := 10) (H := 23023) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 23023) (by decide) (by decide +kernel)) sum23023

theorem h22013 : P.leaf 34 22013 = 134467912 :=
  orient4 (v := 23023) (by decide) (by decide +kernel) h23023

theorem cover23039 : P.CoversSplit 24 10 23039 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1202, 1259, 1601]) (by decide +kernel)

noncomputable def f23039 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (23591936 + i)

theorem c23039_0 : rowSum f23039 0 295 = 111985696 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23039) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23039 (by decide)
  decide +kernel

theorem c23039_1 : rowSum f23039 295 187 = 192459668 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23039) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23039 (by decide)
  decide +kernel

theorem c23039_2 : rowSum f23039 482 476 = 367258780 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23039) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23039 (by decide)
  decide +kernel

theorem c23039_3 : rowSum f23039 958 66 = 75893980 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23039) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23039 (by decide)
  decide +kernel

theorem sum23039 : rowSum f23039 0 1024 = 747598124 :=
  rowSum_append (F := f23039) (lo := 0) (n := 295) (m := 729) (A := 111985696) (B := 635612428) c23039_0 (rowSum_append (F := f23039) (lo := 295) (n := 187) (m := 542) (A := 192459668) (B := 443152760) c23039_1 (rowSum_append (F := f23039) (lo := 482) (n := 476) (m := 66) (A := 367258780) (B := 75893980) c23039_2 (c23039_3)))

theorem h23039 : P.leaf 34 23039 = 747598124 :=
  leaf_weighted (k := 24) (d := 10) (H := 23039) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 23039) (by decide) (by decide +kernel)) sum23039

theorem h22015 : P.leaf 34 22015 = 747598124 :=
  orient4 (v := 23039) (by decide) (by decide +kernel) h23039

def seg : List (ℕ × ℕ) := [(21932, 48), (21933, 48), (21934, 48), (21935, 48), (21948, 48), (21949, 48), (21950, 48), (21951, 48), (21996, 24), (21997, 48), (21998, 24), (21999, 48), (22013, 24), (22015, 24)]

theorem segOK : checkSeg 16 perms 21932 22199 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 21932 22199 576 33215878656 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 33215878656)
    (SegSum.cons (w := 48) h21932 (SegSum.cons (w := 48) h21933 (SegSum.cons (w := 48) h21934 (SegSum.cons (w := 48) h21935 (SegSum.cons (w := 48) h21948 (SegSum.cons (w := 48) h21949 (SegSum.cons (w := 48) h21950 (SegSum.cons (w := 48) h21951 (SegSum.cons (w := 24) h21996 (SegSum.cons (w := 48) h21997 (SegSum.cons (w := 24) h21998 (SegSum.cons (w := 48) h21999 (SegSum.cons (w := 24) h22013 (SegSum.cons (w := 24) h22015 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))) (by decide)

end RACert.S4N1.C0.S62
