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

namespace RACert.S4N1.C0.S89

open RACert RACert.Problem

theorem cover24044 : P.CoversSplit 24 10 24044 0xffffffffeae0a0a0ffffffffeae0a0a0ffff000000000000ffff000000000000ccc0ccc088808080cc00cc0088008000ccc0000040400000cc00000040000000ff00ff00ea00a0000000000000000000ff0055000000000000330011000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 858, 865, 916, 1210, 1259, 1601]) (by decide +kernel)

theorem c24044_0 : P.sumLeaves 24 24621056 830 = 8420247 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24044) (lo := 0) (len := 830) (W := 8420247) check rows elimOK (by decide) (by decide) cover24044 (by decide)
  decide +kernel

theorem c24044_1 : P.sumLeaves 24 24621886 184 = 18092424 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24044) (lo := 830) (len := 184) (W := 18092424) check rows elimOK (by decide) (by decide) cover24044 (by decide)
  decide +kernel

theorem c24044_2 : P.sumLeaves 24 24622070 10 = 8213368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24044) (lo := 1014) (len := 10) (W := 8213368) check rows elimOK (by decide) (by decide) cover24044 (by decide)
  decide +kernel

theorem h24044 : P.leaf 34 24044 = 34726039 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(830, 8420247), (184, 18092424), (10, 8213368)]) (.cons c24044_0 (.cons c24044_1 (.cons c24044_2 (.nil)))) (by decide) (by decide))

theorem cover24045 : P.CoversSplit 24 10 24045 0xffffffffeae0a0a0ffffffffeae0a0a0ffff000000000000ffff000000000000cccccccc88808080cccccccc88808080cccc000040400000cccc000040400000ff00ff00ea00a0000000000000000000ff0055000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(14, [867], [916])]) (by decide +kernel)

theorem c24045_0 : P.sumLeaves 24 24622080 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24045) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover24045 (by decide)
  decide +kernel

theorem contract24045_1 : P.leaf 30 384724 = 6272 := by
  apply (leaf_contract (k := 30) (b := 16) (H := 384724) (ss := [(11, 1, 879), (17, 0, 1259), (27, 0, 1259), (29, 0, 1259), (14, 0, 916), (12, 1, 818), (30, 1, 867), (4, 1, 565), (15, 0, 916), (18, 1, 921), (21, 1, 923), (20, 1, 929), (9, 8, 1021), (31, 1, 1210)]) (ids := [0, 1, 3, 4, 5, 6, 8, 11, 14, 17, 20, 21, 22, 23, 24, 26]) (cs := [2, 3, 1, 4, 5, 6, 7, 7, 8, 1, 1, 9, 0, 0, 10, 0, 1, 11, 1, 1, 12, 13, 14, 15, 16, 0, 17, 0, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c24045_1 : P.sumLeaves 24 24622336 64 = 6272 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384724) rows (by decide) (by decide)).symm.trans contract24045_1

theorem c24045_2 : P.sumLeaves 24 24622400 447 = 16220541 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24045) (lo := 320) (len := 447) (W := 16220541) check rows elimOK (by decide) (by decide) cover24045 (by decide)
  decide +kernel

theorem c24045_3 : P.sumLeaves 24 24622847 232 = 24111422 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24045) (lo := 767) (len := 232) (W := 24111422) check rows elimOK (by decide) (by decide) cover24045 (by decide)
  decide +kernel

theorem c24045_4 : P.sumLeaves 24 24623079 25 = 17788926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24045) (lo := 999) (len := 25) (W := 17788926) check rows elimOK (by decide) (by decide) cover24045 (by decide)
  decide +kernel

theorem h24045 : P.leaf 34 24045 = 58127161 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 6272), (447, 16220541), (232, 24111422), (25, 17788926)]) (.cons c24045_0 (.cons c24045_1 (.cons c24045_2 (.cons c24045_3 (.cons c24045_4 (.nil)))))) (by decide) (by decide))

theorem cover24046 : P.CoversSplit 24 10 24046 0xfffffffffafaaaaafffffffffafaaaaaffff000000005050ffff000000005040ccc0ccc088808880cc00cc0088008800ccc0000040404040cc00000040004000fffffffffafaaaaa0000000000000000ffff00000000505000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(17, [1259], [1251]), (18, [879], [1210, 1264])]) (by decide +kernel)

theorem c24046_0 : P.sumLeaves 24 24623104 682 = 25253703 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24046) (lo := 0) (len := 682) (W := 25253703) check rows elimOK (by decide) (by decide) cover24046 (by decide)
  decide +kernel

theorem c24046_1 : P.sumLeaves 24 24623786 257 = 33168882 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24046) (lo := 682) (len := 257) (W := 33168882) check rows elimOK (by decide) (by decide) cover24046 (by decide)
  decide +kernel

theorem c24046_2 : P.sumLeaves 24 24624043 85 = 64998984 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24046) (lo := 939) (len := 85) (W := 64998984) check rows elimOK (by decide) (by decide) cover24046 (by decide)
  decide +kernel

theorem h24046 : P.leaf 34 24046 = 123421569 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(682, 25253703), (257, 33168882), (85, 64998984)]) (.cons c24046_0 (.cons c24046_1 (.cons c24046_2 (.nil)))) (by decide) (by decide))

theorem cover24047 : P.CoversSplit 24 10 24047 0xfffffffffafaaaaafffffffffafaaaaaffff000000005050ffff000000005040cccccccc88888888cccccccc88888888cccc000040404040cccc000040404040fffffffffafaaaaa0000000000000000ffff55550000505000330011000000100000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(17, [1259], [1251])]) (by decide +kernel)

theorem c24047_0 : P.sumLeaves 24 24624128 571 = 39179926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24047) (lo := 0) (len := 571) (W := 39179926) check rows elimOK (by decide) (by decide) cover24047 (by decide)
  decide +kernel

theorem c24047_1 : P.sumLeaves 24 24624699 319 = 54084518 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24047) (lo := 571) (len := 319) (W := 54084518) check rows elimOK (by decide) (by decide) cover24047 (by decide)
  decide +kernel

theorem c24047_2 : P.sumLeaves 24 24625018 120 = 69736622 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24047) (lo := 890) (len := 120) (W := 69736622) check rows elimOK (by decide) (by decide) cover24047 (by decide)
  decide +kernel

theorem c24047_3 : P.sumLeaves 24 24625138 14 = 45373748 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24047) (lo := 1010) (len := 14) (W := 45373748) check rows elimOK (by decide) (by decide) cover24047 (by decide)
  decide +kernel

theorem h24047 : P.leaf 34 24047 = 208374814 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(571, 39179926), (319, 54084518), (120, 69736622), (14, 45373748)]) (.cons c24047_0 (.cons c24047_1 (.cons c24047_2 (.cons c24047_3 (.nil))))) (by decide) (by decide))

theorem cover24062 : P.CoversSplit 24 10 24062 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaccc0ccc088808880cc00cc0088008800ccc0ccc088808880cc00cc0088008800fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaccc0ccc088808880cc00cc0088008800ccc0ccc088808880cc00cc0088008800 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24062_0 : P.sumLeaves 24 24639488 304 = 31412624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24062) (lo := 0) (len := 304) (W := 31412624) check rows elimOK (by decide) (by decide) cover24062 (by decide)
  decide +kernel

theorem c24062_1 : P.sumLeaves 24 24639792 120 = 47547058 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24062) (lo := 304) (len := 120) (W := 47547058) check rows elimOK (by decide) (by decide) cover24062 (by decide)
  decide +kernel

theorem c24062_2 : P.sumLeaves 24 24639912 194 = 78030222 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24062) (lo := 424) (len := 194) (W := 78030222) check rows elimOK (by decide) (by decide) cover24062 (by decide)
  decide +kernel

theorem c24062_3 : P.sumLeaves 24 24640106 223 = 90230483 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24062) (lo := 618) (len := 223) (W := 90230483) check rows elimOK (by decide) (by decide) cover24062 (by decide)
  decide +kernel

theorem c24062_4 : P.sumLeaves 24 24640329 115 = 146073822 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24062) (lo := 841) (len := 115) (W := 146073822) check rows elimOK (by decide) (by decide) cover24062 (by decide)
  decide +kernel

theorem c24062_5 : P.sumLeaves 24 24640444 68 = 143220162 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24062) (lo := 956) (len := 68) (W := 143220162) check rows elimOK (by decide) (by decide) cover24062 (by decide)
  decide +kernel

theorem h24062 : P.leaf 34 24062 = 536514371 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(304, 31412624), (120, 47547058), (194, 78030222), (223, 90230483), (115, 146073822), (68, 143220162)]) (.cons c24062_0 (.cons c24062_1 (.cons c24062_2 (.cons c24062_3 (.cons c24062_4 (.cons c24062_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24044, 24), (24045, 24), (24046, 48), (24047, 48), (24062, 24)]

theorem segOK : checkSeg 16 perms 24044 24063 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24044 24063 168 31031048088 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 31031048088)
    (SegSum.cons (w := 24) h24044 (SegSum.cons (w := 24) h24045 (SegSum.cons (w := 48) h24046 (SegSum.cons (w := 48) h24047 (SegSum.cons (w := 24) h24062 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S89
