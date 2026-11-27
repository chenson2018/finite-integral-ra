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

namespace RACert.S4N1.C0.S86

open RACert RACert.Problem

theorem cover23993 : P.CoversSplit 24 10 23993 0xfffffffffaf0a0a0fffffffffaf0a0a0fffffffffaf0a0a0ffff000000000000cccccccc88808080cc00cc0088008000cccccccc88808080cc00000000000000ff00ff00fa00a000ffffff00faf0a000ff00ff00fa00a000ffff0000000000000000000000000000cccccccc8880808000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 858, 865, 916, 1202, 1210, 1251, 1259, 1308, 1601]) (ps := [(14, [867], [916])]) (by decide +kernel)

theorem c23993_0 : P.sumLeaves 24 24568832 447 = 3291244 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23993) (lo := 0) (len := 447) (W := 3291244) check rows elimOK (by decide) (by decide) cover23993 (by decide)
  decide +kernel

theorem c23993_1 : P.sumLeaves 24 24569279 383 = 9825798 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23993) (lo := 447) (len := 383) (W := 9825798) check rows elimOK (by decide) (by decide) cover23993 (by decide)
  decide +kernel

theorem c23993_2 : P.sumLeaves 24 24569662 143 = 11677912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23993) (lo := 830) (len := 143) (W := 11677912) check rows elimOK (by decide) (by decide) cover23993 (by decide)
  decide +kernel

theorem c23993_3 : P.sumLeaves 24 24569805 51 = 11536570 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23993) (lo := 973) (len := 51) (W := 11536570) check rows elimOK (by decide) (by decide) cover23993 (by decide)
  decide +kernel

theorem h23993 : P.leaf 34 23993 = 36331524 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(447, 3291244), (383, 9825798), (143, 11677912), (51, 11536570)]) (.cons c23993_0 (.cons c23993_1 (.cons c23993_2 (.cons c23993_3 (.nil))))) (by decide) (by decide))

theorem cover23994 : P.CoversSplit 24 10 23994 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000ccc0ccc088808080cc00cc0088008000ccc0ccc088808080cc00000000000000fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000ccc0ccc088808080cc00cc008800800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 865, 1202, 1210, 1251, 1259, 1308, 1601]) (by decide +kernel)

theorem c23994_0 : P.sumLeaves 24 24569856 401 = 4254876 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23994) (lo := 0) (len := 401) (W := 4254876) check rows elimOK (by decide) (by decide) cover23994 (by decide)
  decide +kernel

theorem c23994_1 : P.sumLeaves 24 24570257 182 = 8965203 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23994) (lo := 401) (len := 182) (W := 8965203) check rows elimOK (by decide) (by decide) cover23994 (by decide)
  decide +kernel

theorem c23994_2 : P.sumLeaves 24 24570439 300 = 10757918 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23994) (lo := 583) (len := 300) (W := 10757918) check rows elimOK (by decide) (by decide) cover23994 (by decide)
  decide +kernel

theorem c23994_3 : P.sumLeaves 24 24570739 128 = 21213038 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23994) (lo := 883) (len := 128) (W := 21213038) check rows elimOK (by decide) (by decide) cover23994 (by decide)
  decide +kernel

theorem c23994_4 : P.sumLeaves 24 24570867 13 = 7038688 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23994) (lo := 1011) (len := 13) (W := 7038688) check rows elimOK (by decide) (by decide) cover23994 (by decide)
  decide +kernel

theorem h23994 : P.leaf 34 23994 = 52229723 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(401, 4254876), (182, 8965203), (300, 10757918), (128, 21213038), (13, 7038688)]) (.cons c23994_0 (.cons c23994_1 (.cons c23994_2 (.cons c23994_3 (.cons c23994_4 (.nil)))))) (by decide) (by decide))

theorem cover23995 : P.CoversSplit 24 10 23995 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000cccccccc88888080cc00cc0088008000cccccccc88888080cc00000000000000fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000cccccccc88888080cc00cc008800800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 858, 865, 916, 1202, 1210, 1251, 1259, 1308, 1601]) (by decide +kernel)

theorem c23995_0 : P.sumLeaves 24 24570880 383 = 9061884 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23995) (lo := 0) (len := 383) (W := 9061884) check rows elimOK (by decide) (by decide) cover23995 (by decide)
  decide +kernel

theorem c23995_1 : P.sumLeaves 24 24571263 128 = 19578828 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23995) (lo := 383) (len := 128) (W := 19578828) check rows elimOK (by decide) (by decide) cover23995 (by decide)
  decide +kernel

theorem c23995_2 : P.sumLeaves 24 24571391 357 = 23368274 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23995) (lo := 511) (len := 357) (W := 23368274) check rows elimOK (by decide) (by decide) cover23995 (by decide)
  decide +kernel

theorem c23995_3 : P.sumLeaves 24 24571748 128 = 44372010 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23995) (lo := 868) (len := 128) (W := 44372010) check rows elimOK (by decide) (by decide) cover23995 (by decide)
  decide +kernel

theorem c23995_4 : P.sumLeaves 24 24571876 28 = 27275014 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23995) (lo := 996) (len := 28) (W := 27275014) check rows elimOK (by decide) (by decide) cover23995 (by decide)
  decide +kernel

theorem h23995 : P.leaf 34 23995 = 123656010 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(383, 9061884), (128, 19578828), (357, 23368274), (128, 44372010), (28, 27275014)]) (.cons c23995_0 (.cons c23995_1 (.cons c23995_2 (.cons c23995_3 (.cons c23995_4 (.nil)))))) (by decide) (by decide))

theorem cover23996 : P.CoversSplit 24 10 23996 0xff00ff00fa00a000ff00ff00fa00a000ff00ff00fa00a000ff00000000000000cc00cc0088008000cc00cc0088008000cc00cc0088008000cc00000000000000ff00ff00fa00a000ff00ff00fa00a000ff00ff00fa00a000ff000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 858, 916, 1210, 1251, 1308, 1601]) (by decide +kernel)

theorem c23996_0 : P.sumLeaves 24 24571904 667 = 12735442 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23996) (lo := 0) (len := 667) (W := 12735442) check rows elimOK (by decide) (by decide) cover23996 (by decide)
  decide +kernel

theorem c23996_1 : P.sumLeaves 24 24572571 352 = 37930312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23996) (lo := 667) (len := 352) (W := 37930312) check rows elimOK (by decide) (by decide) cover23996 (by decide)
  decide +kernel

theorem c23996_2 : P.sumLeaves 24 24572923 5 = 5763156 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23996) (lo := 1019) (len := 5) (W := 5763156) check rows elimOK (by decide) (by decide) cover23996 (by decide)
  decide +kernel

theorem h23996 : P.leaf 34 23996 = 56428910 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(667, 12735442), (352, 37930312), (5, 5763156)]) (.cons c23996_0 (.cons c23996_1 (.cons c23996_2 (.nil)))) (by decide) (by decide))

theorem cover23997 : P.CoversSplit 24 10 23997 0xfffffffffaf0a0a0fffffffffaf0a0a0fffffffffaf0a0a0ffff000000000000cccccccc88808080cccccccc88808080cccccccc88808080cccc000000000000ff00ff00fa00a000ff33ff33fa30a020ff00ff00fa00a000ff330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 858, 865, 916, 1202, 1210, 1251, 1259, 1308, 1601]) (by decide +kernel)

theorem c23997_0 : P.sumLeaves 24 24572928 563 = 23615141 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23997) (lo := 0) (len := 563) (W := 23615141) check rows elimOK (by decide) (by decide) cover23997 (by decide)
  decide +kernel

theorem c23997_1 : P.sumLeaves 24 24573491 297 = 24398604 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23997) (lo := 563) (len := 297) (W := 24398604) check rows elimOK (by decide) (by decide) cover23997 (by decide)
  decide +kernel

theorem c23997_2 : P.sumLeaves 24 24573788 132 = 47767259 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23997) (lo := 860) (len := 132) (W := 47767259) check rows elimOK (by decide) (by decide) cover23997 (by decide)
  decide +kernel

theorem c23997_3 : P.sumLeaves 24 24573920 32 = 34114292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23997) (lo := 992) (len := 32) (W := 34114292) check rows elimOK (by decide) (by decide) cover23997 (by decide)
  decide +kernel

theorem h23997 : P.leaf 34 23997 = 129895296 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(563, 23615141), (297, 24398604), (132, 47767259), (32, 34114292)]) (.cons c23997_0 (.cons c23997_1 (.cons c23997_2 (.cons c23997_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(23993, 24), (23994, 48), (23995, 48), (23996, 48), (23997, 48)]

theorem segOK : checkSeg 16 perms 23993 23998 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 23993 23998 216 18258033648 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 18258033648)
    (SegSum.cons (w := 24) h23993 (SegSum.cons (w := 48) h23994 (SegSum.cons (w := 48) h23995 (SegSum.cons (w := 48) h23996 (SegSum.cons (w := 48) h23997 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S86
