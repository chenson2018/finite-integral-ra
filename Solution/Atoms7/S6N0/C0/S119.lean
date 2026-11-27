/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S119

open RACert RACert.Problem

theorem cover241663 : P.CoversSplit 26 10 241663 0xffffffffffffffffffffffffffffaaaaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffffffffffaaaaffffffffffccffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffccffccffffaaaaffccaa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c241663_0 : P.sumLeaves 26 247462912 126 = 406922450 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241663) (lo := 0) (len := 126) (W := 406922450) check rows elimOK (by decide) (by decide) cover241663 (by decide)
  decide +kernel

theorem c241663_1 : P.sumLeaves 26 247463038 112 = 565111903 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241663) (lo := 126) (len := 112) (W := 565111903) check rows elimOK (by decide) (by decide) cover241663 (by decide)
  decide +kernel

theorem c241663_2 : P.sumLeaves 26 247463150 126 = 752287819 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241663) (lo := 238) (len := 126) (W := 752287819) check rows elimOK (by decide) (by decide) cover241663 (by decide)
  decide +kernel

theorem c241663_3 : P.sumLeaves 26 247463276 104 = 1097695281 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241663) (lo := 364) (len := 104) (W := 1097695281) check rows elimOK (by decide) (by decide) cover241663 (by decide)
  decide +kernel

theorem c241663_4 : P.sumLeaves 26 247463380 122 = 1169958291 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241663) (lo := 468) (len := 122) (W := 1169958291) check rows elimOK (by decide) (by decide) cover241663 (by decide)
  decide +kernel

theorem c241663_5 : P.sumLeaves 26 247463502 112 = 981957514 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241663) (lo := 590) (len := 112) (W := 981957514) check rows elimOK (by decide) (by decide) cover241663 (by decide)
  decide +kernel

theorem c241663_6 : P.sumLeaves 26 247463614 118 = 1199340111 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241663) (lo := 702) (len := 118) (W := 1199340111) check rows elimOK (by decide) (by decide) cover241663 (by decide)
  decide +kernel

theorem c241663_7 : P.sumLeaves 26 247463732 108 = 1254853469 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241663) (lo := 820) (len := 108) (W := 1254853469) check rows elimOK (by decide) (by decide) cover241663 (by decide)
  decide +kernel

theorem c241663_8 : P.sumLeaves 26 247463840 96 = 1679807550 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241663) (lo := 928) (len := 96) (W := 1679807550) check rows elimOK (by decide) (by decide) cover241663 (by decide)
  decide +kernel

theorem h241663 : P.leaf 36 241663 = 9107934388 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(126, 406922450), (112, 565111903), (126, 752287819), (104, 1097695281), (122, 1169958291), (112, 981957514), (118, 1199340111), (108, 1254853469), (96, 1679807550)]) (.cons c241663_0 (.cons c241663_1 (.cons c241663_2 (.cons c241663_3 (.cons c241663_4 (.cons c241663_5 (.cons c241663_6 (.cons c241663_7 (.cons c241663_8 (.nil)))))))))) (by decide) (by decide))

theorem cover242467 : P.CoversSplit 26 10 242467 0xfffffffffffffffffffffafafffff0f0ffffffffffccccccffffaaaaff008000fffffafafffffafafafaa0a0fafaa0a0fffffafaffccc8c8fafaa0a0fa008000ffffffffffccffccfffffafaffccf0c0ffccffcccc00cc00ffccaa88cc0080000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 873, 930, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c242467_0 : P.sumLeaves 26 248286208 443 = 29995274 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242467) (lo := 0) (len := 443) (W := 29995274) check rows elimOK (by decide) (by decide) cover242467 (by decide)
  decide +kernel

theorem c242467_1 : P.sumLeaves 26 248286651 159 = 51481932 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242467) (lo := 443) (len := 159) (W := 51481932) check rows elimOK (by decide) (by decide) cover242467 (by decide)
  decide +kernel

theorem c242467_2 : P.sumLeaves 26 248286810 138 = 41658716 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242467) (lo := 602) (len := 138) (W := 41658716) check rows elimOK (by decide) (by decide) cover242467 (by decide)
  decide +kernel

theorem c242467_3 : P.sumLeaves 26 248286948 141 = 47516810 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242467) (lo := 740) (len := 141) (W := 47516810) check rows elimOK (by decide) (by decide) cover242467 (by decide)
  decide +kernel

theorem c242467_4 : P.sumLeaves 26 248287089 108 = 46409932 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242467) (lo := 881) (len := 108) (W := 46409932) check rows elimOK (by decide) (by decide) cover242467 (by decide)
  decide +kernel

theorem c242467_5 : P.sumLeaves 26 248287197 35 = 37281792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242467) (lo := 989) (len := 35) (W := 37281792) check rows elimOK (by decide) (by decide) cover242467 (by decide)
  decide +kernel

theorem h242467 : P.leaf 36 242467 = 254344456 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(443, 29995274), (159, 51481932), (138, 41658716), (141, 47516810), (108, 46409932), (35, 37281792)]) (.cons c242467_0 (.cons c242467_1 (.cons c242467_2 (.cons c242467_3 (.cons c242467_4 (.cons c242467_5 (.nil))))))) (by decide) (by decide))

theorem cover242471 : P.CoversSplit 26 10 242471 0xfffffffffffffffffffffffffffff0f0ffffffffffffccccffffaaaaff008000fffffafafffffafafafaa0a0fafaa0a0fffffafaffffc8c8fafaa0a0fa008000ffffffffffccffccffffffffffccf0c0ffccffcccc00cc00ffccaa88cc0080000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 873, 930, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c242471_0 : P.sumLeaves 26 248290304 439 = 47782619 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242471) (lo := 0) (len := 439) (W := 47782619) check rows elimOK (by decide) (by decide) cover242471 (by decide)
  decide +kernel

theorem c242471_1 : P.sumLeaves 26 248290743 155 = 83606344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242471) (lo := 439) (len := 155) (W := 83606344) check rows elimOK (by decide) (by decide) cover242471 (by decide)
  decide +kernel

theorem c242471_2 : P.sumLeaves 26 248290898 136 = 50678926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242471) (lo := 594) (len := 136) (W := 50678926) check rows elimOK (by decide) (by decide) cover242471 (by decide)
  decide +kernel

theorem c242471_3 : P.sumLeaves 26 248291034 139 = 74471488 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242471) (lo := 730) (len := 139) (W := 74471488) check rows elimOK (by decide) (by decide) cover242471 (by decide)
  decide +kernel

theorem c242471_4 : P.sumLeaves 26 248291173 104 = 65870897 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242471) (lo := 869) (len := 104) (W := 65870897) check rows elimOK (by decide) (by decide) cover242471 (by decide)
  decide +kernel

theorem c242471_5 : P.sumLeaves 26 248291277 51 = 74196088 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242471) (lo := 973) (len := 51) (W := 74196088) check rows elimOK (by decide) (by decide) cover242471 (by decide)
  decide +kernel

theorem h242471 : P.leaf 36 242471 = 396606362 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(439, 47782619), (155, 83606344), (136, 50678926), (139, 74471488), (104, 65870897), (51, 74196088)]) (.cons c242471_0 (.cons c242471_1 (.cons c242471_2 (.cons c242471_3 (.cons c242471_4 (.cons c242471_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(241663, 90), (242467, 12), (242471, 120)]

theorem segOK : checkSeg 20 perms 241663 242479 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 241663 242479 222 870358991832 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 870358991832)
    (SegSum.cons (w := 90) h241663 (SegSum.cons (w := 12) h242467 (SegSum.cons (w := 120) h242471 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S119
