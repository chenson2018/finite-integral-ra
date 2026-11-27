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

namespace RACert.S6N0.C0.S38

open RACert RACert.Problem

theorem cover32505 : P.CoversSplit 26 10 32505 0xf0f0f0f0f0f0f0c0f0f0f0f0f0f0f0c000000000000000000030003000000000000000000000000000005050000050400000000000000000000000100000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 923, 972, 979, 1265, 1273, 1322, 1665]) (by decide +kernel)

theorem c32505_0 : P.sumLeaves 26 33285120 1024 = 59119112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32505) (lo := 0) (len := 1024) (W := 59119112) check rows elimOK (by decide) (by decide) cover32505 (by decide)
  decide +kernel

theorem h32505 : P.leaf 36 32505 = 59119112 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 59119112)]) (.cons c32505_0 (.nil)) (by decide) (by decide))

theorem cover32506 : P.CoversSplit 26 10 32506 0xf0f0f0f0f0f0f0c0f0f0f0f0f0f0f0c000000000000000000030003000000000000000000000000000005050000050400000000000000000000000100000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1265, 1273, 1322, 1665]) (by decide +kernel)

theorem c32506_0 : P.sumLeaves 26 33286144 1024 = 124874332 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32506) (lo := 0) (len := 1024) (W := 124874332) check rows elimOK (by decide) (by decide) cover32506 (by decide)
  decide +kernel

theorem h32506 : P.leaf 36 32506 = 124874332 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 124874332)]) (.cons c32506_0 (.nil)) (by decide) (by decide))

theorem cover32507 : P.CoversSplit 26 10 32507 0xf0f0f0f0f0f0f0c0f0f0f0f0f0f0f0c000000000000000000030003000000000000000000000000000005050000050400000000000000000000000100000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000100000000000000000000000000000001000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1265, 1273, 1322, 1665]) (by decide +kernel)

theorem c32507_0 : P.sumLeaves 26 33287168 1024 = 260108342 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32507) (lo := 0) (len := 1024) (W := 260108342) check rows elimOK (by decide) (by decide) cover32507 (by decide)
  decide +kernel

theorem h32507 : P.leaf 36 32507 = 260108342 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 260108342)]) (.cons c32507_0 (.nil)) (by decide) (by decide))

theorem cover32510 : P.CoversSplit 26 10 32510 0xfffffffffffffac8fffffafafffffac800000000000000000030003000000000fffffafafffffac8f0f0f0f0f0f0f0c00000000000000000003000300000000000330033000000000033003200000000003300330000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c32510_0 : P.sumLeaves 26 33290240 750 = 66019384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32510) (lo := 0) (len := 750) (W := 66019384) check rows elimOK (by decide) (by decide) cover32510 (by decide)
  decide +kernel

theorem c32510_1 : P.sumLeaves 26 33290990 238 = 246695902 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32510) (lo := 750) (len := 238) (W := 246695902) check rows elimOK (by decide) (by decide) cover32510 (by decide)
  decide +kernel

theorem c32510_2 : P.sumLeaves 26 33291228 36 = 178590026 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32510) (lo := 988) (len := 36) (W := 178590026) check rows elimOK (by decide) (by decide) cover32510 (by decide)
  decide +kernel

theorem h32510 : P.leaf 36 32510 = 491305312 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(750, 66019384), (238, 246695902), (36, 178590026)]) (.cons c32510_0 (.cons c32510_1 (.cons c32510_2 (.nil)))) (by decide) (by decide))

theorem cover32511 : P.CoversSplit 26 10 32511 0xfffffffffffffac8fffffafafffffac800000000000000000030003000000000fffffafafffffac8f0f0f0f0f0f0f0c00000000000000000003000300000000000330033000000000033003200000000003300330000000000300030000000000033003200000000003000300000000000330032000000000030003000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c32511_0 : P.sumLeaves 26 33291264 724 = 107459230 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32511) (lo := 0) (len := 724) (W := 107459230) check rows elimOK (by decide) (by decide) cover32511 (by decide)
  decide +kernel

theorem c32511_1 : P.sumLeaves 26 33291988 235 = 416749748 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32511) (lo := 724) (len := 235) (W := 416749748) check rows elimOK (by decide) (by decide) cover32511 (by decide)
  decide +kernel

theorem c32511_2 : P.sumLeaves 26 33292223 65 = 443087504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32511) (lo := 959) (len := 65) (W := 443087504) check rows elimOK (by decide) (by decide) cover32511 (by decide)
  decide +kernel

theorem h32511 : P.leaf 36 32511 = 967296482 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(724, 107459230), (235, 416749748), (65, 443087504)]) (.cons c32511_0 (.cons c32511_1 (.cons c32511_2 (.nil)))) (by decide) (by decide))

theorem cover32736 : P.CoversSplit 26 10 32736 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32736_0 : P.sumLeaves 26 33521664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32736) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32736 (by decide)
  decide +kernel

theorem h32736 : P.leaf 36 32736 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32736_0 (.nil)) (by decide) (by decide))

theorem cover32737 : P.CoversSplit 26 10 32737 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32737_0 : P.sumLeaves 26 33522688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32737) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32737 (by decide)
  decide +kernel

theorem h32737 : P.leaf 36 32737 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32737_0 (.nil)) (by decide) (by decide))

theorem cover32739 : P.CoversSplit 26 10 32739 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32739_0 : P.sumLeaves 26 33524736 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32739) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32739 (by decide)
  decide +kernel

theorem h32739 : P.leaf 36 32739 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32739_0 (.nil)) (by decide) (by decide))

theorem cover32741 : P.CoversSplit 26 10 32741 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32741_0 : P.sumLeaves 26 33526784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32741) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32741 (by decide)
  decide +kernel

theorem h32741 : P.leaf 36 32741 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32741_0 (.nil)) (by decide) (by decide))

theorem cover32743 : P.CoversSplit 26 10 32743 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32743_0 : P.sumLeaves 26 33528832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32743) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32743 (by decide)
  decide +kernel

theorem h32743 : P.leaf 36 32743 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32743_0 (.nil)) (by decide) (by decide))

theorem cover32751 : P.CoversSplit 26 10 32751 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32751_0 : P.sumLeaves 26 33537024 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32751) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32751 (by decide)
  decide +kernel

theorem h32751 : P.leaf 36 32751 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32751_0 (.nil)) (by decide) (by decide))

theorem cover32752 : P.CoversSplit 26 10 32752 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00800000000000000000000fa000000fa0000000000000000000000fa000000fa080000000000000000000000000000000000000000f0c0f0c000000000f0c0f0c8000000000000000000000000000000000000000000000000000000000000fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979]) (by decide +kernel)

theorem c32752_0 : P.sumLeaves 26 33538048 924 = 1038816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32752) (lo := 0) (len := 924) (W := 1038816) check rows elimOK (by decide) (by decide) cover32752 (by decide)
  decide +kernel

theorem c32752_1 : P.sumLeaves 26 33538972 100 = 700032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32752) (lo := 924) (len := 100) (W := 700032) check rows elimOK (by decide) (by decide) cover32752 (by decide)
  decide +kernel

theorem h32752 : P.leaf 36 32752 = 1738848 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(924, 1038816), (100, 700032)]) (.cons c32752_0 (.cons c32752_1 (.nil))) (by decide) (by decide))

theorem cover32753 : P.CoversSplit 26 10 32753 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00800000000000000000000fa000000fa0000000000000000000000fa000000fa080000000000000000000000000000000000000000f0c0f0c000000000f0c0f0c8000000000000000000000000000000000000000000000000000000000000fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979]) (by decide +kernel)

theorem c32753_0 : P.sumLeaves 26 33539072 924 = 27912584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32753) (lo := 0) (len := 924) (W := 27912584) check rows elimOK (by decide) (by decide) cover32753 (by decide)
  decide +kernel

theorem c32753_1 : P.sumLeaves 26 33539996 100 = 33134188 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32753) (lo := 924) (len := 100) (W := 33134188) check rows elimOK (by decide) (by decide) cover32753 (by decide)
  decide +kernel

theorem h32753 : P.leaf 36 32753 = 61046772 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(924, 27912584), (100, 33134188)]) (.cons c32753_0 (.cons c32753_1 (.nil))) (by decide) (by decide))

theorem cover32755 : P.CoversSplit 26 10 32755 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00800000000000000000000fa000000fa0000000000000000000000fa000000fa080000000000000000000000000000000000000000f0c0f0c000000000f0c0f0c8000000000000000000000000000000000000000000000000000000000000fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979]) (by decide +kernel)

theorem c32755_0 : P.sumLeaves 26 33541120 924 = 67236456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32755) (lo := 0) (len := 924) (W := 67236456) check rows elimOK (by decide) (by decide) cover32755 (by decide)
  decide +kernel

theorem c32755_1 : P.sumLeaves 26 33542044 100 = 62222536 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32755) (lo := 924) (len := 100) (W := 62222536) check rows elimOK (by decide) (by decide) cover32755 (by decide)
  decide +kernel

theorem h32755 : P.leaf 36 32755 = 129458992 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(924, 67236456), (100, 62222536)]) (.cons c32755_0 (.cons c32755_1 (.nil))) (by decide) (by decide))

theorem cover32756 : P.CoversSplit 26 10 32756 0xff00ff00ff00fa00ff00fa00ff00fa00ff00ff00ff00fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff00fa00fa00f000fa00f00000000000000000000000000000000000000000003300320000000000320032000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 880, 972, 979, 1265, 1273, 1315, 1658]) (by decide +kernel)

theorem c32756_0 : P.sumLeaves 26 33542144 747 = 24426130 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32756) (lo := 0) (len := 747) (W := 24426130) check rows elimOK (by decide) (by decide) cover32756 (by decide)
  decide +kernel

theorem c32756_1 : P.sumLeaves 26 33542891 224 = 54459080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32756) (lo := 747) (len := 224) (W := 54459080) check rows elimOK (by decide) (by decide) cover32756 (by decide)
  decide +kernel

theorem c32756_2 : P.sumLeaves 26 33543115 53 = 36201936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32756) (lo := 971) (len := 53) (W := 36201936) check rows elimOK (by decide) (by decide) cover32756 (by decide)
  decide +kernel

theorem h32756 : P.leaf 36 32756 = 115087146 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(747, 24426130), (224, 54459080), (53, 36201936)]) (.cons c32756_0 (.cons c32756_1 (.cons c32756_2 (.nil)))) (by decide) (by decide))

theorem cover32757 : P.CoversSplit 26 10 32757 0xff00ff00ff00fa00ff00fa00ff00fa00ff00ff00ff00fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff00fa00fa00f000fa00f00000000000000000000000000000000000000000003300320000000000320032000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 929, 972, 979, 1265, 1273, 1315, 1658]) (by decide +kernel)

theorem c32757_0 : P.sumLeaves 26 33543168 747 = 87216562 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32757) (lo := 0) (len := 747) (W := 87216562) check rows elimOK (by decide) (by decide) cover32757 (by decide)
  decide +kernel

theorem c32757_1 : P.sumLeaves 26 33543915 224 = 191832624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32757) (lo := 747) (len := 224) (W := 191832624) check rows elimOK (by decide) (by decide) cover32757 (by decide)
  decide +kernel

theorem c32757_2 : P.sumLeaves 26 33544139 53 = 120909276 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32757) (lo := 971) (len := 53) (W := 120909276) check rows elimOK (by decide) (by decide) cover32757 (by decide)
  decide +kernel

theorem h32757 : P.leaf 36 32757 = 399958462 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(747, 87216562), (224, 191832624), (53, 120909276)]) (.cons c32757_0 (.cons c32757_1 (.cons c32757_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(32505, 360), (32506, 720), (32507, 720), (32510, 360), (32511, 360), (32736, 90), (32737, 360), (32739, 180), (32741, 360), (32743, 360), (32751, 90), (32752, 180), (32753, 360), (32755, 180), (32756, 360), (32757, 720)]

theorem segOK : checkSeg 20 perms 32505 32759 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 32505 32759 5760 1198560965760 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1198560965760)
    (SegSum.cons (w := 360) h32505 (SegSum.cons (w := 720) h32506 (SegSum.cons (w := 720) h32507 (SegSum.cons (w := 360) h32510 (SegSum.cons (w := 360) h32511 (SegSum.cons (w := 90) h32736 (SegSum.cons (w := 360) h32737 (SegSum.cons (w := 180) h32739 (SegSum.cons (w := 360) h32741 (SegSum.cons (w := 360) h32743 (SegSum.cons (w := 90) h32751 (SegSum.cons (w := 180) h32752 (SegSum.cons (w := 360) h32753 (SegSum.cons (w := 180) h32755 (SegSum.cons (w := 360) h32756 (SegSum.cons (w := 720) h32757 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))) (by decide)

end RACert.S6N0.C0.S38
