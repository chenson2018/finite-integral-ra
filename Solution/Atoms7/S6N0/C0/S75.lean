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

namespace RACert.S6N0.C0.S75

open RACert RACert.Problem

theorem cover97022 : P.CoversSplit 26 10 97022 0xfffffffffffffafafffffffafffffafa00000000000000000000000000300000fffffafafffffafaf0f0f0f0f0f0f0f00000000000000000000000000030000000000000003300320000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97022_0 : P.sumLeaves 26 99350528 760 = 52592300 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97022) (lo := 0) (len := 760) (W := 52592300) check rows elimOK (by decide) (by decide) cover97022 (by decide)
  decide +kernel

theorem c97022_1 : P.sumLeaves 26 99351288 232 = 164065490 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97022) (lo := 760) (len := 232) (W := 164065490) check rows elimOK (by decide) (by decide) cover97022 (by decide)
  decide +kernel

theorem c97022_2 : P.sumLeaves 26 99351520 32 = 107758508 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97022) (lo := 992) (len := 32) (W := 107758508) check rows elimOK (by decide) (by decide) cover97022 (by decide)
  decide +kernel

theorem h97022 : P.leaf 36 97022 = 324416298 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(760, 52592300), (232, 164065490), (32, 107758508)]) (.cons c97022_0 (.cons c97022_1 (.cons c97022_2 (.nil)))) (by decide) (by decide))

theorem cover97023 : P.CoversSplit 26 10 97023 0xfffffffffffffafafffffffafffffafa00000000000000000000000000300000fffffafafffffafaf0f0f0f0f0f0f0f00000000000000000000000000030000000000000003300320000000000330032000000000000000000000000000000000000000000330032000000000030003000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97023_0 : P.sumLeaves 26 99351552 749 = 93859655 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97023) (lo := 0) (len := 749) (W := 93859655) check rows elimOK (by decide) (by decide) cover97023 (by decide)
  decide +kernel

theorem c97023_1 : P.sumLeaves 26 99352301 232 = 306549872 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97023) (lo := 749) (len := 232) (W := 306549872) check rows elimOK (by decide) (by decide) cover97023 (by decide)
  decide +kernel

theorem c97023_2 : P.sumLeaves 26 99352533 43 = 205520112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97023) (lo := 981) (len := 43) (W := 205520112) check rows elimOK (by decide) (by decide) cover97023 (by decide)
  decide +kernel

theorem h97023 : P.leaf 36 97023 = 605929639 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(749, 93859655), (232, 306549872), (43, 205520112)]) (.cons c97023_0 (.cons c97023_1 (.cons c97023_2 (.nil)))) (by decide) (by decide))

theorem cover97091 : P.CoversSplit 26 10 97091 0xa0000000a00000000000000000000000a0000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 523, 530, 579, 608, 972, 979, 1266, 1273]) (by decide +kernel)

theorem c97091_0 : P.sumLeaves 26 99421184 1024 = 1145320 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97091) (lo := 0) (len := 1024) (W := 1145320) check rows elimOK (by decide) (by decide) cover97091 (by decide)
  decide +kernel

theorem h97091 : P.leaf 36 97091 = 1145320 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1145320)]) (.cons c97091_0 (.nil)) (by decide) (by decide))

theorem cover97095 : P.CoversSplit 26 10 97095 0xaa000000aa0000000000000000000000aa000000aa0200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 523, 972, 979, 1266, 1273, 1315, 1658]) (by decide +kernel)

theorem c97095_0 : P.sumLeaves 26 99425280 1024 = 5899608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97095) (lo := 0) (len := 1024) (W := 5899608) check rows elimOK (by decide) (by decide) cover97095 (by decide)
  decide +kernel

theorem h97095 : P.leaf 36 97095 = 5899608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5899608)]) (.cons c97095_0 (.nil)) (by decide) (by decide))

theorem cover97099 : P.CoversSplit 26 10 97099 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 523, 530, 579, 972, 979, 1273]) (by decide +kernel)

theorem c97099_0 : P.sumLeaves 26 99429376 1024 = 4562654 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97099) (lo := 0) (len := 1024) (W := 4562654) check rows elimOK (by decide) (by decide) cover97099 (by decide)
  decide +kernel

theorem h97099 : P.leaf 36 97099 = 4562654 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4562654)]) (.cons c97099_0 (.nil)) (by decide) (by decide))

theorem cover97103 : P.CoversSplit 26 10 97103 0xaaaa0000aaaa00000000000000000000aaaa0000aaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [523, 979, 1266, 1273, 1315, 1658]) (by decide +kernel)

theorem c97103_0 : P.sumLeaves 26 99433472 1024 = 12893924 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97103) (lo := 0) (len := 1024) (W := 12893924) check rows elimOK (by decide) (by decide) cover97103 (by decide)
  decide +kernel

theorem h97103 : P.leaf 36 97103 = 12893924 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 12893924)]) (.cons c97103_0 (.nil)) (by decide) (by decide))

theorem cover97107 : P.CoversSplit 26 10 97107 0xa0000000a00000000000000000000000a0000000a00000000000000000000000000000000000000000000500000005000000000000000000000005000000050000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000400 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 579, 608, 972, 979, 1273, 1315]) (by decide +kernel)

theorem c97107_0 : P.sumLeaves 26 99437568 1024 = 15243180 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97107) (lo := 0) (len := 1024) (W := 15243180) check rows elimOK (by decide) (by decide) cover97107 (by decide)
  decide +kernel

theorem h97107 : P.leaf 36 97107 = 15243180 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15243180)]) (.cons c97107_0 (.nil)) (by decide) (by decide))

theorem cover97108 : P.CoversSplit 26 10 97108 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500050005000500050005000000050000000500050005010500050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97108_0 : P.sumLeaves 26 99438592 1024 = 2939080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97108) (lo := 0) (len := 1024) (W := 2939080) check rows elimOK (by decide) (by decide) cover97108 (by decide)
  decide +kernel

theorem h97108 : P.leaf 36 97108 = 2939080 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2939080)]) (.cons c97108_0 (.nil)) (by decide) (by decide))

theorem cover97109 : P.CoversSplit 26 10 97109 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500050005000500050005000000050000000500050005010500050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 923, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97109_0 : P.sumLeaves 26 99439616 1024 = 58315676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97109) (lo := 0) (len := 1024) (W := 58315676) check rows elimOK (by decide) (by decide) cover97109 (by decide)
  decide +kernel

theorem h97109 : P.leaf 36 97109 = 58315676 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 58315676)]) (.cons c97109_0 (.nil)) (by decide) (by decide))

theorem cover97111 : P.CoversSplit 26 10 97111 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500050005000500050005000000050000000500050005010500050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97111_0 : P.sumLeaves 26 99441664 1024 = 137459282 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97111) (lo := 0) (len := 1024) (W := 137459282) check rows elimOK (by decide) (by decide) cover97111 (by decide)
  decide +kernel

theorem h97111 : P.leaf 36 97111 = 137459282 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 137459282)]) (.cons c97111_0 (.nil)) (by decide) (by decide))

theorem cover97113 : P.CoversSplit 26 10 97113 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000500a0a00000a0a000000000000000000000a0a000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 923, 972, 979, 1273]) (by decide +kernel)

theorem c97113_0 : P.sumLeaves 26 99443712 1024 = 29026773 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97113) (lo := 0) (len := 1024) (W := 29026773) check rows elimOK (by decide) (by decide) cover97113 (by decide)
  decide +kernel

theorem h97113 : P.leaf 36 97113 = 29026773 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 29026773)]) (.cons c97113_0 (.nil)) (by decide) (by decide))

theorem cover97115 : P.CoversSplit 26 10 97115 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000500a0a00000a0a000000000000000000000a0a000008000000000000000000000000000000000000000000005050000050500000000000000000000050500000400 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 972, 979, 1273]) (by decide +kernel)

theorem c97115_0 : P.sumLeaves 26 99445760 1024 = 80116446 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97115) (lo := 0) (len := 1024) (W := 80116446) check rows elimOK (by decide) (by decide) cover97115 (by decide)
  decide +kernel

theorem h97115 : P.leaf 36 97115 = 80116446 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 80116446)]) (.cons c97115_0 (.nil)) (by decide) (by decide))

theorem cover97116 : P.CoversSplit 26 10 97116 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000505050505050505050500000505000005050505050405000505000005000000ffff0000ffff05050000000000000000ffff0000cc00040005050000040004000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97116_0 : P.sumLeaves 26 99446784 728 = 15623316 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97116) (lo := 0) (len := 728) (W := 15623316) check rows elimOK (by decide) (by decide) cover97116 (by decide)
  decide +kernel

theorem c97116_1 : P.sumLeaves 26 99447512 296 = 74199196 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97116) (lo := 728) (len := 296) (W := 74199196) check rows elimOK (by decide) (by decide) cover97116 (by decide)
  decide +kernel

theorem h97116 : P.leaf 36 97116 = 89822512 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(728, 15623316), (296, 74199196)]) (.cons c97116_0 (.cons c97116_1 (.nil))) (by decide) (by decide))

theorem cover97117 : P.CoversSplit 26 10 97117 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000505050505050505050500000505000005050505050405000505000005000000ffff0000ffff05050000000000000000ffff0000cc00040005050000040004000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 923, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97117_0 : P.sumLeaves 26 99447808 728 = 33657406 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97117) (lo := 0) (len := 728) (W := 33657406) check rows elimOK (by decide) (by decide) cover97117 (by decide)
  decide +kernel

theorem c97117_1 : P.sumLeaves 26 99448536 296 = 166955096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97117) (lo := 728) (len := 296) (W := 166955096) check rows elimOK (by decide) (by decide) cover97117 (by decide)
  decide +kernel

theorem h97117 : P.leaf 36 97117 = 200612502 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(728, 33657406), (296, 166955096)]) (.cons c97117_0 (.cons c97117_1 (.nil))) (by decide) (by decide))

theorem cover97119 : P.CoversSplit 26 10 97119 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000505050505050505050500000505000005050505050405000505000005000000ffff0000ffff05050000000000000000ffff0000cc00040005050000040004000505050505050505050500000505000005050505040004000505000004000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97119_0 : P.sumLeaves 26 99449856 506 = 52100134 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97119) (lo := 0) (len := 506) (W := 52100134) check rows elimOK (by decide) (by decide) cover97119 (by decide)
  decide +kernel

theorem c97119_1 : P.sumLeaves 26 99450362 473 = 199442608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97119) (lo := 506) (len := 473) (W := 199442608) check rows elimOK (by decide) (by decide) cover97119 (by decide)
  decide +kernel

theorem c97119_2 : P.sumLeaves 26 99450835 45 = 212477733 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97119) (lo := 979) (len := 45) (W := 212477733) check rows elimOK (by decide) (by decide) cover97119 (by decide)
  decide +kernel

theorem h97119 : P.leaf 36 97119 = 464020475 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(506, 52100134), (473, 199442608), (45, 212477733)]) (.cons c97119_0 (.cons c97119_1 (.cons c97119_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(97022, 720), (97023, 720), (97091, 180), (97095, 360), (97099, 180), (97103, 360), (97107, 360), (97108, 180), (97109, 720), (97111, 360), (97113, 360), (97115, 360), (97116, 360), (97117, 720), (97119, 360)]

theorem segOK : checkSeg 20 perms 97022 97122 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 97022 97122 6300 1158247424520 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1158247424520)
    (SegSum.cons (w := 720) h97022 (SegSum.cons (w := 720) h97023 (SegSum.cons (w := 180) h97091 (SegSum.cons (w := 360) h97095 (SegSum.cons (w := 180) h97099 (SegSum.cons (w := 360) h97103 (SegSum.cons (w := 360) h97107 (SegSum.cons (w := 180) h97108 (SegSum.cons (w := 720) h97109 (SegSum.cons (w := 360) h97111 (SegSum.cons (w := 360) h97113 (SegSum.cons (w := 360) h97115 (SegSum.cons (w := 360) h97116 (SegSum.cons (w := 720) h97117 (SegSum.cons (w := 360) h97119 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))) (by decide)

end RACert.S6N0.C0.S75
