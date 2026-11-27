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

namespace RACert.S6N0.C0.S65

open RACert RACert.Problem

theorem cover89023 : P.CoversSplit 26 10 89023 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000fffff0f000000000fafaf0f000000000fffff0f000000030fafaf0f00000000000000000000000000000000000000000003300330000000000320032000000000000000000000000000000000000000000330030000000000032003000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89023_0 : P.sumLeaves 26 91159552 749 = 61100743 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89023) (lo := 0) (len := 749) (W := 61100743) check rows elimOK (by decide) (by decide) cover89023 (by decide)
  decide +kernel

theorem c89023_1 : P.sumLeaves 26 91160301 200 = 166379005 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89023) (lo := 749) (len := 200) (W := 166379005) check rows elimOK (by decide) (by decide) cover89023 (by decide)
  decide +kernel

theorem c89023_2 : P.sumLeaves 26 91160501 75 = 127959882 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89023) (lo := 949) (len := 75) (W := 127959882) check rows elimOK (by decide) (by decide) cover89023 (by decide)
  decide +kernel

theorem h89023 : P.leaf 36 89023 = 355439630 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(749, 61100743), (200, 166379005), (75, 127959882)]) (.cons c89023_0 (.cons c89023_1 (.cons c89023_2 (.nil)))) (by decide) (by decide))

theorem cover89029 : P.CoversSplit 26 10 89029 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89029_0 : P.sumLeaves 26 91165696 1024 = 1488936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89029) (lo := 0) (len := 1024) (W := 1488936) check rows elimOK (by decide) (by decide) cover89029 (by decide)
  decide +kernel

theorem h89029 : P.leaf 36 89029 = 1488936 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1488936)]) (.cons c89029_0 (.nil)) (by decide) (by decide))

theorem cover89030 : P.CoversSplit 26 10 89030 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000000000000000000000000000000000000000000000000000000000000000000000000000333301010000000033330100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 874, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89030_0 : P.sumLeaves 26 91166720 1024 = 1487300 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89030) (lo := 0) (len := 1024) (W := 1487300) check rows elimOK (by decide) (by decide) cover89030 (by decide)
  decide +kernel

theorem h89030 : P.leaf 36 89030 = 1487300 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1487300)]) (.cons c89030_0 (.nil)) (by decide) (by decide))

theorem cover89031 : P.CoversSplit 26 10 89031 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000000000000000000000000000000000000000000000000000000000000000000000000000333301010000000033330100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89031_0 : P.sumLeaves 26 91167744 1024 = 14280416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89031) (lo := 0) (len := 1024) (W := 14280416) check rows elimOK (by decide) (by decide) cover89031 (by decide)
  decide +kernel

theorem h89031 : P.leaf 36 89031 = 14280416 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14280416)]) (.cons c89031_0 (.nil)) (by decide) (by decide))

theorem cover89037 : P.CoversSplit 26 10 89037 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89037_0 : P.sumLeaves 26 91173888 989 = 3490600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89037) (lo := 0) (len := 989) (W := 3490600) check rows elimOK (by decide) (by decide) cover89037 (by decide)
  decide +kernel

theorem c89037_1 : P.sumLeaves 26 91174877 35 = 1059968 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89037) (lo := 989) (len := 35) (W := 1059968) check rows elimOK (by decide) (by decide) cover89037 (by decide)
  decide +kernel

theorem h89037 : P.leaf 36 89037 = 4550568 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(989, 3490600), (35, 1059968)]) (.cons c89037_0 (.cons c89037_1 (.nil))) (by decide) (by decide))

theorem cover89038 : P.CoversSplit 26 10 89038 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff000000000000fafa0000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89038_0 : P.sumLeaves 26 91174912 819 = 1637620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89038) (lo := 0) (len := 819) (W := 1637620) check rows elimOK (by decide) (by decide) cover89038 (by decide)
  decide +kernel

theorem c89038_1 : P.sumLeaves 26 91175731 193 = 3337620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89038) (lo := 819) (len := 193) (W := 3337620) check rows elimOK (by decide) (by decide) cover89038 (by decide)
  decide +kernel

theorem c89038_2 : P.sumLeaves 26 91175924 12 = 1600448 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89038) (lo := 1012) (len := 12) (W := 1600448) check rows elimOK (by decide) (by decide) cover89038 (by decide)
  decide +kernel

theorem h89038 : P.leaf 36 89038 = 6575688 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(819, 1637620), (193, 3337620), (12, 1600448)]) (.cons c89038_0 (.cons c89038_1 (.cons c89038_2 (.nil)))) (by decide) (by decide))

theorem cover89039 : P.CoversSplit 26 10 89039 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff000000000000fafa0000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89039_0 : P.sumLeaves 26 91175936 819 = 7039120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89039) (lo := 0) (len := 819) (W := 7039120) check rows elimOK (by decide) (by decide) cover89039 (by decide)
  decide +kernel

theorem c89039_1 : P.sumLeaves 26 91176755 193 = 18728768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89039) (lo := 819) (len := 193) (W := 18728768) check rows elimOK (by decide) (by decide) cover89039 (by decide)
  decide +kernel

theorem c89039_2 : P.sumLeaves 26 91176948 12 = 4301760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89039) (lo := 1012) (len := 12) (W := 4301760) check rows elimOK (by decide) (by decide) cover89039 (by decide)
  decide +kernel

theorem h89039 : P.leaf 36 89039 = 30069648 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(819, 7039120), (193, 18728768), (12, 4301760)]) (.cons c89039_0 (.cons c89039_1 (.cons c89039_2 (.nil)))) (by decide) (by decide))

theorem cover89046 : P.CoversSplit 26 10 89046 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000050005000501050100000000000000000500050005010500000000000000000000000000333301010000000033330100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 874, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89046_0 : P.sumLeaves 26 91183104 988 = 42534720 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89046) (lo := 0) (len := 988) (W := 42534720) check rows elimOK (by decide) (by decide) cover89046 (by decide)
  decide +kernel

theorem c89046_1 : P.sumLeaves 26 91184092 36 = 33431896 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89046) (lo := 988) (len := 36) (W := 33431896) check rows elimOK (by decide) (by decide) cover89046 (by decide)
  decide +kernel

theorem h89046 : P.leaf 36 89046 = 75966616 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(988, 42534720), (36, 33431896)]) (.cons c89046_0 (.cons c89046_1 (.nil))) (by decide) (by decide))

theorem cover89047 : P.CoversSplit 26 10 89047 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000050005000501050100000000000000000500050005010500000000000000000000000000333301010000000033330100000000000000000000000000000000000000000001010101000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89047_0 : P.sumLeaves 26 91184128 984 = 108493600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89047) (lo := 0) (len := 984) (W := 108493600) check rows elimOK (by decide) (by decide) cover89047 (by decide)
  decide +kernel

theorem c89047_1 : P.sumLeaves 26 91185112 40 = 61317208 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89047) (lo := 984) (len := 40) (W := 61317208) check rows elimOK (by decide) (by decide) cover89047 (by decide)
  decide +kernel

theorem h89047 : P.leaf 36 89047 = 169810808 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(984, 108493600), (40, 61317208)]) (.cons c89047_0 (.cons c89047_1 (.nil))) (by decide) (by decide))

theorem cover89052 : P.CoversSplit 26 10 89052 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c80000050505050504050400000000000000000505050505040500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89052_0 : P.sumLeaves 26 91189248 947 = 5548848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89052) (lo := 0) (len := 947) (W := 5548848) check rows elimOK (by decide) (by decide) cover89052 (by decide)
  decide +kernel

theorem c89052_1 : P.sumLeaves 26 91190195 77 = 13199912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89052) (lo := 947) (len := 77) (W := 13199912) check rows elimOK (by decide) (by decide) cover89052 (by decide)
  decide +kernel

theorem h89052 : P.leaf 36 89052 = 18748760 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(947, 5548848), (77, 13199912)]) (.cons c89052_0 (.cons c89052_1 (.nil))) (by decide) (by decide))

theorem cover89053 : P.CoversSplit 26 10 89053 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c80000050505050504050400000000000000000505050505040500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89053_0 : P.sumLeaves 26 91190272 947 = 23005622 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89053) (lo := 0) (len := 947) (W := 23005622) check rows elimOK (by decide) (by decide) cover89053 (by decide)
  decide +kernel

theorem c89053_1 : P.sumLeaves 26 91191219 77 = 31864072 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89053) (lo := 947) (len := 77) (W := 31864072) check rows elimOK (by decide) (by decide) cover89053 (by decide)
  decide +kernel

theorem h89053 : P.leaf 36 89053 = 54869694 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(947, 23005622), (77, 31864072)]) (.cons c89053_0 (.cons c89053_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(89023, 720), (89029, 360), (89030, 720), (89031, 720), (89037, 720), (89038, 720), (89039, 720), (89046, 360), (89047, 360), (89052, 720), (89053, 720)]

theorem segOK : checkSeg 20 perms 89023 89054 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 89023 89054 6840 438951516480 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 438951516480)
    (SegSum.cons (w := 720) h89023 (SegSum.cons (w := 360) h89029 (SegSum.cons (w := 720) h89030 (SegSum.cons (w := 720) h89031 (SegSum.cons (w := 720) h89037 (SegSum.cons (w := 720) h89038 (SegSum.cons (w := 720) h89039 (SegSum.cons (w := 360) h89046 (SegSum.cons (w := 360) h89047 (SegSum.cons (w := 720) h89052 (SegSum.cons (w := 720) h89053 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))) (by decide)

end RACert.S6N0.C0.S65
