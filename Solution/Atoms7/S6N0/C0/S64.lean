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

namespace RACert.S6N0.C0.S64

open RACert RACert.Problem

theorem cover88991 : P.CoversSplit 26 10 88991 0xffff000000000000ffff000000000000ffff00000000000cfafa0000000000080f0f0f0f000000000a0a0a0a000000000f0f0f0f0000000c0a0a0a0a000000080000000000000000000000000000000000ff000000cc000c00fa000000c8000800000000000000000000000000000000000f000f000c000c000a000a00080008 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 922, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c88991_0 : P.sumLeaves 26 91126784 820 = 8958674 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88991) (lo := 0) (len := 820) (W := 8958674) check rows elimOK (by decide) (by decide) cover88991 (by decide)
  decide +kernel

theorem c88991_1 : P.sumLeaves 26 91127604 204 = 56169715 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88991) (lo := 820) (len := 204) (W := 56169715) check rows elimOK (by decide) (by decide) cover88991 (by decide)
  decide +kernel

theorem h88991 : P.leaf 36 88991 = 65128389 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(820, 8958674), (204, 56169715)]) (.cons c88991_0 (.cons c88991_1 (.nil))) (by decide) (by decide))

theorem cover88999 : P.CoversSplit 26 10 88999 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 922, 972, 979, 1272, 1315, 1322, 1658]) (by decide +kernel)

theorem c88999_0 : P.sumLeaves 26 91134976 1024 = 7550600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88999) (lo := 0) (len := 1024) (W := 7550600) check rows elimOK (by decide) (by decide) cover88999 (by decide)
  decide +kernel

theorem h88999 : P.leaf 36 88999 = 7550600 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7550600)]) (.cons c88999_0 (.nil)) (by decide) (by decide))

theorem cover89001 : P.CoversSplit 26 10 89001 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [480, 536, 923, 972, 1272]) (by decide +kernel)

theorem c89001_0 : P.sumLeaves 26 91137024 1024 = 2684026 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89001) (lo := 0) (len := 1024) (W := 2684026) check rows elimOK (by decide) (by decide) cover89001 (by decide)
  decide +kernel

theorem h89001 : P.leaf 36 89001 = 2684026 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2684026)]) (.cons c89001_0 (.nil)) (by decide) (by decide))

theorem cover89003 : P.CoversSplit 26 10 89003 0xf0f0f0f000000000f0f0f0f500000000f0f0f0f000000030f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 922, 972, 979, 1272, 1273, 1322, 1658, 1665]) (by decide +kernel)

theorem c89003_0 : P.sumLeaves 26 91139072 1024 = 7321098 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89003) (lo := 0) (len := 1024) (W := 7321098) check rows elimOK (by decide) (by decide) cover89003 (by decide)
  decide +kernel

theorem h89003 : P.leaf 36 89003 = 7321098 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7321098)]) (.cons c89003_0 (.nil)) (by decide) (by decide))

theorem cover89005 : P.CoversSplit 26 10 89005 0xffffffff00000000fffffffa00000000ffffffff00000000fafafafa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [536, 922, 923, 972, 1272, 1658]) (by decide +kernel)

theorem c89005_0 : P.sumLeaves 26 91141120 1002 = 4344446 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89005) (lo := 0) (len := 1002) (W := 4344446) check rows elimOK (by decide) (by decide) cover89005 (by decide)
  decide +kernel

theorem c89005_1 : P.sumLeaves 26 91142122 22 = 1793240 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89005) (lo := 1002) (len := 22) (W := 1793240) check rows elimOK (by decide) (by decide) cover89005 (by decide)
  decide +kernel

theorem h89005 : P.leaf 36 89005 = 6137686 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1002, 4344446), (22, 1793240)]) (.cons c89005_0 (.cons c89005_1 (.nil))) (by decide) (by decide))

theorem cover89007 : P.CoversSplit 26 10 89007 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300330000000000320032000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 922, 972, 979, 1272, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89007_0 : P.sumLeaves 26 91143168 954 = 19220620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89007) (lo := 0) (len := 954) (W := 19220620) check rows elimOK (by decide) (by decide) cover89007 (by decide)
  decide +kernel

theorem c89007_1 : P.sumLeaves 26 91144122 70 = 15558120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89007) (lo := 954) (len := 70) (W := 15558120) check rows elimOK (by decide) (by decide) cover89007 (by decide)
  decide +kernel

theorem h89007 : P.leaf 36 89007 = 34778740 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(954, 19220620), (70, 15558120)]) (.cons c89007_0 (.cons c89007_1 (.nil))) (by decide) (by decide))

theorem cover89012 : P.CoversSplit 26 10 89012 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000cc00c00000000000c000c00000000000cc00c00000000000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 874, 922, 923, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89012_0 : P.sumLeaves 26 91148288 1024 = 291776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89012) (lo := 0) (len := 1024) (W := 291776) check rows elimOK (by decide) (by decide) cover89012 (by decide)
  decide +kernel

theorem h89012 : P.leaf 36 89012 = 291776 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 291776)]) (.cons c89012_0 (.nil)) (by decide) (by decide))

theorem cover89013 : P.CoversSplit 26 10 89013 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000cc00c00000000000c000c00000000000cc00c00000000000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 922, 923, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89013_0 : P.sumLeaves 26 91149312 1024 = 2462500 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89013) (lo := 0) (len := 1024) (W := 2462500) check rows elimOK (by decide) (by decide) cover89013 (by decide)
  decide +kernel

theorem h89013 : P.leaf 36 89013 = 2462500 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2462500)]) (.cons c89013_0 (.nil)) (by decide) (by decide))

theorem cover89014 : P.CoversSplit 26 10 89014 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000cc00c00000000000c800c00000000000cc00c00000000000c800c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 874, 922, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c89014_0 : P.sumLeaves 26 91150336 1024 = 11263224 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89014) (lo := 0) (len := 1024) (W := 11263224) check rows elimOK (by decide) (by decide) cover89014 (by decide)
  decide +kernel

theorem h89014 : P.leaf 36 89014 = 11263224 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11263224)]) (.cons c89014_0 (.nil)) (by decide) (by decide))

theorem cover89015 : P.CoversSplit 26 10 89015 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000cc00c00000000000c800c00000000000cc00c00000000000c800c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 922, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89015_0 : P.sumLeaves 26 91151360 1024 = 68153292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89015) (lo := 0) (len := 1024) (W := 68153292) check rows elimOK (by decide) (by decide) cover89015 (by decide)
  decide +kernel

theorem h89015 : P.leaf 36 89015 = 68153292 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 68153292)]) (.cons c89015_0 (.nil)) (by decide) (by decide))

theorem cover89018 : P.CoversSplit 26 10 89018 0xf0f0f0f000000000f0f0f0f500000000f0f0f0f000000030f0f0f0f000000000000000000000000000005050000000000000000000000000000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 874, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c89018_0 : P.sumLeaves 26 91154432 1024 = 4638636 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89018) (lo := 0) (len := 1024) (W := 4638636) check rows elimOK (by decide) (by decide) cover89018 (by decide)
  decide +kernel

theorem h89018 : P.leaf 36 89018 = 4638636 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4638636)]) (.cons c89018_0 (.nil)) (by decide) (by decide))

theorem cover89019 : P.CoversSplit 26 10 89019 0xf0f0f0f000000000f0f0f0f500000000f0f0f0f000000030f0f0f0f000000000000000000000000000005050000000000000000000000000000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000001000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 922, 972, 979, 1273, 1322, 1658, 1665]) (by decide +kernel)

theorem c89019_0 : P.sumLeaves 26 91155456 1024 = 55588634 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89019) (lo := 0) (len := 1024) (W := 55588634) check rows elimOK (by decide) (by decide) cover89019 (by decide)
  decide +kernel

theorem h89019 : P.leaf 36 89019 = 55588634 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 55588634)]) (.cons c89019_0 (.nil)) (by decide) (by decide))

theorem cover89020 : P.CoversSplit 26 10 89020 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000fffff0f000000000f0f0f0f000000000fffff0f000000030f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 874, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89020_0 : P.sumLeaves 26 91156480 820 = 770708 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89020) (lo := 0) (len := 820) (W := 770708) check rows elimOK (by decide) (by decide) cover89020 (by decide)
  decide +kernel

theorem c89020_1 : P.sumLeaves 26 91157300 194 = 2710824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89020) (lo := 820) (len := 194) (W := 2710824) check rows elimOK (by decide) (by decide) cover89020 (by decide)
  decide +kernel

theorem c89020_2 : P.sumLeaves 26 91157494 10 = 844800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89020) (lo := 1014) (len := 10) (W := 844800) check rows elimOK (by decide) (by decide) cover89020 (by decide)
  decide +kernel

theorem h89020 : P.leaf 36 89020 = 4326332 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(820, 770708), (194, 2710824), (10, 844800)]) (.cons c89020_0 (.cons c89020_1 (.cons c89020_2 (.nil)))) (by decide) (by decide))

theorem cover89021 : P.CoversSplit 26 10 89021 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000fffff0f000000000f0f0f0f000000000fffff0f000000030f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89021_0 : P.sumLeaves 26 91157504 820 = 4148714 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89021) (lo := 0) (len := 820) (W := 4148714) check rows elimOK (by decide) (by decide) cover89021 (by decide)
  decide +kernel

theorem c89021_1 : P.sumLeaves 26 91158324 194 = 15392240 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89021) (lo := 820) (len := 194) (W := 15392240) check rows elimOK (by decide) (by decide) cover89021 (by decide)
  decide +kernel

theorem c89021_2 : P.sumLeaves 26 91158518 10 = 2622240 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89021) (lo := 1014) (len := 10) (W := 2622240) check rows elimOK (by decide) (by decide) cover89021 (by decide)
  decide +kernel

theorem h89021 : P.leaf 36 89021 = 22163194 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(820, 4148714), (194, 15392240), (10, 2622240)]) (.cons c89021_0 (.cons c89021_1 (.cons c89021_2 (.nil)))) (by decide) (by decide))

theorem cover89022 : P.CoversSplit 26 10 89022 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000fffff0f000000000fafaf0f000000000fffff0f000000030fafaf0f00000000000000000000000000000000000000000003300330000000000320032000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 874, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89022_0 : P.sumLeaves 26 91158528 760 = 17700151 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89022) (lo := 0) (len := 760) (W := 17700151) check rows elimOK (by decide) (by decide) cover89022 (by decide)
  decide +kernel

theorem c89022_1 : P.sumLeaves 26 91159288 232 = 33380865 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89022) (lo := 760) (len := 232) (W := 33380865) check rows elimOK (by decide) (by decide) cover89022 (by decide)
  decide +kernel

theorem c89022_2 : P.sumLeaves 26 91159520 32 = 27183908 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89022) (lo := 992) (len := 32) (W := 27183908) check rows elimOK (by decide) (by decide) cover89022 (by decide)
  decide +kernel

theorem h89022 : P.leaf 36 89022 = 78264924 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(760, 17700151), (232, 33380865), (32, 27183908)]) (.cons c89022_0 (.cons c89022_1 (.cons c89022_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(88991, 720), (88999, 720), (89001, 360), (89003, 720), (89005, 720), (89007, 720), (89012, 360), (89013, 720), (89014, 720), (89015, 720), (89018, 360), (89019, 360), (89020, 720), (89021, 720), (89022, 720)]

theorem segOK : checkSeg 20 perms 88991 89023 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 88991 89023 9360 244189090800 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 244189090800)
    (SegSum.cons (w := 720) h88991 (SegSum.cons (w := 720) h88999 (SegSum.cons (w := 360) h89001 (SegSum.cons (w := 720) h89003 (SegSum.cons (w := 720) h89005 (SegSum.cons (w := 720) h89007 (SegSum.cons (w := 360) h89012 (SegSum.cons (w := 720) h89013 (SegSum.cons (w := 720) h89014 (SegSum.cons (w := 720) h89015 (SegSum.cons (w := 360) h89018 (SegSum.cons (w := 360) h89019 (SegSum.cons (w := 720) h89020 (SegSum.cons (w := 720) h89021 (SegSum.cons (w := 720) h89022 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))) (by decide)

end RACert.S6N0.C0.S64
