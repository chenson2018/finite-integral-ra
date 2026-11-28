/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S57

open RACert RACert.Problem

theorem cover105946 : P.CoversSplit 26 10 105946 0xa0a0a0a0a0a0a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 531, 629, 930, 965, 1658]) (by decide +kernel)

theorem h105946 : P.leaf 36 105946 = 12162696 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 105946) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 105946) (weight := fun _ => 1) (xs := [965, 967, 973, 975, 981, 983, 989, 991, 997, 999, 1005, 1007, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover105946 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89836 : P.leaf 36 89836 = 12162696 :=
  orient4 (v := 105946) (by decide) (by decide +kernel) h105946

theorem cover105947 : P.CoversSplit 26 10 105947 0xa0a0a0a0a0a0a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000202020200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 930, 965, 1658, 1665]) (by decide +kernel)

theorem h105947 : P.leaf 36 105947 = 23687720 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 105947) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 105947) (weight := fun _ => 1) (xs := [453, 461, 469, 477, 965, 967, 973, 975, 981, 983, 989, 991, 997, 999, 1005, 1007, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover105947 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89837 : P.leaf 36 89837 = 23687720 :=
  orient4 (v := 105947) (by decide) (by decide +kernel) h105947

theorem cover105950 : P.CoversSplit 26 10 105950 0xfffffffffffffafa000000000000000000000000000000000000000011001000000000000000000055550000555500000000000000000000000000001100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 531, 629, 636, 922, 930, 1315, 1322, 1658, 1665]) (ps := [(21, [1272], [1658])]) (by decide +kernel)

theorem c105950_0 : P.sumLeaves 26 108492800 1024 = 83975897 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 105950) (lo := 0) (len := 1024) (W := 83975897) check rows elimOK (by decide) (by decide) cover105950 (by decide)
  decide +kernel

theorem h105950 : P.leaf 36 105950 = 83975897 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 83975897)]) (.cons c105950_0 (.nil)) (by decide) (by decide))

theorem h89838 : P.leaf 36 89838 = 83975897 :=
  orient4 (v := 105950) (by decide) (by decide +kernel) h105950

theorem cover105951 : P.CoversSplit 26 10 105951 0xfffffffffffffafa000000000000000000000000000000000000000011001000000000000000000055555050555550500000000000000000000000001100100000000000333332320000000000000000000000003300320000000000110010000000000000000000000000001111101000000000000000000000000011001000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 629, 636, 922, 930, 1315, 1322, 1658, 1665]) (ps := [(21, [1272], [1658])]) (by decide +kernel)

theorem c105951_0 : P.sumLeaves 26 108493824 997 = 76429605 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 105951) (lo := 0) (len := 997) (W := 76429605) check rows elimOK (by decide) (by decide) cover105951 (by decide)
  decide +kernel

theorem c105951_1 : P.sumLeaves 26 108494821 27 = 68555286 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 105951) (lo := 997) (len := 27) (W := 68555286) check rows elimOK (by decide) (by decide) cover105951 (by decide)
  decide +kernel

theorem h105951 : P.leaf 36 105951 = 144984891 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(997, 76429605), (27, 68555286)]) (.cons c105951_0 (.cons c105951_1 (.nil))) (by decide) (by decide))

theorem h89839 : P.leaf 36 89839 = 144984891 :=
  orient4 (v := 105951) (by decide) (by decide +kernel) h105951

theorem cover306587 : P.CoversSplit 26 10 306587 0x8888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 537, 538, 629, 636, 1266, 1272, 1665]) (by decide +kernel)

theorem h306587 : P.leaf 36 306587 = 3056816 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 306587) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 306587) (weight := fun _ => 1) (xs := [1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover306587 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89844 : P.leaf 36 89844 = 3056816 :=
  orient84 (v := 306587) (by decide) (by decide +kernel) h306587

theorem cover105971 : P.CoversSplit 26 10 105971 0x8800880088008800000000000000000000000000000000000000000000000000000000000000000000004000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 629, 636, 930, 965, 1658]) (by decide +kernel)

theorem h105971 : P.leaf 36 105971 = 13162180 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 105971) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 105971) (weight := fun _ => 1) (xs := [654, 686, 971, 975, 987, 991, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover105971 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89845 : P.leaf 36 89845 = 13162180 :=
  orient4 (v := 105971) (by decide) (by decide +kernel) h105971

theorem cover105974 : P.CoversSplit 26 10 105974 0xcc00cc00cc00c800000000000000000000000000000000000000000000110000440040004400400044000000440000000000000000000000000000000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 531, 629, 636, 922, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h105974 : P.leaf 36 105974 = 36881367 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 105974) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 105974) (weight := fun _ => 1) (xs := [528, 532, 666, 670, 698, 702, 718, 730, 734, 750, 762, 766, 784, 788, 971, 974, 975, 986, 987, 990, 991, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover105974 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89846 : P.leaf 36 89846 = 36881367 :=
  orient4 (v := 105974) (by decide) (by decide +kernel) h105974

theorem cover105975 : P.CoversSplit 26 10 105975 0xcc00cc00cc00c800000000000000000000000000000000000000000000110000440040004400400044000000440000000000000000000000000000000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 922, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h105975 : P.leaf 36 105975 = 61861781 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 105975) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 105975) (weight := fun _ => 1) (xs := [528, 532, 666, 670, 698, 702, 718, 730, 734, 750, 762, 766, 784, 788, 971, 974, 975, 986, 987, 990, 991, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover105975 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89847 : P.leaf 36 89847 = 61861781 :=
  orient4 (v := 105975) (by decide) (by decide +kernel) h105975

theorem cover113131 : P.CoversSplit 26 10 113131 0xaaaaaaaaaaaaaaaaaaaaababaaaaaaaa00000000000000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000002200220000000000220022000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 930, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c113131_0 : P.sumLeaves 26 115846144 1024 = 61879366 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 113131) (lo := 0) (len := 1024) (W := 61879366) check rows elimOK (by decide) (by decide) cover113131 (by decide)
  decide +kernel

theorem h113131 : P.leaf 36 113131 = 61879366 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 61879366)]) (.cons c113131_0 (.nil)) (by decide) (by decide))

theorem h89850 : P.leaf 36 89850 = 61879366 :=
  orient86 (v := 113131) (by decide) (by decide +kernel) h113131

theorem cover89851 : P.CoversSplit 26 10 89851 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000030303000000000000000000000005050000050500000000000000000000000000000100000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000100000000000000000000000000000001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c89851_0 : P.sumLeaves 26 92007424 1021 = 125074869 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89851) (lo := 0) (len := 1021) (W := 125074869) check rows elimOK (by decide) (by decide) cover89851 (by decide)
  decide +kernel

theorem c89851_1 : P.sumLeaves 26 92008445 3 = 9475924 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89851) (lo := 1021) (len := 3) (W := 9475924) check rows elimOK (by decide) (by decide) cover89851 (by decide)
  decide +kernel

theorem h89851 : P.leaf 36 89851 = 134550793 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 125074869), (3, 9475924)]) (.cons c89851_0 (.cons c89851_1 (.nil))) (by decide) (by decide))

theorem cover105978 : P.CoversSplit 26 10 105978 0xaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000222222220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 629, 636, 922, 930, 965, 1658, 1665]) (by decide +kernel)

theorem c105978_0 : P.sumLeaves 26 108521472 1024 = 54358576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 105978) (lo := 0) (len := 1024) (W := 54358576) check rows elimOK (by decide) (by decide) cover105978 (by decide)
  decide +kernel

theorem h105978 : P.leaf 36 105978 = 54358576 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 54358576)]) (.cons c105978_0 (.nil)) (by decide) (by decide))

theorem h89852 : P.leaf 36 89852 = 54358576 :=
  orient4 (v := 105978) (by decide) (by decide +kernel) h105978

theorem cover105979 : P.CoversSplit 26 10 105979 0xaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000222222220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 922, 930, 965, 1658, 1665]) (by decide +kernel)

theorem c105979_0 : P.sumLeaves 26 108522496 1024 = 100171362 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 105979) (lo := 0) (len := 1024) (W := 100171362) check rows elimOK (by decide) (by decide) cover105979 (by decide)
  decide +kernel

theorem h105979 : P.leaf 36 105979 = 100171362 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 100171362)]) (.cons c105979_0 (.nil)) (by decide) (by decide))

theorem h89853 : P.leaf 36 89853 = 100171362 :=
  orient4 (v := 105979) (by decide) (by decide +kernel) h105979

theorem cover105982 : P.CoversSplit 26 10 105982 0xfffffffffffffafa000000000000000000000000000000000000000011001000555550505555505055555050555550500000000000000000000000001100100000000000333332320000000000000000000000003300320000000000110010000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [531, 629, 636, 922, 930, 1315, 1658, 1665]) (by decide +kernel)

theorem c105982_0 : P.sumLeaves 26 108525568 982 = 63278769 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 105982) (lo := 0) (len := 982) (W := 63278769) check rows elimOK (by decide) (by decide) cover105982 (by decide)
  decide +kernel

theorem c105982_1 : P.sumLeaves 26 108526550 42 = 161453710 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 105982) (lo := 982) (len := 42) (W := 161453710) check rows elimOK (by decide) (by decide) cover105982 (by decide)
  decide +kernel

theorem h105982 : P.leaf 36 105982 = 224732479 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(982, 63278769), (42, 161453710)]) (.cons c105982_0 (.cons c105982_1 (.nil))) (by decide) (by decide))

theorem h89854 : P.leaf 36 89854 = 224732479 :=
  orient4 (v := 105982) (by decide) (by decide +kernel) h105982

theorem cover105983 : P.CoversSplit 26 10 105983 0xfffffffffffffafa000000000000000000000000000000000000000011001000555550505555505055555050555550500000000000000000000000001100100000000000333332320000000000000000000000003300320000000000110010000000000011111010000000001111101000000000110010000000000011001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 922, 930, 1315, 1658, 1665]) (by decide +kernel)

theorem c105983_0 : P.sumLeaves 26 108526592 961 = 66692596 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 105983) (lo := 0) (len := 961) (W := 66692596) check rows elimOK (by decide) (by decide) cover105983 (by decide)
  decide +kernel

theorem c105983_1 : P.sumLeaves 26 108527553 63 = 279206522 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 105983) (lo := 961) (len := 63) (W := 279206522) check rows elimOK (by decide) (by decide) cover105983 (by decide)
  decide +kernel

theorem h105983 : P.leaf 36 105983 = 345899118 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(961, 66692596), (63, 279206522)]) (.cons c105983_0 (.cons c105983_1 (.nil))) (by decide) (by decide))

theorem h89855 : P.leaf 36 89855 = 345899118 :=
  orient4 (v := 105983) (by decide) (by decide +kernel) h105983

theorem cover90021 : P.CoversSplit 26 10 90021 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 536, 538, 922, 923, 972, 979, 1272, 1658]) (by decide +kernel)

theorem h90021 : P.leaf 36 90021 = 34703072 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 90021) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 90021) (weight := fun _ => 1) (xs := [811, 814, 815, 827, 830, 831, 874, 875, 878, 879, 890, 891, 894, 895, 938, 939, 942, 943, 954, 955, 958, 959, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover90021 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover90023 : P.CoversSplit 26 10 90023 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 922, 972, 979, 1272, 1315, 1322, 1658]) (by decide +kernel)

theorem h90023 : P.leaf 36 90023 = 57540284 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 90023) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 90023) (weight := fun _ => 1) (xs := [811, 814, 815, 827, 830, 831, 874, 875, 878, 879, 890, 891, 894, 895, 938, 939, 942, 943, 954, 955, 958, 959, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover90023 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover90024 : P.CoversSplit 26 10 90024 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 558, 566, 874, 923, 972, 1272]) (by decide +kernel)

noncomputable def f90024 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92184576 + i)

theorem c90024_0 : rowSum f90024 0 1024 = 7582166 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90024) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90024 (by decide)
  decide +kernel

theorem sum90024 : rowSum f90024 0 1024 = 7582166 :=
  c90024_0

theorem h90024 : P.leaf 36 90024 = 7582166 :=
  leaf_weighted (k := 26) (d := 10) (H := 90024) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 90024) (by decide) (by decide +kernel)) sum90024

theorem cover90025 : P.CoversSplit 26 10 90025 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [480, 536, 923, 972, 1272]) (by decide +kernel)

noncomputable def f90025 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92185600 + i)

theorem c90025_0 : rowSum f90025 0 1024 = 50552484 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90025) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90025 (by decide)
  decide +kernel

theorem sum90025 : rowSum f90025 0 1024 = 50552484 :=
  c90025_0

theorem h90025 : P.leaf 36 90025 = 50552484 :=
  leaf_weighted (k := 26) (d := 10) (H := 90025) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 90025) (by decide) (by decide +kernel)) sum90025

theorem cover307027 : P.CoversSplit 26 10 307027 0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000aa00af00aa00af00000000000000000000000000000000000000000000000000aa00aa00aa22aa22000000000000000000000000000000000000000000000000aa00af00aa22af22000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 489, 579, 930, 1266, 1272]) (by decide +kernel)

noncomputable def f307027 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (314395648 + i)

theorem c307027_0 : rowSum f307027 0 1024 = 11111183 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 307027) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover307027 (by decide)
  decide +kernel

theorem sum307027 : rowSum f307027 0 1024 = 11111183 :=
  c307027_0

theorem h307027 : P.leaf 36 307027 = 11111183 :=
  leaf_weighted (k := 26) (d := 10) (H := 307027) (keep := keep8) (twice := twice8) rows (by decide) (by decide) (bal8) (invRow8 (H := 307027) (by decide) (by decide +kernel)) sum307027

theorem h90026 : P.leaf 36 90026 = 11111183 :=
  orient74 (v := 307027) (by decide) (by decide +kernel) h307027

theorem cover90027 : P.CoversSplit 26 10 90027 0xf0f0f0f000000000f0f0f0f500000000f0f0f0f000000030f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1272, 1322, 1658, 1665]) (by decide +kernel)

theorem c90027_0 : P.sumLeaves 26 92187648 1024 = 93269754 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90027) (lo := 0) (len := 1024) (W := 93269754) check rows elimOK (by decide) (by decide) cover90027 (by decide)
  decide +kernel

theorem h90027 : P.leaf 36 90027 = 93269754 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 93269754)]) (.cons c90027_0 (.nil)) (by decide) (by decide))

theorem cover106395 : P.CoversSplit 26 10 106395 0xffffffff00000000fffffafa0000000000000000000000000000000000000000fffff0f000000000aaaaa0a00000000000000000000000000000000000000000ffffffff00000000fffffafa0000000000000000000000000000000000000000fffff0f000000000aaaaa0a00000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 537, 929, 1315, 1658]) (by decide +kernel)

noncomputable def f106395 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (108948480 + i)

theorem c106395_0 : rowSum f106395 0 958 = 148092304 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 106395) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover106395 (by decide)
  decide +kernel

theorem c106395_1 : rowSum f106395 958 66 = 35336610 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 106395) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover106395 (by decide)
  decide +kernel

theorem sum106395 : rowSum f106395 0 1024 = 183428914 :=
  rowSum_append (F := f106395) (lo := 0) (n := 958) (m := 66) (A := 148092304) (B := 35336610) c106395_0 (c106395_1)

theorem h106395 : P.leaf 36 106395 = 183428914 :=
  leaf_weighted (k := 26) (d := 10) (H := 106395) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 106395) (by decide) (by decide +kernel)) sum106395

theorem h90029 : P.leaf 36 90029 = 183428914 :=
  orient4 (v := 106395) (by decide) (by decide +kernel) h106395

theorem cover106399 : P.CoversSplit 26 10 106399 0xffffffff00000000fffffafa0000000000000000000000000000000000000000fffff0f000000000aaaaa0a00000000000000000000000000000000000000000ffffffff00330030fffffafa0033003000330033000000000022002200000000fffff0f000330030aaaaa0a00022002000330030000000000022002000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 1273, 1315, 1658]) (by decide +kernel)

noncomputable def f106399 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (108952576 + i)

theorem c106399_0 : rowSum f106399 0 929 = 200392296 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 106399) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover106399 (by decide)
  decide +kernel

theorem c106399_1 : rowSum f106399 929 95 = 105526106 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 106399) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover106399 (by decide)
  decide +kernel

theorem sum106399 : rowSum f106399 0 1024 = 305918402 :=
  rowSum_append (F := f106399) (lo := 0) (n := 929) (m := 95) (A := 200392296) (B := 105526106) c106399_0 (c106399_1)

theorem h106399 : P.leaf 36 106399 = 305918402 :=
  leaf_weighted (k := 26) (d := 10) (H := 106399) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 106399) (by decide) (by decide +kernel)) sum106399

theorem h90031 : P.leaf 36 90031 = 305918402 :=
  orient4 (v := 106399) (by decide) (by decide +kernel) h106399

theorem cover306643 : P.CoversSplit 26 10 306643 0x8800000088000000880000008800000000000000000000000000000000000000000000000000000000000800000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 489, 530, 629, 636, 930, 1665]) (by decide +kernel)

theorem h306643 : P.leaf 36 306643 = 9365408 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 306643) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 306643) (weight := fun _ => 1) (xs := [651, 683, 923, 927, 955, 959, 987, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover306643 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h90036 : P.leaf 36 90036 = 9365408 :=
  orient84 (v := 306643) (by decide) (by decide +kernel) h306643

theorem cover113142 : P.CoversSplit 26 10 113142 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 531, 629, 636, 867, 930, 1266, 1315]) (by decide +kernel)

theorem h113142 : P.leaf 36 113142 = 82993914 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 113142) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 113142) (weight := fun _ => 1) (xs := [907, 910, 911, 922, 923, 926, 927, 938, 939, 942, 943, 954, 955, 958, 959, 971, 974, 975, 986, 987, 990, 991, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover113142 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h90037 : P.leaf 36 90037 = 82993914 :=
  orient72 (v := 113142) (by decide) (by decide +kernel) h113142

theorem cover113139 : P.CoversSplit 26 10 113139 0x8800880088008800880088008800880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 629, 636, 930, 1266, 1273]) (by decide +kernel)

theorem h113139 : P.leaf 36 113139 = 35363640 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 113139) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 113139) (weight := fun _ => 1) (xs := [907, 911, 923, 927, 939, 943, 955, 959, 971, 975, 987, 991, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover113139 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h90038 : P.leaf 36 90038 = 35363640 :=
  orient72 (v := 113139) (by decide) (by decide +kernel) h113139

def seg : List (ℕ × ℕ) := [(89836, 720), (89837, 720), (89838, 720), (89839, 720), (89844, 720), (89845, 720), (89846, 720), (89847, 720), (89850, 720), (89851, 720), (89852, 720), (89853, 720), (89854, 720), (89855, 720), (90021, 360), (90023, 360), (90024, 72), (90025, 360), (90026, 360), (90027, 720), (90029, 360), (90031, 360), (90036, 720), (90037, 720), (90038, 720)]

theorem segOK : checkSeg 20 perms 89836 90039 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 89836 90039 15192 1328215063752 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1328215063752)
    (SegSum.cons (w := 720) h89836 (SegSum.cons (w := 720) h89837 (SegSum.cons (w := 720) h89838 (SegSum.cons (w := 720) h89839 (SegSum.cons (w := 720) h89844 (SegSum.cons (w := 720) h89845 (SegSum.cons (w := 720) h89846 (SegSum.cons (w := 720) h89847 (SegSum.cons (w := 720) h89850 (SegSum.cons (w := 720) h89851 (SegSum.cons (w := 720) h89852 (SegSum.cons (w := 720) h89853 (SegSum.cons (w := 720) h89854 (SegSum.cons (w := 720) h89855 (SegSum.cons (w := 360) h90021 (SegSum.cons (w := 360) h90023 (SegSum.cons (w := 72) h90024 (SegSum.cons (w := 360) h90025 (SegSum.cons (w := 360) h90026 (SegSum.cons (w := 720) h90027 (SegSum.cons (w := 360) h90029 (SegSum.cons (w := 360) h90031 (SegSum.cons (w := 720) h90036 (SegSum.cons (w := 720) h90037 (SegSum.cons (w := 720) h90038 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S57
