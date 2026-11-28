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

namespace RACert.S4N1.C0.S28

open RACert RACert.Problem

theorem cover18735 : P.CoversSplit 24 10 18735 0x8800000088000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000880000000000000000000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 865, 915, 916, 1202, 1210]) (by decide +kernel)

theorem h18735 : P.leaf 34 18735 = 838544 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 18735) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 18735) (weight := fun _ => 1) (xs := [379, 383, 475, 479, 507, 511, 891, 895, 987, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover18735 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5493 : P.leaf 34 5493 = 838544 :=
  orient4 (v := 18735) (by decide) (by decide +kernel) h18735

theorem cover5494 : P.CoversSplit 24 10 5494 0xf0f00000a0a000000000000000000000f0f00000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 860, 865, 867, 908, 916, 1202, 1258, 1264]) (by decide +kernel)

theorem h5494 : P.leaf 34 5494 = 1334263 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5494) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5494) (weight := fun _ => 1) (xs := [848, 850, 884, 885, 886, 887, 892, 893, 894, 895, 981, 983, 989, 991, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5494 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover18751 : P.CoversSplit 24 10 18751 0xff00fa00aa00a000ff00fa00aa00a000ff00fa000000a000ff000000000000000000000000000000000000000000000000000000000000000000000000000000f000f000a000a000f0000000a0000000f000f00000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 529, 572, 858, 859, 865, 866, 915, 921, 1202, 1217, 1251, 1264, 1308]) (by decide +kernel)

theorem c18751_0 : P.sumLeaves 24 19201024 1024 = 20654174 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18751) (lo := 0) (len := 1024) (W := 20654174) check rows elimOK (by decide) (by decide) cover18751 (by decide)
  decide +kernel

theorem h18751 : P.leaf 34 18751 = 20654174 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20654174)]) (.cons c18751_0 (.nil)) (by decide) (by decide))

theorem h5495 : P.leaf 34 5495 = 20654174 :=
  orient4 (v := 18751) (by decide) (by decide +kernel) h18751

theorem h5496 : P.leaf 34 5496 = 0 := by
  exact leaf_contract_zero (ss := [(28, 2, 466), (2, 1, 472), (15, 1, 487), (14, 8, 558), (35, 0, 867), (7, 6, 474), (16, 10, 872), (33, 0, 909), (18, 11, 879), (32, 1, 1264), (27, 1, 572), (29, 1, 473), (34, 1, 572), (8, 1, 1266)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5497 : P.CoversSplit 24 10 5497 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5497 : P.leaf 34 5497 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5497) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5497) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5497 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5498 : P.CoversSplit 24 10 5498 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5498 : P.leaf 34 5498 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5498) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5498) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5498 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5499 : P.CoversSplit 24 10 5499 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5499 : P.leaf 34 5499 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5499) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5499) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5499 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5500 : P.CoversSplit 24 10 5500 0xc000000080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 572, 858, 860, 865, 867, 909, 916, 1202, 1209, 1258, 1264]) (by decide +kernel)

theorem h5500 : P.leaf 34 5500 = 213184 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5500) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5500) (weight := fun _ => 1) (xs := [975, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5500 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5501 : P.CoversSplit 24 10 5501 0xcc00cc00880080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 572, 858, 860, 865, 909, 1202, 1209, 1258, 1259, 1264]) (by decide +kernel)

theorem h5501 : P.leaf 34 5501 = 2228662 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5501) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5501) (weight := fun _ => 1) (xs := [463, 475, 479, 490, 491, 494, 495, 506, 507, 510, 511, 975, 987, 991, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5501 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5502 : P.CoversSplit 24 10 5502 0xf0f00000a0a000000000000000000000f0f00000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 860, 865, 867, 916, 1202, 1258, 1264]) (by decide +kernel)

theorem h5502 : P.leaf 34 5502 = 4295091 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5502) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5502) (weight := fun _ => 1) (xs := [848, 850, 884, 885, 886, 887, 892, 893, 894, 895, 981, 983, 989, 991, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5502 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover18815 : P.CoversSplit 24 10 18815 0xff00fa00aa00aa00ff00fa00aa00aa00ff00fa00aa00aa00ff00fa00aa00aa000000000000000000000000000000000000000000000000000000000000000000f000f000a000a000f0000000a0000000f000f00000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 859, 865, 866, 915, 921, 1202, 1264, 1308]) (by decide +kernel)

theorem c18815_0 : P.sumLeaves 24 19266560 969 = 25250501 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18815) (lo := 0) (len := 969) (W := 25250501) check rows elimOK (by decide) (by decide) cover18815 (by decide)
  decide +kernel

theorem c18815_1 : P.sumLeaves 24 19267529 55 = 13353420 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18815) (lo := 969) (len := 55) (W := 13353420) check rows elimOK (by decide) (by decide) cover18815 (by decide)
  decide +kernel

theorem h18815 : P.leaf 34 18815 = 38603921 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(969, 25250501), (55, 13353420)]) (.cons c18815_0 (.cons c18815_1 (.nil))) (by decide) (by decide))

theorem h5503 : P.leaf 34 5503 = 38603921 :=
  orient4 (v := 18815) (by decide) (by decide +kernel) h18815

theorem cover5600 : P.CoversSplit 24 10 5600 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h5600 : P.leaf 34 5600 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5600) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5600) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5600 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5601 : P.CoversSplit 24 10 5601 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5601 : P.leaf 34 5601 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5601) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5601) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5601 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5603 : P.CoversSplit 24 10 5603 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5603 : P.leaf 34 5603 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5603) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5603) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5603 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5604 : P.CoversSplit 24 10 5604 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h5604 : P.leaf 34 5604 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5604) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5604) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5604 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5605 : P.CoversSplit 24 10 5605 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5605 : P.leaf 34 5605 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5605) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5605) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5605 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5607 : P.CoversSplit 24 10 5607 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5607 : P.leaf 34 5607 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5607) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5607) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5607 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5608 : P.CoversSplit 24 10 5608 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h5608 : P.leaf 34 5608 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5608) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5608) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5608 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5609 : P.CoversSplit 24 10 5609 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5609 : P.leaf 34 5609 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5609) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5609) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5609 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5611 : P.CoversSplit 24 10 5611 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5611 : P.leaf 34 5611 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5611) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5611) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5611 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5612 : P.CoversSplit 24 10 5612 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h5612 : P.leaf 34 5612 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5612) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5612) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5612 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5613 : P.CoversSplit 24 10 5613 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5613 : P.leaf 34 5613 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5613) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5613) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5613 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5615 : P.CoversSplit 24 10 5615 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5615 : P.leaf 34 5615 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5615) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5615) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5615 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11617 : P.CoversSplit 24 10 11617 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 572, 858, 865, 1209, 1210, 1258, 1266]) (by decide +kernel)

theorem h11617 : P.leaf 34 11617 = 7058 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 11617) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 11617) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover11617 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5616 : P.leaf 34 5616 = 7058 :=
  orient32 (v := 11617) (by decide) (by decide +kernel) h11617

theorem cover5617 : P.CoversSplit 24 10 5617 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5617 : P.leaf 34 5617 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5617) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5617) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5617 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5619 : P.CoversSplit 24 10 5619 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5619 : P.leaf 34 5619 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5619) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5619) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5619 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover18862 : P.CoversSplit 24 10 18862 0xa0000000a00000000000000000000000a0000000000000000000000000000000800000008000000080800000808000008000000000000000808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 858, 859, 865, 879, 915, 1202, 1259, 1601]) (by decide +kernel)

theorem h18862 : P.leaf 34 18862 = 266200 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 18862) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 18862) (weight := fun _ => 1) (xs := [567, 575, 639, 663, 671, 695, 703, 735, 767, 893, 895, 989, 991, 1021, 1023]) check rows elimOK (by decide) (by decide) cover18862 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5620 : P.leaf 34 5620 = 266200 :=
  orient4 (v := 18862) (by decide) (by decide +kernel) h18862

theorem cover18863 : P.CoversSplit 24 10 18863 0xaa000000aa0000000000000000000000aa0000000000000000000000000000008800000088000000000000000000000088000000000000000000000000000000aa000000aa0000000000000000000000aa0000000000000000000000000000000000000000000000220000002200000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 858, 859, 865, 915, 1202, 1210, 1259, 1308, 1601]) (by decide +kernel)

theorem c18863_0 : P.sumLeaves 24 19315712 1024 = 3641858 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18863) (lo := 0) (len := 1024) (W := 3641858) check rows elimOK (by decide) (by decide) cover18863 (by decide)
  decide +kernel

theorem h18863 : P.leaf 34 18863 = 3641858 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3641858)]) (.cons c18863_0 (.nil)) (by decide) (by decide))

theorem h5621 : P.leaf 34 5621 = 3641858 :=
  orient4 (v := 18863) (by decide) (by decide +kernel) h18863

theorem cover5623 : P.CoversSplit 24 10 5623 0xffffffffaaaaaaaaffff0000aaaa0000ffffffffaaaaaaaaffff0000aaaa0000cccccccc88888888cccc000088880000cccccccc88888888cccc000088880000ffffffffaaaaaaaaffff0000aaaa0000ffffffffaaaaaaaaffff0000aaaa0000cccccccc88888888cccc000088880000cccccccc88888888cccc000088880000 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 860, 865, 866, 916, 1202, 1258, 1601]) (by decide +kernel)

noncomputable def f5623 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5757952 + i)

theorem c5623_0 : rowSum f5623 0 407 = 11212024 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5623) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5623 (by decide)
  decide +kernel

theorem c5623_1 : rowSum f5623 407 355 = 47036682 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5623) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5623 (by decide)
  decide +kernel

theorem c5623_2 : rowSum f5623 762 262 = 31383416 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5623) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5623 (by decide)
  decide +kernel

theorem sum5623 : rowSum f5623 0 1024 = 89632122 :=
  rowSum_append (F := f5623) (lo := 0) (n := 407) (m := 617) (A := 11212024) (B := 78420098) c5623_0 (rowSum_append (F := f5623) (lo := 407) (n := 355) (m := 262) (A := 47036682) (B := 31383416) c5623_1 (c5623_2))

theorem h5623 : P.leaf 34 5623 = 89632122 :=
  leaf_weighted (k := 24) (d := 10) (H := 5623) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 5623) (by decide) (by decide +kernel)) sum5623

theorem cover5624 : P.CoversSplit 24 10 5624 0xf0000000a000aa00000000000000000000000000000000000000000000000000c000000080088808c0c0000080888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 860, 865, 867, 909, 1202, 1258, 1601]) (by decide +kernel)

theorem h5624 : P.leaf 34 5624 = 55770 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 5624) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5624) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5624) (weight := rowWeight keep0 twice0) (xs := [3, 7, 11, 15, 19, 23, 31, 54, 55, 62, 63, 67, 75, 79, 83, 95, 126, 127, 329, 331, 333, 335, 349, 351, 380, 381, 382, 383]) check rows elimOK (by decide) (by decide) cover5624 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5625 : P.CoversSplit 24 10 5625 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5625 : P.leaf 34 5625 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5625) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5625) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5625 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5627 : P.CoversSplit 24 10 5627 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5627 : P.leaf 34 5627 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5627) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5627) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5627 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(5493, 48), (5494, 48), (5495, 48), (5496, 48), (5497, 48), (5498, 48), (5499, 48), (5500, 48), (5501, 48), (5502, 48), (5503, 48), (5600, 24), (5601, 48), (5603, 24), (5604, 24), (5605, 48), (5607, 24), (5608, 24), (5609, 48), (5611, 24), (5612, 24), (5613, 48), (5615, 24), (5616, 24), (5617, 48), (5619, 24), (5620, 24), (5621, 48), (5623, 24), (5624, 24), (5625, 48), (5627, 24)]

theorem segOK : checkSeg 16 perms 5493 5628 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 5493 5628 1200 5605933056 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5605933056)
    (SegSum.cons (w := 48) h5493 (SegSum.cons (w := 48) h5494 (SegSum.cons (w := 48) h5495 (SegSum.cons (w := 48) h5496 (SegSum.cons (w := 48) h5497 (SegSum.cons (w := 48) h5498 (SegSum.cons (w := 48) h5499 (SegSum.cons (w := 48) h5500 (SegSum.cons (w := 48) h5501 (SegSum.cons (w := 48) h5502 (SegSum.cons (w := 48) h5503 (SegSum.cons (w := 24) h5600 (SegSum.cons (w := 48) h5601 (SegSum.cons (w := 24) h5603 (SegSum.cons (w := 24) h5604 (SegSum.cons (w := 48) h5605 (SegSum.cons (w := 24) h5607 (SegSum.cons (w := 24) h5608 (SegSum.cons (w := 48) h5609 (SegSum.cons (w := 24) h5611 (SegSum.cons (w := 24) h5612 (SegSum.cons (w := 48) h5613 (SegSum.cons (w := 24) h5615 (SegSum.cons (w := 24) h5616 (SegSum.cons (w := 48) h5617 (SegSum.cons (w := 24) h5619 (SegSum.cons (w := 24) h5620 (SegSum.cons (w := 48) h5621 (SegSum.cons (w := 24) h5623 (SegSum.cons (w := 24) h5624 (SegSum.cons (w := 48) h5625 (SegSum.cons (w := 24) h5627 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S28
