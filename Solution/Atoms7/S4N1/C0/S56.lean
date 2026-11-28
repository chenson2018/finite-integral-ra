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

namespace RACert.S4N1.C0.S56

open RACert RACert.Problem

theorem cover15840 : P.CoversSplit 24 10 15840 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h15840 : P.leaf 34 15840 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 15840) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 15840) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15840 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15841 : P.CoversSplit 24 10 15841 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h15841 : P.leaf 34 15841 = 970812 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 15841) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 15841) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover15841 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15843 : P.CoversSplit 24 10 15843 0x8000000000000400000000000000000080000000000000000000000000000000000000000001000100200000000100000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h15843 : P.leaf 34 15843 = 7943796 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 15843) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 15843) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 15843) (weight := rowWeight keep0 twice0) (xs := [208, 511, 592, 656, 693, 704, 720, 895, 970, 1023]) check rows elimOK (by decide) (by decide) cover15843 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15844 : P.CoversSplit 24 10 15844 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h15844 : P.leaf 34 15844 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 15844) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 15844) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15844 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15845 : P.CoversSplit 24 10 15845 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h15845 : P.leaf 34 15845 = 4500882 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 15845) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 15845) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover15845 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15847 : P.CoversSplit 24 10 15847 0x8000000000000400000000000000000080000000000000000000000000000000000000000001000100200000000100000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h15847 : P.leaf 34 15847 = 8644920 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 15847) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 15847) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 15847) (weight := rowWeight keep0 twice0) (xs := [208, 511, 592, 656, 693, 704, 720, 895, 970, 1023]) check rows elimOK (by decide) (by decide) cover15847 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15852 : P.CoversSplit 24 10 15852 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h15852 : P.leaf 34 15852 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 15852) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 15852) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15852 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15853 : P.CoversSplit 24 10 15853 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h15853 : P.leaf 34 15853 = 5548783 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 15853) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 15853) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover15853 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15855 : P.CoversSplit 24 10 15855 0x8000000000000400000000000000000080000000000000000000000000000000000000000001000100200000000100000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h15855 : P.leaf 34 15855 = 10447916 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 15855) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 15855) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 15855) (weight := rowWeight keep0 twice0) (xs := [208, 511, 592, 656, 693, 704, 720, 895, 970, 1023]) check rows elimOK (by decide) (by decide) cover15855 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover52623 : P.CoversSplit 24 10 52623 0xaa000000ab000a000000000000000000aa000000ab000a000000000000000000aa020000ab020a022200000023000200aa020000ab020a022200000023000200aa000000ab000a000000000000000000aa000000aa000a000000000000000000aa020000ab020a022200000023000200aa000000aa000a002200000022000200 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 865, 1217, 1609]) (by decide +kernel)

noncomputable def f52623 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (53885952 + i)

theorem c52623_0 : rowSum f52623 0 1024 = 42030206 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 52623) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover52623 (by decide)
  decide +kernel

theorem sum52623 : rowSum f52623 0 1024 = 42030206 :=
  c52623_0

theorem h52623 : P.leaf 34 52623 = 42030206 :=
  leaf_weighted (k := 24) (d := 10) (H := 52623) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 52623) (by decide) (by decide +kernel)) sum52623

theorem h15857 : P.leaf 34 15857 = 42030206 :=
  orient4 (v := 52623) (by decide) (by decide +kernel) h52623

theorem cover15859 : P.CoversSplit 24 10 15859 0xfffffffffffafafaffff0000fffa0000fffffffffffafafaffff0000fffa0000fffcfffcfac8fac8ffcc0000fac80000fffcfffcfac8fac8ffcc0000fac80000fffffffffffafafaffff0000fffa0000fffffffffafafafaffff0000fafa0000fffcfffcfac8fac8ffcc0000fac80000ffccffccfac8fac8ffcc0000fac80000 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 866, 1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f15859 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (16239616 + i)

theorem c15859_0 : rowSum f15859 0 232 = 31504080 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15859) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15859 (by decide)
  decide +kernel

theorem c15859_1 : rowSum f15859 232 240 = 77265586 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15859) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15859 (by decide)
  decide +kernel

theorem c15859_2 : rowSum f15859 472 473 = 164100744 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15859) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15859 (by decide)
  decide +kernel

theorem c15859_3 : rowSum f15859 945 79 = 70185772 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15859) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15859 (by decide)
  decide +kernel

theorem sum15859 : rowSum f15859 0 1024 = 343056182 :=
  rowSum_append (F := f15859) (lo := 0) (n := 232) (m := 792) (A := 31504080) (B := 311552102) c15859_0 (rowSum_append (F := f15859) (lo := 232) (n := 240) (m := 552) (A := 77265586) (B := 234286516) c15859_1 (rowSum_append (F := f15859) (lo := 472) (n := 473) (m := 79) (A := 164100744) (B := 70185772) c15859_2 (c15859_3)))

theorem h15859 : P.leaf 34 15859 = 343056182 :=
  leaf_weighted (k := 24) (d := 10) (H := 15859) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 15859) (by decide) (by decide +kernel)) sum15859

theorem cover15860 : P.CoversSplit 24 10 15860 0xf0000000f000fa000000000000000000f0000000f000fa000000000000000000f0000000f008fa08f0c00000f0c80000f0000000f008fa08f0c00000f0c80000f0000000f000fa000000000000000000f0000000f000fa000000000000000000f0000000f008fa08f0c00000f0c80000f0000000f008fa08f0c00000f0c8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 865, 866, 908]) (by decide +kernel)

noncomputable def f15860 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (16240640 + i)

theorem c15860_0 : rowSum f15860 0 1023 = 17602781 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15860) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15860 (by decide)
  decide +kernel

theorem c15860_1 : rowSum f15860 1023 1 = 590932 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15860) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15860 (by decide)
  decide +kernel

theorem sum15860 : rowSum f15860 0 1024 = 18193713 :=
  rowSum_append (F := f15860) (lo := 0) (n := 1023) (m := 1) (A := 17602781) (B := 590932) c15860_0 (c15860_1)

theorem h15860 : P.leaf 34 15860 = 18193713 :=
  leaf_weighted (k := 24) (d := 10) (H := 15860) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 15860) (by decide) (by decide +kernel)) sum15860

theorem cover52655 : P.CoversSplit 24 10 52655 0xff00fa00fe00f0000000000000000000ff00fa00fe00f0000000000000000000ff02fa02fe02f0003300320032003000ff02fa02fe02f0003300320032003000ff00fa00fe00f0000000000000000000ff00fa00fa00f0000000000000000000ff02fa02fe02f0003300320032003000ff00fa00000000003300320000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1202, 1217, 1308, 1609]) (by decide +kernel)

theorem c52655_0 : P.sumLeaves 24 53918720 489 = 24361618 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 52655) (lo := 0) (len := 489) (W := 24361618) check rows elimOK (by decide) (by decide) cover52655 (by decide)
  decide +kernel

theorem c52655_1 : P.sumLeaves 24 53919209 357 = 50750002 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 52655) (lo := 489) (len := 357) (W := 50750002) check rows elimOK (by decide) (by decide) cover52655 (by decide)
  decide +kernel

theorem c52655_2 : P.sumLeaves 24 53919566 178 = 53191836 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 52655) (lo := 846) (len := 178) (W := 53191836) check rows elimOK (by decide) (by decide) cover52655 (by decide)
  decide +kernel

theorem h52655 : P.leaf 34 52655 = 128303456 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(489, 24361618), (357, 50750002), (178, 53191836)]) (.cons c52655_0 (.cons c52655_1 (.cons c52655_2 (.nil)))) (by decide) (by decide))

theorem h15861 : P.leaf 34 15861 = 128303456 :=
  orient4 (v := 52655) (by decide) (by decide +kernel) h52655

theorem cover15863 : P.CoversSplit 24 10 15863 0xfffffffffffafafaffff0000fffa0000fffffffffffafafaffff0000fffa0000fffcfffcfac8fac8ffcc0000fac80000fffcfffcfac8fac8ffcc0000fac80000fffffffffffafafaffff0000fffa0000fffffffffafafafaffff0000fafa0000fffcfffcfac8fac8ffcc0000fac80000ffccffccfac8fac8ffcc0000fac80000 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 866, 1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f15863 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (16243712 + i)

theorem c15863_0 : rowSum f15863 0 232 = 39127838 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15863) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15863 (by decide)
  decide +kernel

theorem c15863_1 : rowSum f15863 232 240 = 108443366 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15863) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15863 (by decide)
  decide +kernel

theorem c15863_2 : rowSum f15863 472 473 = 229454856 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15863) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15863 (by decide)
  decide +kernel

theorem c15863_3 : rowSum f15863 945 79 = 101411068 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15863) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15863 (by decide)
  decide +kernel

theorem sum15863 : rowSum f15863 0 1024 = 478437128 :=
  rowSum_append (F := f15863) (lo := 0) (n := 232) (m := 792) (A := 39127838) (B := 439309290) c15863_0 (rowSum_append (F := f15863) (lo := 232) (n := 240) (m := 552) (A := 108443366) (B := 330865924) c15863_1 (rowSum_append (F := f15863) (lo := 472) (n := 473) (m := 79) (A := 229454856) (B := 101411068) c15863_2 (c15863_3)))

theorem h15863 : P.leaf 34 15863 = 478437128 :=
  leaf_weighted (k := 24) (d := 10) (H := 15863) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 15863) (by decide) (by decide +kernel)) sum15863

theorem cover15868 : P.CoversSplit 24 10 15868 0xf0000000f000fa000000000000000000f0000000f000fa000000000000000000f0000000f008fa08f0c00000f0c8fac8f0000000f008fa08f0c00000f0c8fac8f0000000f000fa000000000000000000f0000000f000fa000000000000000000f0000000f008fa08f0c00000f0c8fac8f0000000f008fa08f0c00000f0c8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 865]) (by decide +kernel)

noncomputable def f15868 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (16248832 + i)

theorem c15868_0 : rowSum f15868 0 695 = 26448510 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15868) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15868 (by decide)
  decide +kernel

theorem c15868_1 : rowSum f15868 695 329 = 21567245 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15868) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15868 (by decide)
  decide +kernel

theorem sum15868 : rowSum f15868 0 1024 = 48015755 :=
  rowSum_append (F := f15868) (lo := 0) (n := 695) (m := 329) (A := 26448510) (B := 21567245) c15868_0 (c15868_1)

theorem h15868 : P.leaf 34 15868 = 48015755 :=
  leaf_weighted (k := 24) (d := 10) (H := 15868) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 15868) (by decide) (by decide +kernel)) sum15868

theorem cover15869 : P.CoversSplit 24 10 15869 0xff00ff00ff00f0000000000000000000ff00ff00ff00f0000000000000000000ff03ff03fa00f0003300330032003000ff03ff03fa00f0003300330032003000ff00ff00ff00f0000000000000000000ff00ff00fa00f0000000000000000000ff03ff03fa00f0003300330032003000ff00ff00fa00f0003300330032003000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 858, 865, 1209, 1217, 1609]) (by decide +kernel)

theorem c15869_0 : P.sumLeaves 24 16249856 364 = 27707520 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 15869) (lo := 0) (len := 364) (W := 27707520) check rows elimOK (by decide) (by decide) cover15869 (by decide)
  decide +kernel

theorem c15869_1 : P.sumLeaves 24 16250220 352 = 60159988 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 15869) (lo := 364) (len := 352) (W := 60159988) check rows elimOK (by decide) (by decide) cover15869 (by decide)
  decide +kernel

theorem c15869_2 : P.sumLeaves 24 16250572 308 = 131575135 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 15869) (lo := 716) (len := 308) (W := 131575135) check rows elimOK (by decide) (by decide) cover15869 (by decide)
  decide +kernel

theorem h15869 : P.leaf 34 15869 = 219442643 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(364, 27707520), (352, 60159988), (308, 131575135)]) (.cons c15869_0 (.cons c15869_1 (.cons c15869_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(15840, 3), (15841, 12), (15843, 6), (15844, 12), (15845, 24), (15847, 12), (15852, 6), (15853, 12), (15855, 6), (15857, 12), (15859, 12), (15860, 24), (15861, 48), (15863, 24), (15868, 12), (15869, 24)]

theorem segOK : checkSeg 16 perms 15840 15871 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 15840 15871 249 28941900840 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 28941900840)
    (SegSum.cons (w := 3) h15840 (SegSum.cons (w := 12) h15841 (SegSum.cons (w := 6) h15843 (SegSum.cons (w := 12) h15844 (SegSum.cons (w := 24) h15845 (SegSum.cons (w := 12) h15847 (SegSum.cons (w := 6) h15852 (SegSum.cons (w := 12) h15853 (SegSum.cons (w := 6) h15855 (SegSum.cons (w := 12) h15857 (SegSum.cons (w := 12) h15859 (SegSum.cons (w := 24) h15860 (SegSum.cons (w := 48) h15861 (SegSum.cons (w := 24) h15863 (SegSum.cons (w := 12) h15868 (SegSum.cons (w := 24) h15869 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))) (by decide)

end RACert.S4N1.C0.S56
