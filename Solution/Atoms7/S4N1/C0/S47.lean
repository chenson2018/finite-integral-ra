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

namespace RACert.S4N1.C0.S47

open RACert RACert.Problem

theorem cover7676 : P.CoversSplit 24 10 7676 0xf0000000f000aa000000000000000000f0000000f0000a000000000000000000c000000080088808c0c0000080888888c000000080080808c0c0000080880808f0000000f000aa000000000000000000f0000000f0000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 858, 865, 916, 1210, 1601]) (ps := [(11, [879, 909], [858])]) (by decide +kernel)

theorem c7676_0 : P.sumLeaves 24 7860224 1024 = 10966876 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7676) (lo := 0) (len := 1024) (W := 10966876) check rows elimOK (by decide) (by decide) cover7676 (by decide)
  decide +kernel

theorem h7676 : P.leaf 34 7676 = 10966876 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10966876)]) (.cons c7676_0 (.nil)) (by decide) (by decide))

theorem cover19951 : P.CoversSplit 24 10 19951 0xff00fa00fa00aa000000000000000000ff000000000050000000000000000000cc00c800880088003300320022002200cc000000400040003300000010001000ff00fa00fa00aa000000000000000000ff0050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c19951_0 : P.sumLeaves 24 20429824 1016 = 38701404 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19951) (lo := 0) (len := 1016) (W := 38701404) check rows elimOK (by decide) (by decide) cover19951 (by decide)
  decide +kernel

theorem c19951_1 : P.sumLeaves 24 20430840 8 = 17369360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19951) (lo := 1016) (len := 8) (W := 17369360) check rows elimOK (by decide) (by decide) cover19951 (by decide)
  decide +kernel

theorem h19951 : P.leaf 34 19951 = 56070764 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1016, 38701404), (8, 17369360)]) (.cons c19951_0 (.cons c19951_1 (.nil))) (by decide) (by decide))

theorem h7677 : P.leaf 34 7677 = 56070764 :=
  orient4 (v := 19951) (by decide) (by decide +kernel) h19951

theorem cover7678 : P.CoversSplit 24 10 7678 0xf0f00000f0f50000f0f00000f0f50000f0f00000f0f50000f0f00000f0f50000c0f0000080800000c000000080000000c0f0000080800000c000000080000000f0f00000f0f50000f0f00000f0f50000f0f00000f0f00000f0f00000f0f00000c0f0000080800000c000000080000000c0c0000080800000c000000080000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 865, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c7678_0 : P.sumLeaves 24 7862272 631 = 28433191 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7678) (lo := 0) (len := 631) (W := 28433191) check rows elimOK (by decide) (by decide) cover7678 (by decide)
  decide +kernel

theorem c7678_1 : P.sumLeaves 24 7862903 393 = 85464140 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7678) (lo := 631) (len := 393) (W := 85464140) check rows elimOK (by decide) (by decide) cover7678 (by decide)
  decide +kernel

theorem h7678 : P.leaf 34 7678 = 113897331 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(631, 28433191), (393, 85464140)]) (.cons c7678_0 (.cons c7678_1 (.nil))) (by decide) (by decide))

theorem cover19967 : P.CoversSplit 24 10 19967 0xfffafafafafaaaaafffafafafafaaaaafffafafafafaaaaafffafafafafaaaaaccc8c8c888888888ffc8fac8aa88aa88ccc8c8c888888888ffc8fac8aa88aa88fffafafafafaaaaafffafafafafaaaaafffafafafafaaaaafffafafafafaaaaaccc8c8c888888888ffc8fac8aa88aa88ccc8c8c888888888ffc8fac8aa88aa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c19967_0 : P.sumLeaves 24 20446208 235 = 27087328 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19967) (lo := 0) (len := 235) (W := 27087328) check rows elimOK (by decide) (by decide) cover19967 (by decide)
  decide +kernel

theorem c19967_1 : P.sumLeaves 24 20446443 143 = 46037939 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19967) (lo := 235) (len := 143) (W := 46037939) check rows elimOK (by decide) (by decide) cover19967 (by decide)
  decide +kernel

theorem c19967_2 : P.sumLeaves 24 20446586 132 = 72184952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19967) (lo := 378) (len := 132) (W := 72184952) check rows elimOK (by decide) (by decide) cover19967 (by decide)
  decide +kernel

theorem c19967_3 : P.sumLeaves 24 20446718 232 = 77226500 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19967) (lo := 510) (len := 232) (W := 77226500) check rows elimOK (by decide) (by decide) cover19967 (by decide)
  decide +kernel

theorem c19967_4 : P.sumLeaves 24 20446950 146 = 102970775 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19967) (lo := 742) (len := 146) (W := 102970775) check rows elimOK (by decide) (by decide) cover19967 (by decide)
  decide +kernel

theorem c19967_5 : P.sumLeaves 24 20447096 132 = 160923480 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19967) (lo := 888) (len := 132) (W := 160923480) check rows elimOK (by decide) (by decide) cover19967 (by decide)
  decide +kernel

theorem c19967_6 : P.sumLeaves 24 20447228 4 = 14926240 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19967) (lo := 1020) (len := 4) (W := 14926240) check rows elimOK (by decide) (by decide) cover19967 (by decide)
  decide +kernel

theorem h19967 : P.leaf 34 19967 = 501357214 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(235, 27087328), (143, 46037939), (132, 72184952), (232, 77226500), (146, 102970775), (132, 160923480), (4, 14926240)]) (.cons c19967_0 (.cons c19967_1 (.cons c19967_2 (.cons c19967_3 (.cons c19967_4 (.cons c19967_5 (.cons c19967_6 (.nil)))))))) (by decide) (by decide))

theorem h7679 : P.leaf 34 7679 = 501357214 :=
  orient4 (v := 19967) (by decide) (by decide +kernel) h19967

theorem cover20142 : P.CoversSplit 24 10 20142 0xaa000000aa000000aa000000aa000000aa0000000a000000aa0000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 573, 916, 921, 1202]) (by decide +kernel)

theorem h20142 : P.leaf 34 20142 = 5231144 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 20142) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 20142) (weight := fun _ => 1) (xs := [793, 795, 825, 827, 829, 831, 857, 859, 889, 891, 893, 895, 921, 923, 925, 927, 953, 955, 957, 959, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover20142 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7924 : P.leaf 34 7924 = 5231144 :=
  orient4 (v := 20142) (by decide) (by decide +kernel) h20142

theorem cover36655 : P.CoversSplit 24 10 36655 0xff00ff00f0000000ff00ff00f0000000ff00ff00f0000000ff00ff00f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 529, 915, 921, 1202, 1209]) (by decide +kernel)

theorem c36655_0 : P.sumLeaves 24 37534720 1024 = 25222704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36655) (lo := 0) (len := 1024) (W := 25222704) check rows elimOK (by decide) (by decide) cover36655 (by decide)
  decide +kernel

theorem h36655 : P.leaf 34 36655 = 25222704 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 25222704)]) (.cons c36655_0 (.nil)) (by decide) (by decide))

theorem h7925 : P.leaf 34 7925 = 25222704 :=
  orient5 (v := 36655) (by decide) (by decide +kernel) h36655

theorem cover36670 : P.CoversSplit 24 10 36670 0xff00ff00f0000000ff00ff00f0000000aa00af0000000000aa00af00000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 529, 572, 915, 921, 1202, 1209, 1258]) (ps := [(14, [965], [1272])]) (by decide +kernel)

theorem c36670_0 : P.sumLeaves 24 37550080 1024 = 26808738 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36670) (lo := 0) (len := 1024) (W := 26808738) check rows elimOK (by decide) (by decide) cover36670 (by decide)
  decide +kernel

theorem h36670 : P.leaf 34 36670 = 26808738 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 26808738)]) (.cons c36670_0 (.nil)) (by decide) (by decide))

theorem h7926 : P.leaf 34 7926 = 26808738 :=
  orient5 (v := 36670) (by decide) (by decide +kernel) h36670

theorem cover36671 : P.CoversSplit 24 10 36671 0xff00ff00f0000000ff00ff00f0000000ff00ff00f0000000ff00ff00f00000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 529, 572, 915, 921, 1202, 1209, 1258, 1308]) (ps := [(14, [965], [1272])]) (by decide +kernel)

theorem c36671_0 : P.sumLeaves 24 37551104 1024 = 42981068 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36671) (lo := 0) (len := 1024) (W := 42981068) check rows elimOK (by decide) (by decide) cover36671 (by decide)
  decide +kernel

theorem h36671 : P.leaf 34 36671 = 42981068 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 42981068)]) (.cons c36671_0 (.nil)) (by decide) (by decide))

theorem h7927 : P.leaf 34 7927 = 42981068 :=
  orient5 (v := 36671) (by decide) (by decide +kernel) h36671

theorem cover7932 : P.CoversSplit 24 10 7932 0xfffffffffafa00000000000000000000fffffffffafa000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 573, 916, 1210, 1259, 1264, 1308]) (by decide +kernel)

noncomputable def f7932 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (8122368 + i)

theorem c7932_0 : rowSum f7932 0 1024 = 28835658 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7932) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover7932 (by decide)
  decide +kernel

theorem sum7932 : rowSum f7932 0 1024 = 28835658 :=
  c7932_0

theorem h7932 : P.leaf 34 7932 = 28835658 :=
  leaf_weighted (k := 24) (d := 10) (H := 7932) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 7932) (by decide) (by decide +kernel)) sum7932

theorem cover7933 : P.CoversSplit 24 10 7933 0xffffffffffff00000000000000000000ffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 573, 916, 1209, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

noncomputable def f7933 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (8123392 + i)

theorem c7933_0 : rowSum f7933 0 1024 = 38904925 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7933) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover7933 (by decide)
  decide +kernel

theorem sum7933 : rowSum f7933 0 1024 = 38904925 :=
  c7933_0

theorem h7933 : P.leaf 34 7933 = 38904925 :=
  leaf_weighted (k := 24) (d := 10) (H := 7933) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 7933) (by decide) (by decide +kernel)) sum7933

theorem cover7934 : P.CoversSplit 24 10 7934 0xffffffffffff00000000000000000000ffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 916, 1209, 1210, 1217, 1258, 1259, 1264, 1308]) (by decide +kernel)

noncomputable def f7934 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (8124416 + i)

theorem c7934_0 : rowSum f7934 0 1024 = 62437892 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7934) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover7934 (by decide)
  decide +kernel

theorem sum7934 : rowSum f7934 0 1024 = 62437892 :=
  c7934_0

theorem h7934 : P.leaf 34 7934 = 62437892 :=
  leaf_weighted (k := 24) (d := 10) (H := 7934) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 7934) (by decide) (by decide +kernel)) sum7934

def seg : List (ℕ × ℕ) := [(7676, 48), (7677, 48), (7678, 48), (7679, 48), (7924, 48), (7925, 48), (7926, 48), (7927, 48), (7932, 24), (7933, 24), (7934, 24)]

theorem segOK : checkSeg 16 perms 7676 7935 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7676 7935 456 40686003672 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 40686003672)
    (SegSum.cons (w := 48) h7676 (SegSum.cons (w := 48) h7677 (SegSum.cons (w := 48) h7678 (SegSum.cons (w := 48) h7679 (SegSum.cons (w := 48) h7924 (SegSum.cons (w := 48) h7925 (SegSum.cons (w := 48) h7926 (SegSum.cons (w := 48) h7927 (SegSum.cons (w := 24) h7932 (SegSum.cons (w := 24) h7933 (SegSum.cons (w := 24) h7934 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))) (by decide)

end RACert.S4N1.C0.S47
