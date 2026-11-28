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

namespace RACert.S4N1.C0.S75

open RACert RACert.Problem

theorem cover59884 : P.CoversSplit 24 10 59884 0xffffffffeae0a0a0ffffffffeae0a0a0f5f5f5f540400000f5f5f5f540400000eec0eec0eac0a080cc00cc00c8008000e4c0e4c040400000c400c40040000000ff33ff33ea20a020ff33ff33ea20a020f531f53140000000f531f531400000002200220022002000000000000000000020002000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 858, 859, 865, 915]) (by decide +kernel)

noncomputable def f59884 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (61321216 + i)

theorem c59884_0 : rowSum f59884 0 655 = 12734391 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59884) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59884 (by decide)
  decide +kernel

theorem c59884_1 : rowSum f59884 655 369 = 21991648 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59884) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59884 (by decide)
  decide +kernel

theorem sum59884 : rowSum f59884 0 1024 = 34726039 :=
  rowSum_append (F := f59884) (lo := 0) (n := 655) (m := 369) (A := 12734391) (B := 21991648) c59884_0 (c59884_1)

theorem h59884 : P.leaf 34 59884 = 34726039 :=
  leaf_weighted (k := 24) (d := 10) (H := 59884) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 59884) (by decide) (by decide +kernel)) sum59884

theorem h24044 : P.leaf 34 24044 = 34726039 :=
  orient24 (v := 59884) (by decide) (by decide +kernel) h59884

theorem cover59900 : P.CoversSplit 24 10 59900 0xfffffffffaf0a0a0fffffffffaf0a0a0f500f50050000000f500f50050000000ffc0ffc0fac0a080cc00cc00c8008000f500f50040000000c400c40040000000f030f030f030a020f030f030f030a020f000f00050000000f000f000500000003000300020002000000000000000000030003000100000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 858, 859, 865, 866, 908, 915, 1202, 1601]) (ps := [(12, [859, 915], [859, 915])]) (by decide +kernel)

noncomputable def f59900 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (61337600 + i)

theorem c59900_0 : rowSum f59900 0 764 = 32083186 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59900) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59900 (by decide)
  decide +kernel

theorem c59900_1 : rowSum f59900 764 260 = 26043975 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59900) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59900 (by decide)
  decide +kernel

theorem sum59900 : rowSum f59900 0 1024 = 58127161 :=
  rowSum_append (F := f59900) (lo := 0) (n := 764) (m := 260) (A := 32083186) (B := 26043975) c59900_0 (c59900_1)

theorem h59900 : P.leaf 34 59900 = 58127161 :=
  leaf_weighted (k := 24) (d := 10) (H := 59900) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 59900) (by decide) (by decide +kernel)) sum59900

theorem h24045 : P.leaf 34 24045 = 58127161 :=
  orient24 (v := 59900) (by decide) (by decide +kernel) h59900

theorem cover24046 : P.CoversSplit 24 10 24046 0xfffffffffafaaaaafffffffffafaaaaaffff000000005050ffff000000005040ccc0ccc088808880cc00cc0088008800ccc0000040404040cc00000040004000fffffffffafaaaaa0000000000000000ffff00000000505000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(17, [1259], [1251]), (18, [879], [1210, 1264])]) (by decide +kernel)

theorem c24046_0 : P.sumLeaves 24 24623104 682 = 25253703 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24046) (lo := 0) (len := 682) (W := 25253703) check rows elimOK (by decide) (by decide) cover24046 (by decide)
  decide +kernel

theorem c24046_1 : P.sumLeaves 24 24623786 257 = 33168882 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24046) (lo := 682) (len := 257) (W := 33168882) check rows elimOK (by decide) (by decide) cover24046 (by decide)
  decide +kernel

theorem c24046_2 : P.sumLeaves 24 24624043 85 = 64998984 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24046) (lo := 939) (len := 85) (W := 64998984) check rows elimOK (by decide) (by decide) cover24046 (by decide)
  decide +kernel

theorem h24046 : P.leaf 34 24046 = 123421569 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(682, 25253703), (257, 33168882), (85, 64998984)]) (.cons c24046_0 (.cons c24046_1 (.cons c24046_2 (.nil)))) (by decide) (by decide))

theorem cover24047 : P.CoversSplit 24 10 24047 0xfffffffffafaaaaafffffffffafaaaaaffff000000005050ffff000000005040cccccccc88888888cccccccc88888888cccc000040404040cccc000040404040fffffffffafaaaaa0000000000000000ffff55550000505000330011000000100000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(17, [1259], [1251])]) (by decide +kernel)

theorem c24047_0 : P.sumLeaves 24 24624128 571 = 39179926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24047) (lo := 0) (len := 571) (W := 39179926) check rows elimOK (by decide) (by decide) cover24047 (by decide)
  decide +kernel

theorem c24047_1 : P.sumLeaves 24 24624699 319 = 54084518 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24047) (lo := 571) (len := 319) (W := 54084518) check rows elimOK (by decide) (by decide) cover24047 (by decide)
  decide +kernel

theorem c24047_2 : P.sumLeaves 24 24625018 120 = 69736622 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24047) (lo := 890) (len := 120) (W := 69736622) check rows elimOK (by decide) (by decide) cover24047 (by decide)
  decide +kernel

theorem c24047_3 : P.sumLeaves 24 24625138 14 = 45373748 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24047) (lo := 1010) (len := 14) (W := 45373748) check rows elimOK (by decide) (by decide) cover24047 (by decide)
  decide +kernel

theorem h24047 : P.leaf 34 24047 = 208374814 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(571, 39179926), (319, 54084518), (120, 69736622), (14, 45373748)]) (.cons c24047_0 (.cons c24047_1 (.cons c24047_2 (.cons c24047_3 (.nil))))) (by decide) (by decide))

theorem cover59887 : P.CoversSplit 24 10 59887 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88ccccccccc8c88888fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88ccccccccc8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 859, 865, 915, 1202, 1601]) (by decide +kernel)

noncomputable def f59887 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (61324288 + i)

theorem c59887_0 : rowSum f59887 0 226 = 55780340 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59887) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59887 (by decide)
  decide +kernel

theorem c59887_1 : rowSum f59887 226 206 = 90979020 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59887) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59887 (by decide)
  decide +kernel

theorem c59887_2 : rowSum f59887 432 300 = 199576228 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59887) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59887 (by decide)
  decide +kernel

theorem c59887_3 : rowSum f59887 732 292 = 190178783 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59887) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59887 (by decide)
  decide +kernel

theorem sum59887 : rowSum f59887 0 1024 = 536514371 :=
  rowSum_append (F := f59887) (lo := 0) (n := 226) (m := 798) (A := 55780340) (B := 480734031) c59887_0 (rowSum_append (F := f59887) (lo := 226) (n := 206) (m := 592) (A := 90979020) (B := 389755011) c59887_1 (rowSum_append (F := f59887) (lo := 432) (n := 300) (m := 292) (A := 199576228) (B := 190178783) c59887_2 (c59887_3)))

theorem h59887 : P.leaf 34 59887 = 536514371 :=
  leaf_weighted (k := 24) (d := 10) (H := 59887) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 59887) (by decide) (by decide +kernel)) sum59887

theorem h24062 : P.leaf 34 24062 = 536514371 :=
  orient24 (v := 59887) (by decide) (by decide +kernel) h59887

theorem cover59903 : P.CoversSplit 24 10 59903 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88ccccccccc8c88888fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88ccccccccc8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 859, 865, 915, 1202, 1601]) (by decide +kernel)

noncomputable def f59903 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (61340672 + i)

theorem c59903_0 : rowSum f59903 0 226 = 153468798 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59903) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59903 (by decide)
  decide +kernel

theorem c59903_1 : rowSum f59903 226 206 = 229509969 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59903) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59903 (by decide)
  decide +kernel

theorem c59903_2 : rowSum f59903 432 300 = 340963070 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59903) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59903 (by decide)
  decide +kernel

theorem c59903_3 : rowSum f59903 732 292 = 284473183 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59903) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59903 (by decide)
  decide +kernel

theorem sum59903 : rowSum f59903 0 1024 = 1008415020 :=
  rowSum_append (F := f59903) (lo := 0) (n := 226) (m := 798) (A := 153468798) (B := 854946222) c59903_0 (rowSum_append (F := f59903) (lo := 226) (n := 206) (m := 592) (A := 229509969) (B := 625436253) c59903_1 (rowSum_append (F := f59903) (lo := 432) (n := 300) (m := 292) (A := 340963070) (B := 284473183) c59903_2 (c59903_3)))

theorem h59903 : P.leaf 34 59903 = 1008415020 :=
  leaf_weighted (k := 24) (d := 10) (H := 59903) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 59903) (by decide) (by decide +kernel)) sum59903

theorem h24063 : P.leaf 34 24063 = 1008415020 :=
  orient24 (v := 59903) (by decide) (by decide +kernel) h59903

def seg : List (ℕ × ℕ) := [(24044, 24), (24045, 24), (24046, 48), (24047, 48), (24062, 24), (24063, 24)]

theorem segOK : checkSeg 16 perms 24044 24318 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24044 24318 192 55233008568 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 55233008568)
    (SegSum.cons (w := 24) h24044 (SegSum.cons (w := 24) h24045 (SegSum.cons (w := 48) h24046 (SegSum.cons (w := 48) h24047 (SegSum.cons (w := 24) h24062 (SegSum.cons (w := 24) h24063 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S75
