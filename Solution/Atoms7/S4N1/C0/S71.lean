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

namespace RACert.S4N1.C0.S71

open RACert RACert.Problem

theorem cover23871 : P.CoversSplit 24 10 23871 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000cccccccc88888080cc00cc0088008000cccccccc88888080cc00000000000000fffffffffafaa0a0ffff0000fafa0000fffffffffafaa0a0ffff0000000000000000000000000000cc0000008800000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 572, 858, 865, 1202, 1210, 1251, 1259, 1264, 1308, 1601, 1609]) (by decide +kernel)

theorem c23871_0 : P.sumLeaves 24 24443904 446 = 22394338 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23871) (lo := 0) (len := 446) (W := 22394338) check rows elimOK (by decide) (by decide) cover23871 (by decide)
  decide +kernel

theorem c23871_1 : P.sumLeaves 24 24444350 297 = 41670895 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23871) (lo := 446) (len := 297) (W := 41670895) check rows elimOK (by decide) (by decide) cover23871 (by decide)
  decide +kernel

theorem c23871_2 : P.sumLeaves 24 24444647 188 = 71389445 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23871) (lo := 743) (len := 188) (W := 71389445) check rows elimOK (by decide) (by decide) cover23871 (by decide)
  decide +kernel

theorem c23871_3 : P.sumLeaves 24 24444835 93 = 109212459 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23871) (lo := 931) (len := 93) (W := 109212459) check rows elimOK (by decide) (by decide) cover23871 (by decide)
  decide +kernel

theorem h23871 : P.leaf 34 23871 = 244667137 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(446, 22394338), (297, 41670895), (188, 71389445), (93, 109212459)]) (.cons c23871_0 (.cons c23871_1 (.cons c23871_2 (.cons c23871_3 (.nil))))) (by decide) (by decide))

theorem cover28012 : P.CoversSplit 24 10 28012 0xcc00cc00c80080000000000000000000cc000000000000000000000000000000dd0cdd0cc80080000000000000000000dd0c0000000000000000000000000000cc00cc00c80080000000000000000000cc0004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 572, 858, 865, 915, 1210, 1601]) (by decide +kernel)

noncomputable def f28012 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (28684288 + i)

theorem c28012_0 : rowSum f28012 0 1024 = 5542664 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28012) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28012 (by decide)
  decide +kernel

theorem sum28012 : rowSum f28012 0 1024 = 5542664 :=
  c28012_0

theorem h28012 : P.leaf 34 28012 = 5542664 :=
  leaf_weighted (k := 24) (d := 10) (H := 28012) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 28012) (by decide) (by decide +kernel)) sum28012

theorem h23916 : P.leaf 34 23916 = 5542664 :=
  orient5 (v := 28012) (by decide) (by decide +kernel) h28012

theorem cover28013 : P.CoversSplit 24 10 28013 0xcc00cc00c80080000000000000000000cc000000000000000000000000000000cc00cc00c80080000000000000000000cc000000000000000000000000000000cc00cc00c80080000000000000000000cc0004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 858, 865, 1202, 1210, 1601]) (by decide +kernel)

noncomputable def f28013 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (28685312 + i)

theorem c28013_0 : rowSum f28013 0 1024 = 8933112 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28013) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28013 (by decide)
  decide +kernel

theorem sum28013 : rowSum f28013 0 1024 = 8933112 :=
  c28013_0

theorem h28013 : P.leaf 34 28013 = 8933112 :=
  leaf_weighted (k := 24) (d := 10) (H := 28013) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 28013) (by decide) (by decide +kernel)) sum28013

theorem h23917 : P.leaf 34 23917 = 8933112 :=
  orient5 (v := 28013) (by decide) (by decide +kernel) h28013

theorem cover23918 : P.CoversSplit 24 10 23918 0xccccccccc8c888880000000000000000cccc0000000040400000000000000000ccc0ccc088808880cc00cc0088008800ccc0000040404040cc00000040004000ccccccccc8c888880000000000000000cccc00000000404000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 572, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(18, [879], [1210])]) (by decide +kernel)

theorem c23918_0 : P.sumLeaves 24 24492032 979 = 18393236 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23918) (lo := 0) (len := 979) (W := 18393236) check rows elimOK (by decide) (by decide) cover23918 (by decide)
  decide +kernel

theorem c23918_1 : P.sumLeaves 24 24493011 45 = 17197182 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23918) (lo := 979) (len := 45) (W := 17197182) check rows elimOK (by decide) (by decide) cover23918 (by decide)
  decide +kernel

theorem h23918 : P.leaf 34 23918 = 35590418 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(979, 18393236), (45, 17197182)]) (.cons c23918_0 (.cons c23918_1 (.nil))) (by decide) (by decide))

theorem cover23919 : P.CoversSplit 24 10 23919 0xccccccccc8c888880000000000000000cccc0000000040400000000000000000cccccccc888888880000000000000000cccc0000404040400000000000000000ccccccccc8c888880000000000000000cccc44440000404000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 572, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c23919_0 : P.sumLeaves 24 24493056 994 = 39960692 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23919) (lo := 0) (len := 994) (W := 39960692) check rows elimOK (by decide) (by decide) cover23919 (by decide)
  decide +kernel

theorem c23919_1 : P.sumLeaves 24 24494050 30 = 18146182 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23919) (lo := 994) (len := 30) (W := 18146182) check rows elimOK (by decide) (by decide) cover23919 (by decide)
  decide +kernel

theorem h23919 : P.leaf 34 23919 = 58106874 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(994, 39960692), (30, 18146182)]) (.cons c23919_0 (.cons c23919_1 (.nil))) (by decide) (by decide))

theorem cover28540 : P.CoversSplit 24 10 28540 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac80000000000000000ffccffccfac8fac80000000000000000fffffffffafafafaffff0000fafa0000ffffffff00000000ffff00000000000000000000000000000000000000000000ffcc0000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 1264, 1308, 1601, 1609]) (by decide +kernel)

noncomputable def f28540 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (29224960 + i)

theorem c28540_0 : rowSum f28540 0 603 = 46181966 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28540) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28540 (by decide)
  decide +kernel

theorem c28540_1 : rowSum f28540 603 272 = 52091951 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28540) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28540 (by decide)
  decide +kernel

theorem c28540_2 : rowSum f28540 875 149 = 155905340 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28540) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28540 (by decide)
  decide +kernel

theorem sum28540 : rowSum f28540 0 1024 = 254179257 :=
  rowSum_append (F := f28540) (lo := 0) (n := 603) (m := 421) (A := 46181966) (B := 207997291) c28540_0 (rowSum_append (F := f28540) (lo := 603) (n := 272) (m := 149) (A := 52091951) (B := 155905340) c28540_1 (c28540_2))

theorem h28540 : P.leaf 34 28540 = 254179257 :=
  leaf_weighted (k := 24) (d := 10) (H := 28540) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 28540) (by decide) (by decide +kernel)) sum28540

theorem h23934 : P.leaf 34 23934 = 254179257 :=
  orient5 (v := 28540) (by decide) (by decide +kernel) h28540

theorem cover28541 : P.CoversSplit 24 10 28541 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac80000000000000000ffccffccfac8fac80000000000000000fffffffffafafafaffff0000fafa0000ffffffff00000000ffff00000000000000000000000000000000000000000000ffcc0000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 1202, 1210, 1259, 1264, 1308, 1601, 1609]) (by decide +kernel)

noncomputable def f28541 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (29225984 + i)

theorem c28541_0 : rowSum f28541 0 603 = 76580658 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28541) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28541 (by decide)
  decide +kernel

theorem c28541_1 : rowSum f28541 603 272 = 93922131 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28541) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28541 (by decide)
  decide +kernel

theorem c28541_2 : rowSum f28541 875 149 = 232923266 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28541) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28541 (by decide)
  decide +kernel

theorem sum28541 : rowSum f28541 0 1024 = 403426055 :=
  rowSum_append (F := f28541) (lo := 0) (n := 603) (m := 421) (A := 76580658) (B := 326845397) c28541_0 (rowSum_append (F := f28541) (lo := 603) (n := 272) (m := 149) (A := 93922131) (B := 232923266) c28541_1 (c28541_2))

theorem h28541 : P.leaf 34 28541 = 403426055 :=
  leaf_weighted (k := 24) (d := 10) (H := 28541) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 28541) (by decide) (by decide +kernel)) sum28541

theorem h23935 : P.leaf 34 23935 = 403426055 :=
  orient5 (v := 28541) (by decide) (by decide +kernel) h28541

theorem cover23972 : P.CoversSplit 24 10 23972 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h23972 : P.leaf 34 23972 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 23972) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 23972) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover23972 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover59580 : P.CoversSplit 24 10 59580 0x80008000c000800080008000c000800080008000400000008000800040000000a000a000f000a00080008000c0008000a000a00040000000800080004000000080008000c000800080008000c0008000800080004000000080008000400000002000200020002000000000000000000020002000100000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 472, 473, 859, 915, 1202, 1601]) (ps := [(12, [859, 915], [859, 915])]) (by decide +kernel)

noncomputable def f59580 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (61009920 + i)

theorem c59580_0 : rowSum f59580 0 1024 = 3875868 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59580) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59580 (by decide)
  decide +kernel

theorem sum59580 : rowSum f59580 0 1024 = 3875868 :=
  c59580_0

theorem h59580 : P.leaf 34 59580 = 3875868 :=
  leaf_weighted (k := 24) (d := 10) (H := 59580) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 59580) (by decide) (by decide +kernel)) sum59580

theorem h23973 : P.leaf 34 23973 = 3875868 :=
  orient24 (v := 59580) (by decide) (by decide +kernel) h59580

theorem cover58684 : P.CoversSplit 24 10 58684 0xf000f000f0000000f000f000f0000000f000f00000000000f000f00000000000f000f000f00000000000000000000000f000f000000000000000000000000000f000f000f0000000f000f000f0000000f000f00000000000f000f000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 472, 529, 860, 915, 1202, 1601]) (by decide +kernel)

noncomputable def f58684 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (60092416 + i)

theorem c58684_0 : rowSum f58684 0 1024 = 11127630 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58684) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58684 (by decide)
  decide +kernel

theorem sum58684 : rowSum f58684 0 1024 = 11127630 :=
  c58684_0

theorem h58684 : P.leaf 34 58684 = 11127630 :=
  leaf_weighted (k := 24) (d := 10) (H := 58684) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 58684) (by decide) (by decide +kernel)) sum58684

theorem h23974 : P.leaf 34 23974 = 11127630 :=
  orient5 (v := 58684) (by decide) (by decide +kernel) h58684

theorem cover23975 : P.CoversSplit 24 10 23975 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000008888000088880000888800008888000088880000000000008888000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 517, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c23975_0 : P.sumLeaves 24 24550400 1021 = 22883818 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23975) (lo := 0) (len := 1021) (W := 22883818) check rows elimOK (by decide) (by decide) cover23975 (by decide)
  decide +kernel

theorem c23975_1 : P.sumLeaves 24 24551421 3 = 2886040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23975) (lo := 1021) (len := 3) (W := 2886040) check rows elimOK (by decide) (by decide) cover23975 (by decide)
  decide +kernel

theorem h23975 : P.leaf 34 23975 = 25769858 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 22883818), (3, 2886040)]) (.cons c23975_0 (.cons c23975_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(23871, 48), (23916, 24), (23917, 24), (23918, 48), (23919, 48), (23934, 24), (23935, 24), (23972, 12), (23973, 24), (23974, 24), (23975, 48)]

theorem segOK : checkSeg 16 perms 23871 23976 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 23871 23976 348 33968475840 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 33968475840)
    (SegSum.cons (w := 48) h23871 (SegSum.cons (w := 24) h23916 (SegSum.cons (w := 24) h23917 (SegSum.cons (w := 48) h23918 (SegSum.cons (w := 48) h23919 (SegSum.cons (w := 24) h23934 (SegSum.cons (w := 24) h23935 (SegSum.cons (w := 12) h23972 (SegSum.cons (w := 24) h23973 (SegSum.cons (w := 24) h23974 (SegSum.cons (w := 48) h23975 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))) (by decide)

end RACert.S4N1.C0.S71
