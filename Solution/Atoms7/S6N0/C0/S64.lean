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

namespace RACert.S6N0.C0.S64

open RACert RACert.Problem

theorem cover370651 : P.CoversSplit 26 10 370651 0xffffff00f0f0f000fffffa00f0f0f000ffffff00f0c0f000aaaaaa00a080a000ffffff00f0f0f000aaaaaa00a0a0a000ffffff00f0c0f000aaaaaa00a080a000ffffff00f0f0f000fffffa00f0f0f000ffffff00f0c0f000aaaaaa00a080a000ffffff00f0f0f000aaaaaa00a0a0a000ffffff00f0c0f000aaaaaa00a080a000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 873, 874, 880, 881, 1658]) (by decide +kernel)

noncomputable def f370651 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (379546624 + i)

theorem c370651_0 : rowSum f370651 0 366 = 84830825 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 370651) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover370651 (by decide)
  decide +kernel

theorem c370651_1 : rowSum f370651 366 337 = 358498406 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 370651) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover370651 (by decide)
  decide +kernel

theorem c370651_2 : rowSum f370651 703 301 = 400251734 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 370651) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover370651 (by decide)
  decide +kernel

theorem c370651_3 : rowSum f370651 1004 20 = 86216356 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 370651) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover370651 (by decide)
  decide +kernel

theorem sum370651 : rowSum f370651 0 1024 = 929797321 :=
  rowSum_append (F := f370651) (lo := 0) (n := 366) (m := 658) (A := 84830825) (B := 844966496) c370651_0 (rowSum_append (F := f370651) (lo := 366) (n := 337) (m := 321) (A := 358498406) (B := 486468090) c370651_1 (rowSum_append (F := f370651) (lo := 703) (n := 301) (m := 20) (A := 400251734) (B := 86216356) c370651_2 (c370651_3)))

theorem h370651 : P.leaf 36 370651 = 929797321 :=
  leaf_weighted (k := 26) (d := 10) (H := 370651) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 370651) (by decide) (by decide +kernel)) sum370651

theorem h97276 : P.leaf 36 97276 = 929797321 :=
  orient84 (v := 370651) (by decide) (by decide +kernel) h370651

theorem cover370655 : P.CoversSplit 26 10 370655 0xffffff00ffffff00fffffa00fffffa00ffffff00ffccff00aaaaaa00aa88aa00ffffff00ffffff00aaaaaa00aaaaaa00ffffff00ffccff00aaaaaa00aa88aa00ffffff00ffffff00fffffa00fffffa00ffffff00ffccff00aaaaaa00aa88aa00ffffff00ffffff00aaaaaa00aaaaaa00ffffff00ffccff00aaaaaa00aa88aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 873, 874, 881, 1658]) (by decide +kernel)

theorem c370655_0 : P.sumLeaves 26 379550720 206 = 152632428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 370655) (lo := 0) (len := 206) (W := 152632428) check rows elimOK (by decide) (by decide) cover370655 (by decide)
  decide +kernel

theorem c370655_1 : P.sumLeaves 26 379550926 166 = 190934513 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 370655) (lo := 206) (len := 166) (W := 190934513) check rows elimOK (by decide) (by decide) cover370655 (by decide)
  decide +kernel

theorem c370655_2 : P.sumLeaves 26 379551092 132 = 422269687 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 370655) (lo := 372) (len := 132) (W := 422269687) check rows elimOK (by decide) (by decide) cover370655 (by decide)
  decide +kernel

theorem c370655_3 : P.sumLeaves 26 379551224 197 = 352602515 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 370655) (lo := 504) (len := 197) (W := 352602515) check rows elimOK (by decide) (by decide) cover370655 (by decide)
  decide +kernel

theorem c370655_4 : P.sumLeaves 26 379551421 175 = 361056054 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 370655) (lo := 701) (len := 175) (W := 361056054) check rows elimOK (by decide) (by decide) cover370655 (by decide)
  decide +kernel

theorem c370655_5 : P.sumLeaves 26 379551596 132 = 448623707 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 370655) (lo := 876) (len := 132) (W := 448623707) check rows elimOK (by decide) (by decide) cover370655 (by decide)
  decide +kernel

theorem c370655_6 : P.sumLeaves 26 379551728 16 = 176985030 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 370655) (lo := 1008) (len := 16) (W := 176985030) check rows elimOK (by decide) (by decide) cover370655 (by decide)
  decide +kernel

theorem h370655 : P.leaf 36 370655 = 2105103934 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(206, 152632428), (166, 190934513), (132, 422269687), (197, 352602515), (175, 361056054), (132, 448623707), (16, 176985030)]) (.cons c370655_0 (.cons c370655_1 (.cons c370655_2 (.cons c370655_3 (.cons c370655_4 (.cons c370655_5 (.cons c370655_6 (.nil)))))))) (by decide) (by decide))

theorem h97277 : P.leaf 36 97277 = 2105103934 :=
  orient84 (v := 370655) (by decide) (by decide +kernel) h370655

theorem cover293887 : P.CoversSplit 26 10 293887 0xffffffffffffffffffffaaaaffffaaaaffffffffccccccccfac8aa88c8c88888fffffffffffffffffafaaaaafafaaaaaffffffffccccccccfac8aa88c8c88888ffffffffffffffffffffaaaaffffaaaaffccffccccccccccfac8aa88c8c88888fffffffffffffffffafaaaaafafaaaaaffccffccccccccccfac8aa88c8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f293887 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (300940288 + i)

theorem c293887_0 : rowSum f293887 0 278 = 827595262 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 293887) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover293887 (by decide)
  decide +kernel

theorem c293887_1 : rowSum f293887 278 158 = 1333917296 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 293887) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover293887 (by decide)
  decide +kernel

theorem c293887_2 : rowSum f293887 436 407 = 1540127566 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 293887) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover293887 (by decide)
  decide +kernel

theorem c293887_3 : rowSum f293887 843 181 = 1487581321 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 293887) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover293887 (by decide)
  decide +kernel

theorem sum293887 : rowSum f293887 0 1024 = 5189221445 :=
  rowSum_append (F := f293887) (lo := 0) (n := 278) (m := 746) (A := 827595262) (B := 4361626183) c293887_0 (rowSum_append (F := f293887) (lo := 278) (n := 158) (m := 588) (A := 1333917296) (B := 3027708887) c293887_1 (rowSum_append (F := f293887) (lo := 436) (n := 407) (m := 181) (A := 1540127566) (B := 1487581321) c293887_2 (c293887_3)))

theorem h293887 : P.leaf 36 293887 = 5189221445 :=
  leaf_weighted (k := 26) (d := 10) (H := 293887) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 293887) (by decide) (by decide +kernel)) sum293887

theorem h97279 : P.leaf 36 97279 = 5189221445 :=
  orient80 (v := 293887) (by decide) (by decide +kernel) h293887

theorem cover97783 : P.CoversSplit 26 10 97783 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h97783 : P.leaf 36 97783 = 10320176 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 97783) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 97783) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover97783 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover97787 : P.CoversSplit 26 10 97787 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h97787 : P.leaf 36 97787 = 8219805 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 97787) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 97787) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover97787 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover97788 : P.CoversSplit 26 10 97788 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h97788 : P.leaf 36 97788 = 13088244 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 97788) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 97788) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover97788 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover97789 : P.CoversSplit 26 10 97789 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h97789 : P.leaf 36 97789 = 13921772 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 97789) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 97789) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover97789 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover97791 : P.CoversSplit 26 10 97791 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h97791 : P.leaf 36 97791 = 15556414 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 97791) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 97791) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover97791 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover98035 : P.CoversSplit 26 10 98035 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem h98035 : P.leaf 36 98035 = 57646968 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 98035) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 98035) (weight := fun _ => 1) (xs := [654, 655, 686, 687, 910, 911, 926, 927, 942, 943, 958, 959, 974, 975, 990, 991, 1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover98035 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover114611 : P.CoversSplit 26 10 114611 0xcc00cc0000000000cc00c8000000000000000000000000000000000000000000cc00c00000000000880080000000000000000000000000000000000000000000cc00cc0000000000cc00c8000000000000000000000000000000000000000000cc00c00000000000880080000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 930, 1315, 1658]) (by decide +kernel)

noncomputable def f114611 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (117361664 + i)

theorem c114611_0 : rowSum f114611 0 1024 = 157509264 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 114611) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover114611 (by decide)
  decide +kernel

theorem sum114611 : rowSum f114611 0 1024 = 157509264 :=
  c114611_0

theorem h114611 : P.leaf 36 114611 = 157509264 :=
  leaf_weighted (k := 26) (d := 10) (H := 114611) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 114611) (by decide) (by decide +kernel)) sum114611

theorem h98038 : P.leaf 36 98038 = 157509264 :=
  orient72 (v := 114611) (by decide) (by decide +kernel) h114611

theorem cover114615 : P.CoversSplit 26 10 114615 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c00000000000880080000000000000000000000000000000000000000000cc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c00000000000880080000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 930, 1315, 1658]) (by decide +kernel)

noncomputable def f114615 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (117365760 + i)

theorem c114615_0 : rowSum f114615 0 1024 = 241084462 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 114615) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover114615 (by decide)
  decide +kernel

theorem sum114615 : rowSum f114615 0 1024 = 241084462 :=
  c114615_0

theorem h114615 : P.leaf 36 114615 = 241084462 :=
  leaf_weighted (k := 26) (d := 10) (H := 114615) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 114615) (by decide) (by decide +kernel)) sum114615

theorem h98039 : P.leaf 36 98039 = 241084462 :=
  orient72 (v := 114615) (by decide) (by decide +kernel) h114615

theorem cover612845 : P.CoversSplit 26 10 612845 0xf0f0f0f000000000f0f0f0f400000000f0f0f0f000000020f0f0f0f400000020000000000000000000005050000000000000000000000000000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 629, 636, 922, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

noncomputable def f612845 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (627553280 + i)

theorem c612845_0 : rowSum f612845 0 1024 = 17088193 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 612845) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover612845 (by decide)
  decide +kernel

theorem sum612845 : rowSum f612845 0 1024 = 17088193 :=
  c612845_0

theorem h612845 : P.leaf 36 612845 = 17088193 :=
  leaf_weighted (k := 26) (d := 10) (H := 612845) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 612845) (by decide) (by decide +kernel)) sum612845

theorem h98040 : P.leaf 36 98040 = 17088193 :=
  orient348 (v := 612845) (by decide) (by decide +kernel) h612845

theorem cover311155 : P.CoversSplit 26 10 311155 0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000aa00af00aa00af0000000a0000000a0000000000000000000000000000000000aa00aa00aa22aa22000000000000000000000000220022000000000000000000aa00af00aa22af2300000a0000000a0200000000220023000000000000000200 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 930]) (by decide +kernel)

noncomputable def f311155 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (318622720 + i)

theorem c311155_0 : rowSum f311155 0 1024 = 133308928 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 311155) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover311155 (by decide)
  decide +kernel

theorem sum311155 : rowSum f311155 0 1024 = 133308928 :=
  c311155_0

theorem h311155 : P.leaf 36 311155 = 133308928 :=
  leaf_weighted (k := 26) (d := 10) (H := 311155) (keep := keep8) (twice := twice8) rows (by decide) (by decide) (bal8) (invRow8 (H := 311155) (by decide) (by decide +kernel)) sum311155

theorem h98041 : P.leaf 36 98041 = 133308928 :=
  orient6 (v := 311155) (by decide) (by decide +kernel) h311155

def seg : List (ℕ × ℕ) := [(97276, 360), (97277, 720), (97279, 360), (97783, 90), (97787, 90), (97788, 180), (97789, 360), (97791, 180), (98035, 720), (98038, 360), (98039, 360), (98040, 360), (98041, 360)]

theorem segOK : checkSeg 20 perms 97276 98042 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 97276 98042 4500 3969500584770 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3969500584770)
    (SegSum.cons (w := 360) h97276 (SegSum.cons (w := 720) h97277 (SegSum.cons (w := 360) h97279 (SegSum.cons (w := 90) h97783 (SegSum.cons (w := 90) h97787 (SegSum.cons (w := 180) h97788 (SegSum.cons (w := 360) h97789 (SegSum.cons (w := 180) h97791 (SegSum.cons (w := 720) h98035 (SegSum.cons (w := 360) h98038 (SegSum.cons (w := 360) h98039 (SegSum.cons (w := 360) h98040 (SegSum.cons (w := 360) h98041 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))) (by decide)

end RACert.S6N0.C0.S64
