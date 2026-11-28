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

namespace RACert.S6N0.C0.S72

open RACert RACert.Problem

theorem cover605150 : P.CoversSplit 26 10 605150 0xfffffffafffffafafffffffafffffafafffffffafffcfa00fffffffafffcfa00fffffafafffffafaffffaaaaffffaaaafffffafafffcfa00ffffaaaafffcaa00fffffffafffffafafffffffafffffafaffccffc8cc00c800ffccffc8cc00c8000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 880, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem c605150_0 : P.sumLeaves 26 619673600 426 = 125511129 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 605150) (lo := 0) (len := 426) (W := 125511129) check rows elimOK (by decide) (by decide) cover605150 (by decide)
  decide +kernel

theorem c605150_1 : P.sumLeaves 26 619674026 116 = 193010611 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 605150) (lo := 426) (len := 116) (W := 193010611) check rows elimOK (by decide) (by decide) cover605150 (by decide)
  decide +kernel

theorem c605150_2 : P.sumLeaves 26 619674142 128 = 147202971 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 605150) (lo := 542) (len := 128) (W := 147202971) check rows elimOK (by decide) (by decide) cover605150 (by decide)
  decide +kernel

theorem c605150_3 : P.sumLeaves 26 619674270 124 = 189476458 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 605150) (lo := 670) (len := 124) (W := 189476458) check rows elimOK (by decide) (by decide) cover605150 (by decide)
  decide +kernel

theorem c605150_4 : P.sumLeaves 26 619674394 116 = 197374568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 605150) (lo := 794) (len := 116) (W := 197374568) check rows elimOK (by decide) (by decide) cover605150 (by decide)
  decide +kernel

theorem c605150_5 : P.sumLeaves 26 619674510 104 = 244338936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 605150) (lo := 910) (len := 104) (W := 244338936) check rows elimOK (by decide) (by decide) cover605150 (by decide)
  decide +kernel

theorem c605150_6 : P.sumLeaves 26 619674614 10 = 65781612 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 605150) (lo := 1014) (len := 10) (W := 65781612) check rows elimOK (by decide) (by decide) cover605150 (by decide)
  decide +kernel

theorem h605150 : P.leaf 36 605150 = 1162696285 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(426, 125511129), (116, 193010611), (128, 147202971), (124, 189476458), (116, 197374568), (104, 244338936), (10, 65781612)]) (.cons c605150_0 (.cons c605150_1 (.cons c605150_2 (.cons c605150_3 (.cons c605150_4 (.cons c605150_5 (.cons c605150_6 (.nil)))))))) (by decide) (by decide))

theorem h120813 : P.leaf 36 120813 = 1162696285 :=
  orient86 (v := 605150) (by decide) (by decide +kernel) h605150

theorem cover605182 : P.CoversSplit 26 10 605182 0xfffffffafffffafafffffffafffffafafffffffafffcfac8fffffffafffcfac8fffffafafffffafafffffafafffffafafffffafafffcfac8fffffafafffcfac8fffffffafffffafafffffffafffffafaffccffc8ccccc8c8ffccffc8ccccc8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

noncomputable def f605182 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (619706368 + i)

theorem c605182_0 : rowSum f605182 0 468 = 515298051 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 605182) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover605182 (by decide)
  decide +kernel

theorem c605182_1 : rowSum f605182 468 186 = 591572490 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 605182) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover605182 (by decide)
  decide +kernel

theorem c605182_2 : rowSum f605182 654 190 = 691850371 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 605182) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover605182 (by decide)
  decide +kernel

theorem c605182_3 : rowSum f605182 844 176 = 907148623 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 605182) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover605182 (by decide)
  decide +kernel

theorem c605182_4 : rowSum f605182 1020 4 = 66225856 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 605182) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover605182 (by decide)
  decide +kernel

theorem sum605182 : rowSum f605182 0 1024 = 2772095391 :=
  rowSum_append (F := f605182) (lo := 0) (n := 468) (m := 556) (A := 515298051) (B := 2256797340) c605182_0 (rowSum_append (F := f605182) (lo := 468) (n := 186) (m := 370) (A := 591572490) (B := 1665224850) c605182_1 (rowSum_append (F := f605182) (lo := 654) (n := 190) (m := 180) (A := 691850371) (B := 973374479) c605182_2 (rowSum_append (F := f605182) (lo := 844) (n := 176) (m := 4) (A := 907148623) (B := 66225856) c605182_3 (c605182_4))))

theorem h605182 : P.leaf 36 605182 = 2772095391 :=
  leaf_weighted (k := 26) (d := 10) (H := 605182) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 605182) (by decide) (by decide +kernel)) sum605182

theorem h120815 : P.leaf 36 120815 = 2772095391 :=
  orient86 (v := 605182) (by decide) (by decide +kernel) h605182

theorem cover604543 : P.CoversSplit 26 10 604543 0xaa00aa0000000000aa00ab0000000000aa00aa0000000002aa00ab0000000002000000000000000000000a0000000000000000000000000000000a000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 629, 636, 874, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

noncomputable def f604543 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (619052032 + i)

theorem c604543_0 : rowSum f604543 0 1024 = 199612380 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 604543) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover604543 (by decide)
  decide +kernel

theorem sum604543 : rowSum f604543 0 1024 = 199612380 :=
  c604543_0

theorem h604543 : P.leaf 36 604543 = 199612380 :=
  leaf_weighted (k := 26) (d := 10) (H := 604543) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 604543) (by decide) (by decide +kernel)) sum604543

theorem h120819 : P.leaf 36 120819 = 199612380 :=
  orient86 (v := 604543) (by decide) (by decide +kernel) h604543

theorem cover485805 : P.CoversSplit 26 10 485805 0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc01cc01cc00c800cc00c800cc00cc00cc00cc00c800c800c800c800cc00cc00cc01cc01c800c800c800c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 580, 629, 636, 972, 979, 1658]) (by decide +kernel)

noncomputable def f485805 (i : ℕ) := rowWeight keep7 twice7 i * P.leaf 26 (497464320 + i)

theorem c485805_0 : rowSum f485805 0 1024 = 191796470 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 485805) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover485805 (by decide)
  decide +kernel

theorem sum485805 : rowSum f485805 0 1024 = 191796470 :=
  c485805_0

theorem h485805 : P.leaf 36 485805 = 191796470 :=
  leaf_weighted (k := 26) (d := 10) (H := 485805) (keep := keep7) (twice := twice7) rows (by decide) (by decide) (bal7) (invRow7 (H := 485805) (by decide) (by decide +kernel)) sum485805

theorem h120820 : P.leaf 36 120820 = 191796470 :=
  orient348 (v := 485805) (by decide) (by decide +kernel) h485805

theorem cover321525 : P.CoversSplit 26 10 321525 0xffffff00ffffff00fffffa00fffffa00ffffff00ffccff00fac8fa00fac8fa00ffffff00ffffff00fafafa00fafafa00ffffff00ffccff00fac8fa00fac8fa00ffffff00ffccff00fffffa00ffccfa00ffccff00ffccff00fac8fa00fac8fa00ffffff00ffccff00fafafa00fac8fa00ffccff00ffccff00fac8fa00fac8fa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 874, 881, 1658, 1665]) (by decide +kernel)

theorem c321525_0 : P.sumLeaves 26 329241600 183 = 80804623 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 321525) (lo := 0) (len := 183) (W := 80804623) check rows elimOK (by decide) (by decide) cover321525 (by decide)
  decide +kernel

theorem c321525_1 : P.sumLeaves 26 329241783 164 = 139504216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 321525) (lo := 183) (len := 164) (W := 139504216) check rows elimOK (by decide) (by decide) cover321525 (by decide)
  decide +kernel

theorem c321525_2 : P.sumLeaves 26 329241947 152 = 209421507 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 321525) (lo := 347) (len := 152) (W := 209421507) check rows elimOK (by decide) (by decide) cover321525 (by decide)
  decide +kernel

theorem c321525_3 : P.sumLeaves 26 329242099 162 = 178894840 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 321525) (lo := 499) (len := 162) (W := 178894840) check rows elimOK (by decide) (by decide) cover321525 (by decide)
  decide +kernel

theorem c321525_4 : P.sumLeaves 26 329242261 158 = 223940336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 321525) (lo := 661) (len := 158) (W := 223940336) check rows elimOK (by decide) (by decide) cover321525 (by decide)
  decide +kernel

theorem c321525_5 : P.sumLeaves 26 329242419 140 = 184420376 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 321525) (lo := 819) (len := 140) (W := 184420376) check rows elimOK (by decide) (by decide) cover321525 (by decide)
  decide +kernel

theorem c321525_6 : P.sumLeaves 26 329242559 65 = 201358713 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 321525) (lo := 959) (len := 65) (W := 201358713) check rows elimOK (by decide) (by decide) cover321525 (by decide)
  decide +kernel

theorem h321525 : P.leaf 36 321525 = 1218344611 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(183, 80804623), (164, 139504216), (152, 209421507), (162, 178894840), (158, 223940336), (140, 184420376), (65, 201358713)]) (.cons c321525_0 (.cons c321525_1 (.cons c321525_2 (.cons c321525_3 (.cons c321525_4 (.cons c321525_5 (.cons c321525_6 (.nil)))))))) (by decide) (by decide))

theorem h120821 : P.leaf 36 120821 = 1218344611 :=
  orient80 (v := 321525) (by decide) (by decide +kernel) h321525

def seg : List (ℕ × ℕ) := [(120813, 720), (120815, 360), (120819, 360), (120820, 360), (120821, 720)]

theorem segOK : checkSeg 20 perms 120813 120823 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 120813 120823 2520 2853210971880 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2853210971880)
    (SegSum.cons (w := 720) h120813 (SegSum.cons (w := 360) h120815 (SegSum.cons (w := 360) h120819 (SegSum.cons (w := 360) h120820 (SegSum.cons (w := 720) h120821 (show SegSum (P.leaf 36) [] 0 from rfl)))))) (by decide)

end RACert.S6N0.C0.S72
