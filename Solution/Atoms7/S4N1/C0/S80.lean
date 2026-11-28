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

namespace RACert.S4N1.C0.S80

open RACert RACert.Problem

theorem cover24510 : P.CoversSplit 24 10 24510 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cccccccc88888080cccccccc88888080cccccccc88888080fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cccccccc8888808000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 916, 1202, 1210, 1259, 1308, 1601]) (by decide +kernel)

theorem c24510_0 : P.sumLeaves 24 25098240 337 = 18158578 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24510) (lo := 0) (len := 337) (W := 18158578) check rows elimOK (by decide) (by decide) cover24510 (by decide)
  decide +kernel

theorem c24510_1 : P.sumLeaves 24 25098577 128 = 51981538 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24510) (lo := 337) (len := 128) (W := 51981538) check rows elimOK (by decide) (by decide) cover24510 (by decide)
  decide +kernel

theorem c24510_2 : P.sumLeaves 24 25098705 213 = 55372197 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24510) (lo := 465) (len := 213) (W := 55372197) check rows elimOK (by decide) (by decide) cover24510 (by decide)
  decide +kernel

theorem c24510_3 : P.sumLeaves 24 25098918 182 = 72009035 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24510) (lo := 678) (len := 182) (W := 72009035) check rows elimOK (by decide) (by decide) cover24510 (by decide)
  decide +kernel

theorem c24510_4 : P.sumLeaves 24 25099100 128 = 154318211 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24510) (lo := 860) (len := 128) (W := 154318211) check rows elimOK (by decide) (by decide) cover24510 (by decide)
  decide +kernel

theorem c24510_5 : P.sumLeaves 24 25099228 36 = 96561020 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24510) (lo := 988) (len := 36) (W := 96561020) check rows elimOK (by decide) (by decide) cover24510 (by decide)
  decide +kernel

theorem h24510 : P.leaf 34 24510 = 448400579 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(337, 18158578), (128, 51981538), (213, 55372197), (182, 72009035), (128, 154318211), (36, 96561020)]) (.cons c24510_0 (.cons c24510_1 (.cons c24510_2 (.cons c24510_3 (.cons c24510_4 (.cons c24510_5 (.nil))))))) (by decide) (by decide))

theorem cover24511 : P.CoversSplit 24 10 24511 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cccccccc88888080cccccccc88888080cccccccc88888080fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cccccccc8888808000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 916, 1202, 1210, 1259, 1308, 1601]) (by decide +kernel)

theorem c24511_0 : P.sumLeaves 24 25099264 337 = 33349657 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24511) (lo := 0) (len := 337) (W := 33349657) check rows elimOK (by decide) (by decide) cover24511 (by decide)
  decide +kernel

theorem c24511_1 : P.sumLeaves 24 25099601 128 = 84207562 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24511) (lo := 337) (len := 128) (W := 84207562) check rows elimOK (by decide) (by decide) cover24511 (by decide)
  decide +kernel

theorem c24511_2 : P.sumLeaves 24 25099729 213 = 82767012 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24511) (lo := 465) (len := 213) (W := 82767012) check rows elimOK (by decide) (by decide) cover24511 (by decide)
  decide +kernel

theorem c24511_3 : P.sumLeaves 24 25099942 182 = 130285849 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24511) (lo := 678) (len := 182) (W := 130285849) check rows elimOK (by decide) (by decide) cover24511 (by decide)
  decide +kernel

theorem c24511_4 : P.sumLeaves 24 25100124 128 = 242909644 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24511) (lo := 860) (len := 128) (W := 242909644) check rows elimOK (by decide) (by decide) cover24511 (by decide)
  decide +kernel

theorem c24511_5 : P.sumLeaves 24 25100252 36 = 131741622 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24511) (lo := 988) (len := 36) (W := 131741622) check rows elimOK (by decide) (by decide) cover24511 (by decide)
  decide +kernel

theorem h24511 : P.leaf 34 24511 = 705261346 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(337, 33349657), (128, 84207562), (213, 82767012), (182, 130285849), (128, 242909644), (36, 131741622)]) (.cons c24511_0 (.cons c24511_1 (.cons c24511_2 (.cons c24511_3 (.cons c24511_4 (.cons c24511_5 (.nil))))))) (by decide) (by decide))

theorem cover60255 : P.CoversSplit 24 10 60255 0xfffffffffafa0000fffffffffafa0000ffffffffc8000000ffffffffc8000000ffccffccfac800000000000000000000ffccffccc80000000000000000000000fffffffffafa0000fffffffffafa0000ffffffffc8000000ffffffffc8000000a080a080a08000000000000000000000a080a080000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 523, 565, 572, 866, 908, 1202, 1308, 1601]) (by decide +kernel)

noncomputable def f60255 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (61701120 + i)

theorem c60255_0 : rowSum f60255 0 467 = 27472802 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60255) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover60255 (by decide)
  decide +kernel

theorem c60255_1 : rowSum f60255 467 490 = 84020119 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60255) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover60255 (by decide)
  decide +kernel

theorem c60255_2 : rowSum f60255 957 67 = 22192032 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60255) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover60255 (by decide)
  decide +kernel

theorem sum60255 : rowSum f60255 0 1024 = 133684953 :=
  rowSum_append (F := f60255) (lo := 0) (n := 467) (m := 557) (A := 27472802) (B := 106212151) c60255_0 (rowSum_append (F := f60255) (lo := 467) (n := 490) (m := 67) (A := 84020119) (B := 22192032) c60255_1 (c60255_2))

theorem h60255 : P.leaf 34 60255 = 133684953 :=
  leaf_weighted (k := 24) (d := 10) (H := 60255) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 60255) (by decide) (by decide +kernel)) sum60255

theorem h24539 : P.leaf 34 24539 = 133684953 :=
  orient5 (v := 60255) (by decide) (by decide +kernel) h60255

theorem cover24540 : P.CoversSplit 24 10 24540 0xffaaffaaf0a0a0a0ffaaffaaf0a0a0a0aaaaafaa00000000aaaaafaa00000000cc88cc8880008000cc00cc008000800088888c880000000088008c0000000000ff00ff00f000a000ff22ff22f020a020aa00af0000000000aa22af22000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 472, 473, 516, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

def k24540 : ℕ := 0x8aef000000000000ffff8aef0000000000000000000000000000000000000000ffffffff8aef0000ffffffffffff8aef00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8aef0000ffffffffffff8aef
def t24540 : ℕ := 0x8ae000000000000ffff08ae0000000000000000000000000000000000000000ffffffff08ae0000ffffffffffff08ae00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff0000000008ae000000000000ffff08ae

noncomputable def f24540 (i : ℕ) := rowWeight k24540 t24540 i * P.leaf 24 (25128960 + i)

theorem c24540_0 : rowSum f24540 0 256 = 0 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24540) (keep := k24540) (twice := t24540) check rows elimOK (by decide) (by decide) cover24540 (by decide)
  decide +kernel

theorem contract24540_1 : P.leaf 30 392644 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (20, 1, 531), (21, 1, 537)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24540_1 : rowSum f24540 256 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k24540) (twice := t24540) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 392644) rows (by decide) (by decide)).symm.trans contract24540_1)

theorem contract24540_2 : P.leaf 30 392645 = 0 := by
  exact leaf_contract_zero (ss := [(29, 1, 916), (8, 0, 1266), (20, 1, 531), (21, 1, 537)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24540_2 : rowSum f24540 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k24540) (twice := t24540) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 392645) rows (by decide) (by decide)).symm.trans contract24540_2)

theorem c24540_3 : rowSum f24540 384 633 = 120358444 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24540) (keep := k24540) (twice := t24540) check rows elimOK (by decide) (by decide) cover24540 (by decide)
  decide +kernel

theorem c24540_4 : rowSum f24540 1017 7 = 8587368 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24540) (keep := k24540) (twice := t24540) check rows elimOK (by decide) (by decide) cover24540 (by decide)
  decide +kernel

theorem sum24540 : rowSum f24540 0 1024 = 128945812 :=
  rowSum_append (F := f24540) (lo := 0) (n := 256) (m := 768) (A := 0) (B := 128945812) c24540_0 (rowSum_append (F := f24540) (lo := 256) (n := 64) (m := 704) (A := 0) (B := 128945812) c24540_1 (rowSum_append (F := f24540) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 128945812) c24540_2 (rowSum_append (F := f24540) (lo := 384) (n := 633) (m := 7) (A := 120358444) (B := 8587368) c24540_3 (c24540_4))))

theorem h24540 : P.leaf 34 24540 = 128945812 :=
  leaf_weighted (k := 24) (d := 10) (H := 24540) (keep := k24540) (twice := t24540) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow5 (H := 24540) (by decide) (by decide +kernel)) sum24540

theorem cover24541 : P.CoversSplit 24 10 24541 0xfffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0cccccccc80008000cc00cc0080008000cccccccc80008000cc00cc0080008000ff00ff00f000a000ff33ff33f030a020ff00ff00a000a000ff33ff33a020a0200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 916, 1202, 1210, 1259, 1601]) (ps := [(14, [1217], [916, 1266])]) (by decide +kernel)

theorem c24541_0 : P.sumLeaves 24 25129984 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24541) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover24541 (by decide)
  decide +kernel

theorem contract24541_1 : P.leaf 30 392660 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (14, 0, 1266), (5, 1, 433), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24541_1 : P.sumLeaves 24 25130240 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 392660) rows (by decide) (by decide)).symm.trans contract24541_1

theorem contract24541_2 : P.leaf 30 392661 = 0 := by
  exact leaf_contract_zero (ss := [(29, 1, 916), (8, 0, 1266), (14, 0, 1266), (5, 1, 433), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24541_2 : P.sumLeaves 24 25130304 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 392661) rows (by decide) (by decide)).symm.trans contract24541_2

theorem c24541_3 : P.sumLeaves 24 25130368 355 = 59829198 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24541) (lo := 384) (len := 355) (W := 59829198) check rows elimOK (by decide) (by decide) cover24541 (by decide)
  decide +kernel

theorem c24541_4 : P.sumLeaves 24 25130723 150 = 57740028 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24541) (lo := 739) (len := 150) (W := 57740028) check rows elimOK (by decide) (by decide) cover24541 (by decide)
  decide +kernel

theorem c24541_5 : P.sumLeaves 24 25130873 135 = 135317765 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24541) (lo := 889) (len := 135) (W := 135317765) check rows elimOK (by decide) (by decide) cover24541 (by decide)
  decide +kernel

theorem h24541 : P.leaf 34 24541 = 252886991 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (355, 59829198), (150, 57740028), (135, 135317765)]) (.cons c24541_0 (.cons c24541_1 (.cons c24541_2 (.cons c24541_3 (.cons c24541_4 (.cons c24541_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24510, 48), (24511, 48), (24539, 6), (24540, 24), (24541, 48)]

theorem segOK : checkSeg 16 perms 24510 24543 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24510 24543 174 71411157174 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 71411157174)
    (SegSum.cons (w := 48) h24510 (SegSum.cons (w := 48) h24511 (SegSum.cons (w := 6) h24539 (SegSum.cons (w := 24) h24540 (SegSum.cons (w := 48) h24541 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S80
