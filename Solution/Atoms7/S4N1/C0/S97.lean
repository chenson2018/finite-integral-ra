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

namespace RACert.S4N1.C0.S97

open RACert RACert.Problem

theorem cover24539 : P.CoversSplit 24 10 24539 0xfffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0cccccccc80008000cc00cc0080008000cccccccc80008000cc00cc0080008000fffffffff0f0a0a0fffffffff0f0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0cccccccc80008000cc00cc0080008000cc00cc0080008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [1609], [1266]), (14, [1217], [1266])]) (by decide +kernel)

noncomputable def f24539 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (25127936 + i)

theorem c24539_0 : rowSum f24539 0 417 = 7512166 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24539) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24539 (by decide)
  decide +kernel

theorem c24539_1 : rowSum f24539 417 341 = 63322806 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24539) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24539 (by decide)
  decide +kernel

theorem c24539_2 : rowSum f24539 758 266 = 62849981 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24539) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24539 (by decide)
  decide +kernel

theorem sum24539 : rowSum f24539 0 1024 = 133684953 :=
  rowSum_append (F := f24539) (lo := 0) (n := 417) (m := 607) (A := 7512166) (B := 126172787) c24539_0 (rowSum_append (F := f24539) (lo := 417) (n := 341) (m := 266) (A := 63322806) (B := 62849981) c24539_1 (c24539_2))

theorem h24539 : P.leaf 34 24539 = 133684953 :=
  leaf_weighted (k := 24) (d := 10) (H := 24539) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 24539) (by decide) (by decide +kernel)) sum24539

theorem cover24540 : P.CoversSplit 24 10 24540 0xffaaffaaf0a0a0a0ffaaffaaf0a0a0a0aaaaafaa00000000aaaaafaa00000000cc88cc8880008000cc00cc008000800088888c880000000088008c0000000000ff00ff00f000a000ff22ff22f020a020aa00af0000000000aa22af22000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 472, 473, 516, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f24540 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (25128960 + i)

theorem c24540_0 : rowSum f24540 0 949 = 83895036 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24540) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24540 (by decide)
  decide +kernel

theorem c24540_1 : rowSum f24540 949 75 = 45050776 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24540) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24540 (by decide)
  decide +kernel

theorem sum24540 : rowSum f24540 0 1024 = 128945812 :=
  rowSum_append (F := f24540) (lo := 0) (n := 949) (m := 75) (A := 83895036) (B := 45050776) c24540_0 (c24540_1)

theorem h24540 : P.leaf 34 24540 = 128945812 :=
  leaf_weighted (k := 24) (d := 10) (H := 24540) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 24540) (by decide) (by decide +kernel)) sum24540

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

theorem cover24543 : P.CoversSplit 24 10 24543 0xfffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0cccccccc80008000cc00cc0080008000cccccccc80008000cc00cc0080008000fffffffff0f0a0a0fffffffff0f0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0cccccccc80008000cc00cc0080008000cc00cc0080008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [1609], [1266]), (14, [1217], [1266])]) (by decide +kernel)

noncomputable def f24543 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (25132032 + i)

theorem c24543_0 : rowSum f24543 0 417 = 35909048 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24543) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24543 (by decide)
  decide +kernel

theorem c24543_1 : rowSum f24543 417 341 = 205216143 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24543) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24543 (by decide)
  decide +kernel

theorem c24543_2 : rowSum f24543 758 266 = 179193450 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24543) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24543 (by decide)
  decide +kernel

theorem sum24543 : rowSum f24543 0 1024 = 420318641 :=
  rowSum_append (F := f24543) (lo := 0) (n := 417) (m := 607) (A := 35909048) (B := 384409593) c24543_0 (rowSum_append (F := f24543) (lo := 417) (n := 341) (m := 266) (A := 205216143) (B := 179193450) c24543_1 (c24543_2))

theorem h24543 : P.leaf 34 24543 = 420318641 :=
  leaf_weighted (k := 24) (d := 10) (H := 24543) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 24543) (by decide) (by decide +kernel)) sum24543

theorem cover24556 : P.CoversSplit 24 10 24556 0xffffffffeaeaaaaaffffffffeaeaaaaaffffffffeaeaaaaaffffffffeaeaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888ff00ff00ea00aa000000000000000000ff00ff00ea00aa0000330033002200220000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 916, 1210, 1259, 1601]) (by decide +kernel)

theorem c24556_0 : P.sumLeaves 24 25145344 614 = 21761861 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24556) (lo := 0) (len := 614) (W := 21761861) check rows elimOK (by decide) (by decide) cover24556 (by decide)
  decide +kernel

theorem c24556_1 : P.sumLeaves 24 25145958 202 = 24802814 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24556) (lo := 614) (len := 202) (W := 24802814) check rows elimOK (by decide) (by decide) cover24556 (by decide)
  decide +kernel

theorem c24556_2 : P.sumLeaves 24 25146160 124 = 43944941 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24556) (lo := 816) (len := 124) (W := 43944941) check rows elimOK (by decide) (by decide) cover24556 (by decide)
  decide +kernel

theorem c24556_3 : P.sumLeaves 24 25146284 84 = 78388738 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24556) (lo := 940) (len := 84) (W := 78388738) check rows elimOK (by decide) (by decide) cover24556 (by decide)
  decide +kernel

theorem h24556 : P.leaf 34 24556 = 168898354 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(614, 21761861), (202, 24802814), (124, 43944941), (84, 78388738)]) (.cons c24556_0 (.cons c24556_1 (.cons c24556_2 (.cons c24556_3 (.nil))))) (by decide) (by decide))

theorem cover24557 : P.CoversSplit 24 10 24557 0xffffffffeaeaaaaaffffffffeaeaaaaaffffffffeaeaaaaaffffffffeaeaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888ff00ff00ea00aa000000000000000000ff00ff00ea00aa0000330033002200220000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24557_0 : P.sumLeaves 24 25146368 614 = 35764795 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24557) (lo := 0) (len := 614) (W := 35764795) check rows elimOK (by decide) (by decide) cover24557 (by decide)
  decide +kernel

theorem c24557_1 : P.sumLeaves 24 25146982 202 = 49301775 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24557) (lo := 614) (len := 202) (W := 49301775) check rows elimOK (by decide) (by decide) cover24557 (by decide)
  decide +kernel

theorem c24557_2 : P.sumLeaves 24 25147184 124 = 69112514 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24557) (lo := 816) (len := 124) (W := 69112514) check rows elimOK (by decide) (by decide) cover24557 (by decide)
  decide +kernel

theorem c24557_3 : P.sumLeaves 24 25147308 84 = 111306662 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24557) (lo := 940) (len := 84) (W := 111306662) check rows elimOK (by decide) (by decide) cover24557 (by decide)
  decide +kernel

theorem h24557 : P.leaf 34 24557 = 265485746 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(614, 35764795), (202, 49301775), (124, 69112514), (84, 111306662)]) (.cons c24557_0 (.cons c24557_1 (.cons c24557_2 (.cons c24557_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24539, 6), (24540, 24), (24541, 48), (24543, 24), (24556, 24), (24557, 24)]

theorem segOK : checkSeg 16 perms 24539 24558 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24539 24558 150 36548250558 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 36548250558)
    (SegSum.cons (w := 6) h24539 (SegSum.cons (w := 24) h24540 (SegSum.cons (w := 48) h24541 (SegSum.cons (w := 24) h24543 (SegSum.cons (w := 24) h24556 (SegSum.cons (w := 24) h24557 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S97
