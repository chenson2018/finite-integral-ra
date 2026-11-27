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

namespace RACert.S4N1.C0.S94

open RACert RACert.Problem

theorem cover24485 : P.CoversSplit 24 10 24485 0xffffffffeaeaa0a0ffffffffeaeaa0a0ffffffffeaeaa0a0ffffffffeaeaa0a0cccccccc88888080cccccccc88888080cccccccc88888080cccccccc88888080ff00ff00ea00a0000000000000000000ff00ff00ea00a00000330033002200200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24485_0 : P.sumLeaves 24 25072640 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24485) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover24485 (by decide)
  decide +kernel

theorem contract24485_1 : P.leaf 30 391764 = 1932 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 391764) (ss := [(8, 3, 524), (17, 0, 1259), (4, 1, 565), (3, 1, 419), (2, 1, 475), (5, 1, 615), (27, 0, 1259), (16, 1, 529), (9, 1, 566), (29, 0, 1259), (14, 0, 916), (13, 1, 480), (15, 0, 916), (18, 1, 921), (21, 1, 923), (20, 1, 929)]) (ids := [4, 8, 9, 10, 17, 21, 22, 23, 24, 26, 28, 29, 5, 20]) (cs := [1, 1, 1, 1, 2, 14, 1, 1, 3, 4, 5, 1, 0, 0, 1, 0, 1, 6, 1, 1, 15, 7, 8, 9, 10, 0, 11, 0, 12, 13]) (bs := [12, 2]) (W := 1932) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c24485_1 : P.sumLeaves 24 25072896 64 = 1932 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 391764) rows (by decide) (by decide)).symm.trans contract24485_1

theorem c24485_2 : P.sumLeaves 24 25072960 354 = 4750201 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24485) (lo := 320) (len := 354) (W := 4750201) check rows elimOK (by decide) (by decide) cover24485 (by decide)
  decide +kernel

theorem c24485_3 : P.sumLeaves 24 25073314 188 = 7221181 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24485) (lo := 674) (len := 188) (W := 7221181) check rows elimOK (by decide) (by decide) cover24485 (by decide)
  decide +kernel

theorem c24485_4 : P.sumLeaves 24 25073502 132 = 13826592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24485) (lo := 862) (len := 132) (W := 13826592) check rows elimOK (by decide) (by decide) cover24485 (by decide)
  decide +kernel

theorem c24485_5 : P.sumLeaves 24 25073634 30 = 9772222 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24485) (lo := 994) (len := 30) (W := 9772222) check rows elimOK (by decide) (by decide) cover24485 (by decide)
  decide +kernel

theorem h24485 : P.leaf 34 24485 = 35572128 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 1932), (354, 4750201), (188, 7221181), (132, 13826592), (30, 9772222)]) (.cons c24485_0 (.cons c24485_1 (.cons c24485_2 (.cons c24485_3 (.cons c24485_4 (.cons c24485_5 (.nil))))))) (by decide) (by decide))

theorem cover24487 : P.CoversSplit 24 10 24487 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cccccccc88888080cccccccc88888080cccccccc88888080fffffffffafaa0a00000000000000000fffffffffafaa0a000330033003200200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 1202, 1210, 1259, 1308, 1601]) (by decide +kernel)

theorem c24487_0 : P.sumLeaves 24 25074688 500 = 19445908 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24487) (lo := 0) (len := 500) (W := 19445908) check rows elimOK (by decide) (by decide) cover24487 (by decide)
  decide +kernel

theorem c24487_1 : P.sumLeaves 24 25075188 262 = 20661043 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24487) (lo := 500) (len := 262) (W := 20661043) check rows elimOK (by decide) (by decide) cover24487 (by decide)
  decide +kernel

theorem c24487_2 : P.sumLeaves 24 25075450 130 = 31366516 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24487) (lo := 762) (len := 130) (W := 31366516) check rows elimOK (by decide) (by decide) cover24487 (by decide)
  decide +kernel

theorem c24487_3 : P.sumLeaves 24 25075580 128 = 61079523 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24487) (lo := 892) (len := 128) (W := 61079523) check rows elimOK (by decide) (by decide) cover24487 (by decide)
  decide +kernel

theorem c24487_4 : P.sumLeaves 24 25075708 4 = 5409136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24487) (lo := 1020) (len := 4) (W := 5409136) check rows elimOK (by decide) (by decide) cover24487 (by decide)
  decide +kernel

theorem h24487 : P.leaf 34 24487 = 137962126 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(500, 19445908), (262, 20661043), (130, 31366516), (128, 61079523), (4, 5409136)]) (.cons c24487_0 (.cons c24487_1 (.cons c24487_2 (.cons c24487_3 (.cons c24487_4 (.nil)))))) (by decide) (by decide))

theorem cover24490 : P.CoversSplit 24 10 24490 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000008888000088880000880000008800000088880000000000008800000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 916, 1202, 1259, 1601]) (by decide +kernel)

theorem c24490_0 : P.sumLeaves 24 25077760 1024 = 9383092 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24490) (lo := 0) (len := 1024) (W := 9383092) check rows elimOK (by decide) (by decide) cover24490 (by decide)
  decide +kernel

theorem h24490 : P.leaf 34 24490 = 9383092 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9383092)]) (.cons c24490_0 (.nil)) (by decide) (by decide))

theorem cover24491 : P.CoversSplit 24 10 24491 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cc00cc0088008000cccccccc88888080cc00cc0088008000fffffffffafaa0a00000000000000000fffffffffafaa0a000330033003200200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 916, 1202, 1210, 1259, 1308, 1601]) (by decide +kernel)

theorem c24491_0 : P.sumLeaves 24 25078784 500 = 13501660 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24491) (lo := 0) (len := 500) (W := 13501660) check rows elimOK (by decide) (by decide) cover24491 (by decide)
  decide +kernel

theorem c24491_1 : P.sumLeaves 24 25079284 302 = 25594812 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24491) (lo := 500) (len := 302) (W := 25594812) check rows elimOK (by decide) (by decide) cover24491 (by decide)
  decide +kernel

theorem c24491_2 : P.sumLeaves 24 25079586 128 = 35605583 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24491) (lo := 802) (len := 128) (W := 35605583) check rows elimOK (by decide) (by decide) cover24491 (by decide)
  decide +kernel

theorem c24491_3 : P.sumLeaves 24 25079714 94 = 59787168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24491) (lo := 930) (len := 94) (W := 59787168) check rows elimOK (by decide) (by decide) cover24491 (by decide)
  decide +kernel

theorem h24491 : P.leaf 34 24491 = 134489223 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(500, 13501660), (302, 25594812), (128, 35605583), (94, 59787168)]) (.cons c24491_0 (.cons c24491_1 (.cons c24491_2 (.cons c24491_3 (.nil))))) (by decide) (by decide))

theorem cover24492 : P.CoversSplit 24 10 24492 0xaaaa0000aaaaa0a0aaaa0000aaaaa0a0aaaa000000000000aaaa0000000000008888000088888080888800008888808088880000000000008888000000000000aa000000aa00a0000000000000000000aa0000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 916, 1202, 1259, 1601]) (by decide +kernel)

theorem c24492_0 : P.sumLeaves 24 25079808 1017 = 20387359 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24492) (lo := 0) (len := 1017) (W := 20387359) check rows elimOK (by decide) (by decide) cover24492 (by decide)
  decide +kernel

theorem c24492_1 : P.sumLeaves 24 25080825 7 = 5032160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24492) (lo := 1017) (len := 7) (W := 5032160) check rows elimOK (by decide) (by decide) cover24492 (by decide)
  decide +kernel

theorem h24492 : P.leaf 34 24492 = 25419519 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1017, 20387359), (7, 5032160)]) (.cons c24492_0 (.cons c24492_1 (.nil))) (by decide) (by decide))

theorem cover24493 : P.CoversSplit 24 10 24493 0xffffffffeaeaa0a0ffffffffeaeaa0a0ffffffffeaeaa0a0ffffffffeaeaa0a0cccccccc88888080cccccccc88888080cccccccc88888080cccccccc88888080ff00ff00ea00a0000000000000000000ff00ff00ea00a00000330033002200200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24493_0 : P.sumLeaves 24 25080832 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24493) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover24493 (by decide)
  decide +kernel

theorem contract24493_1 : P.leaf 30 391892 = 10646 := by
  apply (leaf_contract (k := 30) (b := 17) (H := 391892) (ss := [(3, 1, 524), (17, 0, 1259), (4, 1, 536), (27, 0, 1259), (16, 1, 529), (29, 0, 1259), (14, 0, 916), (15, 0, 916), (18, 1, 921), (21, 1, 923), (20, 1, 929), (9, 8, 1021), (8, 1, 1315)]) (ids := [0, 3, 4, 5, 8, 9, 10, 11, 17, 20, 21, 22, 23, 24, 26, 28, 29]) (cs := [2, 1, 1, 3, 4, 5, 1, 1, 6, 7, 8, 9, 0, 0, 1, 0, 1, 10, 1, 1, 11, 12, 13, 14, 15, 0, 16, 0, 17, 18]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c24493_1 : P.sumLeaves 24 25081088 64 = 10646 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 391892) rows (by decide) (by decide)).symm.trans contract24493_1

theorem c24493_2 : P.sumLeaves 24 25081152 354 = 18190732 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24493) (lo := 320) (len := 354) (W := 18190732) check rows elimOK (by decide) (by decide) cover24493 (by decide)
  decide +kernel

theorem c24493_3 : P.sumLeaves 24 25081506 188 = 31360057 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24493) (lo := 674) (len := 188) (W := 31360057) check rows elimOK (by decide) (by decide) cover24493 (by decide)
  decide +kernel

theorem c24493_4 : P.sumLeaves 24 25081694 132 = 56561479 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24493) (lo := 862) (len := 132) (W := 56561479) check rows elimOK (by decide) (by decide) cover24493 (by decide)
  decide +kernel

theorem c24493_5 : P.sumLeaves 24 25081826 30 = 35071334 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24493) (lo := 994) (len := 30) (W := 35071334) check rows elimOK (by decide) (by decide) cover24493 (by decide)
  decide +kernel

theorem h24493 : P.leaf 34 24493 = 141194248 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 10646), (354, 18190732), (188, 31360057), (132, 56561479), (30, 35071334)]) (.cons c24493_0 (.cons c24493_1 (.cons c24493_2 (.cons c24493_3 (.cons c24493_4 (.cons c24493_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24485, 12), (24487, 24), (24490, 24), (24491, 48), (24492, 48), (24493, 48)]

theorem segOK : checkSeg 16 perms 24485 24494 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24485 24494 204 18416094288 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 18416094288)
    (SegSum.cons (w := 12) h24485 (SegSum.cons (w := 24) h24487 (SegSum.cons (w := 24) h24490 (SegSum.cons (w := 48) h24491 (SegSum.cons (w := 48) h24492 (SegSum.cons (w := 48) h24493 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S94
