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

namespace RACert.S4N1.C0.S32

open RACert RACert.Problem

theorem cover25955 : P.CoversSplit 24 10 25955 0xc0000000c00000000000000000000000c0000000000000000000000000000000c0000000c00000000000000000000000c0000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000003000000030000000000000000000000030000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [472, 515, 522, 572, 858, 865, 1202, 1210]) (by decide +kernel)

theorem h25955 : P.leaf 34 25955 = 1940589 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 25955) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 25955) (weight := fun _ => 1) (xs := [52, 53, 148, 149, 180, 181, 382, 383, 478, 479, 510, 511, 638, 639, 734, 735, 766, 767, 894, 895, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover25955 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6004 : P.leaf 34 6004 = 1940589 :=
  orient32 (v := 25955) (by decide) (by decide +kernel) h25955

theorem cover19247 : P.CoversSplit 24 10 19247 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffff000000000000ffff000000000000cccccccc888880800000000000000000cccc000000000000000000000000000088888888888880800000000000000000888800000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 529, 572, 859, 915, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c19247_0 : P.sumLeaves 24 19708928 930 = 7495162 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19247) (lo := 0) (len := 930) (W := 7495162) check rows elimOK (by decide) (by decide) cover19247 (by decide)
  decide +kernel

theorem c19247_1 : P.sumLeaves 24 19709858 94 = 15987334 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19247) (lo := 930) (len := 94) (W := 15987334) check rows elimOK (by decide) (by decide) cover19247 (by decide)
  decide +kernel

theorem h19247 : P.leaf 34 19247 = 23482496 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(930, 7495162), (94, 15987334)]) (.cons c19247_0 (.cons c19247_1 (.nil))) (by decide) (by decide))

theorem h6005 : P.leaf 34 6005 = 23482496 :=
  orient4 (v := 19247) (by decide) (by decide +kernel) h19247

theorem cover19371 : P.CoversSplit 24 10 19371 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffff000000000000ffff000000000000cccccccc88888080cc00cc0088008000cccc000000000000cc00000000000000ffffffffaaaaa0a00000000000000000ffff55550000000033330000000000000000000000000000330000002200000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 859, 915, 916, 1202, 1210, 1259, 1308, 1601]) (ps := [(17, [1251], [1259]), (18, [923], [1264])]) (by decide +kernel)

theorem c19371_0 : P.sumLeaves 24 19835904 671 = 4971190 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19371) (lo := 0) (len := 671) (W := 4971190) check rows elimOK (by decide) (by decide) cover19371 (by decide)
  decide +kernel

theorem c19371_1 : P.sumLeaves 24 19836575 278 = 10134999 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19371) (lo := 671) (len := 278) (W := 10134999) check rows elimOK (by decide) (by decide) cover19371 (by decide)
  decide +kernel

theorem c19371_2 : P.sumLeaves 24 19836853 75 = 14861312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19371) (lo := 949) (len := 75) (W := 14861312) check rows elimOK (by decide) (by decide) cover19371 (by decide)
  decide +kernel

theorem h19371 : P.leaf 34 19371 = 29967501 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(671, 4971190), (278, 10134999), (75, 14861312)]) (.cons c19371_0 (.cons c19371_1 (.cons c19371_2 (.nil)))) (by decide) (by decide))

theorem h6006 : P.leaf 34 6006 = 29967501 :=
  orient24 (v := 19371) (by decide) (by decide +kernel) h19371

theorem cover19263 : P.CoversSplit 24 10 19263 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffffffff0000a0a0ffffffff0000a0a0cccccccc888880800000000000000000cccccccc000080800000000000000000ffffffffaaaaa0a0ffff0000aaaa0000ffffffff00000000ffff0000000000000000000000000000000000000000000000000000808000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 529, 572, 859, 866, 915, 1202, 1217, 1259, 1264, 1308, 1601, 1609]) (by decide +kernel)

theorem c19263_0 : P.sumLeaves 24 19725312 490 = 6765045 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19263) (lo := 0) (len := 490) (W := 6765045) check rows elimOK (by decide) (by decide) cover19263 (by decide)
  decide +kernel

theorem c19263_1 : P.sumLeaves 24 19725802 340 = 14993201 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19263) (lo := 490) (len := 340) (W := 14993201) check rows elimOK (by decide) (by decide) cover19263 (by decide)
  decide +kernel

theorem c19263_2 : P.sumLeaves 24 19726142 164 = 39601287 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19263) (lo := 830) (len := 164) (W := 39601287) check rows elimOK (by decide) (by decide) cover19263 (by decide)
  decide +kernel

theorem c19263_3 : P.sumLeaves 24 19726306 30 = 24790900 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19263) (lo := 994) (len := 30) (W := 24790900) check rows elimOK (by decide) (by decide) cover19263 (by decide)
  decide +kernel

theorem h19263 : P.leaf 34 19263 = 86150433 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(490, 6765045), (340, 14993201), (164, 39601287), (30, 24790900)]) (.cons c19263_0 (.cons c19263_1 (.cons c19263_2 (.cons c19263_3 (.nil))))) (by decide) (by decide))

theorem h6007 : P.leaf 34 6007 = 86150433 :=
  orient4 (v := 19263) (by decide) (by decide +kernel) h19263

theorem cover19278 : P.CoversSplit 24 10 19278 0xffffffff00000000ffffffff0000000000000000000000000000000000000000cccccccc0000000000000000000000000000000000000000000000000000000088aa88aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 523, 565, 572, 879, 915, 1202, 1259, 1601]) (by decide +kernel)

theorem c19278_0 : P.sumLeaves 24 19740672 1024 = 3280476 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19278) (lo := 0) (len := 1024) (W := 3280476) check rows elimOK (by decide) (by decide) cover19278 (by decide)
  decide +kernel

theorem h19278 : P.leaf 34 19278 = 3280476 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3280476)]) (.cons c19278_0 (.nil)) (by decide) (by decide))

theorem h6008 : P.leaf 34 6008 = 3280476 :=
  orient4 (v := 19278) (by decide) (by decide +kernel) h19278

theorem cover19279 : P.CoversSplit 24 10 19279 0xffffffff00000000ffffffff0000000000000000000000000000000000000000cccccccc0000000000000000000000000000000000000000000000000000000088aa88aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 523, 565, 572, 879, 915, 1259, 1601]) (by decide +kernel)

theorem c19279_0 : P.sumLeaves 24 19741696 1024 = 9560738 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19279) (lo := 0) (len := 1024) (W := 9560738) check rows elimOK (by decide) (by decide) cover19279 (by decide)
  decide +kernel

theorem h19279 : P.leaf 34 19279 = 9560738 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9560738)]) (.cons c19279_0 (.nil)) (by decide) (by decide))

theorem h6009 : P.leaf 34 6009 = 9560738 :=
  orient4 (v := 19279) (by decide) (by decide +kernel) h19279

theorem cover42851 : P.CoversSplit 24 10 42851 0xffffffffaaaa0000ffffffffaaaa0000ffff00000000a0a0ffff00000000a0a00000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000cc00cc000000000033330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [474, 515, 572, 860, 915, 1202, 1209, 1258]) (ps := [(7, [565], [572]), (14, [958], [1272])]) (by decide +kernel)

theorem c42851_0 : P.sumLeaves 24 43879424 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 42851) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover42851 (by decide)
  decide +kernel

theorem contract42851_1 : P.leaf 30 685620 = 0 := by
  exact leaf_contract_zero (ss := [(19, 4, 529), (16, 0, 1258), (8, 0, 874), (6, 1, 482), (14, 1, 482), (7, 1, 488), (30, 4, 523), (27, 1, 572)]) (q := 586) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c42851_1 : P.sumLeaves 24 43879680 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 685620) rows (by decide) (by decide)).symm.trans contract42851_1

theorem contract42851_2 : P.leaf 30 685621 = 0 := by
  exact leaf_contract_zero (ss := [(19, 4, 529), (27, 1, 572), (29, 1, 915), (14, 0, 1272), (12, 1, 480), (2, 1, 482), (8, 1, 482), (4, 1, 425), (15, 1, 488)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c42851_2 : P.sumLeaves 24 43879744 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 685621) rows (by decide) (by decide)).symm.trans contract42851_2

theorem c42851_3 : P.sumLeaves 24 43879808 605 = 4742065 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 42851) (lo := 384) (len := 605) (W := 4742065) check rows elimOK (by decide) (by decide) cover42851 (by decide)
  decide +kernel

theorem c42851_4 : P.sumLeaves 24 43880413 35 = 3760776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 42851) (lo := 989) (len := 35) (W := 3760776) check rows elimOK (by decide) (by decide) cover42851 (by decide)
  decide +kernel

theorem h42851 : P.leaf 34 42851 = 8502841 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (605, 4742065), (35, 3760776)]) (.cons c42851_0 (.cons c42851_1 (.cons c42851_2 (.cons c42851_3 (.cons c42851_4 (.nil)))))) (by decide) (by decide))

theorem h6010 : P.leaf 34 6010 = 8502841 :=
  orient32 (v := 42851) (by decide) (by decide +kernel) h42851

theorem cover19295 : P.CoversSplit 24 10 19295 0xffffffff00000000ffffffff00000000a0a0000000000000a0a0000000000000cccccccc00000000000000000000000080800000000000000000000000000000ffffffff00000000ffff000000000000a5a5050500000000a5a50000000000000000000000000000000000000000000080800000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 523, 565, 572, 859, 866, 879, 1210, 1259, 1264, 1601, 1609]) (ps := [(8, [537], [516])]) (by decide +kernel)

theorem c19295_0 : P.sumLeaves 24 19758080 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19295) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover19295 (by decide)
  decide +kernel

theorem contract19295_1 : P.leaf 30 308724 = 0 := by
  exact leaf_contract_zero (ss := [(31, 1, 565), (17, 1, 1259), (30, 1, 1264), (8, 0, 1266), (14, 0, 537), (5, 1, 433), (20, 1, 531), (21, 0, 537), (9, 1, 678), (12, 1, 825)]) (q := 923) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c19295_1 : P.sumLeaves 24 19758336 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 308724) rows (by decide) (by decide)).symm.trans contract19295_1

theorem contract19295_2 : P.leaf 30 308725 = 0 := by
  exact leaf_contract_zero (ss := [(31, 1, 565), (8, 0, 1266), (14, 0, 537), (5, 1, 433), (20, 1, 531), (21, 0, 537), (12, 1, 825)]) (q := 923) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c19295_2 : P.sumLeaves 24 19758400 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 308725) rows (by decide) (by decide)).symm.trans contract19295_2

theorem c19295_3 : P.sumLeaves 24 19758464 566 = 10709244 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19295) (lo := 384) (len := 566) (W := 10709244) check rows elimOK (by decide) (by decide) cover19295 (by decide)
  decide +kernel

theorem c19295_4 : P.sumLeaves 24 19759030 74 = 15261555 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19295) (lo := 950) (len := 74) (W := 15261555) check rows elimOK (by decide) (by decide) cover19295 (by decide)
  decide +kernel

theorem h19295 : P.leaf 34 19295 = 25970799 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (566, 10709244), (74, 15261555)]) (.cons c19295_0 (.cons c19295_1 (.cons c19295_2 (.cons c19295_3 (.cons c19295_4 (.nil)))))) (by decide) (by decide))

theorem h6011 : P.leaf 34 6011 = 25970799 :=
  orient4 (v := 19295) (by decide) (by decide +kernel) h19295

theorem cover19310 : P.CoversSplit 24 10 19310 0xffffffffaaaaaaaaffffffffaaaaaaaaf5f5000000000000f5f5000000000000cccccccc888888880000000000000000c4c40000000000000000000000000000cccccccc888888880000000000000000c4c444440000000000300000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 572, 859, 879, 915, 1202, 1210, 1259, 1601]) (ps := [(17, [871, 1251], [1259])]) (by decide +kernel)

theorem c19310_0 : P.sumLeaves 24 19773440 909 = 4249505 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19310) (lo := 0) (len := 909) (W := 4249505) check rows elimOK (by decide) (by decide) cover19310 (by decide)
  decide +kernel

theorem c19310_1 : P.sumLeaves 24 19774349 115 = 11696930 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19310) (lo := 909) (len := 115) (W := 11696930) check rows elimOK (by decide) (by decide) cover19310 (by decide)
  decide +kernel

theorem h19310 : P.leaf 34 19310 = 15946435 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(909, 4249505), (115, 11696930)]) (.cons c19310_0 (.cons c19310_1 (.nil))) (by decide) (by decide))

theorem h6012 : P.leaf 34 6012 = 15946435 :=
  orient4 (v := 19310) (by decide) (by decide +kernel) h19310

theorem cover19311 : P.CoversSplit 24 10 19311 0xffffffffaaaaaaaaffffffffaaaaaaaaffff000000000000ffff000000000000cccccccc888888880000000000000000cccc0000000000000000000000000000cccccccc888888880000000000000000cccc44440000000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 572, 859, 915, 1202, 1210, 1259, 1601]) (ps := [(17, [1251], [1259])]) (by decide +kernel)

theorem c19311_0 : P.sumLeaves 24 19774464 888 = 9631194 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19311) (lo := 0) (len := 888) (W := 9631194) check rows elimOK (by decide) (by decide) cover19311 (by decide)
  decide +kernel

theorem c19311_1 : P.sumLeaves 24 19775352 128 = 23269256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19311) (lo := 888) (len := 128) (W := 23269256) check rows elimOK (by decide) (by decide) cover19311 (by decide)
  decide +kernel

theorem c19311_2 : P.sumLeaves 24 19775480 8 = 5778812 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19311) (lo := 1016) (len := 8) (W := 5778812) check rows elimOK (by decide) (by decide) cover19311 (by decide)
  decide +kernel

theorem h19311 : P.leaf 34 19311 = 38679262 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(888, 9631194), (128, 23269256), (8, 5778812)]) (.cons c19311_0 (.cons c19311_1 (.cons c19311_2 (.nil)))) (by decide) (by decide))

theorem h6013 : P.leaf 34 6013 = 38679262 :=
  orient4 (v := 19311) (by decide) (by decide +kernel) h19311

def seg : List (ℕ × ℕ) := [(6004, 48), (6005, 48), (6006, 48), (6007, 48), (6008, 48), (6009, 48), (6010, 48), (6011, 48), (6012, 48), (6013, 48)]

theorem segOK : checkSeg 16 perms 6004 6014 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6004 6014 480 11687115360 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 11687115360)
    (SegSum.cons (w := 48) h6004 (SegSum.cons (w := 48) h6005 (SegSum.cons (w := 48) h6006 (SegSum.cons (w := 48) h6007 (SegSum.cons (w := 48) h6008 (SegSum.cons (w := 48) h6009 (SegSum.cons (w := 48) h6010 (SegSum.cons (w := 48) h6011 (SegSum.cons (w := 48) h6012 (SegSum.cons (w := 48) h6013 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))) (by decide)

end RACert.S4N1.C0.S32
