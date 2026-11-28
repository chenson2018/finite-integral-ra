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

namespace RACert.S4N1.C0.S65

open RACert RACert.Problem

theorem cover22332 : P.CoversSplit 24 10 22332 0xfca8fca8f8a80000fca8fca8f8a80000fca8fca800000000fca8000000000000cc88cc8888880000cc00cc0088000000cc88cc8800000000cc00000000000000fc20fc20f8200000fc20fc20f8200000fc20fc2040000000fc200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 473, 508, 529, 867, 909, 916, 1202, 1210, 1217, 1251, 1601]) (ps := [(8, [615], [1217])]) (by decide +kernel)

theorem c22332_0 : P.sumLeaves 24 22867968 750 = 5393378 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22332) (lo := 0) (len := 750) (W := 5393378) check rows elimOK (by decide) (by decide) cover22332 (by decide)
  decide +kernel

theorem c22332_1 : P.sumLeaves 24 22868718 274 = 18170360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22332) (lo := 750) (len := 274) (W := 18170360) check rows elimOK (by decide) (by decide) cover22332 (by decide)
  decide +kernel

theorem h22332 : P.leaf 34 22332 = 23563738 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(750, 5393378), (274, 18170360)]) (.cons c22332_0 (.cons c22332_1 (.nil))) (by decide) (by decide))

theorem cover23399 : P.CoversSplit 24 10 23399 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffff000000000000ffff000000000000cccccccc88888080cc00cc0088008000cccc000000000000cc00000000000000ffffffffaaaaa0a00000000000000000ffff55550000000033330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 859, 1202, 1210, 1259, 1601]) (ps := [(17, [1251], [1259])]) (by decide +kernel)

theorem c23399_0 : P.sumLeaves 24 23960576 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23399) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover23399 (by decide)
  decide +kernel

theorem contract23399_1 : P.leaf 30 374388 = 0 := by
  exact leaf_contract_zero (ss := [(4, 1, 565), (17, 0, 1259), (8, 0, 880), (5, 1, 622), (21, 0, 880), (6, 1, 482), (14, 1, 482)]) (q := 629) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c23399_1 : P.sumLeaves 24 23960832 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 374388) rows (by decide) (by decide)).symm.trans contract23399_1

theorem c23399_2 : P.sumLeaves 24 23960896 415 = 13071913 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23399) (lo := 320) (len := 415) (W := 13071913) check rows elimOK (by decide) (by decide) cover23399 (by decide)
  decide +kernel

theorem c23399_3 : P.sumLeaves 24 23961311 240 = 20435216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23399) (lo := 735) (len := 240) (W := 20435216) check rows elimOK (by decide) (by decide) cover23399 (by decide)
  decide +kernel

theorem c23399_4 : P.sumLeaves 24 23961551 49 = 25360024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23399) (lo := 975) (len := 49) (W := 25360024) check rows elimOK (by decide) (by decide) cover23399 (by decide)
  decide +kernel

theorem h23399 : P.leaf 34 23399 = 58867153 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (415, 13071913), (240, 20435216), (49, 25360024)]) (.cons c23399_0 (.cons c23399_1 (.cons c23399_2 (.cons c23399_3 (.cons c23399_4 (.nil)))))) (by decide) (by decide))

theorem h22333 : P.leaf 34 22333 = 58867153 :=
  orient4 (v := 23399) (by decide) (by decide +kernel) h23399

theorem cover27371 : P.CoversSplit 24 10 27371 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffff000000000a0affff000000000a0aff00ff0080008000cc00cc0080008000ff00000008000800cc00000008000800ffffffffaaaaa0a0ffff0000aaaa0000ffff0f0f00000000ffff0000000000000000000000000000000000000000000033000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 859, 915, 1202, 1210, 1259, 1264, 1601, 1609]) (ps := [(8, [622], [1609]), (14, [958], [1266])]) (by decide +kernel)

theorem c27371_0 : P.sumLeaves 24 28027904 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 27371) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover27371 (by decide)
  decide +kernel

theorem contract27371_1 : P.leaf 30 437940 = 0 := by
  exact leaf_contract_zero (ss := [(4, 1, 536), (30, 1, 1264), (31, 1, 1210), (14, 0, 1266), (12, 1, 908), (21, 0, 1266), (2, 1, 488), (8, 1, 488)]) (q := 972) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c27371_1 : P.sumLeaves 24 28028160 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 437940) rows (by decide) (by decide)).symm.trans contract27371_1

theorem contract27371_2 : P.leaf 30 437941 = 0 := by
  exact leaf_contract_zero (ss := [(4, 1, 536), (14, 0, 1266), (12, 1, 908), (31, 1, 958), (21, 0, 1266), (2, 1, 488), (8, 1, 488)]) (q := 972) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c27371_2 : P.sumLeaves 24 28028224 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 437941) rows (by decide) (by decide)).symm.trans contract27371_2

theorem c27371_3 : P.sumLeaves 24 28028288 360 = 16718832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 27371) (lo := 384) (len := 360) (W := 16718832) check rows elimOK (by decide) (by decide) cover27371 (by decide)
  decide +kernel

theorem c27371_4 : P.sumLeaves 24 28028648 212 = 22212883 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 27371) (lo := 744) (len := 212) (W := 22212883) check rows elimOK (by decide) (by decide) cover27371 (by decide)
  decide +kernel

theorem c27371_5 : P.sumLeaves 24 28028860 68 = 25983944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 27371) (lo := 956) (len := 68) (W := 25983944) check rows elimOK (by decide) (by decide) cover27371 (by decide)
  decide +kernel

theorem h27371 : P.leaf 34 27371 = 64915659 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (360, 16718832), (212, 22212883), (68, 25983944)]) (.cons c27371_0 (.cons c27371_1 (.cons c27371_2 (.cons c27371_3 (.cons c27371_4 (.cons c27371_5 (.nil))))))) (by decide) (by decide))

theorem h22334 : P.leaf 34 22334 = 64915659 :=
  orient24 (v := 27371) (by decide) (by decide +kernel) h27371

theorem cover22335 : P.CoversSplit 24 10 22335 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff000000000000cccccccc88880000cc00cc0088000000cccccccc00000000cc00000000000000fffffffffafa0000fffffffffafa0000ffffffff40000000ffff0000000000000000000000000000cc00cc008800000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 529, 572, 860, 909, 916, 1202, 1210, 1217, 1251, 1308, 1601, 1609]) (ps := [(8, [615], [1217])]) (by decide +kernel)

theorem c22335_0 : P.sumLeaves 24 22871040 441 = 11634709 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22335) (lo := 0) (len := 441) (W := 11634709) check rows elimOK (by decide) (by decide) cover22335 (by decide)
  decide +kernel

theorem c22335_1 : P.sumLeaves 24 22871481 318 = 32131256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22335) (lo := 441) (len := 318) (W := 32131256) check rows elimOK (by decide) (by decide) cover22335 (by decide)
  decide +kernel

theorem c22335_2 : P.sumLeaves 24 22871799 200 = 64158695 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22335) (lo := 759) (len := 200) (W := 64158695) check rows elimOK (by decide) (by decide) cover22335 (by decide)
  decide +kernel

theorem c22335_3 : P.sumLeaves 24 22871999 65 = 51304377 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22335) (lo := 959) (len := 65) (W := 51304377) check rows elimOK (by decide) (by decide) cover22335 (by decide)
  decide +kernel

theorem h22335 : P.leaf 34 22335 = 159229037 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(441, 11634709), (318, 32131256), (200, 64158695), (65, 51304377)]) (.cons c22335_0 (.cons c22335_1 (.cons c22335_2 (.cons c22335_3 (.nil))))) (by decide) (by decide))

theorem cover58663 : P.CoversSplit 24 10 58663 0xfffffffffefa0000fffffffffefa00008000c400000000008000c40000000000ffecffecfee8000000000000000000008000c400000000000000000000000000800080008000000080a080a080a00000800080000000000080008001000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 860, 865, 872, 915, 1202, 1601]) (by decide +kernel)

noncomputable def f58663 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (60070912 + i)

theorem c58663_0 : rowSum f58663 0 1024 = 11767338 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58663) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover58663 (by decide)
  decide +kernel

theorem sum58663 : rowSum f58663 0 1024 = 11767338 :=
  c58663_0

theorem h58663 : P.leaf 34 58663 = 11767338 :=
  leaf_weighted (k := 24) (d := 10) (H := 58663) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 58663) (by decide) (by decide +kernel)) sum58663

theorem h22364 : P.leaf 34 22364 = 11767338 :=
  orient32 (v := 58663) (by decide) (by decide +kernel) h58663

theorem cover58679 : P.CoversSplit 24 10 58679 0xfffffffffffa0000fffffffffffa0000f000f50000000000f000f50000000000fffcfffcfff800000000000000000000f000f500000000000000000000000000f000f000f0000000f0f0f0f0f0f00000f000f00000000000f000f005000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 529, 572, 858, 860, 865, 872, 915, 1202, 1601]) (by decide +kernel)

theorem c58679_0 : P.sumLeaves 24 60087296 759 = 13263215 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 58679) (lo := 0) (len := 759) (W := 13263215) check rows elimOK (by decide) (by decide) cover58679 (by decide)
  decide +kernel

theorem c58679_1 : P.sumLeaves 24 60088055 240 = 22233224 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 58679) (lo := 759) (len := 240) (W := 22233224) check rows elimOK (by decide) (by decide) cover58679 (by decide)
  decide +kernel

theorem c58679_2 : P.sumLeaves 24 60088295 25 = 9372072 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 58679) (lo := 999) (len := 25) (W := 9372072) check rows elimOK (by decide) (by decide) cover58679 (by decide)
  decide +kernel

theorem h58679 : P.leaf 34 58679 = 44868511 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(759, 13263215), (240, 22233224), (25, 9372072)]) (.cons c58679_0 (.cons c58679_1 (.cons c58679_2 (.nil)))) (by decide) (by decide))

theorem h22365 : P.leaf 34 22365 = 44868511 :=
  orient32 (v := 58679) (by decide) (by decide +kernel) h58679

theorem cover22367 : P.CoversSplit 24 10 22367 0xfffffffff0f0a0a0fffffffff0f0a0a0ffffffff0000a0a0ffffffff0000a0a0cccccccc80008000cc00cc0080008000cccccccc00008000cc00cc0000008000fffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a00000000000000000cc00cc0080008000cccccccc80008000cc00cc0080008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 572, 1202, 1210, 1217, 1259, 1601, 1609]) (by decide +kernel)

def k22367 : ℕ := 0x8aef000000000000ffff8aef0000000000000000000000000000000000000000ffffffff8aef0000ffffffffffff8aef00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def t22367 : ℕ := 0x8ae000000000000ffff08ae0000000000000000000000000000000000000000ffffffff08ae0000ffffffffffff08ae00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000

noncomputable def f22367 (i : ℕ) := rowWeight k22367 t22367 i * P.leaf 24 (22903808 + i)

theorem contract22367_0 : P.leaf 30 357872 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (4, 1, 578), (29, 1, 1259), (8, 0, 1266), (5, 1, 615), (14, 0, 1266), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22367_0 : rowSum f22367 0 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k22367) (twice := t22367) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 357872) rows (by decide) (by decide)).symm.trans contract22367_0)

theorem contract22367_1 : P.leaf 30 357873 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (4, 1, 578), (8, 0, 1266), (5, 1, 615), (14, 0, 1266), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22367_1 : rowSum f22367 64 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k22367) (twice := t22367) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 357873) rows (by decide) (by decide)).symm.trans contract22367_1)

theorem c22367_2 : rowSum f22367 128 128 = 66320 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22367) (keep := k22367) (twice := t22367) check rows elimOK (by decide) (by decide) cover22367 (by decide)
  decide +kernel

theorem contract22367_3 : P.leaf 30 357876 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (5, 1, 615), (14, 0, 1266), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22367_3 : rowSum f22367 256 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k22367) (twice := t22367) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 357876) rows (by decide) (by decide)).symm.trans contract22367_3)

theorem contract22367_4 : P.leaf 30 357877 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (5, 1, 615), (14, 0, 1266), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22367_4 : rowSum f22367 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k22367) (twice := t22367) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 357877) rows (by decide) (by decide)).symm.trans contract22367_4)

theorem c22367_5 : rowSum f22367 384 318 = 63144610 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22367) (keep := k22367) (twice := t22367) check rows elimOK (by decide) (by decide) cover22367 (by decide)
  decide +kernel

theorem c22367_6 : rowSum f22367 702 322 = 91165840 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22367) (keep := k22367) (twice := t22367) check rows elimOK (by decide) (by decide) cover22367 (by decide)
  decide +kernel

theorem sum22367 : rowSum f22367 0 1024 = 154376770 :=
  rowSum_append (F := f22367) (lo := 0) (n := 64) (m := 960) (A := 0) (B := 154376770) c22367_0 (rowSum_append (F := f22367) (lo := 64) (n := 64) (m := 896) (A := 0) (B := 154376770) c22367_1 (rowSum_append (F := f22367) (lo := 128) (n := 128) (m := 768) (A := 66320) (B := 154310450) c22367_2 (rowSum_append (F := f22367) (lo := 256) (n := 64) (m := 704) (A := 0) (B := 154310450) c22367_3 (rowSum_append (F := f22367) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 154310450) c22367_4 (rowSum_append (F := f22367) (lo := 384) (n := 318) (m := 322) (A := 63144610) (B := 91165840) c22367_5 (c22367_6))))))

theorem h22367 : P.leaf 34 22367 = 154376770 :=
  leaf_weighted (k := 24) (d := 10) (H := 22367) (keep := k22367) (twice := t22367) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow5 (H := 22367) (by decide) (by decide +kernel)) sum22367

def seg : List (ℕ × ℕ) := [(22332, 48), (22333, 48), (22334, 48), (22335, 48), (22364, 24), (22365, 48), (22367, 24)]

theorem segOK : checkSeg 16 perms 22332 22372 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22332 22372 288 20856775296 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 20856775296)
    (SegSum.cons (w := 48) h22332 (SegSum.cons (w := 48) h22333 (SegSum.cons (w := 48) h22334 (SegSum.cons (w := 48) h22335 (SegSum.cons (w := 24) h22364 (SegSum.cons (w := 48) h22365 (SegSum.cons (w := 24) h22367 (show SegSum (P.leaf 34) [] 0 from rfl)))))))) (by decide)

end RACert.S4N1.C0.S65
