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

namespace RACert.S4N1.C0.S76

open RACert RACert.Problem

theorem cover22334 : P.CoversSplit 24 10 22334 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff000000000000cccccccc88880000cc00cc0088000000cccccccc00000000cc00000000000000fffffffffafa0000fffffffffafa0000ffffffff40000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 529, 572, 860, 867, 909, 916, 1202, 1210, 1217, 1251, 1601]) (ps := [(8, [615], [1217])]) (by decide +kernel)

theorem c22334_0 : P.sumLeaves 24 22870016 469 = 6254883 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22334) (lo := 0) (len := 469) (W := 6254883) check rows elimOK (by decide) (by decide) cover22334 (by decide)
  decide +kernel

theorem c22334_1 : P.sumLeaves 24 22870485 352 = 13094503 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22334) (lo := 469) (len := 352) (W := 13094503) check rows elimOK (by decide) (by decide) cover22334 (by decide)
  decide +kernel

theorem c22334_2 : P.sumLeaves 24 22870837 168 = 25871248 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22334) (lo := 821) (len := 168) (W := 25871248) check rows elimOK (by decide) (by decide) cover22334 (by decide)
  decide +kernel

theorem c22334_3 : P.sumLeaves 24 22871005 35 = 19695025 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22334) (lo := 989) (len := 35) (W := 19695025) check rows elimOK (by decide) (by decide) cover22334 (by decide)
  decide +kernel

theorem h22334 : P.leaf 34 22334 = 64915659 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(469, 6254883), (352, 13094503), (168, 25871248), (35, 19695025)]) (.cons c22334_0 (.cons c22334_1 (.cons c22334_2 (.cons c22334_3 (.nil))))) (by decide) (by decide))

theorem cover22335 : P.CoversSplit 24 10 22335 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff000000000000cccccccc88880000cc00cc0088000000cccccccc00000000cc00000000000000fffffffffafa0000fffffffffafa0000ffffffff40000000ffff0000000000000000000000000000cc00cc008800000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 529, 572, 860, 909, 916, 1202, 1210, 1217, 1251, 1308, 1601, 1609]) (ps := [(8, [615], [1217])]) (by decide +kernel)

theorem c22335_0 : P.sumLeaves 24 22871040 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22335) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover22335 (by decide)
  decide +kernel

theorem contract22335_1 : P.leaf 30 357362 = 9976 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 357362) (ss := [(3, 1, 524), (4, 1, 578), (25, 1, 1258), (18, 1, 1308), (29, 27, 1601), (27, 1, 572), (8, 0, 1609), (5, 1, 580), (14, 0, 1609), (9, 1, 629), (21, 1, 629), (20, 1, 678), (15, 1, 874), (12, 1, 965), (16, 1, 1265)]) (ids := [0, 4, 5, 8, 9, 11, 17, 21, 22, 24, 26, 28, 29, 15, 20]) (cs := [2, 1, 1, 1, 3, 4, 0, 1, 5, 6, 1, 7, 0, 1, 1, 15, 1, 8, 1, 1, 16, 9, 10, 1, 11, 1, 12, 1, 13, 14]) (bs := [13, 2]) (W := 9976) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c22335_1 : P.sumLeaves 24 22871168 64 = 9976 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 357362) rows (by decide) (by decide)).symm.trans contract22335_1

theorem c22335_2 : P.sumLeaves 24 22871232 277 = 15520937 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22335) (lo := 192) (len := 277) (W := 15520937) check rows elimOK (by decide) (by decide) cover22335 (by decide)
  decide +kernel

theorem c22335_3 : P.sumLeaves 24 22871509 352 = 33391976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22335) (lo := 469) (len := 352) (W := 33391976) check rows elimOK (by decide) (by decide) cover22335 (by decide)
  decide +kernel

theorem c22335_4 : P.sumLeaves 24 22871861 168 = 65820395 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22335) (lo := 821) (len := 168) (W := 65820395) check rows elimOK (by decide) (by decide) cover22335 (by decide)
  decide +kernel

theorem c22335_5 : P.sumLeaves 24 22872029 35 = 44485753 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22335) (lo := 989) (len := 35) (W := 44485753) check rows elimOK (by decide) (by decide) cover22335 (by decide)
  decide +kernel

theorem h22335 : P.leaf 34 22335 = 159229037 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 9976), (277, 15520937), (352, 33391976), (168, 65820395), (35, 44485753)]) (.cons c22335_0 (.cons c22335_1 (.cons c22335_2 (.cons c22335_3 (.cons c22335_4 (.cons c22335_5 (.nil))))))) (by decide) (by decide))

theorem cover22364 : P.CoversSplit 24 10 22364 0xfca8fca8f0a0a0a0fca8fca8f0a0a0a0aca8aca800000000aca8aca800000000cc88cc8880008000cc00cc00800080008c888c88000000008c008c0000000000fc20fc20f020a020fc20fc20f020a020ac20ac2000000000ac20ac20000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 472, 473, 516, 523, 565, 867, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f22364 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (22900736 + i)

theorem c22364_0 : rowSum f22364 0 1023 = 11491946 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22364) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover22364 (by decide)
  decide +kernel

theorem c22364_1 : rowSum f22364 1023 1 = 275392 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22364) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover22364 (by decide)
  decide +kernel

theorem sum22364 : rowSum f22364 0 1024 = 11767338 :=
  rowSum_append (F := f22364) (lo := 0) (n := 1023) (m := 1) (A := 11491946) (B := 275392) c22364_0 (c22364_1)

theorem h22364 : P.leaf 34 22364 = 11767338 :=
  leaf_weighted (k := 24) (d := 10) (H := 22364) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 22364) (by decide) (by decide +kernel)) sum22364

theorem cover22365 : P.CoversSplit 24 10 22365 0xfffffffff0f0a0a0fffffffff0f0a0a0ffffffff00000000ffffffff00000000cccccccc80008000cc00cc0080008000cccccccc00000000cc00cc0000000000ff33ff33f030a020ff33ff33f030a020ff33ff3300000000ff33ff33000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 565, 572, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c22365_0 : P.sumLeaves 24 22901760 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22365) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22365 (by decide)
  decide +kernel

theorem contract22365_1 : P.leaf 30 357844 = 0 := by
  exact leaf_contract_zero (ss := [(31, 1, 565), (8, 0, 1266), (20, 1, 580), (21, 1, 586), (5, 1, 615)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22365_1 : P.sumLeaves 24 22902016 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 357844) rows (by decide) (by decide)).symm.trans contract22365_1

theorem contract22365_2 : P.leaf 30 357845 = 0 := by
  exact leaf_contract_zero (ss := [(31, 1, 565), (8, 0, 1266), (20, 1, 580), (21, 1, 586), (5, 1, 615)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22365_2 : P.sumLeaves 24 22902080 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 357845) rows (by decide) (by decide)).symm.trans contract22365_2

theorem c22365_3 : P.sumLeaves 24 22902144 314 = 9587576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22365) (lo := 384) (len := 314) (W := 9587576) check rows elimOK (by decide) (by decide) cover22365 (by decide)
  decide +kernel

theorem c22365_4 : P.sumLeaves 24 22902458 228 = 12365917 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22365) (lo := 698) (len := 228) (W := 12365917) check rows elimOK (by decide) (by decide) cover22365 (by decide)
  decide +kernel

theorem c22365_5 : P.sumLeaves 24 22902686 98 = 22915018 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22365) (lo := 926) (len := 98) (W := 22915018) check rows elimOK (by decide) (by decide) cover22365 (by decide)
  decide +kernel

theorem h22365 : P.leaf 34 22365 = 44868511 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (314, 9587576), (228, 12365917), (98, 22915018)]) (.cons c22365_0 (.cons c22365_1 (.cons c22365_2 (.cons c22365_3 (.cons c22365_4 (.cons c22365_5 (.nil))))))) (by decide) (by decide))

theorem cover22367 : P.CoversSplit 24 10 22367 0xfffffffff0f0a0a0fffffffff0f0a0a0ffffffff0000a0a0ffffffff0000a0a0cccccccc80008000cc00cc0080008000cccccccc00008000cc00cc0000008000fffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a00000000000000000cc00cc0080008000cccccccc80008000cc00cc0080008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 572, 1202, 1210, 1217, 1259, 1601, 1609]) (by decide +kernel)

noncomputable def f22367 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (22903808 + i)

theorem c22367_0 : rowSum f22367 0 427 = 10401352 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22367) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover22367 (by decide)
  decide +kernel

theorem c22367_1 : rowSum f22367 427 506 = 82425922 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22367) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover22367 (by decide)
  decide +kernel

theorem c22367_2 : rowSum f22367 933 91 = 61549496 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22367) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover22367 (by decide)
  decide +kernel

theorem sum22367 : rowSum f22367 0 1024 = 154376770 :=
  rowSum_append (F := f22367) (lo := 0) (n := 427) (m := 597) (A := 10401352) (B := 143975418) c22367_0 (rowSum_append (F := f22367) (lo := 427) (n := 506) (m := 91) (A := 82425922) (B := 61549496) c22367_1 (c22367_2))

theorem h22367 : P.leaf 34 22367 = 154376770 :=
  leaf_weighted (k := 24) (d := 10) (H := 22367) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 22367) (by decide) (by decide +kernel)) sum22367

theorem cover22372 : P.CoversSplit 24 10 22372 0xcc00cc00c80088000000000000000000cc00cc00c80088000000000000000000cccccccc88808880cc00cc0088008800cc00cc0088008800cc00000000000000cc00cc00c80088000000000000000000cc00cc00c800880000000000000000000000000000000000003300330022002200000000000000000033000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 572, 916, 1210, 1251, 1601]) (ps := [(2, [465, 468], [473])]) (by decide +kernel)

theorem contract22372_0 : P.leaf 30 357952 = 240 := by
  exact leaf_contract_factors (k := 30) (b := 10) (H := 357952) (ss := [(27, 6, 466), (2, 1, 468), (4, 1, 565), (29, 0, 572), (6, 0, 473), (12, 0, 458), (19, 1, 474), (13, 1, 478), (14, 0, 480), (10, 0, 461), (23, 1, 460), (11, 0, 461), (25, 1, 573), (15, 1, 852), (28, 1, 871), (31, 1, 871), (30, 1, 858), (21, 1, 874), (18, 1, 879), (20, 1, 880)]) (ids := [1, 3, 5, 6, 7, 14, 15, 20, 24, 22]) (cs := [1, 2, 1, 3, 0, 4, 5, 6, 0, 0, 0, 1, 0, 1, 7, 8, 1, 1, 1, 1, 9, 1, 11, 1, 10, 0, 1, 0, 1, 1]) (bs := [9, 1]) (W := 240) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c22372_0 : P.sumLeaves 24 22908928 64 = 240 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 357952) rows (by decide) (by decide)).symm.trans contract22372_0

theorem c22372_1 : P.sumLeaves 24 22908992 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22372) (lo := 64) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover22372 (by decide)
  decide +kernel

theorem contract22372_2 : P.leaf 30 357954 = 858 := by
  apply (leaf_contract (k := 30) (b := 15) (H := 357954) (ss := [(27, 6, 466), (2, 1, 475), (29, 0, 572), (6, 0, 473), (12, 0, 458), (19, 1, 474), (13, 1, 478), (14, 0, 480), (10, 0, 461), (23, 1, 460), (11, 0, 461), (4, 1, 558), (25, 1, 573), (15, 1, 852), (18, 1, 879)]) (ids := [1, 3, 5, 6, 7, 14, 15, 18, 19, 20, 22, 24, 26, 28, 29]) (cs := [1, 2, 1, 3, 0, 4, 5, 6, 0, 0, 0, 1, 0, 1, 7, 8, 1, 1, 9, 10, 11, 1, 12, 1, 13, 0, 14, 0, 15, 16]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c22372_2 : P.sumLeaves 24 22909056 64 = 858 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 357954) rows (by decide) (by decide)).symm.trans contract22372_2

theorem c22372_3 : P.sumLeaves 24 22909120 814 = 1341954 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22372) (lo := 192) (len := 814) (W := 1341954) check rows elimOK (by decide) (by decide) cover22372 (by decide)
  decide +kernel

theorem c22372_4 : P.sumLeaves 24 22909934 18 = 330368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22372) (lo := 1006) (len := 18) (W := 330368) check rows elimOK (by decide) (by decide) cover22372 (by decide)
  decide +kernel

theorem h22372 : P.leaf 34 22372 = 1673420 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 240), (64, 0), (64, 858), (814, 1341954), (18, 330368)]) (.cons c22372_0 (.cons c22372_1 (.cons c22372_2 (.cons c22372_3 (.cons c22372_4 (.nil)))))) (by decide) (by decide))

theorem cover22373 : P.CoversSplit 24 10 22373 0xcc00cc00c80088000000000000000000cc00cc00c80088000000000000000000cc00cc00880088000000000000000000cc00cc00880088000000000000000000cc00cc00c80088000000000000000000cc00cc00c800880000000000000000000000000000000000003300330022002200000000000000000033000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 860, 916, 1210, 1251, 1601]) (by decide +kernel)

theorem c22373_0 : P.sumLeaves 24 22909952 1024 = 8049995 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22373) (lo := 0) (len := 1024) (W := 8049995) check rows elimOK (by decide) (by decide) cover22373 (by decide)
  decide +kernel

theorem h22373 : P.leaf 34 22373 = 8049995 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8049995)]) (.cons c22373_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(22334, 48), (22335, 48), (22364, 24), (22365, 48), (22367, 24), (22372, 24), (22373, 48)]

theorem segOK : checkSeg 16 perms 22334 22374 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22334 22374 264 17326654368 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 17326654368)
    (SegSum.cons (w := 48) h22334 (SegSum.cons (w := 48) h22335 (SegSum.cons (w := 24) h22364 (SegSum.cons (w := 48) h22365 (SegSum.cons (w := 24) h22367 (SegSum.cons (w := 24) h22372 (SegSum.cons (w := 48) h22373 (show SegSum (P.leaf 34) [] 0 from rfl)))))))) (by decide)

end RACert.S4N1.C0.S76
