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

namespace RACert.S4N1.C0.S53

open RACert RACert.Problem

theorem cover20383 : P.CoversSplit 24 10 20383 0xfffffffff0f0aaaafffffffff0f0aaaafffffffff0f0aaaafffffffff0f0aaaacccccccc80008800ff00ff00a000aa00cccccccc80008800ff00ff00a000aa00fffffffff0f0aaaafffffffff0f0aaaaffffffff00000000ffffffff00000000cccccccc80008800ff00ff00a000aa0000000000800080000000000080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 915, 1202, 1210, 1259, 1308, 1601]) (ps := [(8, [1217], [1266]), (14, [1609], [1266])]) (by decide +kernel)

def k20383 : ℕ := 0x8aef000000000000ffff8aef0000000000000000000000000000000000000000ffffffff8aef0000ffffffffffff8aef00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8aef0000ffffffffffff8aef
def t20383 : ℕ := 0x8ae000000000000ffff08ae0000000000000000000000000000000000000000ffffffff08ae0000ffffffffffff08ae00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff0000000008ae000000000000ffff08ae

noncomputable def f20383 (i : ℕ) := rowWeight k20383 t20383 i * P.leaf 24 (20872192 + i)

theorem c20383_0 : rowSum f20383 0 256 = 8729144 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 20383) (keep := k20383) (twice := t20383) check rows elimOK (by decide) (by decide) cover20383 (by decide)
  decide +kernel

theorem contract20383_1 : P.leaf 30 326132 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (14, 1, 531), (11, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c20383_1 : rowSum f20383 256 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k20383) (twice := t20383) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 326132) rows (by decide) (by decide)).symm.trans contract20383_1)

theorem contract20383_2 : P.leaf 30 326133 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (14, 1, 531), (11, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c20383_2 : rowSum f20383 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k20383) (twice := t20383) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 326133) rows (by decide) (by decide)).symm.trans contract20383_2)

theorem c20383_3 : rowSum f20383 384 265 = 84579792 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 20383) (keep := k20383) (twice := t20383) check rows elimOK (by decide) (by decide) cover20383 (by decide)
  decide +kernel

theorem c20383_4 : rowSum f20383 649 375 = 135206680 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 20383) (keep := k20383) (twice := t20383) check rows elimOK (by decide) (by decide) cover20383 (by decide)
  decide +kernel

theorem sum20383 : rowSum f20383 0 1024 = 228515616 :=
  rowSum_append (F := f20383) (lo := 0) (n := 256) (m := 768) (A := 8729144) (B := 219786472) c20383_0 (rowSum_append (F := f20383) (lo := 256) (n := 64) (m := 704) (A := 0) (B := 219786472) c20383_1 (rowSum_append (F := f20383) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 219786472) c20383_2 (rowSum_append (F := f20383) (lo := 384) (n := 265) (m := 375) (A := 84579792) (B := 135206680) c20383_3 (c20383_4))))

theorem h20383 : P.leaf 34 20383 = 228515616 :=
  leaf_weighted (k := 24) (d := 10) (H := 20383) (keep := k20383) (twice := t20383) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow5 (H := 20383) (by decide) (by decide +kernel)) sum20383

theorem h8179 : P.leaf 34 8179 = 228515616 :=
  orient4 (v := 20383) (by decide) (by decide +kernel) h20383

theorem cover20398 : P.CoversSplit 24 10 20398 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000008888000088880000888800008888000088880000000000008888000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 1202, 1259, 1601]) (by decide +kernel)

theorem c20398_0 : P.sumLeaves 24 20887552 1021 = 30935748 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20398) (lo := 0) (len := 1021) (W := 30935748) check rows elimOK (by decide) (by decide) cover20398 (by decide)
  decide +kernel

theorem c20398_1 : P.sumLeaves 24 20888573 3 = 2921892 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20398) (lo := 1021) (len := 3) (W := 2921892) check rows elimOK (by decide) (by decide) cover20398 (by decide)
  decide +kernel

theorem h20398 : P.leaf 34 20398 = 33857640 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 30935748), (3, 2921892)]) (.cons c20398_0 (.cons c20398_1 (.nil))) (by decide) (by decide))

theorem h8180 : P.leaf 34 8180 = 33857640 :=
  orient4 (v := 20398) (by decide) (by decide +kernel) h20398

theorem cover53039 : P.CoversSplit 24 10 53039 0xfffffffffefef0f0fffffffffefef0f0fffffffffefef0f0fffffffffefef0f0ffeeffeefeeef0e03300330032003000ffeeffeefeeef0e03300330032003000888888888888808088aa88aa88aa80a0888888888888808088aa88aa88a880a00000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 529, 572, 1202, 1601]) (ps := [(8, [1217], [572])]) (by decide +kernel)

theorem c53039_0 : P.sumLeaves 24 54311936 602 = 30914220 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 53039) (lo := 0) (len := 602) (W := 30914220) check rows elimOK (by decide) (by decide) cover53039 (by decide)
  decide +kernel

theorem c53039_1 : P.sumLeaves 24 54312538 171 = 26019320 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 53039) (lo := 602) (len := 171) (W := 26019320) check rows elimOK (by decide) (by decide) cover53039 (by decide)
  decide +kernel

theorem c53039_2 : P.sumLeaves 24 54312709 112 = 47143555 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 53039) (lo := 773) (len := 112) (W := 47143555) check rows elimOK (by decide) (by decide) cover53039 (by decide)
  decide +kernel

theorem c53039_3 : P.sumLeaves 24 54312821 116 = 76446715 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 53039) (lo := 885) (len := 116) (W := 76446715) check rows elimOK (by decide) (by decide) cover53039 (by decide)
  decide +kernel

theorem c53039_4 : P.sumLeaves 24 54312937 23 = 29669253 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 53039) (lo := 1001) (len := 23) (W := 29669253) check rows elimOK (by decide) (by decide) cover53039 (by decide)
  decide +kernel

theorem h53039 : P.leaf 34 53039 = 210193063 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(602, 30914220), (171, 26019320), (112, 47143555), (116, 76446715), (23, 29669253)]) (.cons c53039_0 (.cons c53039_1 (.cons c53039_2 (.cons c53039_3 (.cons c53039_4 (.nil)))))) (by decide) (by decide))

theorem h8181 : P.leaf 34 8181 = 210193063 :=
  orient5 (v := 53039) (by decide) (by decide +kernel) h53039

theorem cover20414 : P.CoversSplit 24 10 20414 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080ffccffccaa88a080cccccccc88888080ffccffccaa88a080fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080ffccffccaa88a08000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 915, 1202, 1210, 1259, 1308, 1601]) (by decide +kernel)

theorem c20414_0 : P.sumLeaves 24 20903936 313 = 8219533 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20414) (lo := 0) (len := 313) (W := 8219533) check rows elimOK (by decide) (by decide) cover20414 (by decide)
  decide +kernel

theorem c20414_1 : P.sumLeaves 24 20904249 128 = 26227451 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20414) (lo := 313) (len := 128) (W := 26227451) check rows elimOK (by decide) (by decide) cover20414 (by decide)
  decide +kernel

theorem c20414_2 : P.sumLeaves 24 20904377 173 = 39539642 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20414) (lo := 441) (len := 173) (W := 39539642) check rows elimOK (by decide) (by decide) cover20414 (by decide)
  decide +kernel

theorem c20414_3 : P.sumLeaves 24 20904550 197 = 35827184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20414) (lo := 614) (len := 197) (W := 35827184) check rows elimOK (by decide) (by decide) cover20414 (by decide)
  decide +kernel

theorem c20414_4 : P.sumLeaves 24 20904747 128 = 80252243 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20414) (lo := 811) (len := 128) (W := 80252243) check rows elimOK (by decide) (by decide) cover20414 (by decide)
  decide +kernel

theorem c20414_5 : P.sumLeaves 24 20904875 85 = 107667144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20414) (lo := 939) (len := 85) (W := 107667144) check rows elimOK (by decide) (by decide) cover20414 (by decide)
  decide +kernel

theorem h20414 : P.leaf 34 20414 = 297733197 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(313, 8219533), (128, 26227451), (173, 39539642), (197, 35827184), (128, 80252243), (85, 107667144)]) (.cons c20414_0 (.cons c20414_1 (.cons c20414_2 (.cons c20414_3 (.cons c20414_4 (.cons c20414_5 (.nil))))))) (by decide) (by decide))

theorem h8182 : P.leaf 34 8182 = 297733197 :=
  orient4 (v := 20414) (by decide) (by decide +kernel) h20414

theorem cover20415 : P.CoversSplit 24 10 20415 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080ffccffccaa88a080cccccccc88888080ffccffccaa88a080fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080ffccffccaa88a08000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 915, 1202, 1210, 1259, 1308, 1601]) (by decide +kernel)

theorem c20415_0 : P.sumLeaves 24 20904960 313 = 19510136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20415) (lo := 0) (len := 313) (W := 19510136) check rows elimOK (by decide) (by decide) cover20415 (by decide)
  decide +kernel

theorem c20415_1 : P.sumLeaves 24 20905273 128 = 55039665 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20415) (lo := 313) (len := 128) (W := 55039665) check rows elimOK (by decide) (by decide) cover20415 (by decide)
  decide +kernel

theorem c20415_2 : P.sumLeaves 24 20905401 173 = 65632654 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20415) (lo := 441) (len := 173) (W := 65632654) check rows elimOK (by decide) (by decide) cover20415 (by decide)
  decide +kernel

theorem c20415_3 : P.sumLeaves 24 20905574 197 = 72588442 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20415) (lo := 614) (len := 197) (W := 72588442) check rows elimOK (by decide) (by decide) cover20415 (by decide)
  decide +kernel

theorem c20415_4 : P.sumLeaves 24 20905771 128 = 151746969 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20415) (lo := 811) (len := 128) (W := 151746969) check rows elimOK (by decide) (by decide) cover20415 (by decide)
  decide +kernel

theorem c20415_5 : P.sumLeaves 24 20905899 85 = 180697353 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20415) (lo := 939) (len := 85) (W := 180697353) check rows elimOK (by decide) (by decide) cover20415 (by decide)
  decide +kernel

theorem h20415 : P.leaf 34 20415 = 545215219 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(313, 19510136), (128, 55039665), (173, 65632654), (197, 72588442), (128, 151746969), (85, 180697353)]) (.cons c20415_0 (.cons c20415_1 (.cons c20415_2 (.cons c20415_3 (.cons c20415_4 (.cons c20415_5 (.nil))))))) (by decide) (by decide))

theorem h8183 : P.leaf 34 8183 = 545215219 :=
  orient4 (v := 20415) (by decide) (by decide +kernel) h20415

def seg : List (ℕ × ℕ) := [(8179, 24), (8180, 48), (8181, 48), (8182, 48), (8183, 48)]

theorem segOK : checkSeg 16 perms 8179 8184 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8179 8184 216 57660332496 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 57660332496)
    (SegSum.cons (w := 24) h8179 (SegSum.cons (w := 48) h8180 (SegSum.cons (w := 48) h8181 (SegSum.cons (w := 48) h8182 (SegSum.cons (w := 48) h8183 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S53
