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

namespace RACert.S4N1.C0.S75

open RACert RACert.Problem

theorem cover22309 : P.CoversSplit 24 10 22309 0xcc00cc00c800000000000000000000008800cc00000000000000000000000000cc00cc008800000000000000000000008800cc00000000000000000000000000cc00cc00c800000000000000000000008800cc000000000000000000000000000000000000000000003300330022000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [468, 473, 515, 517, 522, 529, 572, 860, 916, 1202, 1210, 1251, 1601]) (by decide +kernel)

theorem c22309_0 : P.sumLeaves 24 22844416 1024 = 1505748 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22309) (lo := 0) (len := 1024) (W := 1505748) check rows elimOK (by decide) (by decide) cover22309 (by decide)
  decide +kernel

theorem h22309 : P.leaf 34 22309 = 1505748 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1505748)]) (.cons c22309_0 (.nil)) (by decide) (by decide))

theorem cover22311 : P.CoversSplit 24 10 22311 0xfffffffffafa0000fffffffffafa00008888cccc000000008888000000000000cccccccc88880000cc00cc00880000008888cccc000000008800000000000000fffffffffafa000000000000000000008888cccc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 860, 916, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem c22311_0 : P.sumLeaves 24 22846464 762 = 7356381 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22311) (lo := 0) (len := 762) (W := 7356381) check rows elimOK (by decide) (by decide) cover22311 (by decide)
  decide +kernel

theorem c22311_1 : P.sumLeaves 24 22847226 250 = 14884651 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22311) (lo := 762) (len := 250) (W := 14884651) check rows elimOK (by decide) (by decide) cover22311 (by decide)
  decide +kernel

theorem c22311_2 : P.sumLeaves 24 22847476 12 = 4440904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22311) (lo := 1012) (len := 12) (W := 4440904) check rows elimOK (by decide) (by decide) cover22311 (by decide)
  decide +kernel

theorem h22311 : P.leaf 34 22311 = 26681936 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(762, 7356381), (250, 14884651), (12, 4440904)]) (.cons c22311_0 (.cons c22311_1 (.cons c22311_2 (.nil)))) (by decide) (by decide))

theorem cover22316 : P.CoversSplit 24 10 22316 0x8800000088000000000000000000000088000000000000000000000000000000888800008880000088000000880000008888000000000000880000000000000088000000880000000000000000000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 473, 508, 515, 517, 522, 572, 916, 1202, 1601]) (ps := [(2, [465], [473])]) (by decide +kernel)

theorem c22316_0 : P.sumLeaves 24 22851584 640 = 221360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22316) (lo := 0) (len := 640) (W := 221360) check rows elimOK (by decide) (by decide) cover22316 (by decide)
  decide +kernel

theorem contract22316_1 : P.leaf 30 357066 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 466), (26, 1, 508), (3, 0, 522), (2, 0, 417), (5, 0, 417), (4, 0, 404)]) (q := 409) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22316_1 : P.sumLeaves 24 22852224 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 357066) rows (by decide) (by decide)).symm.trans contract22316_1

theorem c22316_2 : P.sumLeaves 24 22852288 320 = 731064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22316) (lo := 704) (len := 320) (W := 731064) check rows elimOK (by decide) (by decide) cover22316 (by decide)
  decide +kernel

theorem h22316 : P.leaf 34 22316 = 952424 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(640, 221360), (64, 0), (320, 731064)]) (.cons c22316_0 (.cons c22316_1 (.cons c22316_2 (.nil)))) (by decide) (by decide))

theorem cover22317 : P.CoversSplit 24 10 22317 0xcc00cc00c8000000000000000000000088008c00000000000000000000000000cc00cc0088000000000000000000000088008c00000000000000000000000000cc00cc00c8000000000000000000000088008c000000000000000000000000000000000000000000003300330022000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 529, 572, 860, 916, 1202, 1210, 1251, 1601]) (by decide +kernel)

theorem c22317_0 : P.sumLeaves 24 22852608 1024 = 4161120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22317) (lo := 0) (len := 1024) (W := 4161120) check rows elimOK (by decide) (by decide) cover22317 (by decide)
  decide +kernel

theorem h22317 : P.leaf 34 22317 = 4161120 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4161120)]) (.cons c22317_0 (.nil)) (by decide) (by decide))

theorem cover22318 : P.CoversSplit 24 10 22318 0xaaaa0000aaaa0000aaaa0000aaaa0000888800000000000088880000000000008888000088880000880000008800000088880000000000008800000000000000aaaa0000aaaa00000000000000000000888800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 529, 860, 916, 1202, 1259, 1601]) (by decide +kernel)

theorem c22318_0 : P.sumLeaves 24 22853632 1024 = 5943344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22318) (lo := 0) (len := 1024) (W := 5943344) check rows elimOK (by decide) (by decide) cover22318 (by decide)
  decide +kernel

theorem h22318 : P.leaf 34 22318 = 5943344 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5943344)]) (.cons c22318_0 (.nil)) (by decide) (by decide))

theorem cover22319 : P.CoversSplit 24 10 22319 0xfffffffffafa0000fffffffffafa000088888c8c000000008888000000000000cccccccc88880000cc00cc008800000088888c8c000000008800000000000000fffffffffafa0000000000000000000088888c8c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 860, 916, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem c22319_0 : P.sumLeaves 24 22854656 819 = 15943634 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22319) (lo := 0) (len := 819) (W := 15943634) check rows elimOK (by decide) (by decide) cover22319 (by decide)
  decide +kernel

theorem c22319_1 : P.sumLeaves 24 22855475 199 = 34618296 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22319) (lo := 819) (len := 199) (W := 34618296) check rows elimOK (by decide) (by decide) cover22319 (by decide)
  decide +kernel

theorem c22319_2 : P.sumLeaves 24 22855674 6 = 4842606 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22319) (lo := 1018) (len := 6) (W := 4842606) check rows elimOK (by decide) (by decide) cover22319 (by decide)
  decide +kernel

theorem h22319 : P.leaf 34 22319 = 55404536 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(819, 15943634), (199, 34618296), (6, 4842606)]) (.cons c22319_0 (.cons c22319_1 (.cons c22319_2 (.nil)))) (by decide) (by decide))

theorem cover22327 : P.CoversSplit 24 10 22327 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff000000000000cccccccc88880000cc00cc0088000000cccccccc00000000cc00000000000000fffffffffafa0000fffffffffafa0000ffffffffc8000000ffff0000000000000000000000000000cc00cc008800000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 529, 572, 860, 909, 916, 1202, 1210, 1217, 1251, 1308, 1601, 1609]) (by decide +kernel)

theorem c22327_0 : P.sumLeaves 24 22862848 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22327) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover22327 (by decide)
  decide +kernel

theorem contract22327_1 : P.leaf 30 357234 = 0 := by
  exact leaf_contract_zero (ss := [(4, 1, 578), (25, 1, 1258), (18, 1, 1308), (29, 27, 1601), (27, 1, 572), (2, 1, 475), (13, 1, 922), (16, 1, 1265), (8, 0, 1609), (5, 3, 524), (3, 1, 580)]) (q := 622) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22327_1 : P.sumLeaves 24 22862976 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 357234) rows (by decide) (by decide)).symm.trans contract22327_1

theorem c22327_2 : P.sumLeaves 24 22863040 275 = 11235261 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22327) (lo := 192) (len := 275) (W := 11235261) check rows elimOK (by decide) (by decide) cover22327 (by decide)
  decide +kernel

theorem c22327_3 : P.sumLeaves 24 22863315 352 = 20157734 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22327) (lo := 467) (len := 352) (W := 20157734) check rows elimOK (by decide) (by decide) cover22327 (by decide)
  decide +kernel

theorem c22327_4 : P.sumLeaves 24 22863667 168 = 42336368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22327) (lo := 819) (len := 168) (W := 42336368) check rows elimOK (by decide) (by decide) cover22327 (by decide)
  decide +kernel

theorem c22327_5 : P.sumLeaves 24 22863835 37 = 30498599 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22327) (lo := 987) (len := 37) (W := 30498599) check rows elimOK (by decide) (by decide) cover22327 (by decide)
  decide +kernel

theorem h22327 : P.leaf 34 22327 = 104227962 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 0), (275, 11235261), (352, 20157734), (168, 42336368), (37, 30498599)]) (.cons c22327_0 (.cons c22327_1 (.cons c22327_2 (.cons c22327_3 (.cons c22327_4 (.cons c22327_5 (.nil))))))) (by decide) (by decide))

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

theorem cover22333 : P.CoversSplit 24 10 22333 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff000000000000cccccccc88880000cc00cc0088000000cccccccc00000000cc00000000000000ff33ff33fa320000ff33ff33fa320000ff33ff3340000000ff330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 529, 860, 909, 916, 1202, 1210, 1217, 1251, 1259, 1308, 1601]) (ps := [(8, [615], [1217])]) (by decide +kernel)

theorem c22333_0 : P.sumLeaves 24 22868992 505 = 7069982 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22333) (lo := 0) (len := 505) (W := 7069982) check rows elimOK (by decide) (by decide) cover22333 (by decide)
  decide +kernel

theorem c22333_1 : P.sumLeaves 24 22869497 382 = 17608791 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22333) (lo := 505) (len := 382) (W := 17608791) check rows elimOK (by decide) (by decide) cover22333 (by decide)
  decide +kernel

theorem c22333_2 : P.sumLeaves 24 22869879 136 = 33100108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22333) (lo := 887) (len := 136) (W := 33100108) check rows elimOK (by decide) (by decide) cover22333 (by decide)
  decide +kernel

theorem c22333_3 : P.sumLeaves 24 22870015 1 = 1088272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22333) (lo := 1023) (len := 1) (W := 1088272) check rows elimOK (by decide) (by decide) cover22333 (by decide)
  decide +kernel

theorem h22333 : P.leaf 34 22333 = 58867153 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(505, 7069982), (382, 17608791), (136, 33100108), (1, 1088272)]) (.cons c22333_0 (.cons c22333_1 (.cons c22333_2 (.cons c22333_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(22309, 24), (22311, 48), (22316, 48), (22317, 48), (22318, 48), (22319, 48), (22327, 24), (22332, 48), (22333, 48)]

theorem segOK : checkSeg 16 perms 22309 22334 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22309 22334 384 10965173088 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 10965173088)
    (SegSum.cons (w := 24) h22309 (SegSum.cons (w := 48) h22311 (SegSum.cons (w := 48) h22316 (SegSum.cons (w := 48) h22317 (SegSum.cons (w := 48) h22318 (SegSum.cons (w := 48) h22319 (SegSum.cons (w := 24) h22327 (SegSum.cons (w := 48) h22332 (SegSum.cons (w := 48) h22333 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))) (by decide)

end RACert.S4N1.C0.S75
