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

namespace RACert.S4N1.C0.S9

open RACert RACert.Problem

theorem cover1273 : P.CoversSplit 24 10 1273 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1273 : P.leaf 34 1273 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1273) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1273) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1273 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1274 : P.CoversSplit 24 10 1274 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1274 : P.leaf 34 1274 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1274) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1274) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1274 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1275 : P.CoversSplit 24 10 1275 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1275 : P.leaf 34 1275 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1275) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1275) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1275 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1276 : P.CoversSplit 24 10 1276 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1276 : P.leaf 34 1276 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1276) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1276) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1276 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1277 : P.CoversSplit 24 10 1277 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1277 : P.leaf 34 1277 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1277) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1277) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1277 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1278 : P.CoversSplit 24 10 1278 0xf0005500a00000000000000000000000f0005500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 860, 865, 867, 916, 921, 1202, 1259]) (by decide +kernel)

theorem h1278 : P.leaf 34 1278 = 728844 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1278) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1278) (weight := fun _ => 1) (xs := [872, 874, 876, 878, 892, 893, 894, 895, 989, 991, 1000, 1002, 1004, 1006, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1278 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1279 : P.CoversSplit 24 10 1279 0xff00fa00aa0000000000000000000000ff00fa00aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 860, 865, 867, 916, 921, 1202, 1210, 1259]) (by decide +kernel)

theorem c1279_0 : P.sumLeaves 24 1309696 1024 = 7018820 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1279) (lo := 0) (len := 1024) (W := 7018820) check rows elimOK (by decide) (by decide) cover1279 (by decide)
  decide +kernel

theorem h1279 : P.leaf 34 1279 = 7018820 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7018820)]) (.cons c1279_0 (.nil)) (by decide) (by decide))

theorem cover1408 : P.CoversSplit 24 10 1408 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1408 : P.leaf 34 1408 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1408) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1408) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1408 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1409 : P.CoversSplit 24 10 1409 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1409 : P.leaf 34 1409 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1409) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1409) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1409 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1410 : P.CoversSplit 24 10 1410 0x80000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 515, 516, 522, 858, 860, 865, 867, 916, 1258, 1259, 1301]) (by decide +kernel)

theorem h1410 : P.leaf 34 1410 = 80 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1410) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1410) (weight := fun _ => 1) (xs := [383, 511]) check rows elimOK (by decide) (by decide) cover1410 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1411 : P.CoversSplit 24 10 1411 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1411 : P.leaf 34 1411 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1411) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1411) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1411 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1412 : P.CoversSplit 24 10 1412 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1412 : P.leaf 34 1412 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1412) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1412) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1412 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1413 : P.CoversSplit 24 10 1413 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1413 : P.leaf 34 1413 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1413) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1413) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1413 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1414 : P.CoversSplit 24 10 1414 0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 479, 515, 516, 522, 858, 865, 867, 916, 1258, 1259, 1301]) (ps := [(8, [537], [468])]) (by decide +kernel)

theorem h1414 : P.leaf 34 1414 = 256 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1414) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1414) (weight := fun _ => 1) (xs := [511]) check rows elimOK (by decide) (by decide) cover1414 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1415 : P.CoversSplit 24 10 1415 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1415 : P.leaf 34 1415 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1415) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1415) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1415 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1416 : P.CoversSplit 24 10 1416 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1416 : P.leaf 34 1416 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1416) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1416) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1416 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1417 : P.CoversSplit 24 10 1417 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1417 : P.leaf 34 1417 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1417) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1417) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1417 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1418 : P.leaf 34 1418 = 0 := by
  exact leaf_contract_zero (ss := [(32, 1, 466), (3, 1, 472), (33, 0, 486), (7, 6, 467), (8, 0, 509), (16, 10, 468), (10, 1, 529)]) (q := 615) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover1419 : P.CoversSplit 24 10 1419 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1419 : P.leaf 34 1419 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1419) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1419) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1419 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1420 : P.CoversSplit 24 10 1420 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1420 : P.leaf 34 1420 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1420) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1420) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1420 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1421 : P.CoversSplit 24 10 1421 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1421 : P.leaf 34 1421 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1421) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1421) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1421 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1422 : P.CoversSplit 24 10 1422 0x80000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 515, 516, 522, 858, 860, 865, 867, 916, 1258, 1259, 1301]) (by decide +kernel)

theorem h1422 : P.leaf 34 1422 = 3632 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1422) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1422) (weight := fun _ => 1) (xs := [383, 511]) check rows elimOK (by decide) (by decide) cover1422 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1423 : P.CoversSplit 24 10 1423 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1423 : P.leaf 34 1423 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1423) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1423) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1423 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16399 : P.CoversSplit 24 10 16399 0x8001000100000000000100010000000080010000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000080010001000000000000000000000000800100010000000000010001000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 529, 572, 858, 865, 1202, 1210, 1259, 1301, 1308, 1601, 1651]) (by decide +kernel)

theorem h16399 : P.leaf 34 16399 = 15542 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 16399) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 16399) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16399) (weight := rowWeight keep1 twice1) (xs := [288, 304, 352, 368, 383, 480, 496, 511, 816, 880, 895, 928, 944, 992, 1008, 1023]) check rows elimOK (by decide) (by decide) cover16399 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1426 : P.leaf 34 1426 = 15542 :=
  orient24 (v := 16399) (by decide) (by decide +kernel) h16399

theorem cover1427 : P.CoversSplit 24 10 1427 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1427 : P.leaf 34 1427 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1427) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1427) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1427 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1428 : P.CoversSplit 24 10 1428 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1428 : P.leaf 34 1428 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1428) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1428) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1428 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1429 : P.CoversSplit 24 10 1429 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1429 : P.leaf 34 1429 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1429) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1429) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1429 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1430 : P.CoversSplit 24 10 1430 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1430 : P.leaf 34 1430 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1430) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1430) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1430 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1431 : P.CoversSplit 24 10 1431 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1431 : P.leaf 34 1431 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1431) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1431) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1431 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1432 : P.leaf 34 1432 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (29, 1, 472), (33, 0, 486), (7, 6, 467), (8, 0, 509), (16, 10, 468), (35, 0, 531)]) (q := 615) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover1433 : P.CoversSplit 24 10 1433 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1433 : P.leaf 34 1433 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1433) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1433) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1433 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1434 : P.leaf 34 1434 = 0 := by
  exact leaf_contract_zero (ss := [(33, 0, 486), (7, 6, 467), (8, 0, 509), (16, 10, 468), (35, 0, 531)]) (q := 615) check rows (by decide) (by decide +kernel) (by decide +kernel)

def seg : List (ℕ × ℕ) := [(1273, 48), (1274, 48), (1275, 48), (1276, 48), (1277, 48), (1278, 48), (1279, 48), (1408, 12), (1409, 24), (1410, 24), (1411, 48), (1412, 48), (1413, 48), (1414, 48), (1415, 48), (1416, 48), (1417, 48), (1418, 48), (1419, 48), (1420, 48), (1421, 48), (1422, 48), (1423, 48), (1426, 12), (1427, 24), (1428, 48), (1429, 48), (1430, 48), (1431, 48), (1432, 48), (1433, 48), (1434, 48)]

theorem segOK : checkSeg 16 perms 1273 1435 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1273 1435 1392 372262920 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 372262920)
    (SegSum.cons (w := 48) h1273 (SegSum.cons (w := 48) h1274 (SegSum.cons (w := 48) h1275 (SegSum.cons (w := 48) h1276 (SegSum.cons (w := 48) h1277 (SegSum.cons (w := 48) h1278 (SegSum.cons (w := 48) h1279 (SegSum.cons (w := 12) h1408 (SegSum.cons (w := 24) h1409 (SegSum.cons (w := 24) h1410 (SegSum.cons (w := 48) h1411 (SegSum.cons (w := 48) h1412 (SegSum.cons (w := 48) h1413 (SegSum.cons (w := 48) h1414 (SegSum.cons (w := 48) h1415 (SegSum.cons (w := 48) h1416 (SegSum.cons (w := 48) h1417 (SegSum.cons (w := 48) h1418 (SegSum.cons (w := 48) h1419 (SegSum.cons (w := 48) h1420 (SegSum.cons (w := 48) h1421 (SegSum.cons (w := 48) h1422 (SegSum.cons (w := 48) h1423 (SegSum.cons (w := 12) h1426 (SegSum.cons (w := 24) h1427 (SegSum.cons (w := 48) h1428 (SegSum.cons (w := 48) h1429 (SegSum.cons (w := 48) h1430 (SegSum.cons (w := 48) h1431 (SegSum.cons (w := 48) h1432 (SegSum.cons (w := 48) h1433 (SegSum.cons (w := 48) h1434 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S9
