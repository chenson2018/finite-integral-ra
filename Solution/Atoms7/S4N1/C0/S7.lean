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

namespace RACert.S4N1.C0.S7

open RACert RACert.Problem

theorem cover1207 : P.CoversSplit 24 10 1207 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1207 : P.leaf 34 1207 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1207) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1207) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1207 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1208 : P.leaf 34 1208 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (29, 1, 472), (18, 11, 475), (33, 14, 486), (35, 14, 487), (28, 1, 508), (15, 1, 509), (11, 1, 559), (4, 1, 410), (30, 1, 858), (19, 1, 866), (14, 0, 867), (6, 1, 460), (12, 1, 460), (27, 1, 473), (26, 1, 517), (31, 1, 517), (34, 5, 524), (5, 1, 566), (3, 1, 409), (10, 1, 809), (16, 1, 468), (32, 1, 865), (21, 0, 874), (20, 1, 880), (13, 1, 922)]) (q := 929) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover1209 : P.CoversSplit 24 10 1209 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1209 : P.leaf 34 1209 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1209) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1209) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1209 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1210 : P.CoversSplit 24 10 1210 0xc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 573, 858, 865, 867, 921, 1202, 1251, 1259, 1308]) (by decide +kernel)

theorem h1210 : P.leaf 34 1210 = 2032 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1210) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1210) (weight := fun _ => 1) (xs := [510, 511]) check rows elimOK (by decide) (by decide) cover1210 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1211 : P.CoversSplit 24 10 1211 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1211 : P.leaf 34 1211 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1211) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1211) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1211 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1212 : P.CoversSplit 24 10 1212 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1212 : P.leaf 34 1212 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1212) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1212) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1212 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1213 : P.CoversSplit 24 10 1213 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1213 : P.leaf 34 1213 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1213) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1213) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1213 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1214 : P.CoversSplit 24 10 1214 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1214 : P.leaf 34 1214 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1214) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1214) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1214 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1215 : P.CoversSplit 24 10 1215 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1215 : P.leaf 34 1215 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1215) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1215) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1215 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1216 : P.CoversSplit 24 10 1216 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1216 : P.leaf 34 1216 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1216) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1216) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1216 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1217 : P.CoversSplit 24 10 1217 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1217 : P.leaf 34 1217 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1217) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1217) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1217 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1218 : P.CoversSplit 24 10 1218 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1218 : P.leaf 34 1218 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1218) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1218) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1218 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1219 : P.CoversSplit 24 10 1219 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1219 : P.leaf 34 1219 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1219) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1219) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1219 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1220 : P.CoversSplit 24 10 1220 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1220 : P.leaf 34 1220 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1220) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1220) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1220 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1221 : P.CoversSplit 24 10 1221 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1221 : P.leaf 34 1221 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1221) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1221) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1221 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1222 : P.CoversSplit 24 10 1222 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1222 : P.leaf 34 1222 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1222) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1222) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1222 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1223 : P.CoversSplit 24 10 1223 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1223 : P.leaf 34 1223 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1223) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1223) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1223 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1224 : P.CoversSplit 24 10 1224 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1224 : P.leaf 34 1224 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1224) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1224) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1224 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1225 : P.CoversSplit 24 10 1225 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1225 : P.leaf 34 1225 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1225) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1225) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1225 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1226 : P.CoversSplit 24 10 1226 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1226 : P.leaf 34 1226 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1226) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1226) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1226 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1227 : P.CoversSplit 24 10 1227 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1227 : P.leaf 34 1227 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1227) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1227) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1227 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1228 : P.CoversSplit 24 10 1228 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1228 : P.leaf 34 1228 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1228) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1228) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1228 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1229 : P.CoversSplit 24 10 1229 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1229 : P.leaf 34 1229 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1229) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1229) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1229 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1230 : P.CoversSplit 24 10 1230 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1230 : P.leaf 34 1230 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1230) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1230) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1230 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1231 : P.CoversSplit 24 10 1231 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1231 : P.leaf 34 1231 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1231) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1231) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1231 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1233 : P.CoversSplit 24 10 1233 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem h1233 : P.leaf 34 1233 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1233) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1233) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1233 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1234 : P.CoversSplit 24 10 1234 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1234 : P.leaf 34 1234 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1234) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1234) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1234 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1235 : P.CoversSplit 24 10 1235 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1235 : P.leaf 34 1235 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1235) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1235) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1235 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1236 : P.CoversSplit 24 10 1236 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem h1236 : P.leaf 34 1236 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1236) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1236) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1236 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1237 : P.CoversSplit 24 10 1237 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem h1237 : P.leaf 34 1237 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1237) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1237) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1237 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1238 : P.CoversSplit 24 10 1238 0xa0000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 858, 865, 867, 916, 921, 1202, 1209, 1210, 1259]) (by decide +kernel)

theorem h1238 : P.leaf 34 1238 = 37120 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1238) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1238) (weight := fun _ => 1) (xs := [893, 895, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1238 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1239 : P.CoversSplit 24 10 1239 0xff000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 860, 865, 866, 867, 915, 916, 921, 1202, 1210, 1259]) (by decide +kernel)

theorem h1239 : P.leaf 34 1239 = 708064 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1239) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1239) (weight := fun _ => 1) (xs := [888, 889, 890, 891, 892, 893, 894, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1239 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(1207, 48), (1208, 48), (1209, 48), (1210, 48), (1211, 48), (1212, 48), (1213, 48), (1214, 48), (1215, 48), (1216, 24), (1217, 48), (1218, 48), (1219, 48), (1220, 48), (1221, 48), (1222, 48), (1223, 48), (1224, 48), (1225, 48), (1226, 48), (1227, 48), (1228, 48), (1229, 48), (1230, 48), (1231, 48), (1233, 24), (1234, 48), (1235, 48), (1236, 48), (1237, 48), (1238, 48), (1239, 48)]

theorem segOK : checkSeg 16 perms 1207 1240 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1207 1240 1488 35866368 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 35866368)
    (SegSum.cons (w := 48) h1207 (SegSum.cons (w := 48) h1208 (SegSum.cons (w := 48) h1209 (SegSum.cons (w := 48) h1210 (SegSum.cons (w := 48) h1211 (SegSum.cons (w := 48) h1212 (SegSum.cons (w := 48) h1213 (SegSum.cons (w := 48) h1214 (SegSum.cons (w := 48) h1215 (SegSum.cons (w := 24) h1216 (SegSum.cons (w := 48) h1217 (SegSum.cons (w := 48) h1218 (SegSum.cons (w := 48) h1219 (SegSum.cons (w := 48) h1220 (SegSum.cons (w := 48) h1221 (SegSum.cons (w := 48) h1222 (SegSum.cons (w := 48) h1223 (SegSum.cons (w := 48) h1224 (SegSum.cons (w := 48) h1225 (SegSum.cons (w := 48) h1226 (SegSum.cons (w := 48) h1227 (SegSum.cons (w := 48) h1228 (SegSum.cons (w := 48) h1229 (SegSum.cons (w := 48) h1230 (SegSum.cons (w := 48) h1231 (SegSum.cons (w := 24) h1233 (SegSum.cons (w := 48) h1234 (SegSum.cons (w := 48) h1235 (SegSum.cons (w := 48) h1236 (SegSum.cons (w := 48) h1237 (SegSum.cons (w := 48) h1238 (SegSum.cons (w := 48) h1239 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S7
