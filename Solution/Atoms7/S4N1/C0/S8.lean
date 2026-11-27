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

namespace RACert.S4N1.C0.S8

open RACert RACert.Problem

theorem h1240 : P.leaf 34 1240 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (29, 1, 472), (18, 11, 475), (15, 1, 486), (35, 14, 487), (28, 1, 508), (14, 8, 509), (11, 1, 559), (4, 1, 410), (30, 1, 858), (19, 1, 866), (8, 0, 867), (6, 1, 460), (12, 1, 460), (5, 1, 411), (26, 1, 465), (7, 1, 467), (27, 1, 473), (20, 1, 482), (21, 0, 488), (34, 1, 573), (33, 0, 580), (31, 1, 516), (9, 1, 678), (10, 1, 809), (32, 1, 865), (13, 1, 922)]) (q := 929) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover1241 : P.CoversSplit 24 10 1241 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1241_0 : P.sumLeaves 24 1270784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1241) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1241 (by decide)
  decide +kernel

theorem h1241 : P.leaf 34 1241 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1241_0 (.nil)) (by decide) (by decide))

theorem cover1242 : P.CoversSplit 24 10 1242 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1242_0 : P.sumLeaves 24 1271808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1242) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1242 (by decide)
  decide +kernel

theorem h1242 : P.leaf 34 1242 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1242_0 (.nil)) (by decide) (by decide))

theorem cover1243 : P.CoversSplit 24 10 1243 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1243_0 : P.sumLeaves 24 1272832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1243) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1243 (by decide)
  decide +kernel

theorem h1243 : P.leaf 34 1243 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1243_0 (.nil)) (by decide) (by decide))

theorem cover1244 : P.CoversSplit 24 10 1244 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1244_0 : P.sumLeaves 24 1273856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1244) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1244 (by decide)
  decide +kernel

theorem h1244 : P.leaf 34 1244 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1244_0 (.nil)) (by decide) (by decide))

theorem cover1245 : P.CoversSplit 24 10 1245 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1245_0 : P.sumLeaves 24 1274880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1245) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1245 (by decide)
  decide +kernel

theorem h1245 : P.leaf 34 1245 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1245_0 (.nil)) (by decide) (by decide))

theorem cover1246 : P.CoversSplit 24 10 1246 0xa0000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 858, 865, 867, 916, 921, 1202, 1209, 1210, 1259]) (by decide +kernel)

theorem c1246_0 : P.sumLeaves 24 1275904 1024 = 172352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1246) (lo := 0) (len := 1024) (W := 172352) check rows elimOK (by decide) (by decide) cover1246 (by decide)
  decide +kernel

theorem h1246 : P.leaf 34 1246 = 172352 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 172352)]) (.cons c1246_0 (.nil)) (by decide) (by decide))

theorem cover1247 : P.CoversSplit 24 10 1247 0xff000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 860, 865, 867, 916, 921, 1202, 1210, 1251, 1259]) (by decide +kernel)

theorem c1247_0 : P.sumLeaves 24 1276928 1024 = 1389888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1247) (lo := 0) (len := 1024) (W := 1389888) check rows elimOK (by decide) (by decide) cover1247 (by decide)
  decide +kernel

theorem h1247 : P.leaf 34 1247 = 1389888 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1389888)]) (.cons c1247_0 (.nil)) (by decide) (by decide))

theorem cover1248 : P.CoversSplit 24 10 1248 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1248_0 : P.sumLeaves 24 1277952 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1248) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1248 (by decide)
  decide +kernel

theorem h1248 : P.leaf 34 1248 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1248_0 (.nil)) (by decide) (by decide))

theorem cover1249 : P.CoversSplit 24 10 1249 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1249_0 : P.sumLeaves 24 1278976 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1249) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1249 (by decide)
  decide +kernel

theorem h1249 : P.leaf 34 1249 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1249_0 (.nil)) (by decide) (by decide))

theorem cover1250 : P.CoversSplit 24 10 1250 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1250_0 : P.sumLeaves 24 1280000 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1250) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1250 (by decide)
  decide +kernel

theorem h1250 : P.leaf 34 1250 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1250_0 (.nil)) (by decide) (by decide))

theorem cover1251 : P.CoversSplit 24 10 1251 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1251_0 : P.sumLeaves 24 1281024 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1251) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1251 (by decide)
  decide +kernel

theorem h1251 : P.leaf 34 1251 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1251_0 (.nil)) (by decide) (by decide))

theorem cover1252 : P.CoversSplit 24 10 1252 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1252_0 : P.sumLeaves 24 1282048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1252) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1252 (by decide)
  decide +kernel

theorem h1252 : P.leaf 34 1252 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1252_0 (.nil)) (by decide) (by decide))

theorem cover1253 : P.CoversSplit 24 10 1253 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1253_0 : P.sumLeaves 24 1283072 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1253) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1253 (by decide)
  decide +kernel

theorem h1253 : P.leaf 34 1253 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1253_0 (.nil)) (by decide) (by decide))

theorem cover1254 : P.CoversSplit 24 10 1254 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1254_0 : P.sumLeaves 24 1284096 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1254) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1254 (by decide)
  decide +kernel

theorem h1254 : P.leaf 34 1254 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1254_0 (.nil)) (by decide) (by decide))

theorem cover1255 : P.CoversSplit 24 10 1255 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1255_0 : P.sumLeaves 24 1285120 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1255) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1255 (by decide)
  decide +kernel

theorem h1255 : P.leaf 34 1255 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1255_0 (.nil)) (by decide) (by decide))

theorem cover1256 : P.CoversSplit 24 10 1256 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1256_0 : P.sumLeaves 24 1286144 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1256) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1256 (by decide)
  decide +kernel

theorem h1256 : P.leaf 34 1256 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1256_0 (.nil)) (by decide) (by decide))

theorem cover1257 : P.CoversSplit 24 10 1257 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1257_0 : P.sumLeaves 24 1287168 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1257) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1257 (by decide)
  decide +kernel

theorem h1257 : P.leaf 34 1257 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1257_0 (.nil)) (by decide) (by decide))

theorem cover1258 : P.CoversSplit 24 10 1258 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1258_0 : P.sumLeaves 24 1288192 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1258) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1258 (by decide)
  decide +kernel

theorem h1258 : P.leaf 34 1258 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1258_0 (.nil)) (by decide) (by decide))

theorem cover1259 : P.CoversSplit 24 10 1259 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1259_0 : P.sumLeaves 24 1289216 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1259) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1259 (by decide)
  decide +kernel

theorem h1259 : P.leaf 34 1259 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1259_0 (.nil)) (by decide) (by decide))

theorem cover1260 : P.CoversSplit 24 10 1260 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1260_0 : P.sumLeaves 24 1290240 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1260) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1260 (by decide)
  decide +kernel

theorem h1260 : P.leaf 34 1260 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1260_0 (.nil)) (by decide) (by decide))

theorem cover1261 : P.CoversSplit 24 10 1261 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1261_0 : P.sumLeaves 24 1291264 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1261) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1261 (by decide)
  decide +kernel

theorem h1261 : P.leaf 34 1261 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1261_0 (.nil)) (by decide) (by decide))

theorem cover1262 : P.CoversSplit 24 10 1262 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1262_0 : P.sumLeaves 24 1292288 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1262) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1262 (by decide)
  decide +kernel

theorem h1262 : P.leaf 34 1262 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1262_0 (.nil)) (by decide) (by decide))

theorem cover1263 : P.CoversSplit 24 10 1263 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1263_0 : P.sumLeaves 24 1293312 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1263) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1263 (by decide)
  decide +kernel

theorem h1263 : P.leaf 34 1263 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1263_0 (.nil)) (by decide) (by decide))

theorem cover1265 : P.CoversSplit 24 10 1265 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem c1265_0 : P.sumLeaves 24 1295360 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1265) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1265 (by decide)
  decide +kernel

theorem h1265 : P.leaf 34 1265 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1265_0 (.nil)) (by decide) (by decide))

theorem cover1266 : P.CoversSplit 24 10 1266 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1266_0 : P.sumLeaves 24 1296384 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1266) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1266 (by decide)
  decide +kernel

theorem h1266 : P.leaf 34 1266 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1266_0 (.nil)) (by decide) (by decide))

theorem cover1267 : P.CoversSplit 24 10 1267 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1267_0 : P.sumLeaves 24 1297408 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1267) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1267 (by decide)
  decide +kernel

theorem h1267 : P.leaf 34 1267 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1267_0 (.nil)) (by decide) (by decide))

theorem cover1268 : P.CoversSplit 24 10 1268 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem c1268_0 : P.sumLeaves 24 1298432 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1268) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1268 (by decide)
  decide +kernel

theorem h1268 : P.leaf 34 1268 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1268_0 (.nil)) (by decide) (by decide))

theorem cover1269 : P.CoversSplit 24 10 1269 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem c1269_0 : P.sumLeaves 24 1299456 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1269) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1269 (by decide)
  decide +kernel

theorem h1269 : P.leaf 34 1269 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1269_0 (.nil)) (by decide) (by decide))

theorem h1270 : P.leaf 34 1270 = 116384 := by
  exact leaf_contract_factors (k := 34) (b := 21) (H := 1270) (ss := [(5, 1, 559), (30, 19, 866), (35, 1, 867), (18, 1, 879), (11, 1, 901), (6, 1, 458), (10, 1, 458), (12, 1, 817), (19, 1, 908), (29, 1, 921), (28, 1, 858), (34, 1, 916), (32, 1, 1259)]) (ids := [0, 1, 2, 5, 6, 7, 11, 12, 13, 14, 15, 18, 19, 20, 22, 23, 24, 25, 29, 31, 21]) (cs := [2, 3, 4, 1, 1, 5, 6, 7, 1, 1, 1, 8, 9, 10, 11, 12, 1, 1, 13, 14, 15, 22, 16, 17, 18, 19, 1, 1, 1, 20, 1, 21, 1, 1]) (bs := [20, 1]) (W := 116384) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1271 : P.CoversSplit 24 10 1271 0xff000000aa0000000000000000000000ff000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 860, 865, 866, 867, 915, 916, 921, 1202, 1259]) (by decide +kernel)

theorem c1271_0 : P.sumLeaves 24 1301504 1024 = 1234848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1271) (lo := 0) (len := 1024) (W := 1234848) check rows elimOK (by decide) (by decide) cover1271 (by decide)
  decide +kernel

theorem h1271 : P.leaf 34 1271 = 1234848 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1234848)]) (.cons c1271_0 (.nil)) (by decide) (by decide))

theorem h1272 : P.leaf 34 1272 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (29, 1, 472), (18, 11, 475), (35, 14, 487), (28, 1, 508), (15, 1, 558), (11, 1, 559), (4, 1, 410), (30, 1, 858), (19, 1, 866), (14, 0, 867), (6, 1, 460), (12, 1, 460), (27, 1, 473), (34, 1, 573), (10, 1, 809), (32, 1, 865), (13, 1, 922)]) (q := 929) check rows (by decide) (by decide +kernel) (by decide +kernel)

def seg : List (ℕ × ℕ) := [(1240, 48), (1241, 48), (1242, 48), (1243, 48), (1244, 48), (1245, 48), (1246, 48), (1247, 48), (1248, 24), (1249, 48), (1250, 48), (1251, 48), (1252, 48), (1253, 48), (1254, 48), (1255, 48), (1256, 48), (1257, 48), (1258, 48), (1259, 48), (1260, 48), (1261, 48), (1262, 48), (1263, 48), (1265, 24), (1266, 48), (1267, 48), (1268, 48), (1269, 48), (1270, 48), (1271, 48), (1272, 48)]

theorem segOK : checkSeg 16 perms 1240 1273 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1240 1273 1488 139846656 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 139846656)
    (SegSum.cons (w := 48) h1240 (SegSum.cons (w := 48) h1241 (SegSum.cons (w := 48) h1242 (SegSum.cons (w := 48) h1243 (SegSum.cons (w := 48) h1244 (SegSum.cons (w := 48) h1245 (SegSum.cons (w := 48) h1246 (SegSum.cons (w := 48) h1247 (SegSum.cons (w := 24) h1248 (SegSum.cons (w := 48) h1249 (SegSum.cons (w := 48) h1250 (SegSum.cons (w := 48) h1251 (SegSum.cons (w := 48) h1252 (SegSum.cons (w := 48) h1253 (SegSum.cons (w := 48) h1254 (SegSum.cons (w := 48) h1255 (SegSum.cons (w := 48) h1256 (SegSum.cons (w := 48) h1257 (SegSum.cons (w := 48) h1258 (SegSum.cons (w := 48) h1259 (SegSum.cons (w := 48) h1260 (SegSum.cons (w := 48) h1261 (SegSum.cons (w := 48) h1262 (SegSum.cons (w := 48) h1263 (SegSum.cons (w := 24) h1265 (SegSum.cons (w := 48) h1266 (SegSum.cons (w := 48) h1267 (SegSum.cons (w := 48) h1268 (SegSum.cons (w := 48) h1269 (SegSum.cons (w := 48) h1270 (SegSum.cons (w := 48) h1271 (SegSum.cons (w := 48) h1272 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S8
