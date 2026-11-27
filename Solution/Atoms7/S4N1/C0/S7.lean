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

theorem c1207_0 : P.sumLeaves 24 1235968 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1207) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1207 (by decide)
  decide +kernel

theorem h1207 : P.leaf 34 1207 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1207_0 (.nil)) (by decide) (by decide))

theorem h1208 : P.leaf 34 1208 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (29, 1, 472), (18, 11, 475), (33, 14, 486), (35, 14, 487), (28, 1, 508), (15, 1, 509), (11, 1, 559), (4, 1, 410), (30, 1, 858), (19, 1, 866), (14, 0, 867), (6, 1, 460), (12, 1, 460), (27, 1, 473), (26, 1, 517), (31, 1, 517), (34, 5, 524), (5, 1, 566), (3, 1, 409), (10, 1, 809), (16, 1, 468), (32, 1, 865), (21, 0, 874), (20, 1, 880), (13, 1, 922)]) (q := 929) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover1209 : P.CoversSplit 24 10 1209 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1209_0 : P.sumLeaves 24 1238016 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1209) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1209 (by decide)
  decide +kernel

theorem h1209 : P.leaf 34 1209 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1209_0 (.nil)) (by decide) (by decide))

theorem h1210 : P.leaf 34 1210 = 2032 := by
  exact leaf_contract_factors (k := 34) (b := 12) (H := 1210) (ss := [(33, 14, 486), (19, 1, 866), (35, 0, 867), (34, 5, 524), (5, 1, 426), (18, 1, 879), (11, 1, 901), (12, 1, 818), (29, 1, 921), (27, 1, 573), (13, 1, 922), (15, 1, 930), (30, 1, 1251), (28, 1, 858), (31, 1, 1202), (32, 1, 1259), (10, 1, 809), (16, 1, 468), (14, 1, 1308), (8, 1, 580), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 4, 7, 15, 20, 24, 5, 21, 22, 23]) (cs := [2, 3, 4, 1, 5, 10, 1, 6, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 8, 11, 12, 13, 9, 1, 1, 1, 1, 1, 1, 1, 1, 0]) (bs := [8, 4]) (W := 2032) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1211 : P.CoversSplit 24 10 1211 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1211_0 : P.sumLeaves 24 1240064 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1211) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1211 (by decide)
  decide +kernel

theorem h1211 : P.leaf 34 1211 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1211_0 (.nil)) (by decide) (by decide))

theorem cover1212 : P.CoversSplit 24 10 1212 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1212_0 : P.sumLeaves 24 1241088 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1212) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1212 (by decide)
  decide +kernel

theorem h1212 : P.leaf 34 1212 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1212_0 (.nil)) (by decide) (by decide))

theorem cover1213 : P.CoversSplit 24 10 1213 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1213_0 : P.sumLeaves 24 1242112 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1213) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1213 (by decide)
  decide +kernel

theorem h1213 : P.leaf 34 1213 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1213_0 (.nil)) (by decide) (by decide))

theorem cover1214 : P.CoversSplit 24 10 1214 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1214_0 : P.sumLeaves 24 1243136 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1214) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1214 (by decide)
  decide +kernel

theorem h1214 : P.leaf 34 1214 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1214_0 (.nil)) (by decide) (by decide))

theorem cover1215 : P.CoversSplit 24 10 1215 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1215_0 : P.sumLeaves 24 1244160 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1215) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1215 (by decide)
  decide +kernel

theorem h1215 : P.leaf 34 1215 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1215_0 (.nil)) (by decide) (by decide))

theorem cover1216 : P.CoversSplit 24 10 1216 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1216_0 : P.sumLeaves 24 1245184 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1216) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1216 (by decide)
  decide +kernel

theorem h1216 : P.leaf 34 1216 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1216_0 (.nil)) (by decide) (by decide))

theorem cover1217 : P.CoversSplit 24 10 1217 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1217_0 : P.sumLeaves 24 1246208 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1217) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1217 (by decide)
  decide +kernel

theorem h1217 : P.leaf 34 1217 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1217_0 (.nil)) (by decide) (by decide))

theorem cover1218 : P.CoversSplit 24 10 1218 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1218_0 : P.sumLeaves 24 1247232 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1218) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1218 (by decide)
  decide +kernel

theorem h1218 : P.leaf 34 1218 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1218_0 (.nil)) (by decide) (by decide))

theorem cover1219 : P.CoversSplit 24 10 1219 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1219_0 : P.sumLeaves 24 1248256 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1219) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1219 (by decide)
  decide +kernel

theorem h1219 : P.leaf 34 1219 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1219_0 (.nil)) (by decide) (by decide))

theorem cover1220 : P.CoversSplit 24 10 1220 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1220_0 : P.sumLeaves 24 1249280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1220) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1220 (by decide)
  decide +kernel

theorem h1220 : P.leaf 34 1220 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1220_0 (.nil)) (by decide) (by decide))

theorem cover1221 : P.CoversSplit 24 10 1221 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1221_0 : P.sumLeaves 24 1250304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1221) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1221 (by decide)
  decide +kernel

theorem h1221 : P.leaf 34 1221 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1221_0 (.nil)) (by decide) (by decide))

theorem cover1222 : P.CoversSplit 24 10 1222 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1222_0 : P.sumLeaves 24 1251328 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1222) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1222 (by decide)
  decide +kernel

theorem h1222 : P.leaf 34 1222 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1222_0 (.nil)) (by decide) (by decide))

theorem cover1223 : P.CoversSplit 24 10 1223 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1223_0 : P.sumLeaves 24 1252352 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1223) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1223 (by decide)
  decide +kernel

theorem h1223 : P.leaf 34 1223 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1223_0 (.nil)) (by decide) (by decide))

theorem cover1224 : P.CoversSplit 24 10 1224 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1224_0 : P.sumLeaves 24 1253376 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1224) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1224 (by decide)
  decide +kernel

theorem h1224 : P.leaf 34 1224 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1224_0 (.nil)) (by decide) (by decide))

theorem cover1225 : P.CoversSplit 24 10 1225 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1225_0 : P.sumLeaves 24 1254400 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1225) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1225 (by decide)
  decide +kernel

theorem h1225 : P.leaf 34 1225 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1225_0 (.nil)) (by decide) (by decide))

theorem cover1226 : P.CoversSplit 24 10 1226 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1226_0 : P.sumLeaves 24 1255424 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1226) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1226 (by decide)
  decide +kernel

theorem h1226 : P.leaf 34 1226 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1226_0 (.nil)) (by decide) (by decide))

theorem cover1227 : P.CoversSplit 24 10 1227 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1227_0 : P.sumLeaves 24 1256448 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1227) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1227 (by decide)
  decide +kernel

theorem h1227 : P.leaf 34 1227 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1227_0 (.nil)) (by decide) (by decide))

theorem cover1228 : P.CoversSplit 24 10 1228 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1228_0 : P.sumLeaves 24 1257472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1228) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1228 (by decide)
  decide +kernel

theorem h1228 : P.leaf 34 1228 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1228_0 (.nil)) (by decide) (by decide))

theorem cover1229 : P.CoversSplit 24 10 1229 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1229_0 : P.sumLeaves 24 1258496 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1229) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1229 (by decide)
  decide +kernel

theorem h1229 : P.leaf 34 1229 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1229_0 (.nil)) (by decide) (by decide))

theorem cover1230 : P.CoversSplit 24 10 1230 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1230_0 : P.sumLeaves 24 1259520 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1230) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1230 (by decide)
  decide +kernel

theorem h1230 : P.leaf 34 1230 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1230_0 (.nil)) (by decide) (by decide))

theorem cover1231 : P.CoversSplit 24 10 1231 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1231_0 : P.sumLeaves 24 1260544 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1231) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1231 (by decide)
  decide +kernel

theorem h1231 : P.leaf 34 1231 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1231_0 (.nil)) (by decide) (by decide))

theorem cover1233 : P.CoversSplit 24 10 1233 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem c1233_0 : P.sumLeaves 24 1262592 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1233) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1233 (by decide)
  decide +kernel

theorem h1233 : P.leaf 34 1233 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1233_0 (.nil)) (by decide) (by decide))

theorem cover1234 : P.CoversSplit 24 10 1234 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1234_0 : P.sumLeaves 24 1263616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1234) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1234 (by decide)
  decide +kernel

theorem h1234 : P.leaf 34 1234 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1234_0 (.nil)) (by decide) (by decide))

theorem cover1235 : P.CoversSplit 24 10 1235 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1235_0 : P.sumLeaves 24 1264640 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1235) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1235 (by decide)
  decide +kernel

theorem h1235 : P.leaf 34 1235 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1235_0 (.nil)) (by decide) (by decide))

theorem cover1236 : P.CoversSplit 24 10 1236 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem c1236_0 : P.sumLeaves 24 1265664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1236) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1236 (by decide)
  decide +kernel

theorem h1236 : P.leaf 34 1236 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1236_0 (.nil)) (by decide) (by decide))

theorem cover1237 : P.CoversSplit 24 10 1237 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem c1237_0 : P.sumLeaves 24 1266688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1237) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1237 (by decide)
  decide +kernel

theorem h1237 : P.leaf 34 1237 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1237_0 (.nil)) (by decide) (by decide))

theorem h1238 : P.leaf 34 1238 = 37120 := by
  exact leaf_contract_factors (k := 34) (b := 19) (H := 1238) (ss := [(5, 1, 559), (30, 19, 866), (35, 1, 867), (18, 11, 879), (11, 1, 901), (6, 1, 458), (10, 1, 458), (12, 1, 817), (19, 1, 908), (26, 1, 465), (28, 1, 465), (29, 1, 921), (34, 1, 916), (31, 1, 1210), (32, 1, 1259)]) (ids := [0, 1, 2, 5, 6, 7, 11, 12, 13, 14, 15, 18, 19, 20, 23, 25, 31, 21, 22]) (cs := [2, 3, 4, 1, 1, 5, 6, 7, 1, 1, 1, 8, 9, 10, 11, 12, 1, 1, 13, 14, 15, 19, 20, 16, 1, 17, 1, 1, 1, 1, 1, 18, 1, 1]) (bs := [17, 2]) (W := 37120) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1239 : P.CoversSplit 24 10 1239 0xff000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 860, 865, 866, 867, 915, 916, 921, 1202, 1210, 1259]) (by decide +kernel)

theorem c1239_0 : P.sumLeaves 24 1268736 1024 = 708064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1239) (lo := 0) (len := 1024) (W := 708064) check rows elimOK (by decide) (by decide) cover1239 (by decide)
  decide +kernel

theorem h1239 : P.leaf 34 1239 = 708064 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 708064)]) (.cons c1239_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1207, 48), (1208, 48), (1209, 48), (1210, 48), (1211, 48), (1212, 48), (1213, 48), (1214, 48), (1215, 48), (1216, 24), (1217, 48), (1218, 48), (1219, 48), (1220, 48), (1221, 48), (1222, 48), (1223, 48), (1224, 48), (1225, 48), (1226, 48), (1227, 48), (1228, 48), (1229, 48), (1230, 48), (1231, 48), (1233, 24), (1234, 48), (1235, 48), (1236, 48), (1237, 48), (1238, 48), (1239, 48)]

theorem segOK : checkSeg 16 perms 1207 1240 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1207 1240 1488 35866368 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 35866368)
    (SegSum.cons (w := 48) h1207 (SegSum.cons (w := 48) h1208 (SegSum.cons (w := 48) h1209 (SegSum.cons (w := 48) h1210 (SegSum.cons (w := 48) h1211 (SegSum.cons (w := 48) h1212 (SegSum.cons (w := 48) h1213 (SegSum.cons (w := 48) h1214 (SegSum.cons (w := 48) h1215 (SegSum.cons (w := 24) h1216 (SegSum.cons (w := 48) h1217 (SegSum.cons (w := 48) h1218 (SegSum.cons (w := 48) h1219 (SegSum.cons (w := 48) h1220 (SegSum.cons (w := 48) h1221 (SegSum.cons (w := 48) h1222 (SegSum.cons (w := 48) h1223 (SegSum.cons (w := 48) h1224 (SegSum.cons (w := 48) h1225 (SegSum.cons (w := 48) h1226 (SegSum.cons (w := 48) h1227 (SegSum.cons (w := 48) h1228 (SegSum.cons (w := 48) h1229 (SegSum.cons (w := 48) h1230 (SegSum.cons (w := 48) h1231 (SegSum.cons (w := 24) h1233 (SegSum.cons (w := 48) h1234 (SegSum.cons (w := 48) h1235 (SegSum.cons (w := 48) h1236 (SegSum.cons (w := 48) h1237 (SegSum.cons (w := 48) h1238 (SegSum.cons (w := 48) h1239 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S7
