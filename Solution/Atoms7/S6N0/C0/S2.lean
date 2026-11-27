/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S2

open RACert RACert.Problem

theorem cover1189 : P.CoversSplit 26 10 1189 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000cc00c000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300300000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 873, 881, 922, 972, 1315, 1658, 2008]) (by decide +kernel)

theorem c1189_0 : P.sumLeaves 26 1217536 1024 = 85792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1189) (lo := 0) (len := 1024) (W := 85792) check rows elimOK (by decide) (by decide) cover1189 (by decide)
  decide +kernel

theorem h1189 : P.leaf 36 1189 = 85792 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 85792)]) (.cons c1189_0 (.nil)) (by decide) (by decide))

theorem cover1191 : P.CoversSplit 26 10 1191 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000cc00c000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300300000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 873, 881, 972, 1265, 1315, 1658, 2008]) (by decide +kernel)

theorem c1191_0 : P.sumLeaves 26 1219584 1024 = 671424 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1191) (lo := 0) (len := 1024) (W := 671424) check rows elimOK (by decide) (by decide) cover1191 (by decide)
  decide +kernel

theorem h1191 : P.leaf 36 1191 = 671424 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 671424)]) (.cons c1191_0 (.nil)) (by decide) (by decide))

theorem cover1192 : P.CoversSplit 26 10 1192 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1192_0 : P.sumLeaves 26 1220608 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1192) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1192 (by decide)
  decide +kernel

theorem h1192 : P.leaf 36 1192 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1192_0 (.nil)) (by decide) (by decide))

theorem cover1193 : P.CoversSplit 26 10 1193 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1193_0 : P.sumLeaves 26 1221632 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1193) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1193 (by decide)
  decide +kernel

theorem h1193 : P.leaf 36 1193 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1193_0 (.nil)) (by decide) (by decide))

theorem cover1195 : P.CoversSplit 26 10 1195 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1195_0 : P.sumLeaves 26 1223680 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1195) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1195 (by decide)
  decide +kernel

theorem h1195 : P.leaf 36 1195 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1195_0 (.nil)) (by decide) (by decide))

theorem cover1196 : P.CoversSplit 26 10 1196 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1196_0 : P.sumLeaves 26 1224704 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1196) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1196 (by decide)
  decide +kernel

theorem h1196 : P.leaf 36 1196 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1196_0 (.nil)) (by decide) (by decide))

theorem cover1197 : P.CoversSplit 26 10 1197 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1197_0 : P.sumLeaves 26 1225728 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1197) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1197 (by decide)
  decide +kernel

theorem h1197 : P.leaf 36 1197 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1197_0 (.nil)) (by decide) (by decide))

theorem cover1199 : P.CoversSplit 26 10 1199 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1199_0 : P.sumLeaves 26 1227776 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1199) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1199 (by decide)
  decide +kernel

theorem h1199 : P.leaf 36 1199 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1199_0 (.nil)) (by decide) (by decide))

theorem cover1207 : P.CoversSplit 26 10 1207 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000cc00c800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300320000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 873, 881, 972, 1315, 1658, 2008]) (by decide +kernel)

theorem c1207_0 : P.sumLeaves 26 1235968 1024 = 7228316 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1207) (lo := 0) (len := 1024) (W := 7228316) check rows elimOK (by decide) (by decide) cover1207 (by decide)
  decide +kernel

theorem h1207 : P.leaf 36 1207 = 7228316 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7228316)]) (.cons c1207_0 (.nil)) (by decide) (by decide))

theorem cover1208 : P.CoversSplit 26 10 1208 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1208_0 : P.sumLeaves 26 1236992 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1208) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1208 (by decide)
  decide +kernel

theorem h1208 : P.leaf 36 1208 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1208_0 (.nil)) (by decide) (by decide))

theorem cover1209 : P.CoversSplit 26 10 1209 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1209_0 : P.sumLeaves 26 1238016 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1209) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1209 (by decide)
  decide +kernel

theorem h1209 : P.leaf 36 1209 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1209_0 (.nil)) (by decide) (by decide))

theorem cover1211 : P.CoversSplit 26 10 1211 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1211_0 : P.sumLeaves 26 1240064 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1211) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1211 (by decide)
  decide +kernel

theorem h1211 : P.leaf 36 1211 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1211_0 (.nil)) (by decide) (by decide))

theorem cover1212 : P.CoversSplit 26 10 1212 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1212_0 : P.sumLeaves 26 1241088 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1212) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1212 (by decide)
  decide +kernel

theorem h1212 : P.leaf 36 1212 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1212_0 (.nil)) (by decide) (by decide))

theorem cover1213 : P.CoversSplit 26 10 1213 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1213_0 : P.sumLeaves 26 1242112 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1213) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1213 (by decide)
  decide +kernel

theorem h1213 : P.leaf 36 1213 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1213_0 (.nil)) (by decide) (by decide))

theorem cover1215 : P.CoversSplit 26 10 1215 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1215_0 : P.sumLeaves 26 1244160 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1215) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1215 (by decide)
  decide +kernel

theorem h1215 : P.leaf 36 1215 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1215_0 (.nil)) (by decide) (by decide))

theorem cover1228 : P.CoversSplit 26 10 1228 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem c1228_0 : P.sumLeaves 26 1257472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1228) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1228 (by decide)
  decide +kernel

theorem h1228 : P.leaf 36 1228 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1228_0 (.nil)) (by decide) (by decide))

theorem cover1229 : P.CoversSplit 26 10 1229 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem c1229_0 : P.sumLeaves 26 1258496 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1229) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1229 (by decide)
  decide +kernel

theorem h1229 : P.leaf 36 1229 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1229_0 (.nil)) (by decide) (by decide))

theorem cover1231 : P.CoversSplit 26 10 1231 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem c1231_0 : P.sumLeaves 26 1260544 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1231) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1231 (by decide)
  decide +kernel

theorem h1231 : P.leaf 36 1231 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1231_0 (.nil)) (by decide) (by decide))

theorem cover1244 : P.CoversSplit 26 10 1244 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem c1244_0 : P.sumLeaves 26 1273856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1244) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1244 (by decide)
  decide +kernel

theorem h1244 : P.leaf 36 1244 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1244_0 (.nil)) (by decide) (by decide))

theorem cover1245 : P.CoversSplit 26 10 1245 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem c1245_0 : P.sumLeaves 26 1274880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1245) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1245 (by decide)
  decide +kernel

theorem h1245 : P.leaf 36 1245 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1245_0 (.nil)) (by decide) (by decide))

theorem cover1247 : P.CoversSplit 26 10 1247 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem c1247_0 : P.sumLeaves 26 1276928 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1247) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1247 (by decide)
  decide +kernel

theorem h1247 : P.leaf 36 1247 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1247_0 (.nil)) (by decide) (by decide))

theorem cover1260 : P.CoversSplit 26 10 1260 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1260_0 : P.sumLeaves 26 1290240 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1260) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1260 (by decide)
  decide +kernel

theorem h1260 : P.leaf 36 1260 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1260_0 (.nil)) (by decide) (by decide))

theorem cover1261 : P.CoversSplit 26 10 1261 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1261_0 : P.sumLeaves 26 1291264 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1261) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1261 (by decide)
  decide +kernel

theorem h1261 : P.leaf 36 1261 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1261_0 (.nil)) (by decide) (by decide))

theorem cover1262 : P.CoversSplit 26 10 1262 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1262_0 : P.sumLeaves 26 1292288 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1262) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1262 (by decide)
  decide +kernel

theorem h1262 : P.leaf 36 1262 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1262_0 (.nil)) (by decide) (by decide))

theorem cover1263 : P.CoversSplit 26 10 1263 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1263_0 : P.sumLeaves 26 1293312 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1263) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1263 (by decide)
  decide +kernel

theorem h1263 : P.leaf 36 1263 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1263_0 (.nil)) (by decide) (by decide))

theorem cover1278 : P.CoversSplit 26 10 1278 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1278_0 : P.sumLeaves 26 1308672 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1278) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1278 (by decide)
  decide +kernel

theorem h1278 : P.leaf 36 1278 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1278_0 (.nil)) (by decide) (by decide))

theorem cover1279 : P.CoversSplit 26 10 1279 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1279_0 : P.sumLeaves 26 1309696 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1279) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1279 (by decide)
  decide +kernel

theorem h1279 : P.leaf 36 1279 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1279_0 (.nil)) (by decide) (by decide))

theorem cover1516 : P.CoversSplit 26 10 1516 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1516_0 : P.sumLeaves 26 1552384 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1516) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1516 (by decide)
  decide +kernel

theorem h1516 : P.leaf 36 1516 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1516_0 (.nil)) (by decide) (by decide))

theorem cover1517 : P.CoversSplit 26 10 1517 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1517_0 : P.sumLeaves 26 1553408 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1517) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1517 (by decide)
  decide +kernel

theorem h1517 : P.leaf 36 1517 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1517_0 (.nil)) (by decide) (by decide))

theorem cover1519 : P.CoversSplit 26 10 1519 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1519_0 : P.sumLeaves 26 1555456 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1519) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1519 (by decide)
  decide +kernel

theorem h1519 : P.leaf 36 1519 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1519_0 (.nil)) (by decide) (by decide))

theorem cover1535 : P.CoversSplit 26 10 1535 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1535_0 : P.sumLeaves 26 1571840 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1535) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1535 (by decide)
  decide +kernel

theorem h1535 : P.leaf 36 1535 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1535_0 (.nil)) (by decide) (by decide))

theorem cover1536 : P.CoversSplit 26 10 1536 0xf00000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000f :=
  coversSplit check rows (by decide) (by decide) (xs := [608, 615, 622, 873, 922, 1265]) (by decide +kernel)

theorem c1536_0 : P.sumLeaves 26 1572864 1024 = 72264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1536) (lo := 0) (len := 1024) (W := 72264) check rows elimOK (by decide) (by decide) cover1536 (by decide)
  decide +kernel

theorem h1536 : P.leaf 36 1536 = 72264 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 72264)]) (.cons c1536_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1189, 360), (1191, 360), (1192, 360), (1193, 720), (1195, 360), (1196, 360), (1197, 720), (1199, 360), (1207, 120), (1208, 360), (1209, 720), (1211, 360), (1212, 360), (1213, 720), (1215, 360), (1228, 360), (1229, 720), (1231, 360), (1244, 360), (1245, 720), (1247, 360), (1260, 360), (1261, 360), (1262, 720), (1263, 720), (1278, 360), (1279, 360), (1516, 60), (1517, 180), (1519, 180), (1535, 60), (1536, 10)]

theorem segOK : checkSeg 20 perms 1189 1537 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 1189 1537 12850 1140718320 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1140718320)
    (SegSum.cons (w := 360) h1189 (SegSum.cons (w := 360) h1191 (SegSum.cons (w := 360) h1192 (SegSum.cons (w := 720) h1193 (SegSum.cons (w := 360) h1195 (SegSum.cons (w := 360) h1196 (SegSum.cons (w := 720) h1197 (SegSum.cons (w := 360) h1199 (SegSum.cons (w := 120) h1207 (SegSum.cons (w := 360) h1208 (SegSum.cons (w := 720) h1209 (SegSum.cons (w := 360) h1211 (SegSum.cons (w := 360) h1212 (SegSum.cons (w := 720) h1213 (SegSum.cons (w := 360) h1215 (SegSum.cons (w := 360) h1228 (SegSum.cons (w := 720) h1229 (SegSum.cons (w := 360) h1231 (SegSum.cons (w := 360) h1244 (SegSum.cons (w := 720) h1245 (SegSum.cons (w := 360) h1247 (SegSum.cons (w := 360) h1260 (SegSum.cons (w := 360) h1261 (SegSum.cons (w := 720) h1262 (SegSum.cons (w := 720) h1263 (SegSum.cons (w := 360) h1278 (SegSum.cons (w := 360) h1279 (SegSum.cons (w := 60) h1516 (SegSum.cons (w := 180) h1517 (SegSum.cons (w := 180) h1519 (SegSum.cons (w := 60) h1535 (SegSum.cons (w := 10) h1536 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S2
