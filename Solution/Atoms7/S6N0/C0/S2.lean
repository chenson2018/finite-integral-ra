/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S2

open RACert RACert.Problem

theorem cover2195 : P.CoversSplit 26 10 2195 0x8000000000000000000000000000000000000000000000000000000000000000800000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 587, 629, 636, 881, 922, 2008]) (by decide +kernel)

theorem h2195 : P.leaf 36 2195 = 85792 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 2195) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 2195) (weight := fun _ => 1) (xs := [256, 341, 682, 767, 1023]) check rows elimOK (by decide) (by decide) cover2195 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1189 : P.leaf 36 1189 = 85792 :=
  orient4 (v := 2195) (by decide) (by decide +kernel) h2195

theorem cover2230 : P.CoversSplit 26 10 2230 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 866, 930, 972, 1315, 2008]) (by decide +kernel)

theorem h2230 : P.leaf 36 2230 = 671424 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 2230) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 2230) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 2230) (weight := rowWeight keep3 twice3) (xs := [320, 321, 324, 325, 336, 337, 340, 341, 746, 747, 750, 751, 762, 763, 766, 767, 1023]) check rows elimOK (by decide) (by decide) cover2230 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1191 : P.leaf 36 1191 = 671424 :=
  orient84 (v := 2230) (by decide) (by decide +kernel) h2230

theorem cover1192 : P.CoversSplit 26 10 1192 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1192 : P.leaf 36 1192 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1192) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1192) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1192 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1193 : P.CoversSplit 26 10 1193 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1193 : P.leaf 36 1193 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1193) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1193) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1193 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1195 : P.CoversSplit 26 10 1195 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1195 : P.leaf 36 1195 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1195) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1195) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1195 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1196 : P.CoversSplit 26 10 1196 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1196 : P.leaf 36 1196 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1196) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1196) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1196 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1197 : P.CoversSplit 26 10 1197 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1197 : P.leaf 36 1197 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1197) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1197) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1197 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1199 : P.CoversSplit 26 10 1199 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1199 : P.leaf 36 1199 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1199) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1199) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1199 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2231 : P.CoversSplit 26 10 2231 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000c8008800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003200220000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 881, 922, 972, 1265, 1315, 1658, 2008]) (by decide +kernel)

theorem h2231 : P.leaf 36 2231 = 7228316 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 2231) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 2231) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 2231) (weight := rowWeight keep3 twice3) (xs := [257, 261, 273, 276, 277, 320, 321, 324, 325, 336, 337, 340, 341, 683, 687, 699, 702, 703, 746, 747, 750, 751, 762, 763, 766, 767, 1023]) check rows elimOK (by decide) (by decide) cover2231 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1207 : P.leaf 36 1207 = 7228316 :=
  orient4 (v := 2231) (by decide) (by decide +kernel) h2231

theorem cover1208 : P.CoversSplit 26 10 1208 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1208 : P.leaf 36 1208 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1208) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1208) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1208 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1209 : P.CoversSplit 26 10 1209 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1209 : P.leaf 36 1209 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1209) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1209) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1209 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1211 : P.CoversSplit 26 10 1211 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1211 : P.leaf 36 1211 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1211) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1211) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1211 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1212 : P.CoversSplit 26 10 1212 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1212 : P.leaf 36 1212 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1212) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1212) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1212 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1213 : P.CoversSplit 26 10 1213 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1213 : P.leaf 36 1213 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1213) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1213) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1213 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1215 : P.CoversSplit 26 10 1215 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1215 : P.leaf 36 1215 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1215) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1215) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1215 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1228 : P.CoversSplit 26 10 1228 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem h1228 : P.leaf 36 1228 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1228) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1228) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1228 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1229 : P.CoversSplit 26 10 1229 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem h1229 : P.leaf 36 1229 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1229) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1229) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1229 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1231 : P.CoversSplit 26 10 1231 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem h1231 : P.leaf 36 1231 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1231) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1231) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1231 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1244 : P.CoversSplit 26 10 1244 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem h1244 : P.leaf 36 1244 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1244) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1244) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1244 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1245 : P.CoversSplit 26 10 1245 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem h1245 : P.leaf 36 1245 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1245) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1245) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1245 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1247 : P.CoversSplit 26 10 1247 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem h1247 : P.leaf 36 1247 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1247) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1247) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1247 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1260 : P.CoversSplit 26 10 1260 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1260 : P.leaf 36 1260 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1260) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1260) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1260 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1261 : P.CoversSplit 26 10 1261 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1261 : P.leaf 36 1261 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1261) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1261) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1261 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1262 : P.CoversSplit 26 10 1262 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1262 : P.leaf 36 1262 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1262) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1262) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1262 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1263 : P.CoversSplit 26 10 1263 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1263 : P.leaf 36 1263 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1263) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1263) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1263 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1278 : P.CoversSplit 26 10 1278 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1278 : P.leaf 36 1278 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1278) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1278) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1278 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1279 : P.CoversSplit 26 10 1279 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1279 : P.leaf 36 1279 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1279) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1279) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1279 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1516 : P.CoversSplit 26 10 1516 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1516 : P.leaf 36 1516 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1516) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1516) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1516 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1517 : P.CoversSplit 26 10 1517 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1517 : P.leaf 36 1517 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1517) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1517) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1517 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1519 : P.CoversSplit 26 10 1519 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1519 : P.leaf 36 1519 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1519) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1519) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1519 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1535 : P.CoversSplit 26 10 1535 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1535 : P.leaf 36 1535 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1535) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1535) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1535 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2304 : P.CoversSplit 26 10 2304 0x800000000000000000000000000000000000000000000000000000000000000000000000000000005500550000000000000000000000000055005500000000000000000000aa00aa00000000000000000000000000aa00aa00000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 629, 636, 881, 972, 979, 1315, 1322, 1658, 1665, 2008]) (by decide +kernel)

noncomputable def f2304 (i : ℕ) := rowWeight keep10 twice10 i * P.leaf 26 (2359296 + i)

theorem c2304_0 : rowSum f2304 0 1024 = 72264 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 2304) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover2304 (by decide)
  decide +kernel

theorem sum2304 : rowSum f2304 0 1024 = 72264 :=
  c2304_0

theorem h2304 : P.leaf 36 2304 = 72264 :=
  leaf_weighted (k := 26) (d := 10) (H := 2304) (keep := keep10) (twice := twice10) rows (by decide) (by decide) (bal10) (invRow10 (H := 2304) (by decide) (by decide +kernel)) sum2304

theorem h1536 : P.leaf 36 1536 = 72264 :=
  orient4 (v := 2304) (by decide) (by decide +kernel) h2304

def seg : List (ℕ × ℕ) := [(1189, 360), (1191, 360), (1192, 360), (1193, 720), (1195, 360), (1196, 360), (1197, 720), (1199, 360), (1207, 120), (1208, 360), (1209, 720), (1211, 360), (1212, 360), (1213, 720), (1215, 360), (1228, 360), (1229, 720), (1231, 360), (1244, 360), (1245, 720), (1247, 360), (1260, 360), (1261, 360), (1262, 720), (1263, 720), (1278, 360), (1279, 360), (1516, 60), (1517, 180), (1519, 180), (1535, 60), (1536, 10)]

theorem segOK : checkSeg 20 perms 1189 1537 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 1189 1537 12850 1140718320 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1140718320)
    (SegSum.cons (w := 360) h1189 (SegSum.cons (w := 360) h1191 (SegSum.cons (w := 360) h1192 (SegSum.cons (w := 720) h1193 (SegSum.cons (w := 360) h1195 (SegSum.cons (w := 360) h1196 (SegSum.cons (w := 720) h1197 (SegSum.cons (w := 360) h1199 (SegSum.cons (w := 120) h1207 (SegSum.cons (w := 360) h1208 (SegSum.cons (w := 720) h1209 (SegSum.cons (w := 360) h1211 (SegSum.cons (w := 360) h1212 (SegSum.cons (w := 720) h1213 (SegSum.cons (w := 360) h1215 (SegSum.cons (w := 360) h1228 (SegSum.cons (w := 720) h1229 (SegSum.cons (w := 360) h1231 (SegSum.cons (w := 360) h1244 (SegSum.cons (w := 720) h1245 (SegSum.cons (w := 360) h1247 (SegSum.cons (w := 360) h1260 (SegSum.cons (w := 360) h1261 (SegSum.cons (w := 720) h1262 (SegSum.cons (w := 720) h1263 (SegSum.cons (w := 360) h1278 (SegSum.cons (w := 360) h1279 (SegSum.cons (w := 60) h1516 (SegSum.cons (w := 180) h1517 (SegSum.cons (w := 180) h1519 (SegSum.cons (w := 60) h1535 (SegSum.cons (w := 10) h1536 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S2
