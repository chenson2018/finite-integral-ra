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

namespace RACert.S6N0.C0.S12

open RACert RACert.Problem

theorem cover3998 : P.CoversSplit 26 10 3998 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h3998 : P.leaf 36 3998 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3998) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3998) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3998 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3999 : P.CoversSplit 26 10 3999 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h3999 : P.leaf 36 3999 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3999) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3999) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3999 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4022 : P.CoversSplit 26 10 4022 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h4022 : P.leaf 36 4022 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4022) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4022) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4022 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4023 : P.CoversSplit 26 10 4023 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h4023 : P.leaf 36 4023 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4023) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4023) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4023 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4024 : P.CoversSplit 26 10 4024 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h4024 : P.leaf 36 4024 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4024) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4024) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4024 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4025 : P.CoversSplit 26 10 4025 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h4025 : P.leaf 36 4025 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4025) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4025) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4025 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4026 : P.CoversSplit 26 10 4026 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h4026 : P.leaf 36 4026 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4026) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4026) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4026 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4027 : P.CoversSplit 26 10 4027 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h4027 : P.leaf 36 4027 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4027) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4027) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4027 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4030 : P.CoversSplit 26 10 4030 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h4030 : P.leaf 36 4030 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4030) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4030) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4030 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4031 : P.CoversSplit 26 10 4031 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h4031 : P.leaf 36 4031 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4031) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4031) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4031 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4040 : P.CoversSplit 26 10 4040 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h4040 : P.leaf 36 4040 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4040) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4040) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4040 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4041 : P.CoversSplit 26 10 4041 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h4041 : P.leaf 36 4041 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4041) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4041) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4041 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4042 : P.CoversSplit 26 10 4042 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h4042 : P.leaf 36 4042 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4042) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4042) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4042 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4043 : P.CoversSplit 26 10 4043 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h4043 : P.leaf 36 4043 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4043) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4043) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4043 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4046 : P.CoversSplit 26 10 4046 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h4046 : P.leaf 36 4046 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4046) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4046) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4046 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4047 : P.CoversSplit 26 10 4047 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h4047 : P.leaf 36 4047 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4047) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4047) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4047 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4058 : P.CoversSplit 26 10 4058 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h4058 : P.leaf 36 4058 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4058) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4058) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4058 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4059 : P.CoversSplit 26 10 4059 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h4059 : P.leaf 36 4059 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4059) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4059) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4059 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4060 : P.CoversSplit 26 10 4060 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h4060 : P.leaf 36 4060 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4060) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4060) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4060 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4061 : P.CoversSplit 26 10 4061 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h4061 : P.leaf 36 4061 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4061) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4061) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4061 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4062 : P.CoversSplit 26 10 4062 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h4062 : P.leaf 36 4062 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4062) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4062) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4062 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4063 : P.CoversSplit 26 10 4063 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h4063 : P.leaf 36 4063 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 4063) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 4063) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover4063 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover295423 : P.CoversSplit 26 10 295423 0xfffffafaffccfac8000000000000000000000000000000001000000000000000555550505544504050500000504000000000000000000000100000000000000033333232330032000000000000000000330032000000000010000000000000001111101011001000101000001000000011001000000000001000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 873, 881, 922, 930, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f295423 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (302513152 + i)

theorem c295423_0 : rowSum f295423 0 1024 = 32719032 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 295423) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover295423 (by decide)
  decide +kernel

theorem sum295423 : rowSum f295423 0 1024 = 32719032 :=
  c295423_0

theorem h295423 : P.leaf 36 295423 = 32719032 :=
  leaf_weighted (k := 26) (d := 10) (H := 295423) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 295423) (by decide) (by decide +kernel)) sum295423

theorem h4094 : P.leaf 36 4094 = 32719032 :=
  orient324 (v := 295423) (by decide) (by decide +kernel) h295423

theorem cover295935 : P.CoversSplit 26 10 295935 0xfffffafaffccfac8fafaaaaafac8aa88ffccfac8ccccc8c88888888888888888fffffafaffccfac8aaaaaaaaaa88aa88ffccfac8ccccc8c88888888888888888fffffafaffccfac8fafaaaaafac8aa88ccccc8c8ccccc8c88888888888888888fffffafaffccfac8aaaaaaaaaa88aa88ccccc8c8ccccc8c88888888888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 881, 922, 930, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f295935 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (303037440 + i)

theorem c295935_0 : rowSum f295935 0 355 = 223275906 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 295935) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover295935 (by decide)
  decide +kernel

theorem c295935_1 : rowSum f295935 355 155 = 293038936 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 295935) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover295935 (by decide)
  decide +kernel

theorem c295935_2 : rowSum f295935 510 514 = 234711288 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 295935) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover295935 (by decide)
  decide +kernel

theorem sum295935 : rowSum f295935 0 1024 = 751026130 :=
  rowSum_append (F := f295935) (lo := 0) (n := 355) (m := 669) (A := 223275906) (B := 527750224) c295935_0 (rowSum_append (F := f295935) (lo := 355) (n := 155) (m := 514) (A := 293038936) (B := 234711288) c295935_1 (c295935_2))

theorem h295935 : P.leaf 36 295935 = 751026130 :=
  leaf_weighted (k := 26) (d := 10) (H := 295935) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 295935) (by decide) (by decide +kernel)) sum295935

theorem h4095 : P.leaf 36 4095 = 751026130 :=
  orient324 (v := 295935) (by decide) (by decide +kernel) h295935

theorem cover7294 : P.CoversSplit 26 10 7294 0x8000000000000001000000000000000000000000000000000000000000000001000004000000000100000400000000010000000000000000000000000000000100000000002000010000000000000000000000000020000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 587, 629, 636, 922, 930, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h7294 : P.leaf 36 7294 = 257784 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 7294) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 7294) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 7294) (weight := rowWeight keep0 twice0) (xs := [256, 320, 341, 448, 469, 512, 640, 682, 704, 746, 768, 960, 1023]) check rows elimOK (by decide) (by decide) cover7294 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7295 : P.CoversSplit 26 10 7295 0x8000000000000001000000000000000000000000000000000000000000000001000004000000000100000400000000010000000000000000000000000000000100000000002000010000000000000000000000000020000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 587, 629, 636, 922, 930, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h7295 : P.leaf 36 7295 = 530568 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 7295) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 7295) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 7295) (weight := rowWeight keep0 twice0) (xs := [256, 320, 341, 448, 469, 512, 640, 682, 704, 746, 768, 960, 1023]) check rows elimOK (by decide) (by decide) cover7295 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover75947 : P.CoversSplit 26 10 75947 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100210000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 538, 587, 629, 636, 881, 972, 1315, 1658]) (by decide +kernel)

theorem h75947 : P.leaf 36 75947 = 21106 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 75947) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 75947) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 75947) (weight := rowWeight keep1 twice1) (xs := [256, 261, 272, 277, 320, 325, 336, 341, 1023]) check rows elimOK (by decide) (by decide) cover75947 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7350 : P.leaf 36 7350 = 21106 :=
  orient85 (v := 75947) (by decide) (by decide +kernel) h75947

theorem cover75951 : P.CoversSplit 26 10 75951 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100210000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 587, 629, 636, 881, 972, 1315, 1658]) (by decide +kernel)

theorem h75951 : P.leaf 36 75951 = 36401 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 75951) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 75951) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 75951) (weight := rowWeight keep1 twice1) (xs := [256, 261, 272, 277, 320, 325, 336, 341, 1023]) check rows elimOK (by decide) (by decide) cover75951 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7351 : P.leaf 36 7351 = 36401 :=
  orient85 (v := 75951) (by decide) (by decide +kernel) h75951

theorem cover7352 : P.CoversSplit 26 10 7352 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h7352 : P.leaf 36 7352 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 7352) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 7352) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7352 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7353 : P.CoversSplit 26 10 7353 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h7353 : P.leaf 36 7353 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 7353) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 7353) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7353 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7354 : P.CoversSplit 26 10 7354 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h7354 : P.leaf 36 7354 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 7354) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 7354) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7354 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7355 : P.CoversSplit 26 10 7355 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h7355 : P.leaf 36 7355 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 7355) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 7355) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7355 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(3998, 720), (3999, 720), (4022, 180), (4023, 180), (4024, 360), (4025, 360), (4026, 720), (4027, 720), (4030, 360), (4031, 360), (4040, 180), (4041, 180), (4042, 720), (4043, 720), (4046, 360), (4047, 360), (4058, 360), (4059, 360), (4060, 360), (4061, 360), (4062, 720), (4063, 720), (4094, 180), (4095, 180), (7294, 20), (7295, 20), (7350, 180), (7351, 180), (7352, 360), (7353, 360), (7354, 720), (7355, 720)]

theorem segOK : checkSeg 20 perms 3998 7358 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 3998 7358 13000 141100247460 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 141100247460)
    (SegSum.cons (w := 720) h3998 (SegSum.cons (w := 720) h3999 (SegSum.cons (w := 180) h4022 (SegSum.cons (w := 180) h4023 (SegSum.cons (w := 360) h4024 (SegSum.cons (w := 360) h4025 (SegSum.cons (w := 720) h4026 (SegSum.cons (w := 720) h4027 (SegSum.cons (w := 360) h4030 (SegSum.cons (w := 360) h4031 (SegSum.cons (w := 180) h4040 (SegSum.cons (w := 180) h4041 (SegSum.cons (w := 720) h4042 (SegSum.cons (w := 720) h4043 (SegSum.cons (w := 360) h4046 (SegSum.cons (w := 360) h4047 (SegSum.cons (w := 360) h4058 (SegSum.cons (w := 360) h4059 (SegSum.cons (w := 360) h4060 (SegSum.cons (w := 360) h4061 (SegSum.cons (w := 720) h4062 (SegSum.cons (w := 720) h4063 (SegSum.cons (w := 180) h4094 (SegSum.cons (w := 180) h4095 (SegSum.cons (w := 20) h7294 (SegSum.cons (w := 20) h7295 (SegSum.cons (w := 180) h7350 (SegSum.cons (w := 180) h7351 (SegSum.cons (w := 360) h7352 (SegSum.cons (w := 360) h7353 (SegSum.cons (w := 720) h7354 (SegSum.cons (w := 720) h7355 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S12
