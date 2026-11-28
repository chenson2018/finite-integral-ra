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

namespace RACert.S4N1.C0.S72

open RACert RACert.Problem

theorem cover23976 : P.CoversSplit 24 10 23976 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem h23976 : P.leaf 34 23976 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 23976) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 23976) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover23976 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover23977 : P.CoversSplit 24 10 23977 0xaaaa0000bab00000aaaa0000bab00000aaaa000000000000aaaa0000000000008888000088800000880000008800000088880000000000008800000000000000aa000000ba0000000000000000000000aa0000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [472, 473, 515, 522, 858, 865, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c23977_0 : P.sumLeaves 24 24552448 1024 = 7402356 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23977) (lo := 0) (len := 1024) (W := 7402356) check rows elimOK (by decide) (by decide) cover23977 (by decide)
  decide +kernel

theorem h23977 : P.leaf 34 23977 = 7402356 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7402356)]) (.cons c23977_0 (.nil)) (by decide) (by decide))

theorem cover40393 : P.CoversSplit 24 10 40393 0xaa000000ba0000000000000000000000aa000000000000000000000000000000aa000000ba0000000000000000000000aa000000000000000000000000000000aa000000ba0000000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 858, 865, 916, 1202, 1209, 1258, 1601]) (by decide +kernel)

theorem c40393_0 : P.sumLeaves 24 41362432 1024 = 3793384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 40393) (lo := 0) (len := 1024) (W := 3793384) check rows elimOK (by decide) (by decide) cover40393 (by decide)
  decide +kernel

theorem h40393 : P.leaf 34 40393 = 3793384 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3793384)]) (.cons c40393_0 (.nil)) (by decide) (by decide))

theorem h23978 : P.leaf 34 23978 = 3793384 :=
  orient25 (v := 40393) (by decide) (by decide +kernel) h40393

theorem cover23979 : P.CoversSplit 24 10 23979 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000008888000088880000880000008800000088880000000000008800000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [472, 515, 517, 522, 858, 865, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c23979_0 : P.sumLeaves 24 24554496 1024 = 21176370 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23979) (lo := 0) (len := 1024) (W := 21176370) check rows elimOK (by decide) (by decide) cover23979 (by decide)
  decide +kernel

theorem h23979 : P.leaf 34 23979 = 21176370 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 21176370)]) (.cons c23979_0 (.nil)) (by decide) (by decide))

theorem cover23980 : P.CoversSplit 24 10 23980 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [508]) (by decide +kernel)

theorem h23980 : P.leaf 34 23980 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 23980) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 23980) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover23980 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover59644 : P.CoversSplit 24 10 59644 0xc000c000c0008000c000c000c0008000c000c00040000000c000c00040000000f0c0f0c0e0c0a080c000c000c0008000f000f00040000000c000c00040000000c000c000c0008000c000c000c0008000c000c00040000000c000c000400000003030303020302020000000000000000030003000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 473, 573, 859, 865, 908, 915, 1202, 1601]) (ps := [(6, [465], [473])]) (by decide +kernel)

theorem c59644_0 : P.sumLeaves 24 61075456 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 59644) (lo := 0) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover59644 (by decide)
  decide +kernel

theorem contract59644_1 : P.leaf 30 954305 = 0 := by
  exact leaf_contract_zero (ss := [(28, 1, 466), (29, 1, 908), (12, 0, 915), (13, 1, 852), (27, 0, 915), (6, 0, 473), (10, 1, 459), (18, 1, 487)]) (q := 803) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c59644_1 : P.sumLeaves 24 61075520 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 954305) rows (by decide) (by decide)).symm.trans contract59644_1

theorem c59644_2 : P.sumLeaves 24 61075584 862 = 13803084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 59644) (lo := 128) (len := 862) (W := 13803084) check rows elimOK (by decide) (by decide) cover59644 (by decide)
  decide +kernel

theorem c59644_3 : P.sumLeaves 24 61076446 34 = 3288800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 59644) (lo := 990) (len := 34) (W := 3288800) check rows elimOK (by decide) (by decide) cover59644 (by decide)
  decide +kernel

theorem h59644 : P.leaf 34 59644 = 17091884 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (862, 13803084), (34, 3288800)]) (.cons c59644_0 (.cons c59644_1 (.cons c59644_2 (.cons c59644_3 (.nil))))) (by decide) (by decide))

theorem h23981 : P.leaf 34 23981 = 17091884 :=
  orient24 (v := 59644) (by decide) (by decide +kernel) h59644

theorem cover40425 : P.CoversSplit 24 10 40425 0xff000000ea0000000000000000000000ff000000000000000000000000000000ff000000ea0000000000000000000000ff000000000000000000000000000000ff000000ea0000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 858, 865, 916, 1202, 1209, 1258, 1601]) (by decide +kernel)

theorem c40425_0 : P.sumLeaves 24 41395200 1024 = 21976726 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 40425) (lo := 0) (len := 1024) (W := 21976726) check rows elimOK (by decide) (by decide) cover40425 (by decide)
  decide +kernel

theorem h40425 : P.leaf 34 40425 = 21976726 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 21976726)]) (.cons c40425_0 (.nil)) (by decide) (by decide))

theorem h23982 : P.leaf 34 23982 = 21976726 :=
  orient25 (v := 40425) (by decide) (by decide +kernel) h40425

theorem cover23983 : P.CoversSplit 24 10 23983 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000008888000088880000888800008888000088880000000000008888000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c23983_0 : P.sumLeaves 24 24558592 1021 = 45678058 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23983) (lo := 0) (len := 1021) (W := 45678058) check rows elimOK (by decide) (by decide) cover23983 (by decide)
  decide +kernel

theorem c23983_1 : P.sumLeaves 24 24559613 3 = 4954192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23983) (lo := 1021) (len := 3) (W := 4954192) check rows elimOK (by decide) (by decide) cover23983 (by decide)
  decide +kernel

theorem h23983 : P.leaf 34 23983 = 50632250 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 45678058), (3, 4954192)]) (.cons c23983_0 (.cons c23983_1 (.nil))) (by decide) (by decide))

theorem cover59196 : P.CoversSplit 24 10 59196 0xfca8fca8f8a80000fca8fca8f8a80000fca8fca8c8000000fca8fca8c8000000fc88fc88f88800000000000000000000fc88fc88c80000000000000000000000fca8fca8f8a80000fca8fca8f8a80000fca8fca8c8000000fca8fca8c8000000a080a080a08000000000000000000000a080a080000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 472, 473, 529, 872, 1202, 1601]) (ps := [(8, [615], [1272])]) (by decide +kernel)

noncomputable def f59196 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (60616704 + i)

theorem c59196_0 : rowSum f59196 0 750 = 45561040 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59196) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover59196 (by decide)
  decide +kernel

theorem c59196_1 : rowSum f59196 750 274 = 52920136 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59196) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover59196 (by decide)
  decide +kernel

theorem sum59196 : rowSum f59196 0 1024 = 98481176 :=
  rowSum_append (F := f59196) (lo := 0) (n := 750) (m := 274) (A := 45561040) (B := 52920136) c59196_0 (c59196_1)

theorem h59196 : P.leaf 34 59196 = 98481176 :=
  leaf_weighted (k := 24) (d := 10) (H := 59196) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 59196) (by decide) (by decide +kernel)) sum59196

theorem h23990 : P.leaf 34 23990 = 98481176 :=
  orient5 (v := 59196) (by decide) (by decide +kernel) h59196

theorem cover59197 : P.CoversSplit 24 10 59197 0xffffffffffff0000ffffffffffff0000ffffffffcc000000ffffffffcc000000ffffffffffff00000000000000000000ffffffffcc0000000000000000000000ffffffffffff0000ffffffffffff0000ffffffffc8000000ffffffffc8000000a0a0a0a0a0a000000000000000000000a080a080000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 529, 872, 1202, 1217, 1601, 1609]) (ps := [(8, [615], [1272])]) (by decide +kernel)

noncomputable def f59197 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (60617728 + i)

theorem c59197_0 : rowSum f59197 0 479 = 31654441 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59197) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover59197 (by decide)
  decide +kernel

theorem c59197_1 : rowSum f59197 479 352 = 62888127 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59197) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover59197 (by decide)
  decide +kernel

theorem c59197_2 : rowSum f59197 831 193 = 123612163 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59197) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover59197 (by decide)
  decide +kernel

theorem sum59197 : rowSum f59197 0 1024 = 218154731 :=
  rowSum_append (F := f59197) (lo := 0) (n := 479) (m := 545) (A := 31654441) (B := 186500290) c59197_0 (rowSum_append (F := f59197) (lo := 479) (n := 352) (m := 193) (A := 62888127) (B := 123612163) c59197_1 (c59197_2))

theorem h59197 : P.leaf 34 59197 = 218154731 :=
  leaf_weighted (k := 24) (d := 10) (H := 59197) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 59197) (by decide) (by decide +kernel)) sum59197

theorem h23991 : P.leaf 34 23991 = 218154731 :=
  orient5 (v := 59197) (by decide) (by decide +kernel) h59197

theorem cover24007 : P.CoversSplit 24 10 24007 0xfffffffff0f0a0a0ffff0000f0f00000ffff000000005050ffff000000000000cccccccc80008000cc00000080000000cccc000040004000cc00000000000000fffffffff0f0a0a00000000000000000ffff55550000505000ff000000000000000000000080000000cc000000800000000000000040000000cc000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [466, 515, 522, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(17, [615], [1251]), (18, [965], [1264])]) (by decide +kernel)

noncomputable def f24007 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (24583168 + i)

theorem c24007_0 : rowSum f24007 0 945 = 20493584 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24007) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24007 (by decide)
  decide +kernel

theorem c24007_1 : rowSum f24007 945 79 = 15837940 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24007) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24007 (by decide)
  decide +kernel

theorem sum24007 : rowSum f24007 0 1024 = 36331524 :=
  rowSum_append (F := f24007) (lo := 0) (n := 945) (m := 79) (A := 20493584) (B := 15837940) c24007_0 (c24007_1)

theorem h24007 : P.leaf 34 24007 = 36331524 :=
  leaf_weighted (k := 24) (d := 10) (H := 24007) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 24007) (by decide) (by decide +kernel)) sum24007

theorem h23993 : P.leaf 34 23993 = 36331524 :=
  orient4 (v := 24007) (by decide) (by decide +kernel) h24007

theorem cover24022 : P.CoversSplit 24 10 24022 0xfffffffff0f0a0a0fffffffff0f0a0a0aaaa000000000000aaaa000000000000ccc0ccc080008000cc00cc008000800088800000000000008800000000000000fffffffff0f0a0a0fffffffff0f0a0a0aaaa000000000000aaaa000000000000ccc0ccc080008000cc00cc008000800088000000000000008800000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(8, [1609], [1266]), (18, [867], [1210])]) (by decide +kernel)

theorem c24022_0 : P.sumLeaves 24 24598528 256 = 598432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24022) (lo := 0) (len := 256) (W := 598432) check rows elimOK (by decide) (by decide) cover24022 (by decide)
  decide +kernel

theorem contract24022_1 : P.leaf 30 384356 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (6, 1, 479), (18, 1, 867), (11, 1, 879), (8, 0, 1266), (20, 1, 531), (21, 1, 537), (5, 1, 565), (31, 1, 615), (30, 1, 1210), (26, 1, 516)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24022_1 : P.sumLeaves 24 24598784 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384356) rows (by decide) (by decide)).symm.trans contract24022_1

theorem contract24022_2 : P.leaf 30 384357 = 0 := by
  exact leaf_contract_zero (ss := [(6, 1, 479), (18, 1, 867), (11, 1, 879), (8, 0, 1266), (20, 1, 531), (21, 1, 537), (31, 1, 615), (30, 1, 1210), (26, 1, 516)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24022_2 : P.sumLeaves 24 24598848 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384357) rows (by decide) (by decide)).symm.trans contract24022_2

theorem c24022_3 : P.sumLeaves 24 24598912 299 = 12979827 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24022) (lo := 384) (len := 299) (W := 12979827) check rows elimOK (by decide) (by decide) cover24022 (by decide)
  decide +kernel

theorem c24022_4 : P.sumLeaves 24 24599211 312 = 20252218 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24022) (lo := 683) (len := 312) (W := 20252218) check rows elimOK (by decide) (by decide) cover24022 (by decide)
  decide +kernel

theorem c24022_5 : P.sumLeaves 24 24599523 29 = 18399246 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24022) (lo := 995) (len := 29) (W := 18399246) check rows elimOK (by decide) (by decide) cover24022 (by decide)
  decide +kernel

theorem h24022 : P.leaf 34 24022 = 52229723 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 598432), (64, 0), (64, 0), (299, 12979827), (312, 20252218), (29, 18399246)]) (.cons c24022_0 (.cons c24022_1 (.cons c24022_2 (.cons c24022_3 (.cons c24022_4 (.cons c24022_5 (.nil))))))) (by decide) (by decide))

theorem h23994 : P.leaf 34 23994 = 52229723 :=
  orient4 (v := 24022) (by decide) (by decide +kernel) h24022

theorem cover24023 : P.CoversSplit 24 10 24023 0xfffffffff0f0a0a0fffffffff0f0a0a0ffff000000005050ffff000000005050cccccccc80008000cc00cc0080008000cccc000040004000cc00000040004000fffffffff0f0a0a0fffffffff0f0a0a0ffff555500000000ffff555500000000cccccccc80008000cc00cc0080008000cc00000000000000cc00000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(8, [615, 1609], [1266]), (18, [965], [1210])]) (by decide +kernel)

theorem c24023_0 : P.sumLeaves 24 24599552 256 = 1108112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24023) (lo := 0) (len := 256) (W := 1108112) check rows elimOK (by decide) (by decide) cover24023 (by decide)
  decide +kernel

theorem contract24023_1 : P.leaf 30 384372 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (8, 0, 1266), (5, 1, 565), (31, 1, 615), (21, 0, 1266), (6, 1, 482), (14, 1, 482)]) (q := 629) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24023_1 : P.sumLeaves 24 24599808 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384372) rows (by decide) (by decide)).symm.trans contract24023_1

theorem contract24023_2 : P.leaf 30 384373 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (8, 0, 1266), (31, 1, 615), (21, 0, 1266), (6, 1, 482), (14, 1, 482)]) (q := 629) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24023_2 : P.sumLeaves 24 24599872 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384373) rows (by decide) (by decide)).symm.trans contract24023_2

theorem c24023_3 : P.sumLeaves 24 24599936 242 = 28753172 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24023) (lo := 384) (len := 242) (W := 28753172) check rows elimOK (by decide) (by decide) cover24023 (by decide)
  decide +kernel

theorem c24023_4 : P.sumLeaves 24 24600178 310 = 31778326 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24023) (lo := 626) (len := 310) (W := 31778326) check rows elimOK (by decide) (by decide) cover24023 (by decide)
  decide +kernel

theorem c24023_5 : P.sumLeaves 24 24600488 88 = 62016400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24023) (lo := 936) (len := 88) (W := 62016400) check rows elimOK (by decide) (by decide) cover24023 (by decide)
  decide +kernel

theorem h24023 : P.leaf 34 24023 = 123656010 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 1108112), (64, 0), (64, 0), (242, 28753172), (310, 31778326), (88, 62016400)]) (.cons c24023_0 (.cons c24023_1 (.cons c24023_2 (.cons c24023_3 (.cons c24023_4 (.cons c24023_5 (.nil))))))) (by decide) (by decide))

theorem h23995 : P.leaf 34 23995 = 123656010 :=
  orient4 (v := 24023) (by decide) (by decide +kernel) h24023

def seg : List (ℕ × ℕ) := [(23976, 24), (23977, 48), (23978, 48), (23979, 48), (23980, 48), (23981, 48), (23982, 48), (23983, 48), (23990, 12), (23991, 24), (23993, 24), (23994, 48), (23995, 48)]

theorem segOK : checkSeg 16 perms 23976 23996 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 23976 23996 516 21591461976 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 21591461976)
    (SegSum.cons (w := 24) h23976 (SegSum.cons (w := 48) h23977 (SegSum.cons (w := 48) h23978 (SegSum.cons (w := 48) h23979 (SegSum.cons (w := 48) h23980 (SegSum.cons (w := 48) h23981 (SegSum.cons (w := 48) h23982 (SegSum.cons (w := 48) h23983 (SegSum.cons (w := 12) h23990 (SegSum.cons (w := 24) h23991 (SegSum.cons (w := 24) h23993 (SegSum.cons (w := 48) h23994 (SegSum.cons (w := 48) h23995 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))))) (by decide)

end RACert.S4N1.C0.S72
