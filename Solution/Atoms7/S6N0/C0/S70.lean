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

namespace RACert.S6N0.C0.S70

open RACert RACert.Problem

theorem cover326655 : P.CoversSplit 26 10 326655 0xffffffffffffffffffffaaaaffffaaaaffffffffccccccccfac8aa88c8c88888fffffffffffffffffafaaaaafafaaaaaffffffffccccccccfac8aa88c8c88888ffffffffffffffffffffaaaaffffaaaaffccffccccccccccfac8aa88c8c88888fffffffffffffffffafaaaaafafaaaaaffccffccccccccccfac8aa88c8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f326655 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (334494720 + i)

theorem c326655_0 : rowSum f326655 0 278 = 1250104067 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 326655) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover326655 (by decide)
  decide +kernel

theorem c326655_1 : rowSum f326655 278 158 = 1580270420 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 326655) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover326655 (by decide)
  decide +kernel

theorem c326655_2 : rowSum f326655 436 407 = 1804357362 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 326655) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover326655 (by decide)
  decide +kernel

theorem c326655_3 : rowSum f326655 843 181 = 1628172149 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 326655) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover326655 (by decide)
  decide +kernel

theorem sum326655 : rowSum f326655 0 1024 = 6262903998 :=
  rowSum_append (F := f326655) (lo := 0) (n := 278) (m := 746) (A := 1250104067) (B := 5012799931) c326655_0 (rowSum_append (F := f326655) (lo := 278) (n := 158) (m := 588) (A := 1580270420) (B := 3432529511) c326655_1 (rowSum_append (F := f326655) (lo := 436) (n := 407) (m := 181) (A := 1804357362) (B := 1628172149) c326655_2 (c326655_3)))

theorem h326655 : P.leaf 36 326655 = 6262903998 :=
  leaf_weighted (k := 26) (d := 10) (H := 326655) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 326655) (by decide) (by decide +kernel)) sum326655

theorem h98303 : P.leaf 36 98303 = 6262903998 :=
  orient80 (v := 326655) (by decide) (by decide +kernel) h326655

theorem cover288157 : P.CoversSplit 26 10 288157 0x8000000000000000000000000000000000000000000000000001000100010001000000000000000000000000000000000000000000000000000100010001000100000000000000000000000000000000000000000000000000010001000100010000000000000000000000000000000000000000000000000001000100010001 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 615, 629, 636, 873, 881, 1265, 1273]) (by decide +kernel)

theorem h288157 : P.leaf 36 288157 = 1176055 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 288157) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 288157) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 288157) (weight := rowWeight keep0 twice0) (xs := [0, 16, 32, 48, 256, 272, 288, 304, 512, 528, 544, 560, 768, 784, 800, 816, 1023]) check rows elimOK (by decide) (by decide) cover288157 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h119623 : P.leaf 36 119623 = 1176055 :=
  orient6 (v := 288157) (by decide) (by decide +kernel) h288157

theorem cover288159 : P.CoversSplit 26 10 288159 0x8000000000000000000000000000000000000000000000000001000100010001000000000000000000000000000000000000000000000000000100010001000100000000000000000000000000000000000000000000000000010001000100010000000000000000000000000000000000000000000000000001000100010001 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 615, 629, 636, 873, 881, 1265, 1273]) (by decide +kernel)

theorem h288159 : P.leaf 36 288159 = 3670795 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 288159) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 288159) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 288159) (weight := rowWeight keep0 twice0) (xs := [0, 16, 32, 48, 256, 272, 288, 304, 512, 528, 544, 560, 768, 784, 800, 816, 1023]) check rows elimOK (by decide) (by decide) cover288159 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h119631 : P.leaf 36 119631 = 3670795 :=
  orient6 (v := 288159) (by decide) (by decide +kernel) h288159

theorem cover288189 : P.CoversSplit 26 10 288189 0xc000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030003000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 629, 636, 873, 881, 958, 972, 1273, 1308]) (by decide +kernel)

theorem h288189 : P.leaf 36 288189 = 7497540 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 288189) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 288189) (weight := fun _ => 1) (xs := [324, 325, 340, 341, 1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover288189 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h119639 : P.leaf 36 119639 = 7497540 :=
  orient6 (v := 288189) (by decide) (by decide +kernel) h288189

theorem cover288191 : P.CoversSplit 26 10 288191 0xc000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030003000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 629, 636, 873, 881, 958, 972, 1273, 1308]) (by decide +kernel)

theorem h288191 : P.leaf 36 288191 = 7920556 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 288191) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 288191) (weight := fun _ => 1) (xs := [324, 325, 340, 341, 1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover288191 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h119647 : P.leaf 36 119647 = 7920556 :=
  orient6 (v := 288191) (by decide) (by decide +kernel) h288191

theorem cover288253 : P.CoversSplit 26 10 288253 0xf000f000f000f000000000000000000000000000000000000001000000000000000000000000000005000000050000000000000000000000000100000000000000000000000000000000000000000000003000300000000000010000000000000000000000000000000000000000000000000000000000000001000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 873, 881, 972, 979, 1658, 1665]) (by decide +kernel)

theorem h288253 : P.leaf 36 288253 = 41888832 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 288253) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 288253) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 288253) (weight := rowWeight keep0 twice0) (xs := [48, 304, 356, 357, 372, 373, 560, 664, 666, 696, 698, 816, 972, 973, 974, 975, 988, 989, 990, 991, 1004, 1005, 1006, 1007, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover288253 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h119671 : P.leaf 36 119671 = 41888832 :=
  orient6 (v := 288253) (by decide) (by decide +kernel) h288253

theorem cover288255 : P.CoversSplit 26 10 288255 0xf000f000f000f000000000000000000000000000000000000001000000000000000000000000000005000000050000000000000000000000000100000000000000000000000000000000000000000000003000300000000000010000000000000000000000000000000000000000000000000000000000000001000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 873, 881, 972, 979, 1658, 1665]) (by decide +kernel)

theorem h288255 : P.leaf 36 288255 = 48168608 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 288255) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 288255) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 288255) (weight := rowWeight keep0 twice0) (xs := [48, 304, 356, 357, 372, 373, 560, 664, 666, 696, 698, 816, 972, 973, 974, 975, 988, 989, 990, 991, 1004, 1005, 1006, 1007, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover288255 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h119679 : P.leaf 36 119679 = 48168608 :=
  orient6 (v := 288255) (by decide) (by decide +kernel) h288255

theorem cover288765 : P.CoversSplit 26 10 288765 0xfffffffffffffffffffafafafffafafafffcfffcffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafafffcfffcffccffccfac8fac8fac8fac8fffffffffffffffffffafafafffafafaffccffccffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffccffccffccffccfac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 881, 972, 979, 1658, 1665]) (by decide +kernel)

noncomputable def f288765 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (295695360 + i)

theorem c288765_0 : rowSum f288765 0 241 = 195459760 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 288765) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover288765 (by decide)
  decide +kernel

theorem c288765_1 : rowSum f288765 241 148 = 341497457 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 288765) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover288765 (by decide)
  decide +kernel

theorem c288765_2 : rowSum f288765 389 106 = 465245716 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 288765) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover288765 (by decide)
  decide +kernel

theorem c288765_3 : rowSum f288765 495 472 = 544244664 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 288765) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover288765 (by decide)
  decide +kernel

theorem c288765_4 : rowSum f288765 967 57 = 272328369 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 288765) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover288765 (by decide)
  decide +kernel

theorem sum288765 : rowSum f288765 0 1024 = 1818775966 :=
  rowSum_append (F := f288765) (lo := 0) (n := 241) (m := 783) (A := 195459760) (B := 1623316206) c288765_0 (rowSum_append (F := f288765) (lo := 241) (n := 148) (m := 635) (A := 341497457) (B := 1281818749) c288765_1 (rowSum_append (F := f288765) (lo := 389) (n := 106) (m := 529) (A := 465245716) (B := 816573033) c288765_2 (rowSum_append (F := f288765) (lo := 495) (n := 472) (m := 57) (A := 544244664) (B := 272328369) c288765_3 (c288765_4))))

theorem h288765 : P.leaf 36 288765 = 1818775966 :=
  leaf_weighted (k := 26) (d := 10) (H := 288765) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 288765) (by decide) (by decide +kernel)) sum288765

theorem h119799 : P.leaf 36 119799 = 1818775966 :=
  orient6 (v := 288765) (by decide) (by decide +kernel) h288765

theorem cover288767 : P.CoversSplit 26 10 288767 0xfffffffffffffffffffafafafffafafafffcfffcffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafafffcfffcffccffccfac8fac8fac8fac8fffffffffffffffffffafafafffafafaffccffccffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffccffccffccffccfac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 881, 972, 979, 1658, 1665]) (by decide +kernel)

noncomputable def f288767 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (295697408 + i)

theorem c288767_0 : rowSum f288767 0 241 = 609283575 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 288767) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover288767 (by decide)
  decide +kernel

theorem c288767_1 : rowSum f288767 241 148 = 1070160338 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 288767) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover288767 (by decide)
  decide +kernel

theorem c288767_2 : rowSum f288767 389 106 = 1215328576 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 288767) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover288767 (by decide)
  decide +kernel

theorem c288767_3 : rowSum f288767 495 472 = 1474788190 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 288767) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover288767 (by decide)
  decide +kernel

theorem c288767_4 : rowSum f288767 967 57 = 605265356 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 288767) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover288767 (by decide)
  decide +kernel

theorem sum288767 : rowSum f288767 0 1024 = 4974826035 :=
  rowSum_append (F := f288767) (lo := 0) (n := 241) (m := 783) (A := 609283575) (B := 4365542460) c288767_0 (rowSum_append (F := f288767) (lo := 241) (n := 148) (m := 635) (A := 1070160338) (B := 3295382122) c288767_1 (rowSum_append (F := f288767) (lo := 389) (n := 106) (m := 529) (A := 1215328576) (B := 2080053546) c288767_2 (rowSum_append (F := f288767) (lo := 495) (n := 472) (m := 57) (A := 1474788190) (B := 605265356) c288767_3 (c288767_4))))

theorem h288767 : P.leaf 36 288767 = 4974826035 :=
  leaf_weighted (k := 26) (d := 10) (H := 288767) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 288767) (by decide) (by decide +kernel)) sum288767

theorem h119807 : P.leaf 36 119807 = 4974826035 :=
  orient6 (v := 288767) (by decide) (by decide +kernel) h288767

theorem cover290237 : P.CoversSplit 26 10 290237 0xcc00cc0000000000000000000000000000000000000000000000000000000000040004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000000000000000000000000000000000000000000000000000000100010000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 629, 636, 881, 1265, 1273, 1308, 1658]) (by decide +kernel)

theorem h290237 : P.leaf 36 290237 = 42104416 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 290237) (keep := keep7) (twice := twice7) rows (by decide) (by decide) bal7 (invRow7 (H := 290237) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 290237) (weight := rowWeight keep7 twice7) (xs := [64, 80, 320, 321, 324, 325, 336, 337, 340, 341, 746, 762, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover290237 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h120663 : P.leaf 36 120663 = 42104416 :=
  orient6 (v := 290237) (by decide) (by decide +kernel) h290237

theorem cover290239 : P.CoversSplit 26 10 290239 0xcc00cc0000000000000000000000000000000000000000000000000000000000040004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000000000000000000000000000000000000000000000000000000100010000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 629, 636, 881, 1265, 1273, 1308, 1658]) (by decide +kernel)

theorem h290239 : P.leaf 36 290239 = 44955216 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 290239) (keep := keep7) (twice := twice7) rows (by decide) (by decide) bal7 (invRow7 (H := 290239) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 290239) (weight := rowWeight keep7 twice7) (xs := [64, 80, 320, 321, 324, 325, 336, 337, 340, 341, 746, 762, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover290239 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h120671 : P.leaf 36 120671 = 44955216 :=
  orient6 (v := 290239) (by decide) (by decide +kernel) h290239

theorem cover290268 : P.CoversSplit 26 10 290268 0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 530, 629, 636, 881, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h290268 : P.leaf 36 290268 = 31166148 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 290268) (keep := keep8) (twice := twice8) rows (by decide) (by decide) bal8 (invRow8 (H := 290268) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 290268) (weight := rowWeight keep8 twice8) (xs := [969, 971, 973, 975, 985, 987, 989, 991, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover290268 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h120678 : P.leaf 36 120678 = 31166148 :=
  orient6 (v := 290268) (by decide) (by decide +kernel) h290268

theorem cover290269 : P.CoversSplit 26 10 290269 0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 629, 636, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h290269 : P.leaf 36 290269 = 67766268 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 290269) (keep := keep8) (twice := twice8) rows (by decide) (by decide) bal8 (invRow8 (H := 290269) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 290269) (weight := rowWeight keep8 twice8) (xs := [969, 971, 973, 975, 985, 987, 989, 991, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover290269 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h120679 : P.leaf 36 120679 = 67766268 :=
  orient6 (v := 290269) (by decide) (by decide +kernel) h290269

theorem cover290270 : P.CoversSplit 26 10 290270 0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 530, 629, 636, 881, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h290270 : P.leaf 36 290270 = 39538944 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 290270) (keep := keep8) (twice := twice8) rows (by decide) (by decide) bal8 (invRow8 (H := 290270) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 290270) (weight := rowWeight keep8 twice8) (xs := [969, 971, 973, 975, 985, 987, 989, 991, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover290270 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h120686 : P.leaf 36 120686 = 39538944 :=
  orient6 (v := 290270) (by decide) (by decide +kernel) h290270

theorem cover290271 : P.CoversSplit 26 10 290271 0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 629, 636, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h290271 : P.leaf 36 290271 = 67892736 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 290271) (keep := keep8) (twice := twice8) rows (by decide) (by decide) bal8 (invRow8 (H := 290271) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 290271) (weight := rowWeight keep8 twice8) (xs := [969, 971, 973, 975, 985, 987, 989, 991, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover290271 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h120687 : P.leaf 36 120687 = 67892736 :=
  orient6 (v := 290271) (by decide) (by decide +kernel) h290271

theorem cover290300 : P.CoversSplit 26 10 290300 0xff00ff00ff00ff00000000000000000000000000000000000000000000000000050005000500050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 629, 636, 881, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c290300_0 : P.sumLeaves 26 297267200 1024 = 88571676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 290300) (lo := 0) (len := 1024) (W := 88571676) check rows elimOK (by decide) (by decide) cover290300 (by decide)
  decide +kernel

theorem h290300 : P.leaf 36 290300 = 88571676 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 88571676)]) (.cons c290300_0 (.nil)) (by decide) (by decide))

theorem h120694 : P.leaf 36 120694 = 88571676 :=
  orient6 (v := 290300) (by decide) (by decide +kernel) h290300

theorem cover290301 : P.CoversSplit 26 10 290301 0xff00ff00ff00ff00000000000000000000000000000000000000000000000000050005000500050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c290301_0 : P.sumLeaves 26 297268224 1024 = 201275848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 290301) (lo := 0) (len := 1024) (W := 201275848) check rows elimOK (by decide) (by decide) cover290301 (by decide)
  decide +kernel

theorem h290301 : P.leaf 36 290301 = 201275848 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 201275848)]) (.cons c290301_0 (.nil)) (by decide) (by decide))

theorem h120695 : P.leaf 36 120695 = 201275848 :=
  orient6 (v := 290301) (by decide) (by decide +kernel) h290301

def seg : List (ℕ × ℕ) := [(98303, 360), (119623, 20), (119631, 20), (119639, 180), (119647, 180), (119671, 180), (119679, 180), (119799, 60), (119807, 60), (120663, 180), (120671, 180), (120678, 360), (120679, 360), (120686, 360), (120687, 360), (120694, 720), (120695, 720)]

theorem segOK : checkSeg 20 perms 98303 120702 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 98303 120702 4480 2979996118420 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2979996118420)
    (SegSum.cons (w := 360) h98303 (SegSum.cons (w := 20) h119623 (SegSum.cons (w := 20) h119631 (SegSum.cons (w := 180) h119639 (SegSum.cons (w := 180) h119647 (SegSum.cons (w := 180) h119671 (SegSum.cons (w := 180) h119679 (SegSum.cons (w := 60) h119799 (SegSum.cons (w := 60) h119807 (SegSum.cons (w := 180) h120663 (SegSum.cons (w := 180) h120671 (SegSum.cons (w := 360) h120678 (SegSum.cons (w := 360) h120679 (SegSum.cons (w := 360) h120686 (SegSum.cons (w := 360) h120687 (SegSum.cons (w := 720) h120694 (SegSum.cons (w := 720) h120695 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))) (by decide)

end RACert.S6N0.C0.S70
