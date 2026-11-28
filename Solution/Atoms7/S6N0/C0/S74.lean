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

namespace RACert.S6N0.C0.S74

open RACert RACert.Problem

theorem cover321535 : P.CoversSplit 26 10 321535 0xfffffffffffffffffffffafafffffafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffffffafafffffafaffccffccffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffccffccffccffccfac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 881, 1658, 1665]) (by decide +kernel)

noncomputable def f321535 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (329251840 + i)

theorem c321535_0 : rowSum f321535 0 241 = 1169563127 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover321535 (by decide)
  decide +kernel

theorem c321535_1 : rowSum f321535 241 148 = 1540967159 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover321535 (by decide)
  decide +kernel

theorem c321535_2 : rowSum f321535 389 102 = 1489293548 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover321535 (by decide)
  decide +kernel

theorem c321535_3 : rowSum f321535 491 403 = 1863485855 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover321535 (by decide)
  decide +kernel

theorem c321535_4 : rowSum f321535 894 130 = 849056574 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover321535 (by decide)
  decide +kernel

theorem sum321535 : rowSum f321535 0 1024 = 6912366263 :=
  rowSum_append (F := f321535) (lo := 0) (n := 241) (m := 783) (A := 1169563127) (B := 5742803136) c321535_0 (rowSum_append (F := f321535) (lo := 241) (n := 148) (m := 635) (A := 1540967159) (B := 4201835977) c321535_1 (rowSum_append (F := f321535) (lo := 389) (n := 102) (m := 533) (A := 1489293548) (B := 2712542429) c321535_2 (rowSum_append (F := f321535) (lo := 491) (n := 403) (m := 130) (A := 1863485855) (B := 849056574) c321535_3 (c321535_4))))

theorem h321535 : P.leaf 36 321535 = 6912366263 :=
  leaf_weighted (k := 26) (d := 10) (H := 321535) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 321535) (by decide) (by decide +kernel)) sum321535

theorem h120831 : P.leaf 36 120831 = 6912366263 :=
  orient80 (v := 321535) (by decide) (by decide +kernel) h321535

theorem cover294396 : P.CoversSplit 26 10 294396 0xffffffffffffffff000000000000000000000000000000000001000000000000050505050505050505050000050500000000000000000000000100000000000000330033003300330000000000000000003300330000000000010000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 629, 636, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f294396 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (301461504 + i)

theorem c294396_0 : rowSum f294396 0 1024 = 300822868 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294396) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294396 (by decide)
  decide +kernel

theorem sum294396 : rowSum f294396 0 1024 = 300822868 :=
  c294396_0

theorem h294396 : P.leaf 36 294396 = 300822868 :=
  leaf_weighted (k := 26) (d := 10) (H := 294396) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 294396) (by decide) (by decide +kernel)) sum294396

theorem h122742 : P.leaf 36 122742 = 300822868 :=
  orient6 (v := 294396) (by decide) (by decide +kernel) h294396

theorem cover294397 : P.CoversSplit 26 10 294397 0xffffffffffffffff000000000000000000000000000000000001000000000000050505050505050505050000050500000000000000000000000100000000000000330033003300330000000000000000003300330000000000010000000000000001000100010001000100000001000000010001000000000001000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f294397 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (301462528 + i)

theorem c294397_0 : rowSum f294397 0 1024 = 575676850 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294397) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294397 (by decide)
  decide +kernel

theorem sum294397 : rowSum f294397 0 1024 = 575676850 :=
  c294397_0

theorem h294397 : P.leaf 36 294397 = 575676850 :=
  leaf_weighted (k := 26) (d := 10) (H := 294397) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 294397) (by decide) (by decide +kernel)) sum294397

theorem h122743 : P.leaf 36 122743 = 575676850 :=
  orient6 (v := 294397) (by decide) (by decide +kernel) h294397

theorem cover294398 : P.CoversSplit 26 10 294398 0xffffffffffffffff000000000000000000000000000000000001000000000000050505050505050505050000050500000000000000000000000100000000000000330033003300330000000000000000003300330000000000010000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 629, 636, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f294398 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (301463552 + i)

theorem c294398_0 : rowSum f294398 0 1024 = 479679303 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294398) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294398 (by decide)
  decide +kernel

theorem sum294398 : rowSum f294398 0 1024 = 479679303 :=
  c294398_0

theorem h294398 : P.leaf 36 294398 = 479679303 :=
  leaf_weighted (k := 26) (d := 10) (H := 294398) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 294398) (by decide) (by decide +kernel)) sum294398

theorem h122750 : P.leaf 36 122750 = 479679303 :=
  orient6 (v := 294398) (by decide) (by decide +kernel) h294398

theorem cover294399 : P.CoversSplit 26 10 294399 0xffffffffffffffff000000000000000000000000000000000001000000000000050505050505050505050000050500000000000000000000000100000000000000330033003300330000000000000000003300330000000000010000000000000001000100010001000100000001000000010001000000000001000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f294399 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (301464576 + i)

theorem c294399_0 : rowSum f294399 0 1024 = 601617498 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294399) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294399 (by decide)
  decide +kernel

theorem sum294399 : rowSum f294399 0 1024 = 601617498 :=
  c294399_0

theorem h294399 : P.leaf 36 294399 = 601617498 :=
  leaf_weighted (k := 26) (d := 10) (H := 294399) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 294399) (by decide) (by decide +kernel)) sum294399

theorem h122751 : P.leaf 36 122751 = 601617498 :=
  orient6 (v := 294399) (by decide) (by decide +kernel) h294399

theorem cover256973 : P.CoversSplit 26 10 256973 0xffffffffffffffffffffffffffffaaaaffffffffffffff00fffffafaffccaa00fffffafafffffafaffffaaaaffffaaaafffffafafffffa00ffffaaaaffccaa00ffffffffffccffccffffffffffccaa88ffffffffff00ff00fffffafaff00aa000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 881, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f256973 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (263140352 + i)

theorem c256973_0 : rowSum f256973 0 406 = 161728000 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 256973) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover256973 (by decide)
  decide +kernel

theorem c256973_1 : rowSum f256973 406 104 = 417447340 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 256973) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover256973 (by decide)
  decide +kernel

theorem c256973_2 : rowSum f256973 510 469 = 353321452 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 256973) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover256973 (by decide)
  decide +kernel

theorem c256973_3 : rowSum f256973 979 45 = 228754860 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 256973) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover256973 (by decide)
  decide +kernel

theorem sum256973 : rowSum f256973 0 1024 = 1161251652 :=
  rowSum_append (F := f256973) (lo := 0) (n := 406) (m := 618) (A := 161728000) (B := 999523652) c256973_0 (rowSum_append (F := f256973) (lo := 406) (n := 104) (m := 514) (A := 417447340) (B := 582076312) c256973_1 (rowSum_append (F := f256973) (lo := 510) (n := 469) (m := 45) (A := 353321452) (B := 228754860) c256973_2 (c256973_3)))

theorem h256973 : P.leaf 36 256973 = 1161251652 :=
  leaf_weighted (k := 26) (d := 10) (H := 256973) (keep := keep8) (twice := twice8) rows (by decide) (by decide) (bal8) (invRow8 (H := 256973) (by decide) (by decide +kernel)) sum256973

theorem h122835 : P.leaf 36 122835 = 1161251652 :=
  orient348 (v := 256973) (by decide) (by decide +kernel) h256973

theorem cover485837 : P.CoversSplit 26 10 485837 0xaa00aa00aa00aa00aa00ab00aa00ab00aa00aa00aa02aa02aa00aa00aa00aa00000000000000000000000a0000000a00000000000000000000000a0000000a0000000000000000000000000000000000000000002200220000000000220022000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 580, 629, 636, 881, 972, 979, 1658, 1665]) (by decide +kernel)

noncomputable def f485837 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (497497088 + i)

theorem c485837_0 : rowSum f485837 0 1024 = 220018384 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 485837) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover485837 (by decide)
  decide +kernel

theorem sum485837 : rowSum f485837 0 1024 = 220018384 :=
  c485837_0

theorem h485837 : P.leaf 36 485837 = 220018384 :=
  leaf_weighted (k := 26) (d := 10) (H := 485837) (keep := keep8) (twice := twice8) rows (by decide) (by decide) (bal8) (invRow8 (H := 485837) (by decide) (by decide +kernel)) sum485837

theorem h122836 : P.leaf 36 122836 = 220018384 :=
  orient348 (v := 485837) (by decide) (by decide +kernel) h485837

theorem cover486349 : P.CoversSplit 26 10 486349 0xfffffffffffffffffffafffafffafffafffffffffffcfffcfffafafaffc8fac8fffffafafffffafafafafafafafafafafffffafafffcfaf8fafafafafac8fac8ffffffffffccffccfffafffaffc8ffc8ffffffffffccffccfffafafaffc8fac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 881, 923, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c486349_0 : P.sumLeaves 26 498021376 378 = 59957671 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 486349) (lo := 0) (len := 378) (W := 59957671) check rows elimOK (by decide) (by decide) cover486349 (by decide)
  decide +kernel

theorem c486349_1 : P.sumLeaves 26 498021754 118 = 149261756 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 486349) (lo := 378) (len := 118) (W := 149261756) check rows elimOK (by decide) (by decide) cover486349 (by decide)
  decide +kernel

theorem c486349_2 : P.sumLeaves 26 498021872 129 = 141509223 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 486349) (lo := 496) (len := 129) (W := 141509223) check rows elimOK (by decide) (by decide) cover486349 (by decide)
  decide +kernel

theorem c486349_3 : P.sumLeaves 26 498022001 118 = 165466380 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 486349) (lo := 625) (len := 118) (W := 165466380) check rows elimOK (by decide) (by decide) cover486349 (by decide)
  decide +kernel

theorem c486349_4 : P.sumLeaves 26 498022119 120 = 222690094 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 486349) (lo := 743) (len := 120) (W := 222690094) check rows elimOK (by decide) (by decide) cover486349 (by decide)
  decide +kernel

theorem c486349_5 : P.sumLeaves 26 498022239 104 = 216354094 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 486349) (lo := 863) (len := 104) (W := 216354094) check rows elimOK (by decide) (by decide) cover486349 (by decide)
  decide +kernel

theorem c486349_6 : P.sumLeaves 26 498022343 57 = 270055206 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 486349) (lo := 967) (len := 57) (W := 270055206) check rows elimOK (by decide) (by decide) cover486349 (by decide)
  decide +kernel

theorem h486349 : P.leaf 36 486349 = 1225294424 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(378, 59957671), (118, 149261756), (129, 141509223), (118, 165466380), (120, 222690094), (104, 216354094), (57, 270055206)]) (.cons c486349_0 (.cons c486349_1 (.cons c486349_2 (.cons c486349_3 (.cons c486349_4 (.cons c486349_5 (.cons c486349_6 (.nil)))))))) (by decide) (by decide))

theorem h122837 : P.leaf 36 122837 = 1225294424 :=
  orient348 (v := 486349) (by decide) (by decide +kernel) h486349

def seg : List (ℕ × ℕ) := [(120831, 360), (122742, 180), (122743, 180), (122750, 180), (122751, 180), (122835, 360), (122836, 360), (122837, 720)]

theorem segOK : checkSeg 20 perms 120831 122839 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 120831 122839 2520 4220324426340 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4220324426340)
    (SegSum.cons (w := 360) h120831 (SegSum.cons (w := 180) h122742 (SegSum.cons (w := 180) h122743 (SegSum.cons (w := 180) h122750 (SegSum.cons (w := 180) h122751 (SegSum.cons (w := 360) h122835 (SegSum.cons (w := 360) h122836 (SegSum.cons (w := 720) h122837 (show SegSum (P.leaf 36) [] 0 from rfl))))))))) (by decide)

end RACert.S6N0.C0.S74
