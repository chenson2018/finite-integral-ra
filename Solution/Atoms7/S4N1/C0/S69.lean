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

namespace RACert.S4N1.C0.S69

open RACert RACert.Problem

theorem cover23532 : P.CoversSplit 24 10 23532 0xffffffffaaaaaaaaffffffffaaaaaaaaf0f0000000000000f0f0000000000000cccccccc88888888cccccccc88888888c0c0000000000000c0c0000000000000ff00ff00aa00aa000000000000000000f00055000000000030300000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 859, 879, 916, 1202, 1210, 1259, 1601]) (ps := [(17, [871, 1251], [1259])]) (by decide +kernel)

noncomputable def f23532 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (24096768 + i)

theorem c23532_0 : rowSum f23532 0 957 = 40956523 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23532) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23532 (by decide)
  decide +kernel

theorem c23532_1 : rowSum f23532 957 67 = 20321512 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23532) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23532 (by decide)
  decide +kernel

theorem sum23532 : rowSum f23532 0 1024 = 61278035 :=
  rowSum_append (F := f23532) (lo := 0) (n := 957) (m := 67) (A := 40956523) (B := 20321512) c23532_0 (c23532_1)

theorem h23532 : P.leaf 34 23532 = 61278035 :=
  leaf_weighted (k := 24) (d := 10) (H := 23532) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 23532) (by decide) (by decide +kernel)) sum23532

theorem h22508 : P.leaf 34 22508 = 61278035 :=
  orient4 (v := 23532) (by decide) (by decide +kernel) h23532

theorem cover23533 : P.CoversSplit 24 10 23533 0xffffffffaaaaaaaaffffffffaaaaaaaaffff000000000000ffff000000000000cccccccc88888888cccccccc88888888cccc000000000000cccc000000000000ff00ff00aa00aa000000000000000000ff0055000000000033330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 879, 916, 1202, 1210, 1259, 1601]) (ps := [(17, [1251], [1259])]) (by decide +kernel)

theorem c23533_0 : P.sumLeaves 24 24097792 746 = 29919064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23533) (lo := 0) (len := 746) (W := 29919064) check rows elimOK (by decide) (by decide) cover23533 (by decide)
  decide +kernel

theorem c23533_1 : P.sumLeaves 24 24098538 223 = 46480538 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23533) (lo := 746) (len := 223) (W := 46480538) check rows elimOK (by decide) (by decide) cover23533 (by decide)
  decide +kernel

theorem c23533_2 : P.sumLeaves 24 24098761 55 = 45432874 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23533) (lo := 969) (len := 55) (W := 45432874) check rows elimOK (by decide) (by decide) cover23533 (by decide)
  decide +kernel

theorem h23533 : P.leaf 34 23533 = 121832476 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(746, 29919064), (223, 46480538), (55, 45432874)]) (.cons c23533_0 (.cons c23533_1 (.cons c23533_2 (.nil)))) (by decide) (by decide))

theorem h22509 : P.leaf 34 22509 = 121832476 :=
  orient4 (v := 23533) (by decide) (by decide +kernel) h23533

theorem cover23548 : P.CoversSplit 24 10 23548 0xffffffffaaaaaaaaffffffffaaaaaaaaf0f0f5f500000000f0f0f5f500000000cccccccc88888888cccccccc88888888c0c0c4c400000000c0c0c4c400000000ff00ff00aa00aa00ff33ff33aa22aa22f000f50000000000f030f531000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 859, 879, 916, 1202, 1259, 1601]) (by decide +kernel)

noncomputable def f23548 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (24113152 + i)

theorem c23548_0 : rowSum f23548 0 702 = 68155548 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23548) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23548 (by decide)
  decide +kernel

theorem c23548_1 : rowSum f23548 702 322 = 96972571 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23548) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23548 (by decide)
  decide +kernel

theorem sum23548 : rowSum f23548 0 1024 = 165128119 :=
  rowSum_append (F := f23548) (lo := 0) (n := 702) (m := 322) (A := 68155548) (B := 96972571) c23548_0 (c23548_1)

theorem h23548 : P.leaf 34 23548 = 165128119 :=
  leaf_weighted (k := 24) (d := 10) (H := 23548) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 23548) (by decide) (by decide +kernel)) sum23548

theorem h22510 : P.leaf 34 22510 = 165128119 :=
  orient4 (v := 23548) (by decide) (by decide +kernel) h23548

theorem cover23549 : P.CoversSplit 24 10 23549 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffff00000000ffffffff00000000cccccccc88888888cccccccc88888888cccccccc00000000cccccccc00000000ff00ff00aa00aa00ff33ff33aa22aa22ff00ff0000000000ff33ff33000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 859, 879, 916, 1202, 1259, 1601]) (by decide +kernel)

theorem c23549_0 : P.sumLeaves 24 24114176 508 = 61534746 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23549) (lo := 0) (len := 508) (W := 61534746) check rows elimOK (by decide) (by decide) cover23549 (by decide)
  decide +kernel

theorem c23549_1 : P.sumLeaves 24 24114684 304 = 57213487 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23549) (lo := 508) (len := 304) (W := 57213487) check rows elimOK (by decide) (by decide) cover23549 (by decide)
  decide +kernel

theorem c23549_2 : P.sumLeaves 24 24114988 144 = 108171937 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23549) (lo := 812) (len := 144) (W := 108171937) check rows elimOK (by decide) (by decide) cover23549 (by decide)
  decide +kernel

theorem c23549_3 : P.sumLeaves 24 24115132 68 = 101173158 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23549) (lo := 956) (len := 68) (W := 101173158) check rows elimOK (by decide) (by decide) cover23549 (by decide)
  decide +kernel

theorem h23549 : P.leaf 34 23549 = 328093328 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(508, 61534746), (304, 57213487), (144, 108171937), (68, 101173158)]) (.cons c23549_0 (.cons c23549_1 (.cons c23549_2 (.cons c23549_3 (.nil))))) (by decide) (by decide))

theorem h22511 : P.leaf 34 22511 = 328093328 :=
  orient4 (v := 23549) (by decide) (by decide +kernel) h23549

theorem cover23535 : P.CoversSplit 24 10 23535 0xffffffffaaaaaaaaffffffffaaaaaaaaffff000000000000ffff000000000000cccccccc88888888cccccccc88888888cccc000000000000cccc000000000000ffffffffaaaaaaaa0000000000000000ffff55550000000033330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 1202, 1210, 1259, 1601]) (ps := [(17, [1251], [1259])]) (by decide +kernel)

noncomputable def f23535 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (24099840 + i)

theorem c23535_0 : rowSum f23535 0 746 = 114134080 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23535) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23535 (by decide)
  decide +kernel

theorem c23535_1 : rowSum f23535 746 278 = 145074128 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23535) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23535 (by decide)
  decide +kernel

theorem sum23535 : rowSum f23535 0 1024 = 259208208 :=
  rowSum_append (F := f23535) (lo := 0) (n := 746) (m := 278) (A := 114134080) (B := 145074128) c23535_0 (c23535_1)

theorem h23535 : P.leaf 34 23535 = 259208208 :=
  leaf_weighted (k := 24) (d := 10) (H := 23535) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 23535) (by decide) (by decide +kernel)) sum23535

theorem h22525 : P.leaf 34 22525 = 259208208 :=
  orient4 (v := 23535) (by decide) (by decide +kernel) h23535

theorem cover23551 : P.CoversSplit 24 10 23551 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [859, 916, 1202, 1259, 1601]) (by decide +kernel)

noncomputable def f23551 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (24116224 + i)

theorem c23551_0 : rowSum f23551 0 295 = 116433589 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23551) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23551 (by decide)
  decide +kernel

theorem c23551_1 : rowSum f23551 295 187 = 223849539 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23551) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23551 (by decide)
  decide +kernel

theorem c23551_2 : rowSum f23551 482 476 = 458583077 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23551) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23551 (by decide)
  decide +kernel

theorem c23551_3 : rowSum f23551 958 66 = 95436521 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23551) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23551 (by decide)
  decide +kernel

theorem sum23551 : rowSum f23551 0 1024 = 894302726 :=
  rowSum_append (F := f23551) (lo := 0) (n := 295) (m := 729) (A := 116433589) (B := 777869137) c23551_0 (rowSum_append (F := f23551) (lo := 295) (n := 187) (m := 542) (A := 223849539) (B := 554019598) c23551_1 (rowSum_append (F := f23551) (lo := 482) (n := 476) (m := 66) (A := 458583077) (B := 95436521) c23551_2 (c23551_3)))

theorem h23551 : P.leaf 34 23551 = 894302726 :=
  leaf_weighted (k := 24) (d := 10) (H := 23551) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 23551) (by decide) (by decide +kernel)) sum23551

theorem h22527 : P.leaf 34 22527 = 894302726 :=
  orient4 (v := 23551) (by decide) (by decide +kernel) h23551

theorem cover23788 : P.CoversSplit 24 10 23788 0xffffffffeae00000ffffffffeae00000ffff00000000a0a0ffff00000000a0800000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc000000800000330033000000200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 573, 858, 865, 916, 1210, 1259, 1601]) (ps := [(17, [1259], [1251])]) (by decide +kernel)

noncomputable def f23788 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (24358912 + i)

theorem c23788_0 : rowSum f23788 0 1023 = 8326213 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23788) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23788 (by decide)
  decide +kernel

theorem c23788_1 : rowSum f23788 1023 1 = 347280 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23788) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23788 (by decide)
  decide +kernel

theorem sum23788 : rowSum f23788 0 1024 = 8673493 :=
  rowSum_append (F := f23788) (lo := 0) (n := 1023) (m := 1) (A := 8326213) (B := 347280) c23788_0 (c23788_1)

theorem h23788 : P.leaf 34 23788 = 8673493 :=
  leaf_weighted (k := 24) (d := 10) (H := 23788) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 23788) (by decide) (by decide +kernel)) sum23788

theorem cover23789 : P.CoversSplit 24 10 23789 0xffffffffeae00000ffffffffeae00000ffff00000000a0a0ffff00000000a0800000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc000000800000330033000000200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(17, [1259], [1251])]) (by decide +kernel)

noncomputable def f23789 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (24359936 + i)

theorem c23789_0 : rowSum f23789 0 1023 = 11412103 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23789) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23789 (by decide)
  decide +kernel

theorem c23789_1 : rowSum f23789 1023 1 = 427432 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23789) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23789 (by decide)
  decide +kernel

theorem sum23789 : rowSum f23789 0 1024 = 11839535 :=
  rowSum_append (F := f23789) (lo := 0) (n := 1023) (m := 1) (A := 11412103) (B := 427432) c23789_0 (c23789_1)

theorem h23789 : P.leaf 34 23789 = 11839535 :=
  leaf_weighted (k := 24) (d := 10) (H := 23789) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 23789) (by decide) (by decide +kernel)) sum23789

def seg : List (ℕ × ℕ) := [(22508, 24), (22509, 48), (22510, 24), (22511, 48), (22525, 24), (22527, 24), (23788, 8), (23789, 8)]

theorem segOK : checkSeg 16 perms 22508 23790 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22508 23790 208 54878552928 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 54878552928)
    (SegSum.cons (w := 24) h22508 (SegSum.cons (w := 48) h22509 (SegSum.cons (w := 24) h22510 (SegSum.cons (w := 48) h22511 (SegSum.cons (w := 24) h22525 (SegSum.cons (w := 24) h22527 (SegSum.cons (w := 8) h23788 (SegSum.cons (w := 8) h23789 (show SegSum (P.leaf 34) [] 0 from rfl))))))))) (by decide)

end RACert.S4N1.C0.S69
