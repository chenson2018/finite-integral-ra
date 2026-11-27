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

namespace RACert.S4N1.C0.S50

open RACert RACert.Problem

theorem cover7535 : P.CoversSplit 24 10 7535 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 572, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem c7535_0 : P.sumLeaves 24 7715840 1024 = 2786828 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7535) (lo := 0) (len := 1024) (W := 2786828) check rows elimOK (by decide) (by decide) cover7535 (by decide)
  decide +kernel

theorem h7535 : P.leaf 34 7535 = 2786828 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2786828)]) (.cons c7535_0 (.nil)) (by decide) (by decide))

theorem cover7540 : P.CoversSplit 24 10 7540 0xc0000000c00080000000000000000000c0000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00080000000000000000000c0000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 572, 858, 865, 866, 916, 1209, 1210, 1258, 1259]) (ps := [(11, [879, 909], [858])]) (by decide +kernel)

theorem c7540_0 : P.sumLeaves 24 7720960 1024 = 887552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7540) (lo := 0) (len := 1024) (W := 887552) check rows elimOK (by decide) (by decide) cover7540 (by decide)
  decide +kernel

theorem h7540 : P.leaf 34 7540 = 887552 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 887552)]) (.cons c7540_0 (.nil)) (by decide) (by decide))

theorem cover7541 : P.CoversSplit 24 10 7541 0xcc00cc00cc0080000000000000000000cc00cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0080000000000000000000cc00cc00c800800000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 572, 858, 865, 866, 1209, 1210, 1217, 1258, 1259]) (by decide +kernel)

theorem c7541_0 : P.sumLeaves 24 7721984 1024 = 6595138 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7541) (lo := 0) (len := 1024) (W := 6595138) check rows elimOK (by decide) (by decide) cover7541 (by decide)
  decide +kernel

theorem h7541 : P.leaf 34 7541 = 6595138 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6595138)]) (.cons c7541_0 (.nil)) (by decide) (by decide))

theorem cover7542 : P.CoversSplit 24 10 7542 0xf0f00000f0f500000000000000000000f0f00000f0f5000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f500000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 865, 866, 908, 1210, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c7542_0 : P.sumLeaves 24 7723008 1024 = 22410038 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7542) (lo := 0) (len := 1024) (W := 22410038) check rows elimOK (by decide) (by decide) cover7542 (by decide)
  decide +kernel

theorem h7542 : P.leaf 34 7542 = 22410038 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 22410038)]) (.cons c7542_0 (.nil)) (by decide) (by decide))

theorem cover7543 : P.CoversSplit 24 10 7543 0xfffffffffffaa0a00000000000000000fffffffffffaa0a000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffaa0a00000000000000000fffffffffafaa0a000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 865, 866, 908, 1209, 1210, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c7543_0 : P.sumLeaves 24 7724032 510 = 11734694 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7543) (lo := 0) (len := 510) (W := 11734694) check rows elimOK (by decide) (by decide) cover7543 (by decide)
  decide +kernel

theorem c7543_1 : P.sumLeaves 24 7724542 508 = 53885370 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7543) (lo := 510) (len := 508) (W := 53885370) check rows elimOK (by decide) (by decide) cover7543 (by decide)
  decide +kernel

theorem c7543_2 : P.sumLeaves 24 7725050 6 = 10894432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7543) (lo := 1018) (len := 6) (W := 10894432) check rows elimOK (by decide) (by decide) cover7543 (by decide)
  decide +kernel

theorem h7543 : P.leaf 34 7543 = 76514496 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(510, 11734694), (508, 53885370), (6, 10894432)]) (.cons c7543_0 (.cons c7543_1 (.cons c7543_2 (.nil)))) (by decide) (by decide))

theorem cover7544 : P.CoversSplit 24 10 7544 0xc0000000c00000000000000000000000c0000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000c0000000c000800000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 572, 858, 865, 867, 909, 916, 1209, 1210, 1258, 1259]) (by decide +kernel)

theorem c7544_0 : P.sumLeaves 24 7725056 1024 = 470220 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7544) (lo := 0) (len := 1024) (W := 470220) check rows elimOK (by decide) (by decide) cover7544 (by decide)
  decide +kernel

theorem h7544 : P.leaf 34 7544 = 470220 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 470220)]) (.cons c7544_0 (.nil)) (by decide) (by decide))

theorem cover7545 : P.CoversSplit 24 10 7545 0xcc000000cc0000000000000000000000cc000000cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000cc0000000000000000000000cc000000c800000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 572, 858, 865, 867, 1209, 1210, 1217, 1258, 1259]) (by decide +kernel)

theorem c7545_0 : P.sumLeaves 24 7726080 1024 = 1682058 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7545) (lo := 0) (len := 1024) (W := 1682058) check rows elimOK (by decide) (by decide) cover7545 (by decide)
  decide +kernel

theorem h7545 : P.leaf 34 7545 = 1682058 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1682058)]) (.cons c7545_0 (.nil)) (by decide) (by decide))

theorem cover7546 : P.CoversSplit 24 10 7546 0xf0f00000f0f500000000000000000000f0f00000f0f5000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f500000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 865, 867, 909, 1210, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c7546_0 : P.sumLeaves 24 7727104 1024 = 6823068 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7546) (lo := 0) (len := 1024) (W := 6823068) check rows elimOK (by decide) (by decide) cover7546 (by decide)
  decide +kernel

theorem h7546 : P.leaf 34 7546 = 6823068 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6823068)]) (.cons c7546_0 (.nil)) (by decide) (by decide))

theorem cover7547 : P.CoversSplit 24 10 7547 0xffff0000fffa00000000000000000000ffff0000fffa000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000fffa00000000000000000000ffff0000fafa000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 865, 867, 916, 1209, 1210, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c7547_0 : P.sumLeaves 24 7728128 986 = 10928075 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7547) (lo := 0) (len := 986) (W := 10928075) check rows elimOK (by decide) (by decide) cover7547 (by decide)
  decide +kernel

theorem c7547_1 : P.sumLeaves 24 7729114 38 = 10607266 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7547) (lo := 986) (len := 38) (W := 10607266) check rows elimOK (by decide) (by decide) cover7547 (by decide)
  decide +kernel

theorem h7547 : P.leaf 34 7547 = 21535341 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(986, 10928075), (38, 10607266)]) (.cons c7547_0 (.cons c7547_1 (.nil))) (by decide) (by decide))

theorem cover7548 : P.CoversSplit 24 10 7548 0xc0000000c00080000000000000000000c0000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00080000000000000000000c0000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 572, 858, 865, 916, 1209, 1210, 1258, 1259]) (ps := [(11, [879, 909], [858])]) (by decide +kernel)

theorem c7548_0 : P.sumLeaves 24 7729152 1024 = 3032032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7548) (lo := 0) (len := 1024) (W := 3032032) check rows elimOK (by decide) (by decide) cover7548 (by decide)
  decide +kernel

theorem h7548 : P.leaf 34 7548 = 3032032 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3032032)]) (.cons c7548_0 (.nil)) (by decide) (by decide))

theorem cover7549 : P.CoversSplit 24 10 7549 0xcc00cc00cc0080000000000000000000cc00cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0080000000000000000000cc00cc00c800800000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 572, 858, 865, 1209, 1210, 1217, 1258, 1259]) (by decide +kernel)

theorem c7549_0 : P.sumLeaves 24 7730176 1024 = 15770124 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7549) (lo := 0) (len := 1024) (W := 15770124) check rows elimOK (by decide) (by decide) cover7549 (by decide)
  decide +kernel

theorem h7549 : P.leaf 34 7549 = 15770124 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15770124)]) (.cons c7549_0 (.nil)) (by decide) (by decide))

theorem cover7550 : P.CoversSplit 24 10 7550 0xf0f00000f0f500000000000000000000f0f00000f0f5000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f500000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 865, 1210, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c7550_0 : P.sumLeaves 24 7731200 1024 = 35434226 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7550) (lo := 0) (len := 1024) (W := 35434226) check rows elimOK (by decide) (by decide) cover7550 (by decide)
  decide +kernel

theorem h7550 : P.leaf 34 7550 = 35434226 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 35434226)]) (.cons c7550_0 (.nil)) (by decide) (by decide))

theorem cover7551 : P.CoversSplit 24 10 7551 0xfffffffffffaa0a00000000000000000fffffffffffaa0a000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffaa0a00000000000000000fffffffffafaa0a000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 865, 1209, 1210, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c7551_0 : P.sumLeaves 24 7732224 510 = 15695997 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7551) (lo := 0) (len := 510) (W := 15695997) check rows elimOK (by decide) (by decide) cover7551 (by decide)
  decide +kernel

theorem c7551_1 : P.sumLeaves 24 7732734 508 = 81938861 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7551) (lo := 510) (len := 508) (W := 81938861) check rows elimOK (by decide) (by decide) cover7551 (by decide)
  decide +kernel

theorem c7551_2 : P.sumLeaves 24 7733242 6 = 12489708 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7551) (lo := 1018) (len := 6) (W := 12489708) check rows elimOK (by decide) (by decide) cover7551 (by decide)
  decide +kernel

theorem h7551 : P.leaf 34 7551 = 110124566 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(510, 15695997), (508, 81938861), (6, 12489708)]) (.cons c7551_0 (.cons c7551_1 (.cons c7551_2 (.nil)))) (by decide) (by decide))

theorem cover7584 : P.CoversSplit 24 10 7584 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7584_0 : P.sumLeaves 24 7766016 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7584) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7584 (by decide)
  decide +kernel

theorem h7584 : P.leaf 34 7584 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7584_0 (.nil)) (by decide) (by decide))

theorem cover7585 : P.CoversSplit 24 10 7585 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 524, 566, 858, 865, 916, 1209, 1258, 1266]) (by decide +kernel)

theorem c7585_0 : P.sumLeaves 24 7767040 1024 = 40456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7585) (lo := 0) (len := 1024) (W := 40456) check rows elimOK (by decide) (by decide) cover7585 (by decide)
  decide +kernel

theorem h7585 : P.leaf 34 7585 = 40456 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 40456)]) (.cons c7585_0 (.nil)) (by decide) (by decide))

theorem cover7587 : P.CoversSplit 24 10 7587 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 566, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

noncomputable def f7587 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (7769088 + i)

theorem c7587_0 : rowSum f7587 0 1024 = 411694 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7587) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover7587 (by decide)
  decide +kernel

theorem sum7587 : rowSum f7587 0 1024 = 411694 :=
  c7587_0

theorem h7587 : P.leaf 34 7587 = 411694 :=
  leaf_weighted (k := 24) (d := 10) (H := 7587) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 7587) (by decide) (by decide +kernel)) sum7587

theorem cover7588 : P.CoversSplit 24 10 7588 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7588_0 : P.sumLeaves 24 7770112 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7588) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7588 (by decide)
  decide +kernel

theorem h7588 : P.leaf 34 7588 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7588_0 (.nil)) (by decide) (by decide))

theorem cover7589 : P.CoversSplit 24 10 7589 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 524, 566, 858, 865, 916, 1209, 1258, 1266]) (by decide +kernel)

theorem c7589_0 : P.sumLeaves 24 7771136 1024 = 194376 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7589) (lo := 0) (len := 1024) (W := 194376) check rows elimOK (by decide) (by decide) cover7589 (by decide)
  decide +kernel

theorem h7589 : P.leaf 34 7589 = 194376 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 194376)]) (.cons c7589_0 (.nil)) (by decide) (by decide))

theorem cover7590 : P.CoversSplit 24 10 7590 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 517, 522, 858, 865, 1209, 1258, 1266]) (by decide +kernel)

theorem c7590_0 : P.sumLeaves 24 7772160 1024 = 579234 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7590) (lo := 0) (len := 1024) (W := 579234) check rows elimOK (by decide) (by decide) cover7590 (by decide)
  decide +kernel

theorem h7590 : P.leaf 34 7590 = 579234 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 579234)]) (.cons c7590_0 (.nil)) (by decide) (by decide))

theorem cover7591 : P.CoversSplit 24 10 7591 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 566, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem c7591_0 : P.sumLeaves 24 7773184 1024 = 1022068 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7591) (lo := 0) (len := 1024) (W := 1022068) check rows elimOK (by decide) (by decide) cover7591 (by decide)
  decide +kernel

theorem h7591 : P.leaf 34 7591 = 1022068 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1022068)]) (.cons c7591_0 (.nil)) (by decide) (by decide))

theorem cover7596 : P.CoversSplit 24 10 7596 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7596_0 : P.sumLeaves 24 7778304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7596) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7596 (by decide)
  decide +kernel

theorem h7596 : P.leaf 34 7596 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7596_0 (.nil)) (by decide) (by decide))

theorem cover7597 : P.CoversSplit 24 10 7597 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 524, 566, 858, 865, 916, 1209, 1258, 1266]) (by decide +kernel)

theorem c7597_0 : P.sumLeaves 24 7779328 1024 = 1047866 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7597) (lo := 0) (len := 1024) (W := 1047866) check rows elimOK (by decide) (by decide) cover7597 (by decide)
  decide +kernel

theorem h7597 : P.leaf 34 7597 = 1047866 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1047866)]) (.cons c7597_0 (.nil)) (by decide) (by decide))

theorem cover7599 : P.CoversSplit 24 10 7599 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 566, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

noncomputable def f7599 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (7781376 + i)

theorem c7599_0 : rowSum f7599 0 1024 = 1934426 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7599) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover7599 (by decide)
  decide +kernel

theorem sum7599 : rowSum f7599 0 1024 = 1934426 :=
  c7599_0

theorem h7599 : P.leaf 34 7599 = 1934426 :=
  leaf_weighted (k := 24) (d := 10) (H := 7599) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 7599) (by decide) (by decide +kernel)) sum7599

theorem cover7601 : P.CoversSplit 24 10 7601 0xff000000000000000000000000000000ff000000000000000000000000000000cc030000000000000000000000000000cc030000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 858, 865, 866, 867, 916, 1202, 1209, 1210, 1308, 1601]) (by decide +kernel)

theorem c7601_0 : P.sumLeaves 24 7783424 1024 = 957904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7601) (lo := 0) (len := 1024) (W := 957904) check rows elimOK (by decide) (by decide) cover7601 (by decide)
  decide +kernel

theorem h7601 : P.leaf 34 7601 = 957904 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 957904)]) (.cons c7601_0 (.nil)) (by decide) (by decide))

theorem cover7602 : P.CoversSplit 24 10 7602 0xf0f0000000000000f0f0000000000000a0a0000000000000a0a0000000000000c0f0000000000000c00000000000000080a00000000000008000000000000000f0f0000000000000f0f000000000000000000000000000000000000000000000c0f0000000000000c00000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 858, 865, 866, 867, 908, 1209, 1308, 1601]) (by decide +kernel)

theorem c7602_0 : P.sumLeaves 24 7784448 192 = 6400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7602) (lo := 0) (len := 192) (W := 6400) check rows elimOK (by decide) (by decide) cover7602 (by decide)
  decide +kernel

theorem contract7602_1 : P.leaf 30 121635 = 16028 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 121635) (ss := [(6, 1, 478), (12, 1, 478), (10, 1, 458), (2, 1, 487), (3, 1, 524), (30, 18, 867), (18, 1, 879), (14, 1, 965), (31, 1, 1251), (28, 1, 858), (16, 1, 1265)]) (ids := [2, 3, 5, 6, 7, 9, 11, 13, 15, 17, 18, 19, 20, 23, 24, 25, 27, 21, 22]) (cs := [1, 1, 2, 3, 1, 4, 5, 6, 1, 7, 1, 8, 1, 9, 1, 10, 1, 11, 12, 13, 14, 19, 20, 15, 16, 17, 1, 18, 1, 1]) (bs := [17, 2]) (W := 16028) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7602_1 : P.sumLeaves 24 7784640 64 = 16028 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 121635) rows (by decide) (by decide)).symm.trans contract7602_1

theorem c7602_2 : P.sumLeaves 24 7784704 512 = 312368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7602) (lo := 256) (len := 512) (W := 312368) check rows elimOK (by decide) (by decide) cover7602 (by decide)
  decide +kernel

theorem contract7602_3 : P.leaf 30 121644 = 20000 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 121644) (ss := [(2, 1, 466), (6, 1, 478), (12, 1, 478), (10, 1, 458), (5, 1, 524), (8, 1, 531), (16, 1, 531), (30, 1, 866), (26, 1, 517), (31, 1, 517), (28, 1, 858), (11, 1, 909), (18, 1, 1265)]) (ids := [1, 2, 5, 7, 11, 12, 13, 15, 17, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [1, 2, 3, 1, 1, 4, 1, 5, 1, 1, 1, 6, 7, 8, 1, 9, 1, 10, 11, 12, 13, 17, 18, 14, 1, 15, 1, 16, 1, 1]) (bs := [15, 2]) (W := 20000) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7602_3 : P.sumLeaves 24 7785216 64 = 20000 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 121644) rows (by decide) (by decide)).symm.trans contract7602_3

theorem contract7602_4 : P.leaf 30 121645 = 50872 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 121645) (ss := [(6, 1, 478), (12, 1, 478), (10, 1, 458), (8, 1, 531), (16, 1, 531), (30, 1, 867), (26, 1, 517), (31, 1, 517), (28, 1, 858), (11, 1, 909), (18, 1, 1265)]) (ids := [0, 1, 2, 3, 5, 7, 11, 12, 13, 15, 17, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [2, 3, 4, 5, 1, 6, 1, 7, 1, 1, 1, 8, 9, 10, 1, 11, 1, 12, 13, 14, 15, 19, 20, 16, 1, 17, 1, 18, 1, 1]) (bs := [17, 2]) (W := 50872) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7602_4 : P.sumLeaves 24 7785280 64 = 50872 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 121645) rows (by decide) (by decide)).symm.trans contract7602_4

theorem c7602_5 : P.sumLeaves 24 7785344 128 = 563896 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7602) (lo := 896) (len := 128) (W := 563896) check rows elimOK (by decide) (by decide) cover7602 (by decide)
  decide +kernel

theorem h7602 : P.leaf 34 7602 = 969564 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 6400), (64, 16028), (512, 312368), (64, 20000), (64, 50872), (128, 563896)]) (.cons c7602_0 (.cons c7602_1 (.cons c7602_2 (.cons c7602_3 (.cons c7602_4 (.cons c7602_5 (.nil))))))) (by decide) (by decide))

theorem cover7603 : P.CoversSplit 24 10 7603 0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ccfc000000000000cc00000000000000ccfc000000000000cc00000000000000ffff000000000000ffff00000000000000000000000000000000000000000000ccfc000000000000cc0000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 858, 865, 866, 867, 916, 1202, 1209, 1210, 1308, 1601]) (by decide +kernel)

theorem c7603_0 : P.sumLeaves 24 7785472 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7603) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover7603 (by decide)
  decide +kernel

theorem contract7603_1 : P.leaf 30 121650 = 37200 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 121650) (ss := [(2, 1, 487), (5, 3, 524), (3, 1, 566), (30, 1, 866), (12, 1, 916), (29, 1, 916), (14, 1, 965), (18, 1, 965), (13, 1, 922), (31, 1, 1251), (27, 1, 1601)]) (ids := [2, 4, 5, 6, 7, 8, 9, 13, 14, 15, 17, 18, 19, 20, 21, 22, 24, 26, 23]) (cs := [1, 1, 2, 1, 3, 4, 5, 6, 7, 8, 1, 1, 1, 9, 10, 11, 1, 12, 13, 14, 15, 16, 17, 20, 18, 1, 19, 1, 1, 1]) (bs := [18, 1]) (W := 37200) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7603_1 : P.sumLeaves 24 7785600 64 = 37200 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 121650) rows (by decide) (by decide)).symm.trans contract7603_1

theorem c7603_2 : P.sumLeaves 24 7785664 320 = 2165604 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7603) (lo := 192) (len := 320) (W := 2165604) check rows elimOK (by decide) (by decide) cover7603 (by decide)
  decide +kernel

theorem contract7603_3 : P.leaf 30 121656 = 51648 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 121656) (ss := [(2, 1, 487), (5, 1, 524), (8, 1, 531), (16, 1, 531), (30, 1, 866), (11, 1, 909), (12, 1, 916), (29, 1, 916), (31, 1, 1251), (18, 1, 1265), (27, 1, 1601)]) (ids := [1, 2, 4, 5, 7, 8, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22, 24, 26, 23]) (cs := [1, 2, 3, 1, 4, 5, 1, 6, 7, 1, 1, 8, 9, 10, 1, 11, 1, 12, 13, 14, 15, 16, 17, 20, 18, 1, 19, 1, 1, 1]) (bs := [18, 1]) (W := 51648) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7603_3 : P.sumLeaves 24 7785984 64 = 51648 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 121656) rows (by decide) (by decide)).symm.trans contract7603_3

theorem c7603_4 : P.sumLeaves 24 7786048 448 = 10291334 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7603) (lo := 576) (len := 448) (W := 10291334) check rows elimOK (by decide) (by decide) cover7603 (by decide)
  decide +kernel

theorem h7603 : P.leaf 34 7603 = 12545786 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 37200), (320, 2165604), (64, 51648), (448, 10291334)]) (.cons c7603_0 (.cons c7603_1 (.cons c7603_2 (.cons c7603_3 (.cons c7603_4 (.nil)))))) (by decide) (by decide))

theorem cover7604 : P.CoversSplit 24 10 7604 0xf0000000000000000000000000000000a0000000000000000000000000000000c000000000000000c00000000000000080000000000000008000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 858, 865, 866, 916, 1202, 1209, 1308, 1601]) (by decide +kernel)

theorem c7604_0 : P.sumLeaves 24 7786496 1024 = 659320 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7604) (lo := 0) (len := 1024) (W := 659320) check rows elimOK (by decide) (by decide) cover7604 (by decide)
  decide +kernel

theorem h7604 : P.leaf 34 7604 = 659320 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 659320)]) (.cons c7604_0 (.nil)) (by decide) (by decide))

theorem cover7605 : P.CoversSplit 24 10 7605 0xff000000000000000000000000000000ff000000000000000000000000000000cc030000000000000000000000000000cc030000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 858, 865, 866, 916, 1202, 1209, 1210, 1251, 1308, 1601]) (by decide +kernel)

theorem c7605_0 : P.sumLeaves 24 7787520 1024 = 2925394 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7605) (lo := 0) (len := 1024) (W := 2925394) check rows elimOK (by decide) (by decide) cover7605 (by decide)
  decide +kernel

theorem h7605 : P.leaf 34 7605 = 2925394 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2925394)]) (.cons c7605_0 (.nil)) (by decide) (by decide))

theorem cover7606 : P.CoversSplit 24 10 7606 0xf0f0000000000000f0f0000000000000a0a0000000000000a0a0000000000000c0f0000000000000c00000000000000080a00000000000008000000000000000f0f0000000000000f0f000000000000000000000000000000000000000000000c0f0000000000000c00000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 858, 865, 866, 908, 1209, 1308, 1601]) (by decide +kernel)

theorem c7606_0 : P.sumLeaves 24 7788544 768 = 2705776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7606) (lo := 0) (len := 768) (W := 2705776) check rows elimOK (by decide) (by decide) cover7606 (by decide)
  decide +kernel

theorem contract7606_1 : P.leaf 30 121708 = 80980 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 121708) (ss := [(2, 1, 466), (5, 1, 524), (8, 1, 531), (6, 1, 468), (16, 1, 531), (30, 1, 866), (26, 1, 517), (31, 1, 517), (28, 1, 858), (11, 1, 909), (18, 1, 1265)]) (ids := [1, 2, 5, 7, 8, 10, 11, 12, 13, 15, 17, 18, 19, 20, 21, 23, 25, 27, 22]) (cs := [1, 2, 3, 1, 1, 4, 1, 5, 6, 1, 7, 8, 9, 10, 1, 11, 1, 12, 13, 14, 15, 16, 20, 17, 1, 18, 1, 19, 1, 1]) (bs := [18, 1]) (W := 80980) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7606_1 : P.sumLeaves 24 7789312 64 = 80980 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 121708) rows (by decide) (by decide)).symm.trans contract7606_1

theorem c7606_2 : P.sumLeaves 24 7789376 192 = 5910744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7606) (lo := 832) (len := 192) (W := 5910744) check rows elimOK (by decide) (by decide) cover7606 (by decide)
  decide +kernel

theorem h7606 : P.leaf 34 7606 = 8697500 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 2705776), (64, 80980), (192, 5910744)]) (.cons c7606_0 (.cons c7606_1 (.cons c7606_2 (.nil)))) (by decide) (by decide))

theorem cover7607 : P.CoversSplit 24 10 7607 0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ccfc000000000000cc00000000000000ccfc000000000000cc00000000000000ffff000000000000ffff00000000000000000000000000000000000000000000ccfc000000000000cc0000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 858, 865, 866, 1202, 1209, 1210, 1251, 1258, 1308, 1601]) (by decide +kernel)

theorem c7607_0 : P.sumLeaves 24 7789568 886 = 11689473 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7607) (lo := 0) (len := 886) (W := 11689473) check rows elimOK (by decide) (by decide) cover7607 (by decide)
  decide +kernel

theorem c7607_1 : P.sumLeaves 24 7790454 138 = 20981880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7607) (lo := 886) (len := 138) (W := 20981880) check rows elimOK (by decide) (by decide) cover7607 (by decide)
  decide +kernel

theorem h7607 : P.leaf 34 7607 = 32671353 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(886, 11689473), (138, 20981880)]) (.cons c7607_0 (.cons c7607_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(7535, 24), (7540, 48), (7541, 48), (7542, 48), (7543, 48), (7544, 48), (7545, 48), (7546, 48), (7547, 48), (7548, 48), (7549, 48), (7550, 48), (7551, 48), (7584, 12), (7585, 48), (7587, 24), (7588, 48), (7589, 48), (7590, 48), (7591, 48), (7596, 24), (7597, 48), (7599, 24), (7601, 24), (7602, 24), (7603, 48), (7604, 48), (7605, 48), (7606, 48), (7607, 48)]

theorem segOK : checkSeg 16 perms 7535 7608 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7535 7608 1260 17529236160 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 17529236160)
    (SegSum.cons (w := 24) h7535 (SegSum.cons (w := 48) h7540 (SegSum.cons (w := 48) h7541 (SegSum.cons (w := 48) h7542 (SegSum.cons (w := 48) h7543 (SegSum.cons (w := 48) h7544 (SegSum.cons (w := 48) h7545 (SegSum.cons (w := 48) h7546 (SegSum.cons (w := 48) h7547 (SegSum.cons (w := 48) h7548 (SegSum.cons (w := 48) h7549 (SegSum.cons (w := 48) h7550 (SegSum.cons (w := 48) h7551 (SegSum.cons (w := 12) h7584 (SegSum.cons (w := 48) h7585 (SegSum.cons (w := 24) h7587 (SegSum.cons (w := 48) h7588 (SegSum.cons (w := 48) h7589 (SegSum.cons (w := 48) h7590 (SegSum.cons (w := 48) h7591 (SegSum.cons (w := 24) h7596 (SegSum.cons (w := 48) h7597 (SegSum.cons (w := 24) h7599 (SegSum.cons (w := 24) h7601 (SegSum.cons (w := 24) h7602 (SegSum.cons (w := 48) h7603 (SegSum.cons (w := 48) h7604 (SegSum.cons (w := 48) h7605 (SegSum.cons (w := 48) h7606 (SegSum.cons (w := 48) h7607 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S50
