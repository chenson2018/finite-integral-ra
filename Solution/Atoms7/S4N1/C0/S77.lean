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

namespace RACert.S4N1.C0.S77

open RACert RACert.Problem

theorem cover26494 : P.CoversSplit 24 10 26494 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa880000000000000000ffccffccfac8aa880000000000000000fffffffffafaaaaaffff0000fafa0000ffffffff00000000ffff0000000000000000000000000000000000000000000000c00000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 872, 1202, 1259, 1264, 1308, 1601, 1609]) (ps := [(14, [965], [1609])]) (by decide +kernel)

theorem c26494_0 : P.sumLeaves 24 27129856 478 = 28545593 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26494) (lo := 0) (len := 478) (W := 28545593) check rows elimOK (by decide) (by decide) cover26494 (by decide)
  decide +kernel

theorem c26494_1 : P.sumLeaves 24 27130334 270 = 44593543 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26494) (lo := 478) (len := 270) (W := 44593543) check rows elimOK (by decide) (by decide) cover26494 (by decide)
  decide +kernel

theorem c26494_2 : P.sumLeaves 24 27130604 124 = 41394863 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26494) (lo := 748) (len := 124) (W := 41394863) check rows elimOK (by decide) (by decide) cover26494 (by decide)
  decide +kernel

theorem c26494_3 : P.sumLeaves 24 27130728 120 = 103221043 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26494) (lo := 872) (len := 120) (W := 103221043) check rows elimOK (by decide) (by decide) cover26494 (by decide)
  decide +kernel

theorem c26494_4 : P.sumLeaves 24 27130848 32 = 69618851 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26494) (lo := 992) (len := 32) (W := 69618851) check rows elimOK (by decide) (by decide) cover26494 (by decide)
  decide +kernel

theorem h26494 : P.leaf 34 26494 = 287373893 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(478, 28545593), (270, 44593543), (124, 41394863), (120, 103221043), (32, 69618851)]) (.cons c26494_0 (.cons c26494_1 (.cons c26494_2 (.cons c26494_3 (.cons c26494_4 (.nil)))))) (by decide) (by decide))

theorem h24382 : P.leaf 34 24382 = 287373893 :=
  orient5 (v := 26494) (by decide) (by decide +kernel) h26494

theorem cover26495 : P.CoversSplit 24 10 26495 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa880000000000000000ffccffccfac8aa880000000000000000fffffffffafaaaaaffff0000fafa0000ffffffff00000000ffff0000000000000000000000000000000000000000000000c00000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 860, 872, 1202, 1259, 1264, 1308, 1601, 1609]) (ps := [(14, [965], [1609])]) (by decide +kernel)

theorem c26495_0 : P.sumLeaves 24 27130880 478 = 44084906 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26495) (lo := 0) (len := 478) (W := 44084906) check rows elimOK (by decide) (by decide) cover26495 (by decide)
  decide +kernel

theorem c26495_1 : P.sumLeaves 24 27131358 270 = 78182964 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26495) (lo := 478) (len := 270) (W := 78182964) check rows elimOK (by decide) (by decide) cover26495 (by decide)
  decide +kernel

theorem c26495_2 : P.sumLeaves 24 27131628 124 = 78659357 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26495) (lo := 748) (len := 124) (W := 78659357) check rows elimOK (by decide) (by decide) cover26495 (by decide)
  decide +kernel

theorem c26495_3 : P.sumLeaves 24 27131752 120 = 174532813 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26495) (lo := 872) (len := 120) (W := 174532813) check rows elimOK (by decide) (by decide) cover26495 (by decide)
  decide +kernel

theorem c26495_4 : P.sumLeaves 24 27131872 32 = 110158557 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26495) (lo := 992) (len := 32) (W := 110158557) check rows elimOK (by decide) (by decide) cover26495 (by decide)
  decide +kernel

theorem h26495 : P.leaf 34 26495 = 485618597 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(478, 44084906), (270, 78182964), (124, 78659357), (120, 174532813), (32, 110158557)]) (.cons c26495_0 (.cons c26495_1 (.cons c26495_2 (.cons c26495_3 (.cons c26495_4 (.nil)))))) (by decide) (by decide))

theorem h24383 : P.leaf 34 24383 = 485618597 :=
  orient5 (v := 26495) (by decide) (by decide +kernel) h26495

theorem cover28014 : P.CoversSplit 24 10 28014 0xcc00cc00c800c8000000000000000000cc000000000000000000000000000000dd0cdd0cd808d8080000000000000000dd0c0000000000000000000000000000cc00cc00c800c8000000000000000000cc0004000000000000000000000000000000000000000000003300320032003200000000000000000033000100000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 572, 858, 865, 915, 1202, 1210, 1601]) (ps := [(18, [1210], [1264])]) (by decide +kernel)

noncomputable def f28014 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (28686336 + i)

theorem c28014_0 : rowSum f28014 0 1024 = 25655516 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28014) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28014 (by decide)
  decide +kernel

theorem sum28014 : rowSum f28014 0 1024 = 25655516 :=
  c28014_0

theorem h28014 : P.leaf 34 28014 = 25655516 :=
  leaf_weighted (k := 24) (d := 10) (H := 28014) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 28014) (by decide) (by decide +kernel)) sum28014

theorem h24428 : P.leaf 34 24428 = 25655516 :=
  orient5 (v := 28014) (by decide) (by decide +kernel) h28014

theorem cover28015 : P.CoversSplit 24 10 28015 0xcc00cc00c800c8000000000000000000cc000000000000000000000000000000cc00cc00c800c8000000000000000000cc000000000000000000000000000000cc00cc00c800c8000000000000000000cc0004000000000000000000000000000000000000000000003300320032003200000000000000000033000100000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 572, 858, 865, 1202, 1210, 1601]) (ps := [(18, [1210], [1264])]) (by decide +kernel)

noncomputable def f28015 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (28687360 + i)

theorem c28015_0 : rowSum f28015 0 1024 = 40112870 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28015) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28015 (by decide)
  decide +kernel

theorem sum28015 : rowSum f28015 0 1024 = 40112870 :=
  c28015_0

theorem h28015 : P.leaf 34 28015 = 40112870 :=
  leaf_weighted (k := 24) (d := 10) (H := 28015) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 28015) (by decide) (by decide +kernel)) sum28015

theorem h24429 : P.leaf 34 24429 = 40112870 :=
  orient5 (v := 28015) (by decide) (by decide +kernel) h28015

theorem cover28030 : P.CoversSplit 24 10 28030 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffc0ffc0fac0fac00000000000000000ffc0ffc0fac0fac00000000000000000ff00ff00fa00fa00ff330000fa320000ff00ff0000000000ff330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 865, 915, 1202, 1259, 1264, 1308, 1601]) (by decide +kernel)

theorem c28030_0 : P.sumLeaves 24 28702720 617 = 31610734 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28030) (lo := 0) (len := 617) (W := 31610734) check rows elimOK (by decide) (by decide) cover28030 (by decide)
  decide +kernel

theorem c28030_1 : P.sumLeaves 24 28703337 202 = 31869289 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28030) (lo := 617) (len := 202) (W := 31869289) check rows elimOK (by decide) (by decide) cover28030 (by decide)
  decide +kernel

theorem c28030_2 : P.sumLeaves 24 28703539 112 = 61743029 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28030) (lo := 819) (len := 112) (W := 61743029) check rows elimOK (by decide) (by decide) cover28030 (by decide)
  decide +kernel

theorem c28030_3 : P.sumLeaves 24 28703651 93 = 102085838 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28030) (lo := 931) (len := 93) (W := 102085838) check rows elimOK (by decide) (by decide) cover28030 (by decide)
  decide +kernel

theorem h28030 : P.leaf 34 28030 = 227308890 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(617, 31610734), (202, 31869289), (112, 61743029), (93, 102085838)]) (.cons c28030_0 (.cons c28030_1 (.cons c28030_2 (.cons c28030_3 (.nil))))) (by decide) (by decide))

theorem h24430 : P.leaf 34 24430 = 227308890 :=
  orient5 (v := 28030) (by decide) (by decide +kernel) h28030

theorem cover28031 : P.CoversSplit 24 10 28031 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac80000000000000000ffccffccfac8fac80000000000000000ff00ff00fa00fa00ff330000fa320000ff00ff0000000000ff330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 865, 915, 1202, 1259, 1264, 1308, 1601]) (by decide +kernel)

theorem c28031_0 : P.sumLeaves 24 28703744 611 = 49519482 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28031) (lo := 0) (len := 611) (W := 49519482) check rows elimOK (by decide) (by decide) cover28031 (by decide)
  decide +kernel

theorem c28031_1 : P.sumLeaves 24 28704355 196 = 55143865 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28031) (lo := 611) (len := 196) (W := 55143865) check rows elimOK (by decide) (by decide) cover28031 (by decide)
  decide +kernel

theorem c28031_2 : P.sumLeaves 24 28704551 110 = 78979169 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28031) (lo := 807) (len := 110) (W := 78979169) check rows elimOK (by decide) (by decide) cover28031 (by decide)
  decide +kernel

theorem c28031_3 : P.sumLeaves 24 28704661 106 = 157939996 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28031) (lo := 917) (len := 106) (W := 157939996) check rows elimOK (by decide) (by decide) cover28031 (by decide)
  decide +kernel

theorem c28031_4 : P.sumLeaves 24 28704767 1 = 4427992 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28031) (lo := 1023) (len := 1) (W := 4427992) check rows elimOK (by decide) (by decide) cover28031 (by decide)
  decide +kernel

theorem h28031 : P.leaf 34 28031 = 346010504 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(611, 49519482), (196, 55143865), (110, 78979169), (106, 157939996), (1, 4427992)]) (.cons c28031_0 (.cons c28031_1 (.cons c28031_2 (.cons c28031_3 (.cons c28031_4 (.nil)))))) (by decide) (by decide))

theorem h24431 : P.leaf 34 24431 = 346010504 :=
  orient5 (v := 28031) (by decide) (by decide +kernel) h28031

def seg : List (ℕ × ℕ) := [(24382, 48), (24383, 48), (24428, 24), (24429, 24), (24430, 48), (24431, 48)]

theorem segOK : checkSeg 16 perms 24382 24446 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24382 24446 240 66201411696 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 66201411696)
    (SegSum.cons (w := 48) h24382 (SegSum.cons (w := 48) h24383 (SegSum.cons (w := 24) h24428 (SegSum.cons (w := 24) h24429 (SegSum.cons (w := 48) h24430 (SegSum.cons (w := 48) h24431 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S77
