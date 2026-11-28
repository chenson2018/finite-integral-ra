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

namespace RACert.S4N1.C0.S48

open RACert RACert.Problem

theorem cover7935 : P.CoversSplit 24 10 7935 0xffffffffffff00000000000000000000ffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 916, 1209, 1210, 1217, 1258, 1259, 1264, 1308]) (by decide +kernel)

noncomputable def f7935 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (8125440 + i)

theorem c7935_0 : rowSum f7935 0 1024 = 62437892 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7935) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover7935 (by decide)
  decide +kernel

theorem sum7935 : rowSum f7935 0 1024 = 62437892 :=
  c7935_0

theorem h7935 : P.leaf 34 7935 = 62437892 :=
  leaf_weighted (k := 24) (d := 10) (H := 7935) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 7935) (by decide) (by decide +kernel)) sum7935

theorem cover26083 : P.CoversSplit 24 10 26083 0xf0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f26083 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (26708992 + i)

theorem c26083_0 : rowSum f26083 0 1024 = 10066248 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26083) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26083 (by decide)
  decide +kernel

theorem sum26083 : rowSum f26083 0 1024 = 10066248 :=
  c26083_0

theorem h26083 : P.leaf 34 26083 = 10066248 :=
  leaf_weighted (k := 24) (d := 10) (H := 26083) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 26083) (by decide) (by decide +kernel)) sum26083

theorem h8052 : P.leaf 34 8052 = 10066248 :=
  orient32 (v := 26083) (by decide) (by decide +kernel) h26083

theorem cover8053 : P.CoversSplit 24 10 8053 0xffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000cc00cc00cc008000cc33cc33cc338020cc00cc00c8008000cc33cc33c82080200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 572, 916, 1209, 1210, 1217, 1258, 1601]) (ps := [(8, [1217], [572]), (14, [1217], [916])]) (by decide +kernel)

noncomputable def f8053 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8246272 + i)

theorem c8053_0 : rowSum f8053 0 757 = 9744497 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8053) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8053 (by decide)
  decide +kernel

theorem c8053_1 : rowSum f8053 757 190 = 35752658 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8053) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8053 (by decide)
  decide +kernel

theorem c8053_2 : rowSum f8053 947 77 = 47284066 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8053) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8053 (by decide)
  decide +kernel

theorem sum8053 : rowSum f8053 0 1024 = 92781221 :=
  rowSum_append (F := f8053) (lo := 0) (n := 757) (m := 267) (A := 9744497) (B := 83036724) c8053_0 (rowSum_append (F := f8053) (lo := 757) (n := 190) (m := 77) (A := 35752658) (B := 47284066) c8053_1 (c8053_2))

theorem h8053 : P.leaf 34 8053 = 92781221 :=
  leaf_weighted (k := 24) (d := 10) (H := 8053) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 8053) (by decide) (by decide +kernel)) sum8053

theorem cover26595 : P.CoversSplit 24 10 26595 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000ffccffccfac8a080cc00cc00c8008000ffccffccfac8a080cc00000000000000fffffffffafaa0a0ffff0000fafa0000fffffffffafaa0a0ffff000000000000ffcc0000fac80000cc000000c8000000ffcc0000fac80000cc00000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 860, 915, 1202, 1251, 1259, 1264, 1601]) (by decide +kernel)

noncomputable def f26595 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (27233280 + i)

theorem c26595_0 : rowSum f26595 0 440 = 23516158 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26595) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26595 (by decide)
  decide +kernel

theorem c26595_1 : rowSum f26595 440 326 = 73924801 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26595) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26595 (by decide)
  decide +kernel

theorem c26595_2 : rowSum f26595 766 258 = 46506552 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26595) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26595 (by decide)
  decide +kernel

theorem sum26595 : rowSum f26595 0 1024 = 143947511 :=
  rowSum_append (F := f26595) (lo := 0) (n := 440) (m := 584) (A := 23516158) (B := 120431353) c26595_0 (rowSum_append (F := f26595) (lo := 440) (n := 326) (m := 258) (A := 73924801) (B := 46506552) c26595_1 (c26595_2))

theorem h26595 : P.leaf 34 26595 = 143947511 :=
  leaf_weighted (k := 24) (d := 10) (H := 26595) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 26595) (by decide) (by decide +kernel)) sum26595

theorem h8054 : P.leaf 34 8054 = 143947511 :=
  orient32 (v := 26595) (by decide) (by decide +kernel) h26595

theorem cover26611 : P.CoversSplit 24 10 26611 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffccffccfac8a080cc00cc00c8008000ffccffccfac8a080cc00cc00c8008000fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffccffccfac8a080cc00cc00c8008000ffccffccfac8a080cc00cc00c8008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [860, 915, 1202, 1259, 1601]) (by decide +kernel)

noncomputable def f26611 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (27249664 + i)

theorem c26611_0 : rowSum f26611 0 295 = 15717349 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26611) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26611 (by decide)
  decide +kernel

theorem c26611_1 : rowSum f26611 295 187 = 70730815 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26611) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26611 (by decide)
  decide +kernel

theorem c26611_2 : rowSum f26611 482 476 = 135567515 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26611) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26611 (by decide)
  decide +kernel

theorem c26611_3 : rowSum f26611 958 66 = 37053168 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26611) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26611 (by decide)
  decide +kernel

theorem sum26611 : rowSum f26611 0 1024 = 259068847 :=
  rowSum_append (F := f26611) (lo := 0) (n := 295) (m := 729) (A := 15717349) (B := 243351498) c26611_0 (rowSum_append (F := f26611) (lo := 295) (n := 187) (m := 542) (A := 70730815) (B := 172620683) c26611_1 (rowSum_append (F := f26611) (lo := 482) (n := 476) (m := 66) (A := 135567515) (B := 37053168) c26611_2 (c26611_3)))

theorem h26611 : P.leaf 34 26611 = 259068847 :=
  leaf_weighted (k := 24) (d := 10) (H := 26611) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 26611) (by decide) (by decide +kernel)) sum26611

theorem h8055 : P.leaf 34 8055 = 259068847 :=
  orient32 (v := 26611) (by decide) (by decide +kernel) h26611

theorem cover42467 : P.CoversSplit 24 10 42467 0xffffffffaaaaa0a0ffff0000aaaa0000ffff000000000000ffff000000000000cccccccc88888080cc00000088000000cccc000000000000cc00000000000000ffffffffaaaaa0a00000000000000000ffff55550000000033330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 522, 858, 860, 865, 915, 1202, 1209, 1258, 1601]) (by decide +kernel)

noncomputable def f42467 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (43486208 + i)

theorem c42467_0 : rowSum f42467 0 953 = 9696392 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 42467) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover42467 (by decide)
  decide +kernel

theorem c42467_1 : rowSum f42467 953 71 = 6548696 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 42467) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover42467 (by decide)
  decide +kernel

theorem sum42467 : rowSum f42467 0 1024 = 16245088 :=
  rowSum_append (F := f42467) (lo := 0) (n := 953) (m := 71) (A := 9696392) (B := 6548696) c42467_0 (c42467_1)

theorem h42467 : P.leaf 34 42467 = 16245088 :=
  leaf_weighted (k := 24) (d := 10) (H := 42467) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 42467) (by decide) (by decide +kernel)) sum42467

theorem h8056 : P.leaf 34 8056 = 16245088 :=
  orient32 (v := 42467) (by decide) (by decide +kernel) h42467

theorem cover8057 : P.CoversSplit 24 10 8057 0xffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000cc00cc00cc008000cc00cc00cc008000cc00cc00c8008000fffffffff8a8a0a0000000000000000000000000000000000000000000000000cc00000080000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 572, 916, 1209, 1210, 1217, 1258, 1601]) (ps := [(5, [523], [572]), (8, [586, 1217], [572, 1609]), (14, [923, 1217], [916])]) (by decide +kernel)

noncomputable def f8057 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8250368 + i)

theorem c8057_0 : rowSum f8057 0 746 = 4199428 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8057) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8057 (by decide)
  decide +kernel

theorem c8057_1 : rowSum f8057 746 193 = 16592876 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8057) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8057 (by decide)
  decide +kernel

theorem c8057_2 : rowSum f8057 939 85 = 27023592 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8057) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8057 (by decide)
  decide +kernel

theorem sum8057 : rowSum f8057 0 1024 = 47815896 :=
  rowSum_append (F := f8057) (lo := 0) (n := 746) (m := 278) (A := 4199428) (B := 43616468) c8057_0 (rowSum_append (F := f8057) (lo := 746) (n := 193) (m := 85) (A := 16592876) (B := 27023592) c8057_1 (c8057_2))

theorem h8057 : P.leaf 34 8057 = 47815896 :=
  leaf_weighted (k := 24) (d := 10) (H := 8057) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 8057) (by decide) (by decide +kernel)) sum8057

theorem cover42979 : P.CoversSplit 24 10 42979 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffff000000000000ffff000000000000cccccccc88888080cc00cc0088008000cccc000000000000cc00000000000000ffffffffaaaaa0a00000000000000000ffff55550000000033330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 860, 915, 1202, 1209, 1258, 1601]) (ps := [(16, [1251], [1258])]) (by decide +kernel)

noncomputable def f42979 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (44010496 + i)

theorem c42979_0 : rowSum f42979 0 933 = 23936560 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 42979) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover42979 (by decide)
  decide +kernel

theorem c42979_1 : rowSum f42979 933 91 = 22077268 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 42979) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover42979 (by decide)
  decide +kernel

theorem sum42979 : rowSum f42979 0 1024 = 46013828 :=
  rowSum_append (F := f42979) (lo := 0) (n := 933) (m := 91) (A := 23936560) (B := 22077268) c42979_0 (c42979_1)

theorem h42979 : P.leaf 34 42979 = 46013828 :=
  leaf_weighted (k := 24) (d := 10) (H := 42979) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 42979) (by decide) (by decide +kernel)) sum42979

theorem h8058 : P.leaf 34 8058 = 46013828 :=
  orient32 (v := 42979) (by decide) (by decide +kernel) h42979

theorem cover42995 : P.CoversSplit 24 10 42995 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffffffffaaaaa0a0ffffffffaaaaa0a0cccccccc88888080cc00cc0088008000cccccccc88888080cc00cc0088008000ffffffffaaaaa0a0ffffffffaaaaa0a0ffffffffaaaaa0a0ffffffffaaaaa0a0cccccccc88888080cc00cc0088008000cccccccc88888080cc00cc0088008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [860, 915, 1202, 1258, 1601]) (by decide +kernel)

noncomputable def f42995 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (44026880 + i)

theorem c42995_0 : rowSum f42995 0 380 = 11999052 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 42995) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover42995 (by decide)
  decide +kernel

theorem c42995_1 : rowSum f42995 380 306 = 43126756 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 42995) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover42995 (by decide)
  decide +kernel

theorem c42995_2 : rowSum f42995 686 338 = 57325533 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 42995) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover42995 (by decide)
  decide +kernel

theorem sum42995 : rowSum f42995 0 1024 = 112451341 :=
  rowSum_append (F := f42995) (lo := 0) (n := 380) (m := 644) (A := 11999052) (B := 100452289) c42995_0 (rowSum_append (F := f42995) (lo := 380) (n := 306) (m := 338) (A := 43126756) (B := 57325533) c42995_1 (c42995_2))

theorem h42995 : P.leaf 34 42995 = 112451341 :=
  leaf_weighted (k := 24) (d := 10) (H := 42995) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 42995) (by decide) (by decide +kernel)) sum42995

theorem h8059 : P.leaf 34 8059 = 112451341 :=
  orient32 (v := 42995) (by decide) (by decide +kernel) h42995

def seg : List (ℕ × ℕ) := [(7935, 24), (8052, 24), (8053, 24), (8054, 24), (8055, 24), (8056, 24), (8057, 24), (8058, 24), (8059, 24)]

theorem segOK : checkSeg 16 perms 7935 8060 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7935 8060 216 18979868928 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 18979868928)
    (SegSum.cons (w := 24) h7935 (SegSum.cons (w := 24) h8052 (SegSum.cons (w := 24) h8053 (SegSum.cons (w := 24) h8054 (SegSum.cons (w := 24) h8055 (SegSum.cons (w := 24) h8056 (SegSum.cons (w := 24) h8057 (SegSum.cons (w := 24) h8058 (SegSum.cons (w := 24) h8059 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))) (by decide)

end RACert.S4N1.C0.S48
