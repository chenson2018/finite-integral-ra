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

namespace RACert.S4N1.C0.S49

open RACert RACert.Problem

theorem cover8060 : P.CoversSplit 24 10 8060 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc00c8008000cc33cc33c8328020cc00cc00c8008000cc33cc33c82080200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 572, 916, 1209, 1210, 1601]) (ps := [(8, [1217], [572]), (14, [1217], [916])]) (by decide +kernel)

noncomputable def f8060 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8253440 + i)

theorem c8060_0 : rowSum f8060 0 801 = 13034825 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8060) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8060 (by decide)
  decide +kernel

theorem c8060_1 : rowSum f8060 801 201 = 47170930 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8060) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8060 (by decide)
  decide +kernel

theorem c8060_2 : rowSum f8060 1002 22 = 22356890 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8060) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8060 (by decide)
  decide +kernel

theorem sum8060 : rowSum f8060 0 1024 = 82562645 :=
  rowSum_append (F := f8060) (lo := 0) (n := 801) (m := 223) (A := 13034825) (B := 69527820) c8060_0 (rowSum_append (F := f8060) (lo := 801) (n := 201) (m := 22) (A := 47170930) (B := 22356890) c8060_1 (c8060_2))

theorem h8060 : P.leaf 34 8060 = 82562645 :=
  leaf_weighted (k := 24) (d := 10) (H := 8060) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 8060) (by decide) (by decide +kernel)) sum8060

theorem cover8061 : P.CoversSplit 24 10 8061 0xffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000cc00cc00cc008000cc33cc33cc338020cc00cc00c8008000cc33cc33c82080200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 572, 916, 1209, 1210, 1217, 1258, 1601]) (ps := [(8, [1217], [572]), (14, [1217], [916])]) (by decide +kernel)

noncomputable def f8061 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8254464 + i)

theorem c8061_0 : rowSum f8061 0 757 = 19738986 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8061) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8061 (by decide)
  decide +kernel

theorem c8061_1 : rowSum f8061 757 190 = 59697108 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8061) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8061 (by decide)
  decide +kernel

theorem c8061_2 : rowSum f8061 947 77 = 67455772 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8061) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8061 (by decide)
  decide +kernel

theorem sum8061 : rowSum f8061 0 1024 = 146891866 :=
  rowSum_append (F := f8061) (lo := 0) (n := 757) (m := 267) (A := 19738986) (B := 127152880) c8061_0 (rowSum_append (F := f8061) (lo := 757) (n := 190) (m := 77) (A := 59697108) (B := 67455772) c8061_1 (c8061_2))

theorem h8061 : P.leaf 34 8061 = 146891866 :=
  leaf_weighted (k := 24) (d := 10) (H := 8061) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 8061) (by decide) (by decide +kernel)) sum8061

theorem cover59363 : P.CoversSplit 24 10 59363 0xfffffffffefea0a0fffffffffefea0a0fffffffffefea0a0fffffffffefea0a0ffeeffeefeeea0a0cc00cc00cc008000ffeeffeefeeea0a0cc00cc00cc008000fffffffffefea0a0fffffffffefea0a0fffffffffafaa0a0fffffffffafaa0a0ffeeffeefeeea0a0cc00cc00cc008000ffccffccfac8a080cc00cc00c8008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 860, 915, 1202, 1217, 1601, 1609]) (by decide +kernel)

noncomputable def f59363 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (60787712 + i)

theorem c59363_0 : rowSum f59363 0 252 = 17844718 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59363) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59363 (by decide)
  decide +kernel

theorem c59363_1 : rowSum f59363 252 215 = 54062972 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59363) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59363 (by decide)
  decide +kernel

theorem c59363_2 : rowSum f59363 467 465 = 100218538 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59363) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59363 (by decide)
  decide +kernel

theorem c59363_3 : rowSum f59363 932 92 = 53025572 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59363) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59363 (by decide)
  decide +kernel

theorem sum59363 : rowSum f59363 0 1024 = 225151800 :=
  rowSum_append (F := f59363) (lo := 0) (n := 252) (m := 772) (A := 17844718) (B := 207307082) c59363_0 (rowSum_append (F := f59363) (lo := 252) (n := 215) (m := 557) (A := 54062972) (B := 153244110) c59363_1 (rowSum_append (F := f59363) (lo := 467) (n := 465) (m := 92) (A := 100218538) (B := 53025572) c59363_2 (c59363_3)))

theorem h59363 : P.leaf 34 59363 = 225151800 :=
  leaf_weighted (k := 24) (d := 10) (H := 59363) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 59363) (by decide) (by decide +kernel)) sum59363

theorem h8062 : P.leaf 34 8062 = 225151800 :=
  orient32 (v := 59363) (by decide) (by decide +kernel) h59363

theorem cover8063 : P.CoversSplit 24 10 8063 0xffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000ffffffffffffa0a0ffffffffffffa0a0fffffffffafaa0a0fffffffffafaa0a00000000000000000cc00cc0080008000cc33cc3380008000cc00cc0080008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

def k8063 : ℕ := 0x8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cefffffffffffffffff
def t8063 : ℕ := 0x8ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce0000000000000000

noncomputable def f8063 (i : ℕ) := rowWeight k8063 t8063 i * P.leaf 24 (8256512 + i)

theorem contract8063_0 : P.leaf 30 129008 = 0 := by
  exact leaf_contract_zero (ss := [(4, 1, 578), (11, 1, 921), (29, 27, 1601), (27, 1, 572), (8, 0, 1609), (5, 1, 622), (14, 1, 1266)]) (q := 1609) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8063_0 : rowSum f8063 0 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k8063) (twice := t8063) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 129008) rows (by decide) (by decide)).symm.trans contract8063_0)

theorem c8063_1 : rowSum f8063 64 353 = 20972134 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8063) (keep := k8063) (twice := t8063) check rows elimOK (by decide) (by decide) cover8063 (by decide)
  decide +kernel

theorem c8063_2 : rowSum f8063 417 356 = 52857653 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8063) (keep := k8063) (twice := t8063) check rows elimOK (by decide) (by decide) cover8063 (by decide)
  decide +kernel

theorem c8063_3 : rowSum f8063 773 181 = 168490874 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8063) (keep := k8063) (twice := t8063) check rows elimOK (by decide) (by decide) cover8063 (by decide)
  decide +kernel

theorem c8063_4 : rowSum f8063 954 70 = 118002851 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8063) (keep := k8063) (twice := t8063) check rows elimOK (by decide) (by decide) cover8063 (by decide)
  decide +kernel

theorem sum8063 : rowSum f8063 0 1024 = 360323512 :=
  rowSum_append (F := f8063) (lo := 0) (n := 64) (m := 960) (A := 0) (B := 360323512) c8063_0 (rowSum_append (F := f8063) (lo := 64) (n := 353) (m := 607) (A := 20972134) (B := 339351378) c8063_1 (rowSum_append (F := f8063) (lo := 417) (n := 356) (m := 251) (A := 52857653) (B := 286493725) c8063_2 (rowSum_append (F := f8063) (lo := 773) (n := 181) (m := 70) (A := 168490874) (B := 118002851) c8063_3 (c8063_4))))

theorem h8063 : P.leaf 34 8063 = 360323512 :=
  leaf_weighted (k := 24) (d := 10) (H := 8063) (keep := k8063) (twice := t8063) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow3 (H := 8063) (by decide) (by decide +kernel)) sum8063

theorem cover50975 : P.CoversSplit 24 10 50975 0xfffffffffa000a00fffffffffa000a00ffffffffc8000800ffffffffc8000800aa88aa88aa000a002200220022000200aa88aa88880008002200220000000000fffffffffa000a00fffffffffa000a00ffffffffc8000800ffffffffc8000800a080a080a00000002000200020000000a080a080000000002000200000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 523, 529, 572, 872, 909, 1202, 1601]) (ps := [(8, [615], [1266])]) (by decide +kernel)

noncomputable def f50975 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (52198400 + i)

theorem c50975_0 : rowSum f50975 0 459 = 8327134 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 50975) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover50975 (by decide)
  decide +kernel

theorem c50975_1 : rowSum f50975 459 564 = 44227834 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 50975) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover50975 (by decide)
  decide +kernel

theorem c50975_2 : rowSum f50975 1023 1 = 691332 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 50975) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover50975 (by decide)
  decide +kernel

theorem sum50975 : rowSum f50975 0 1024 = 53246300 :=
  rowSum_append (F := f50975) (lo := 0) (n := 459) (m := 565) (A := 8327134) (B := 44919166) c50975_0 (rowSum_append (F := f50975) (lo := 459) (n := 564) (m := 1) (A := 44227834) (B := 691332) c50975_1 (c50975_2))

theorem h50975 : P.leaf 34 50975 = 53246300 :=
  leaf_weighted (k := 24) (d := 10) (H := 50975) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 50975) (by decide) (by decide +kernel)) sum50975

theorem h8115 : P.leaf 34 8115 = 53246300 :=
  orient5 (v := 50975) (by decide) (by decide +kernel) h50975

theorem cover20390 : P.CoversSplit 24 10 20390 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000008888000088880000880000008800000088880000000000008800000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 915, 1202, 1259, 1601]) (by decide +kernel)

theorem c20390_0 : P.sumLeaves 24 20879360 1024 = 7236191 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20390) (lo := 0) (len := 1024) (W := 7236191) check rows elimOK (by decide) (by decide) cover20390 (by decide)
  decide +kernel

theorem h20390 : P.leaf 34 20390 = 7236191 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7236191)]) (.cons c20390_0 (.nil)) (by decide) (by decide))

theorem h8116 : P.leaf 34 8116 = 7236191 :=
  orient4 (v := 20390) (by decide) (by decide +kernel) h20390

theorem cover50991 : P.CoversSplit 24 10 50991 0xfffffffffa000000fffffffffa00000088888c8c0000000088888c8c00000000ffccffccfa000000330033003200000088888c8c000000000000000000000000888888888800000088aa88aa88000000888888880000000088888889000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 860, 872, 916, 1202, 1601]) (by decide +kernel)

theorem c50991_0 : P.sumLeaves 24 52214784 811 = 13323769 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 50991) (lo := 0) (len := 811) (W := 13323769) check rows elimOK (by decide) (by decide) cover50991 (by decide)
  decide +kernel

theorem c50991_1 : P.sumLeaves 24 52215595 213 = 35900422 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 50991) (lo := 811) (len := 213) (W := 35900422) check rows elimOK (by decide) (by decide) cover50991 (by decide)
  decide +kernel

theorem h50991 : P.leaf 34 50991 = 49224191 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(811, 13323769), (213, 35900422)]) (.cons c50991_0 (.cons c50991_1 (.nil))) (by decide) (by decide))

theorem h8117 : P.leaf 34 8117 = 49224191 :=
  orient5 (v := 50991) (by decide) (by decide +kernel) h50991

def seg : List (ℕ × ℕ) := [(8060, 24), (8061, 24), (8062, 24), (8063, 24), (8115, 12), (8116, 48), (8117, 48)]

theorem segOK : checkSeg 16 perms 8060 8118 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8060 8118 204 22907369688 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 22907369688)
    (SegSum.cons (w := 24) h8060 (SegSum.cons (w := 24) h8061 (SegSum.cons (w := 24) h8062 (SegSum.cons (w := 24) h8063 (SegSum.cons (w := 12) h8115 (SegSum.cons (w := 48) h8116 (SegSum.cons (w := 48) h8117 (show SegSum (P.leaf 34) [] 0 from rfl)))))))) (by decide)

end RACert.S4N1.C0.S49
