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

namespace RACert.S4N1.C0.S1

open RACert RACert.Problem

theorem cover60 : P.CoversSplit 24 10 60 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h60 : P.leaf 34 60 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 60) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 60) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover60 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover61 : P.CoversSplit 24 10 61 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h61 : P.leaf 34 61 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 61) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 61) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover61 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover62 : P.CoversSplit 24 10 62 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h62 : P.leaf 34 62 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 62) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 62) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover62 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover63 : P.CoversSplit 24 10 63 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h63 : P.leaf 34 63 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 63) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 63) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover63 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover480 : P.CoversSplit 24 10 480 0x8008000000004004000000000000000080080000000040000000000000000000000000001001100120020000100100000000000010011000000000000000000080080000000000000000000000000000000000000000000000000000000000000000000010010000200000001000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 1209, 1217, 1258, 1266, 1609]) (ps := [(2, [467, 474], [467, 474])]) (by decide +kernel)

theorem h480 : P.leaf 34 480 = 91604 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 480) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 480) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 480) (weight := rowWeight keep0 twice0) (xs := [156, 189, 208, 220, 499, 511, 588, 592, 604, 656, 668, 689, 701, 704, 716, 720, 732, 846, 883, 895, 962, 974, 1011, 1023]) check rows elimOK (by decide) (by decide) cover480 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h108 : P.leaf 34 108 = 91604 :=
  orient24 (v := 480) (by decide) (by decide +kernel) h480

theorem cover3169 : P.CoversSplit 24 10 3169 0x800000000000000000000000000000008000000000000000000000000000000000000000000000000033000000330000000000000000000000330000003300008000cc000000cc0000000000000000008000cc000000c80000000000000000000000000000000000003300000033000000000000000000000033000000320000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 572, 858, 865, 1208, 1209, 1217]) (by decide +kernel)

noncomputable def f3169 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (3245056 + i)

theorem c3169_0 : rowSum f3169 0 1024 = 1508403 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3169) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover3169 (by decide)
  decide +kernel

theorem sum3169 : rowSum f3169 0 1024 = 1508403 :=
  c3169_0

theorem h3169 : P.leaf 34 3169 = 1508403 :=
  leaf_weighted (k := 24) (d := 10) (H := 3169) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 3169) (by decide) (by decide +kernel)) sum3169

theorem h109 : P.leaf 34 109 = 1508403 :=
  orient5 (v := 3169) (by decide) (by decide +kernel) h3169

theorem cover110 : P.CoversSplit 24 10 110 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h110 : P.leaf 34 110 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 110) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 110) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover110 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover111 : P.CoversSplit 24 10 111 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h111 : P.leaf 34 111 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 111) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 111) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover111 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover126 : P.CoversSplit 24 10 126 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h126 : P.leaf 34 126 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 126) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 126) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover126 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover127 : P.CoversSplit 24 10 127 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h127 : P.leaf 34 127 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 127) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 127) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover127 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h164 : P.leaf 34 164 = 0 := by
  exact leaf_contract_zero (ss := [(33, 0, 468), (35, 0, 475), (13, 2, 479), (14, 0, 510), (16, 3, 486), (18, 4, 487), (12, 1, 951), (6, 1, 458), (10, 1, 458), (11, 1, 459)]) (q := 958) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover165 : P.CoversSplit 24 10 165 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h165 : P.leaf 34 165 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 165) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 165) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover165 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover167 : P.CoversSplit 24 10 167 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h167 : P.leaf 34 167 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 167) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 167) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover167 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h168 : P.leaf 34 168 = 0 := by
  exact leaf_contract_zero (ss := [(16, 10, 468), (18, 11, 475), (33, 14, 486), (35, 14, 487), (28, 15, 509), (14, 0, 524), (15, 2, 467), (29, 2, 474), (10, 3, 510), (11, 4, 536)]) (q := 880) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover169 : P.CoversSplit 24 10 169 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h169 : P.leaf 34 169 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 169) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 169) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover169 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover171 : P.CoversSplit 24 10 171 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h171 : P.leaf 34 171 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 171) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 171) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover171 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h172 : P.leaf 34 172 = 0 := by
  exact leaf_contract_zero (ss := [(35, 0, 524), (18, 11, 475), (16, 3, 529), (33, 0, 566), (10, 3, 468), (3, 1, 409), (11, 4, 536), (4, 1, 410), (14, 1, 880), (31, 1, 1301), (26, 1, 465), (6, 1, 458), (28, 1, 465), (30, 1, 515), (12, 1, 810), (13, 1, 873)]) (q := 1308) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover173 : P.CoversSplit 24 10 173 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h173 : P.leaf 34 173 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 173) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 173) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover173 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover175 : P.CoversSplit 24 10 175 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h175 : P.leaf 34 175 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 175) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 175) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover175 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover183 : P.CoversSplit 24 10 183 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h183 : P.leaf 34 183 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 183) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 183) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover183 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover184 : P.CoversSplit 24 10 184 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h184 : P.leaf 34 184 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 184) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 184) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover184 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover185 : P.CoversSplit 24 10 185 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h185 : P.leaf 34 185 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 185) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 185) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover185 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover187 : P.CoversSplit 24 10 187 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h187 : P.leaf 34 187 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 187) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 187) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover187 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover188 : P.CoversSplit 24 10 188 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h188 : P.leaf 34 188 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 188) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 188) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover188 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover189 : P.CoversSplit 24 10 189 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h189 : P.leaf 34 189 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 189) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 189) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover189 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover191 : P.CoversSplit 24 10 191 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h191 : P.leaf 34 191 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 191) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 191) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover191 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover204 : P.CoversSplit 24 10 204 0x8000000000000000000000000000000000000000000000000000000000000000000000001001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 516, 522, 523, 536, 566, 573, 858, 859, 865, 915, 1208, 1272]) (by decide +kernel)

theorem h204 : P.leaf 34 204 = 10168 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 204) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 204) (weight := fun _ => 1) (xs := [720, 732, 1023]) check rows elimOK (by decide) (by decide) cover204 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover205 : P.CoversSplit 24 10 205 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h205 : P.leaf 34 205 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 205) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 205) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover205 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover207 : P.CoversSplit 24 10 207 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h207 : P.leaf 34 207 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 207) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 207) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover207 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover220 : P.CoversSplit 24 10 220 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h220 : P.leaf 34 220 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 220) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 220) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover220 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover221 : P.CoversSplit 24 10 221 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h221 : P.leaf 34 221 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 221) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 221) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover221 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover223 : P.CoversSplit 24 10 223 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h223 : P.leaf 34 223 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 223) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 223) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover223 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(60, 48), (61, 48), (62, 48), (63, 48), (108, 12), (109, 12), (110, 24), (111, 24), (126, 12), (127, 12), (164, 8), (165, 24), (167, 24), (168, 24), (169, 48), (171, 24), (172, 24), (173, 48), (175, 24), (183, 8), (184, 24), (185, 48), (187, 24), (188, 24), (189, 48), (191, 24), (204, 24), (205, 48), (207, 24), (220, 24), (221, 48), (223, 24)]

theorem segOK : checkSeg 16 perms 60 236 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 60 236 928 19444116 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 19444116)
    (SegSum.cons (w := 48) h60 (SegSum.cons (w := 48) h61 (SegSum.cons (w := 48) h62 (SegSum.cons (w := 48) h63 (SegSum.cons (w := 12) h108 (SegSum.cons (w := 12) h109 (SegSum.cons (w := 24) h110 (SegSum.cons (w := 24) h111 (SegSum.cons (w := 12) h126 (SegSum.cons (w := 12) h127 (SegSum.cons (w := 8) h164 (SegSum.cons (w := 24) h165 (SegSum.cons (w := 24) h167 (SegSum.cons (w := 24) h168 (SegSum.cons (w := 48) h169 (SegSum.cons (w := 24) h171 (SegSum.cons (w := 24) h172 (SegSum.cons (w := 48) h173 (SegSum.cons (w := 24) h175 (SegSum.cons (w := 8) h183 (SegSum.cons (w := 24) h184 (SegSum.cons (w := 48) h185 (SegSum.cons (w := 24) h187 (SegSum.cons (w := 24) h188 (SegSum.cons (w := 48) h189 (SegSum.cons (w := 24) h191 (SegSum.cons (w := 24) h204 (SegSum.cons (w := 48) h205 (SegSum.cons (w := 24) h207 (SegSum.cons (w := 24) h220 (SegSum.cons (w := 48) h221 (SegSum.cons (w := 24) h223 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S1
