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

theorem c60_0 : P.sumLeaves 24 61440 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 60) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover60 (by decide)
  decide +kernel

theorem h60 : P.leaf 34 60 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c60_0 (.nil)) (by decide) (by decide))

theorem cover61 : P.CoversSplit 24 10 61 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c61_0 : P.sumLeaves 24 62464 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 61) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover61 (by decide)
  decide +kernel

theorem h61 : P.leaf 34 61 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c61_0 (.nil)) (by decide) (by decide))

theorem cover62 : P.CoversSplit 24 10 62 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c62_0 : P.sumLeaves 24 63488 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 62) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover62 (by decide)
  decide +kernel

theorem h62 : P.leaf 34 62 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c62_0 (.nil)) (by decide) (by decide))

theorem cover63 : P.CoversSplit 24 10 63 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c63_0 : P.sumLeaves 24 64512 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 63) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover63 (by decide)
  decide +kernel

theorem h63 : P.leaf 34 63 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c63_0 (.nil)) (by decide) (by decide))

theorem cover108 : P.CoversSplit 24 10 108 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000200000001100000000000000000000002000000011000080008000000044000000000000000000800080000000400000000000000000000000000000000000002000000011000000000000000000000020000000100000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 523, 572, 858, 859, 915, 1208, 1217]) (by decide +kernel)

theorem c108_0 : P.sumLeaves 24 110592 1024 = 91604 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 108) (lo := 0) (len := 1024) (W := 91604) check rows elimOK (by decide) (by decide) cover108 (by decide)
  decide +kernel

theorem h108 : P.leaf 34 108 = 91604 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 91604)]) (.cons c108_0 (.nil)) (by decide) (by decide))

theorem cover109 : P.CoversSplit 24 10 109 0x800000000000000000000000000000008000000000000000000000000000000000000000000000000033000000320000000000000000000000330000003200008000cc000000c80000000000000000008000cc000000c80000000000000000000000000000000000003300000032000000000000000000000033000000320000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 572, 858, 859, 865, 1208, 1209]) (by decide +kernel)

theorem c109_0 : P.sumLeaves 24 111616 1024 = 1508403 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 109) (lo := 0) (len := 1024) (W := 1508403) check rows elimOK (by decide) (by decide) cover109 (by decide)
  decide +kernel

theorem h109 : P.leaf 34 109 = 1508403 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1508403)]) (.cons c109_0 (.nil)) (by decide) (by decide))

theorem cover110 : P.CoversSplit 24 10 110 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c110_0 : P.sumLeaves 24 112640 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 110) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover110 (by decide)
  decide +kernel

theorem h110 : P.leaf 34 110 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c110_0 (.nil)) (by decide) (by decide))

theorem cover111 : P.CoversSplit 24 10 111 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c111_0 : P.sumLeaves 24 113664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 111) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover111 (by decide)
  decide +kernel

theorem h111 : P.leaf 34 111 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c111_0 (.nil)) (by decide) (by decide))

theorem cover126 : P.CoversSplit 24 10 126 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c126_0 : P.sumLeaves 24 129024 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 126) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover126 (by decide)
  decide +kernel

theorem h126 : P.leaf 34 126 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c126_0 (.nil)) (by decide) (by decide))

theorem cover127 : P.CoversSplit 24 10 127 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c127_0 : P.sumLeaves 24 130048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 127) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover127 (by decide)
  decide +kernel

theorem h127 : P.leaf 34 127 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c127_0 (.nil)) (by decide) (by decide))

theorem h164 : P.leaf 34 164 = 0 := by
  exact leaf_contract_zero (ss := [(33, 0, 468), (35, 0, 475), (13, 2, 479), (14, 0, 510), (16, 3, 486), (18, 4, 487), (12, 1, 951), (6, 1, 458), (10, 1, 458), (11, 1, 459)]) (q := 958) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover165 : P.CoversSplit 24 10 165 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c165_0 : P.sumLeaves 24 168960 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 165) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover165 (by decide)
  decide +kernel

theorem h165 : P.leaf 34 165 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c165_0 (.nil)) (by decide) (by decide))

theorem cover167 : P.CoversSplit 24 10 167 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c167_0 : P.sumLeaves 24 171008 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 167) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover167 (by decide)
  decide +kernel

theorem h167 : P.leaf 34 167 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c167_0 (.nil)) (by decide) (by decide))

theorem h168 : P.leaf 34 168 = 0 := by
  exact leaf_contract_zero (ss := [(16, 10, 468), (18, 11, 475), (33, 14, 486), (35, 14, 487), (28, 15, 509), (14, 0, 524), (15, 2, 467), (29, 2, 474), (10, 3, 510), (11, 4, 536)]) (q := 880) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover169 : P.CoversSplit 24 10 169 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c169_0 : P.sumLeaves 24 173056 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 169) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover169 (by decide)
  decide +kernel

theorem h169 : P.leaf 34 169 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c169_0 (.nil)) (by decide) (by decide))

theorem cover171 : P.CoversSplit 24 10 171 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c171_0 : P.sumLeaves 24 175104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 171) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover171 (by decide)
  decide +kernel

theorem h171 : P.leaf 34 171 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c171_0 (.nil)) (by decide) (by decide))

theorem h172 : P.leaf 34 172 = 0 := by
  exact leaf_contract_zero (ss := [(35, 0, 524), (18, 11, 475), (16, 3, 529), (33, 0, 566), (10, 3, 468), (3, 1, 409), (11, 4, 536), (4, 1, 410), (14, 1, 880), (31, 1, 1301), (26, 1, 465), (6, 1, 458), (28, 1, 465), (30, 1, 515), (12, 1, 810), (13, 1, 873)]) (q := 1308) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover173 : P.CoversSplit 24 10 173 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c173_0 : P.sumLeaves 24 177152 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 173) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover173 (by decide)
  decide +kernel

theorem h173 : P.leaf 34 173 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c173_0 (.nil)) (by decide) (by decide))

theorem cover175 : P.CoversSplit 24 10 175 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c175_0 : P.sumLeaves 24 179200 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 175) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover175 (by decide)
  decide +kernel

theorem h175 : P.leaf 34 175 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c175_0 (.nil)) (by decide) (by decide))

theorem cover183 : P.CoversSplit 24 10 183 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c183_0 : P.sumLeaves 24 187392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 183) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover183 (by decide)
  decide +kernel

theorem h183 : P.leaf 34 183 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c183_0 (.nil)) (by decide) (by decide))

theorem cover184 : P.CoversSplit 24 10 184 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c184_0 : P.sumLeaves 24 188416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 184) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover184 (by decide)
  decide +kernel

theorem h184 : P.leaf 34 184 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c184_0 (.nil)) (by decide) (by decide))

theorem cover185 : P.CoversSplit 24 10 185 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c185_0 : P.sumLeaves 24 189440 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 185) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover185 (by decide)
  decide +kernel

theorem h185 : P.leaf 34 185 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c185_0 (.nil)) (by decide) (by decide))

theorem cover187 : P.CoversSplit 24 10 187 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c187_0 : P.sumLeaves 24 191488 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 187) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover187 (by decide)
  decide +kernel

theorem h187 : P.leaf 34 187 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c187_0 (.nil)) (by decide) (by decide))

theorem cover188 : P.CoversSplit 24 10 188 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c188_0 : P.sumLeaves 24 192512 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 188) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover188 (by decide)
  decide +kernel

theorem h188 : P.leaf 34 188 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c188_0 (.nil)) (by decide) (by decide))

theorem cover189 : P.CoversSplit 24 10 189 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c189_0 : P.sumLeaves 24 193536 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 189) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover189 (by decide)
  decide +kernel

theorem h189 : P.leaf 34 189 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c189_0 (.nil)) (by decide) (by decide))

theorem cover191 : P.CoversSplit 24 10 191 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c191_0 : P.sumLeaves 24 195584 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 191) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover191 (by decide)
  decide +kernel

theorem h191 : P.leaf 34 191 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c191_0 (.nil)) (by decide) (by decide))

theorem cover204 : P.CoversSplit 24 10 204 0x8000000000000000000000000000000000000000000000000000000000000000000000001001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 516, 522, 523, 536, 566, 573, 858, 859, 865, 915, 1208, 1272]) (by decide +kernel)

theorem c204_0 : P.sumLeaves 24 208896 1024 = 10168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 204) (lo := 0) (len := 1024) (W := 10168) check rows elimOK (by decide) (by decide) cover204 (by decide)
  decide +kernel

theorem h204 : P.leaf 34 204 = 10168 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10168)]) (.cons c204_0 (.nil)) (by decide) (by decide))

theorem cover205 : P.CoversSplit 24 10 205 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c205_0 : P.sumLeaves 24 209920 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 205) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover205 (by decide)
  decide +kernel

theorem h205 : P.leaf 34 205 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c205_0 (.nil)) (by decide) (by decide))

theorem cover207 : P.CoversSplit 24 10 207 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c207_0 : P.sumLeaves 24 211968 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 207) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover207 (by decide)
  decide +kernel

theorem h207 : P.leaf 34 207 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c207_0 (.nil)) (by decide) (by decide))

theorem cover220 : P.CoversSplit 24 10 220 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c220_0 : P.sumLeaves 24 225280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 220) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover220 (by decide)
  decide +kernel

theorem h220 : P.leaf 34 220 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c220_0 (.nil)) (by decide) (by decide))

theorem cover221 : P.CoversSplit 24 10 221 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c221_0 : P.sumLeaves 24 226304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 221) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover221 (by decide)
  decide +kernel

theorem h221 : P.leaf 34 221 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c221_0 (.nil)) (by decide) (by decide))

theorem cover223 : P.CoversSplit 24 10 223 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c223_0 : P.sumLeaves 24 228352 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 223) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover223 (by decide)
  decide +kernel

theorem h223 : P.leaf 34 223 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c223_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(60, 48), (61, 48), (62, 48), (63, 48), (108, 12), (109, 12), (110, 24), (111, 24), (126, 12), (127, 12), (164, 8), (165, 24), (167, 24), (168, 24), (169, 48), (171, 24), (172, 24), (173, 48), (175, 24), (183, 8), (184, 24), (185, 48), (187, 24), (188, 24), (189, 48), (191, 24), (204, 24), (205, 48), (207, 24), (220, 24), (221, 48), (223, 24)]

theorem segOK : checkSeg 16 perms 60 236 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 60 236 928 19444116 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 19444116)
    (SegSum.cons (w := 48) h60 (SegSum.cons (w := 48) h61 (SegSum.cons (w := 48) h62 (SegSum.cons (w := 48) h63 (SegSum.cons (w := 12) h108 (SegSum.cons (w := 12) h109 (SegSum.cons (w := 24) h110 (SegSum.cons (w := 24) h111 (SegSum.cons (w := 12) h126 (SegSum.cons (w := 12) h127 (SegSum.cons (w := 8) h164 (SegSum.cons (w := 24) h165 (SegSum.cons (w := 24) h167 (SegSum.cons (w := 24) h168 (SegSum.cons (w := 48) h169 (SegSum.cons (w := 24) h171 (SegSum.cons (w := 24) h172 (SegSum.cons (w := 48) h173 (SegSum.cons (w := 24) h175 (SegSum.cons (w := 8) h183 (SegSum.cons (w := 24) h184 (SegSum.cons (w := 48) h185 (SegSum.cons (w := 24) h187 (SegSum.cons (w := 24) h188 (SegSum.cons (w := 48) h189 (SegSum.cons (w := 24) h191 (SegSum.cons (w := 24) h204 (SegSum.cons (w := 48) h205 (SegSum.cons (w := 24) h207 (SegSum.cons (w := 24) h220 (SegSum.cons (w := 48) h221 (SegSum.cons (w := 24) h223 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S1
