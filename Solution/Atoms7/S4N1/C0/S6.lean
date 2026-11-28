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

namespace RACert.S4N1.C0.S6

open RACert RACert.Problem

theorem cover1174 : P.CoversSplit 24 10 1174 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1174 : P.leaf 34 1174 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1174) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1174) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1174 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1175 : P.CoversSplit 24 10 1175 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1175 : P.leaf 34 1175 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1175) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1175) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1175 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1176 : P.leaf 34 1176 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (29, 1, 472), (18, 11, 475), (33, 0, 486), (7, 6, 467), (35, 14, 487), (3, 1, 502), (5, 1, 502), (28, 1, 508), (8, 0, 509), (16, 10, 468), (26, 1, 517), (31, 1, 516), (34, 1, 524), (27, 1, 473), (14, 0, 531), (20, 1, 482), (21, 0, 488), (15, 1, 558), (11, 1, 559), (4, 1, 410), (6, 1, 459), (12, 1, 460), (10, 1, 530)]) (q := 615) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover1177 : P.CoversSplit 24 10 1177 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1177 : P.leaf 34 1177 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1177) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1177) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1177 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1178 : P.leaf 34 1178 = 0 := by
  exact leaf_contract_zero (ss := [(33, 0, 486), (7, 6, 467), (3, 1, 502), (5, 1, 502), (8, 0, 509), (16, 10, 468), (34, 1, 524), (35, 0, 531), (31, 1, 566), (26, 1, 465), (28, 1, 465), (14, 0, 580), (20, 1, 482), (12, 1, 487), (21, 0, 488)]) (q := 615) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover1179 : P.CoversSplit 24 10 1179 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1179 : P.leaf 34 1179 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1179) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1179) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1179 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1180 : P.CoversSplit 24 10 1180 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1180 : P.leaf 34 1180 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1180) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1180) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1180 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1181 : P.CoversSplit 24 10 1181 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1181 : P.leaf 34 1181 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1181) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1181) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1181 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1182 : P.CoversSplit 24 10 1182 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1182 : P.leaf 34 1182 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1182) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1182) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1182 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1183 : P.CoversSplit 24 10 1183 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1183 : P.leaf 34 1183 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1183) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1183) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1183 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1184 : P.CoversSplit 24 10 1184 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1184 : P.leaf 34 1184 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1184) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1184) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1184 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1185 : P.CoversSplit 24 10 1185 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1185 : P.leaf 34 1185 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1185) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1185) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1185 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1186 : P.leaf 34 1186 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 453), (5, 1, 453), (3, 1, 409), (32, 1, 466), (8, 0, 468), (34, 1, 475), (14, 0, 486), (35, 0, 482), (12, 1, 487), (6, 1, 458), (10, 1, 458), (28, 15, 509), (26, 9, 510), (27, 1, 522), (16, 1, 529), (18, 1, 536), (4, 1, 426), (33, 0, 566), (21, 0, 531), (20, 1, 433)]) (q := 608) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover1187 : P.CoversSplit 24 10 1187 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1187 : P.leaf 34 1187 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1187) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1187) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1187 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1188 : P.CoversSplit 24 10 1188 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1188 : P.leaf 34 1188 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1188) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1188) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1188 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1189 : P.CoversSplit 24 10 1189 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1189 : P.leaf 34 1189 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1189) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1189) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1189 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1190 : P.leaf 34 1190 = 0 := by
  exact leaf_contract_zero (ss := [(32, 1, 466), (33, 8, 468), (3, 1, 472), (5, 1, 404), (16, 1, 486), (10, 1, 508), (35, 0, 524), (34, 1, 475), (27, 1, 522), (18, 1, 536), (8, 0, 566), (2, 1, 412), (4, 1, 426), (21, 0, 531), (20, 1, 537), (14, 0, 580), (26, 9, 510), (12, 1, 559), (6, 1, 458), (31, 1, 615), (9, 1, 515), (30, 1, 515), (7, 1, 628), (11, 1, 809), (28, 1, 858), (29, 1, 865), (19, 1, 866), (13, 1, 922)]) (q := 965) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover1191 : P.CoversSplit 24 10 1191 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1191 : P.leaf 34 1191 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1191) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1191) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1191 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1192 : P.CoversSplit 24 10 1192 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1192 : P.leaf 34 1192 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1192) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1192) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1192 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1193 : P.CoversSplit 24 10 1193 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1193 : P.leaf 34 1193 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1193) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1193) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1193 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1194 : P.leaf 34 1194 = 0 := by
  exact leaf_contract_zero (ss := [(32, 1, 466), (3, 1, 472), (33, 14, 486), (10, 1, 508), (16, 1, 468), (35, 0, 524), (18, 1, 536), (14, 0, 566), (6, 1, 460), (12, 1, 460), (34, 1, 487), (27, 1, 522), (11, 1, 818), (29, 1, 865), (30, 19, 866), (21, 0, 874), (20, 1, 880), (19, 1, 908), (26, 1, 515), (28, 1, 858), (2, 1, 409), (15, 1, 509), (31, 1, 517), (13, 1, 922), (8, 0, 923), (5, 1, 419), (7, 1, 628), (9, 1, 678)]) (q := 929) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover1195 : P.CoversSplit 24 10 1195 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1195 : P.leaf 34 1195 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1195) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1195) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1195 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1196 : P.CoversSplit 24 10 1196 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1196 : P.leaf 34 1196 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1196) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1196) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1196 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1197 : P.CoversSplit 24 10 1197 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1197 : P.leaf 34 1197 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1197) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1197) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1197 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1198 : P.leaf 34 1198 = 0 := by
  exact leaf_contract_zero (ss := [(32, 1, 466), (3, 1, 472), (10, 1, 508), (35, 0, 524), (16, 1, 529), (18, 1, 536), (33, 0, 566), (30, 19, 866), (19, 1, 908), (11, 1, 809), (29, 1, 921), (27, 1, 573), (26, 1, 515), (34, 1, 573), (28, 1, 858), (31, 1, 517), (13, 1, 922), (14, 1, 965), (8, 1, 580)]) (q := 1308) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover1199 : P.CoversSplit 24 10 1199 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1199 : P.leaf 34 1199 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1199) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1199) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1199 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1201 : P.CoversSplit 24 10 1201 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem h1201 : P.leaf 34 1201 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1201) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1201) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1201 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1202 : P.leaf 34 1202 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 453), (5, 1, 453), (8, 0, 468), (34, 1, 475), (14, 0, 486), (35, 0, 482), (12, 1, 487), (6, 1, 458), (10, 1, 458), (28, 15, 509), (26, 9, 510), (21, 0, 580), (33, 0, 580), (20, 1, 433), (31, 1, 566)]) (q := 608) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover1203 : P.CoversSplit 24 10 1203 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1203 : P.leaf 34 1203 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1203) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1203) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1203 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1204 : P.CoversSplit 24 10 1204 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem h1204 : P.leaf 34 1204 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1204) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1204) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1204 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1205 : P.CoversSplit 24 10 1205 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem h1205 : P.leaf 34 1205 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1205) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1205) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1205 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1206 : P.CoversSplit 24 10 1206 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1206 : P.leaf 34 1206 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1206) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1206) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1206 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(1174, 48), (1175, 48), (1176, 48), (1177, 48), (1178, 48), (1179, 48), (1180, 48), (1181, 48), (1182, 48), (1183, 48), (1184, 24), (1185, 48), (1186, 48), (1187, 48), (1188, 48), (1189, 48), (1190, 48), (1191, 48), (1192, 48), (1193, 48), (1194, 48), (1195, 48), (1196, 48), (1197, 48), (1198, 48), (1199, 48), (1201, 24), (1202, 48), (1203, 48), (1204, 48), (1205, 48), (1206, 48)]

theorem segOK : checkSeg 16 perms 1174 1207 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1174 1207 1488 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 48) h1174 (SegSum.cons (w := 48) h1175 (SegSum.cons (w := 48) h1176 (SegSum.cons (w := 48) h1177 (SegSum.cons (w := 48) h1178 (SegSum.cons (w := 48) h1179 (SegSum.cons (w := 48) h1180 (SegSum.cons (w := 48) h1181 (SegSum.cons (w := 48) h1182 (SegSum.cons (w := 48) h1183 (SegSum.cons (w := 24) h1184 (SegSum.cons (w := 48) h1185 (SegSum.cons (w := 48) h1186 (SegSum.cons (w := 48) h1187 (SegSum.cons (w := 48) h1188 (SegSum.cons (w := 48) h1189 (SegSum.cons (w := 48) h1190 (SegSum.cons (w := 48) h1191 (SegSum.cons (w := 48) h1192 (SegSum.cons (w := 48) h1193 (SegSum.cons (w := 48) h1194 (SegSum.cons (w := 48) h1195 (SegSum.cons (w := 48) h1196 (SegSum.cons (w := 48) h1197 (SegSum.cons (w := 48) h1198 (SegSum.cons (w := 48) h1199 (SegSum.cons (w := 24) h1201 (SegSum.cons (w := 48) h1202 (SegSum.cons (w := 48) h1203 (SegSum.cons (w := 48) h1204 (SegSum.cons (w := 48) h1205 (SegSum.cons (w := 48) h1206 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S6
