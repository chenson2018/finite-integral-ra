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

namespace RACert.S4N1.C0.S55

open RACert RACert.Problem

theorem cover20463 : P.CoversSplit 24 10 20463 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888ffccffccaa88aa88cccccccc88888888ffccffccaa88aa88fffffffffafaaaaa0000000000000000fffffffffafaaaaa00330022003200220000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 1202, 1210, 1259, 1601]) (ps := [(18, [1210], [1264])]) (by decide +kernel)

theorem c20463_0 : P.sumLeaves 24 20954112 493 = 40312001 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20463) (lo := 0) (len := 493) (W := 40312001) check rows elimOK (by decide) (by decide) cover20463 (by decide)
  decide +kernel

theorem c20463_1 : P.sumLeaves 24 20954605 188 = 40514464 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20463) (lo := 493) (len := 188) (W := 40514464) check rows elimOK (by decide) (by decide) cover20463 (by decide)
  decide +kernel

theorem c20463_2 : P.sumLeaves 24 20954793 154 = 45343666 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20463) (lo := 681) (len := 154) (W := 45343666) check rows elimOK (by decide) (by decide) cover20463 (by decide)
  decide +kernel

theorem c20463_3 : P.sumLeaves 24 20954947 118 = 99749605 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20463) (lo := 835) (len := 118) (W := 99749605) check rows elimOK (by decide) (by decide) cover20463 (by decide)
  decide +kernel

theorem c20463_4 : P.sumLeaves 24 20955065 71 = 127428068 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20463) (lo := 953) (len := 71) (W := 127428068) check rows elimOK (by decide) (by decide) cover20463 (by decide)
  decide +kernel

theorem h20463 : P.leaf 34 20463 = 353347804 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(493, 40312001), (188, 40514464), (154, 45343666), (118, 99749605), (71, 127428068)]) (.cons c20463_0 (.cons c20463_1 (.cons c20463_2 (.cons c20463_3 (.cons c20463_4 (.nil)))))) (by decide) (by decide))

theorem h8189 : P.leaf 34 8189 = 353347804 :=
  orient4 (v := 20463) (by decide) (by decide +kernel) h20463

theorem cover8190 : P.CoversSplit 24 10 8190 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaccffccff88888888cccccccc88888888ccffccff88888888cccccccc88888888ffffffffffffaaaaffffffffffffaaaafffffffffafaaaaafffffffffafaaaaaccffccff88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 916, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c8190_0 : P.sumLeaves 24 8386560 244 = 17362465 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8190) (lo := 0) (len := 244) (W := 17362465) check rows elimOK (by decide) (by decide) cover8190 (by decide)
  decide +kernel

theorem c8190_1 : P.sumLeaves 24 8386804 124 = 30537773 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8190) (lo := 244) (len := 124) (W := 30537773) check rows elimOK (by decide) (by decide) cover8190 (by decide)
  decide +kernel

theorem c8190_2 : P.sumLeaves 24 8386928 112 = 55956534 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8190) (lo := 368) (len := 112) (W := 55956534) check rows elimOK (by decide) (by decide) cover8190 (by decide)
  decide +kernel

theorem c8190_3 : P.sumLeaves 24 8387040 194 = 72886051 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8190) (lo := 480) (len := 194) (W := 72886051) check rows elimOK (by decide) (by decide) cover8190 (by decide)
  decide +kernel

theorem c8190_4 : P.sumLeaves 24 8387234 150 = 67715149 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8190) (lo := 674) (len := 150) (W := 67715149) check rows elimOK (by decide) (by decide) cover8190 (by decide)
  decide +kernel

theorem c8190_5 : P.sumLeaves 24 8387384 112 = 106994618 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8190) (lo := 824) (len := 112) (W := 106994618) check rows elimOK (by decide) (by decide) cover8190 (by decide)
  decide +kernel

theorem c8190_6 : P.sumLeaves 24 8387496 88 = 197709768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8190) (lo := 936) (len := 88) (W := 197709768) check rows elimOK (by decide) (by decide) cover8190 (by decide)
  decide +kernel

theorem h8190 : P.leaf 34 8190 = 549162358 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(244, 17362465), (124, 30537773), (112, 55956534), (194, 72886051), (150, 67715149), (112, 106994618), (88, 197709768)]) (.cons c8190_0 (.cons c8190_1 (.cons c8190_2 (.cons c8190_3 (.cons c8190_4 (.cons c8190_5 (.cons c8190_6 (.nil)))))))) (by decide) (by decide))

theorem cover8191 : P.CoversSplit 24 10 8191 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaccffccff88888888cccccccc88888888ccffccff88888888cccccccc88888888ffffffffffffaaaaffffffffffffaaaafffffffffafaaaaafffffffffafaaaaaccffccff88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [916, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c8191_0 : P.sumLeaves 24 8387584 244 = 47131120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8191) (lo := 0) (len := 244) (W := 47131120) check rows elimOK (by decide) (by decide) cover8191 (by decide)
  decide +kernel

theorem c8191_1 : P.sumLeaves 24 8387828 124 = 67251240 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8191) (lo := 244) (len := 124) (W := 67251240) check rows elimOK (by decide) (by decide) cover8191 (by decide)
  decide +kernel

theorem c8191_2 : P.sumLeaves 24 8387952 112 = 103106099 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8191) (lo := 368) (len := 112) (W := 103106099) check rows elimOK (by decide) (by decide) cover8191 (by decide)
  decide +kernel

theorem c8191_3 : P.sumLeaves 24 8388064 194 = 129255639 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8191) (lo := 480) (len := 194) (W := 129255639) check rows elimOK (by decide) (by decide) cover8191 (by decide)
  decide +kernel

theorem c8191_4 : P.sumLeaves 24 8388258 150 = 146371935 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8191) (lo := 674) (len := 150) (W := 146371935) check rows elimOK (by decide) (by decide) cover8191 (by decide)
  decide +kernel

theorem c8191_5 : P.sumLeaves 24 8388408 112 = 203857960 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8191) (lo := 824) (len := 112) (W := 203857960) check rows elimOK (by decide) (by decide) cover8191 (by decide)
  decide +kernel

theorem c8191_6 : P.sumLeaves 24 8388520 88 = 285450849 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8191) (lo := 936) (len := 88) (W := 285450849) check rows elimOK (by decide) (by decide) cover8191 (by decide)
  decide +kernel

theorem h8191 : P.leaf 34 8191 = 982424842 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(244, 47131120), (124, 67251240), (112, 103106099), (194, 129255639), (150, 146371935), (112, 203857960), (88, 285450849)]) (.cons c8191_0 (.cons c8191_1 (.cons c8191_2 (.cons c8191_3 (.cons c8191_4 (.cons c8191_5 (.cons c8191_6 (.nil)))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(8189, 48), (8190, 48), (8191, 48)]

theorem segOK : checkSeg 16 perms 8189 15840 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8189 15840 144 90476880192 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 90476880192)
    (SegSum.cons (w := 48) h8189 (SegSum.cons (w := 48) h8190 (SegSum.cons (w := 48) h8191 (show SegSum (P.leaf 34) [] 0 from rfl)))) (by decide)

end RACert.S4N1.C0.S55
