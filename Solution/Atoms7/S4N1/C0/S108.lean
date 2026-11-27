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

namespace RACert.S4N1.C0.S108

open RACert RACert.Problem

theorem cover32252 : P.CoversSplit 24 10 32252 0xfffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0ffc0ffc0fac0f0c0ff00ff00fa00f000ffc0ffc0fac0f0c0ff00ff00fa00f000fffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0ffc0ffc0fac0f0c0ff00ff00fa00f000ffc0ffc0fac0f0c0ff00ff00fa00f000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 865]) (by decide +kernel)

noncomputable def f32252 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (33026048 + i)

theorem c32252_0 : rowSum f32252 0 236 = 38288893 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32252) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32252 (by decide)
  decide +kernel

theorem c32252_1 : rowSum f32252 236 208 = 102820545 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32252) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32252 (by decide)
  decide +kernel

theorem c32252_2 : rowSum f32252 444 316 = 172069203 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32252) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32252 (by decide)
  decide +kernel

theorem c32252_3 : rowSum f32252 760 264 = 157044253 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32252) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32252 (by decide)
  decide +kernel

theorem sum32252 : rowSum f32252 0 1024 = 470222894 :=
  rowSum_append (F := f32252) (lo := 0) (n := 236) (m := 788) (A := 38288893) (B := 431934001) c32252_0 (rowSum_append (F := f32252) (lo := 236) (n := 208) (m := 580) (A := 102820545) (B := 329113456) c32252_1 (rowSum_append (F := f32252) (lo := 444) (n := 316) (m := 264) (A := 172069203) (B := 157044253) c32252_2 (c32252_3)))

theorem h32252 : P.leaf 34 32252 = 470222894 :=
  leaf_weighted (k := 24) (d := 10) (H := 32252) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 32252) (by decide) (by decide +kernel)) sum32252

theorem cover32253 : P.CoversSplit 24 10 32253 0xfffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0ffccffccfac0f0c0ffccffccfac0f0c0ffccffccfac0f0c0ffccffccfac0f0c0fffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0ffccffccfac0f0c0ffccffccfac0f0c0ffccffccfac0f0c0ffccffccfac0f0c0 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 858, 865, 1202, 1259, 1601]) (by decide +kernel)

theorem c32253_0 : P.sumLeaves 24 33027072 170 = 32175079 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32253) (lo := 0) (len := 170) (W := 32175079) check rows elimOK (by decide) (by decide) cover32253 (by decide)
  decide +kernel

theorem c32253_1 : P.sumLeaves 24 33027242 140 = 64327735 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32253) (lo := 170) (len := 140) (W := 64327735) check rows elimOK (by decide) (by decide) cover32253 (by decide)
  decide +kernel

theorem c32253_2 : P.sumLeaves 24 33027382 124 = 77863970 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32253) (lo := 310) (len := 124) (W := 77863970) check rows elimOK (by decide) (by decide) cover32253 (by decide)
  decide +kernel

theorem c32253_3 : P.sumLeaves 24 33027506 136 = 116889697 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32253) (lo := 434) (len := 136) (W := 116889697) check rows elimOK (by decide) (by decide) cover32253 (by decide)
  decide +kernel

theorem c32253_4 : P.sumLeaves 24 33027642 168 = 126410594 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32253) (lo := 570) (len := 168) (W := 126410594) check rows elimOK (by decide) (by decide) cover32253 (by decide)
  decide +kernel

theorem c32253_5 : P.sumLeaves 24 33027810 130 = 139687465 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32253) (lo := 738) (len := 130) (W := 139687465) check rows elimOK (by decide) (by decide) cover32253 (by decide)
  decide +kernel

theorem c32253_6 : P.sumLeaves 24 33027940 124 = 195916882 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32253) (lo := 868) (len := 124) (W := 195916882) check rows elimOK (by decide) (by decide) cover32253 (by decide)
  decide +kernel

theorem c32253_7 : P.sumLeaves 24 33028064 32 = 109142388 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32253) (lo := 992) (len := 32) (W := 109142388) check rows elimOK (by decide) (by decide) cover32253 (by decide)
  decide +kernel

theorem h32253 : P.leaf 34 32253 = 862413810 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(170, 32175079), (140, 64327735), (124, 77863970), (136, 116889697), (168, 126410594), (130, 139687465), (124, 195916882), (32, 109142388)]) (.cons c32253_0 (.cons c32253_1 (.cons c32253_2 (.cons c32253_3 (.cons c32253_4 (.cons c32253_5 (.cons c32253_6 (.cons c32253_7 (.nil))))))))) (by decide) (by decide))

theorem cover32255 : P.CoversSplit 24 10 32255 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1202, 1259, 1601]) (by decide +kernel)

noncomputable def f32255 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (33029120 + i)

theorem c32255_0 : rowSum f32255 0 173 = 163792303 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32255) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32255 (by decide)
  decide +kernel

theorem c32255_1 : rowSum f32255 173 216 = 305605095 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32255) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32255 (by decide)
  decide +kernel

theorem c32255_2 : rowSum f32255 389 110 = 421744422 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32255) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32255 (by decide)
  decide +kernel

theorem c32255_3 : rowSum f32255 499 449 = 563974393 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32255) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32255 (by decide)
  decide +kernel

theorem c32255_4 : rowSum f32255 948 76 = 210472880 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32255) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32255 (by decide)
  decide +kernel

theorem sum32255 : rowSum f32255 0 1024 = 1665589093 :=
  rowSum_append (F := f32255) (lo := 0) (n := 173) (m := 851) (A := 163792303) (B := 1501796790) c32255_0 (rowSum_append (F := f32255) (lo := 173) (n := 216) (m := 635) (A := 305605095) (B := 1196191695) c32255_1 (rowSum_append (F := f32255) (lo := 389) (n := 110) (m := 525) (A := 421744422) (B := 774447273) c32255_2 (rowSum_append (F := f32255) (lo := 499) (n := 449) (m := 76) (A := 563974393) (B := 210472880) c32255_3 (c32255_4))))

theorem h32255 : P.leaf 34 32255 = 1665589093 :=
  leaf_weighted (k := 24) (d := 10) (H := 32255) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 32255) (by decide) (by decide +kernel)) sum32255

def seg : List (ℕ × ℕ) := [(32252, 24), (32253, 48), (32255, 24)]

theorem segOK : checkSeg 16 perms 32252 32759 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 32252 32759 96 92655350568 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 92655350568)
    (SegSum.cons (w := 24) h32252 (SegSum.cons (w := 48) h32253 (SegSum.cons (w := 24) h32255 (show SegSum (P.leaf 34) [] 0 from rfl)))) (by decide)

end RACert.S4N1.C0.S108
