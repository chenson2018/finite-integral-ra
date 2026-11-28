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

namespace RACert.S4N1.C0.S89

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
  leaf_weighted (k := 24) (d := 10) (H := 32252) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 32252) (by decide) (by decide +kernel)) sum32252

theorem cover60926 : P.CoversSplit 24 10 60926 0xfffffffffffafafafffffffffffafafafffffffffffafafafffffffffffafafafff0fff0fff0faf0cc00cc00cc00c800fff0fff0fff0faf0cc00cc00cc00c800fffffffffffafafafffffffffffafafafffffffffafafafafffffffffafafafafff0fff0fff0faf0cc00cc00cc00c800ffc0ffc0fac0fac0cc00cc00c800c800 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 865, 1217, 1601, 1609]) (by decide +kernel)

theorem c60926_0 : P.sumLeaves 24 62388224 237 = 47501719 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 60926) (lo := 0) (len := 237) (W := 47501719) check rows elimOK (by decide) (by decide) cover60926 (by decide)
  decide +kernel

theorem c60926_1 : P.sumLeaves 24 62388461 116 = 61541561 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 60926) (lo := 237) (len := 116) (W := 61541561) check rows elimOK (by decide) (by decide) cover60926 (by decide)
  decide +kernel

theorem c60926_2 : P.sumLeaves 24 62388577 106 = 97971420 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 60926) (lo := 353) (len := 106) (W := 97971420) check rows elimOK (by decide) (by decide) cover60926 (by decide)
  decide +kernel

theorem c60926_3 : P.sumLeaves 24 62388683 161 = 110375421 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 60926) (lo := 459) (len := 161) (W := 110375421) check rows elimOK (by decide) (by decide) cover60926 (by decide)
  decide +kernel

theorem c60926_4 : P.sumLeaves 24 62388844 173 = 132939717 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 60926) (lo := 620) (len := 173) (W := 132939717) check rows elimOK (by decide) (by decide) cover60926 (by decide)
  decide +kernel

theorem c60926_5 : P.sumLeaves 24 62389017 102 = 147619217 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 60926) (lo := 793) (len := 102) (W := 147619217) check rows elimOK (by decide) (by decide) cover60926 (by decide)
  decide +kernel

theorem c60926_6 : P.sumLeaves 24 62389119 108 = 198855805 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 60926) (lo := 895) (len := 108) (W := 198855805) check rows elimOK (by decide) (by decide) cover60926 (by decide)
  decide +kernel

theorem c60926_7 : P.sumLeaves 24 62389227 21 = 65608950 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 60926) (lo := 1003) (len := 21) (W := 65608950) check rows elimOK (by decide) (by decide) cover60926 (by decide)
  decide +kernel

theorem h60926 : P.leaf 34 60926 = 862413810 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(237, 47501719), (116, 61541561), (106, 97971420), (161, 110375421), (173, 132939717), (102, 147619217), (108, 198855805), (21, 65608950)]) (.cons c60926_0 (.cons c60926_1 (.cons c60926_2 (.cons c60926_3 (.cons c60926_4 (.cons c60926_5 (.cons c60926_6 (.cons c60926_7 (.nil))))))))) (by decide) (by decide))

theorem h32253 : P.leaf 34 32253 = 862413810 :=
  orient24 (v := 60926) (by decide) (by decide +kernel) h60926

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
  leaf_weighted (k := 24) (d := 10) (H := 32255) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 32255) (by decide) (by decide +kernel)) sum32255

def seg : List (ℕ × ℕ) := [(32252, 24), (32253, 48), (32255, 24)]

theorem segOK : checkSeg 16 perms 32252 32759 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 32252 32759 96 92655350568 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 92655350568)
    (SegSum.cons (w := 24) h32252 (SegSum.cons (w := 48) h32253 (SegSum.cons (w := 24) h32255 (show SegSum (P.leaf 34) [] 0 from rfl)))) (by decide)

end RACert.S4N1.C0.S89
