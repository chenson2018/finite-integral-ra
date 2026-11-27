/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S43

open RACert RACert.Problem

theorem cover77167 : P.CoversSplit 26 10 77167 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77167_0 : P.sumLeaves 26 79019008 1024 = 287230 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77167) (lo := 0) (len := 1024) (W := 287230) check rows elimOK (by decide) (by decide) cover77167 (by decide)
  decide +kernel

theorem h77167 : P.leaf 36 77167 = 287230 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 287230)]) (.cons c77167_0 (.nil)) (by decide) (by decide))

theorem cover77182 : P.CoversSplit 26 10 77182 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77182_0 : P.sumLeaves 26 79034368 1024 = 371608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77182) (lo := 0) (len := 1024) (W := 371608) check rows elimOK (by decide) (by decide) cover77182 (by decide)
  decide +kernel

theorem h77182 : P.leaf 36 77182 = 371608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 371608)]) (.cons c77182_0 (.nil)) (by decide) (by decide))

theorem cover77183 : P.CoversSplit 26 10 77183 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77183_0 : P.sumLeaves 26 79035392 1024 = 1827836 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77183) (lo := 0) (len := 1024) (W := 1827836) check rows elimOK (by decide) (by decide) cover77183 (by decide)
  decide +kernel

theorem h77183 : P.leaf 36 77183 = 1827836 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1827836)]) (.cons c77183_0 (.nil)) (by decide) (by decide))

theorem cover77292 : P.CoversSplit 26 10 77292 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 874, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77292_0 : P.sumLeaves 26 79147008 1024 = 125498 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77292) (lo := 0) (len := 1024) (W := 125498) check rows elimOK (by decide) (by decide) cover77292 (by decide)
  decide +kernel

theorem h77292 : P.leaf 36 77292 = 125498 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 125498)]) (.cons c77292_0 (.nil)) (by decide) (by decide))

theorem cover77293 : P.CoversSplit 26 10 77293 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 874, 881, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77293_0 : P.sumLeaves 26 79148032 1024 = 315830 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77293) (lo := 0) (len := 1024) (W := 315830) check rows elimOK (by decide) (by decide) cover77293 (by decide)
  decide +kernel

theorem h77293 : P.leaf 36 77293 = 315830 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 315830)]) (.cons c77293_0 (.nil)) (by decide) (by decide))

theorem cover77295 : P.CoversSplit 26 10 77295 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 874, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77295_0 : P.sumLeaves 26 79150080 1024 = 1234078 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77295) (lo := 0) (len := 1024) (W := 1234078) check rows elimOK (by decide) (by decide) cover77295 (by decide)
  decide +kernel

theorem h77295 : P.leaf 36 77295 = 1234078 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1234078)]) (.cons c77295_0 (.nil)) (by decide) (by decide))

theorem cover77311 : P.CoversSplit 26 10 77311 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 874, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77311_0 : P.sumLeaves 26 79166464 1024 = 6888880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77311) (lo := 0) (len := 1024) (W := 6888880) check rows elimOK (by decide) (by decide) cover77311 (by decide)
  decide +kernel

theorem h77311 : P.leaf 36 77311 = 6888880 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6888880)]) (.cons c77311_0 (.nil)) (by decide) (by decide))

theorem cover77640 : P.CoversSplit 26 10 77640 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000005555555555555555555555555555555555555555555055005555555555005500a0a00000a0a000000000000000000000a0a00000a000000000000000000000005555555555555555555555555555555555555555550055005555555555005500 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 881, 972, 979, 1322, 1665]) (by decide +kernel)

theorem c77640_0 : P.sumLeaves 26 79503360 224 = 286256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77640) (lo := 0) (len := 224) (W := 286256) check rows elimOK (by decide) (by decide) cover77640 (by decide)
  decide +kernel

theorem c77640_1 : P.sumLeaves 26 79503584 448 = 439116 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77640) (lo := 224) (len := 448) (W := 439116) check rows elimOK (by decide) (by decide) cover77640 (by decide)
  decide +kernel

theorem c77640_2 : P.sumLeaves 26 79504032 352 = 1351961 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77640) (lo := 672) (len := 352) (W := 1351961) check rows elimOK (by decide) (by decide) cover77640 (by decide)
  decide +kernel

theorem h77640 : P.leaf 36 77640 = 2077333 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(224, 286256), (448, 439116), (352, 1351961)]) (.cons c77640_0 (.cons c77640_1 (.cons c77640_2 (.nil)))) (by decide) (by decide))

theorem cover77641 : P.CoversSplit 26 10 77641 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 530, 579, 881, 930, 972]) (by decide +kernel)

theorem c77641_0 : P.sumLeaves 26 79504384 1024 = 91136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77641) (lo := 0) (len := 1024) (W := 91136) check rows elimOK (by decide) (by decide) cover77641 (by decide)
  decide +kernel

theorem h77641 : P.leaf 36 77641 = 91136 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 91136)]) (.cons c77641_0 (.nil)) (by decide) (by decide))

theorem cover77643 : P.CoversSplit 26 10 77643 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 523, 530, 579, 881, 972, 979]) (by decide +kernel)

theorem c77643_0 : P.sumLeaves 26 79506432 1024 = 853040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77643) (lo := 0) (len := 1024) (W := 853040) check rows elimOK (by decide) (by decide) cover77643 (by decide)
  decide +kernel

theorem h77643 : P.leaf 36 77643 = 853040 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 853040)]) (.cons c77643_0 (.nil)) (by decide) (by decide))

theorem cover77647 : P.CoversSplit 26 10 77647 0xfffa0000fffa55500000000000000000fffa0000fff8550055500000550055005050505050505050505050505050505050505050505050005050505050005000fffa0000fffa55500000000000000000fffa0000ff00550055500000550055005050505050505050505050505050505050505050500050005050505050005000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 881, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77647_0 : P.sumLeaves 26 79510528 452 = 2303810 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77647) (lo := 0) (len := 452) (W := 2303810) check rows elimOK (by decide) (by decide) cover77647 (by decide)
  decide +kernel

theorem c77647_1 : P.sumLeaves 26 79510980 340 = 2769799 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77647) (lo := 452) (len := 340) (W := 2769799) check rows elimOK (by decide) (by decide) cover77647 (by decide)
  decide +kernel

theorem c77647_2 : P.sumLeaves 26 79511320 232 = 4351064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77647) (lo := 792) (len := 232) (W := 4351064) check rows elimOK (by decide) (by decide) cover77647 (by decide)
  decide +kernel

theorem h77647 : P.leaf 36 77647 = 9424673 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(452, 2303810), (340, 2769799), (232, 4351064)]) (.cons c77647_0 (.cons c77647_1 (.cons c77647_2 (.nil)))) (by decide) (by decide))

theorem cover77659 : P.CoversSplit 26 10 77659 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000500a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000005050000050500000000000000000000050500000500 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 881, 972, 979]) (by decide +kernel)

theorem c77659_0 : P.sumLeaves 26 79522816 1024 = 3847491 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77659) (lo := 0) (len := 1024) (W := 3847491) check rows elimOK (by decide) (by decide) cover77659 (by decide)
  decide +kernel

theorem h77659 : P.leaf 36 77659 = 3847491 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3847491)]) (.cons c77659_0 (.nil)) (by decide) (by decide))

theorem cover77660 : P.CoversSplit 26 10 77660 0xfffa0000fffa55500000000000000000fffa0000fff8550055500000550055000000000000000000000000000000000000000000000000000000000000000000fffa0000fffa55500000000000000000fffa0000ff00550055500000550055000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 880, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77660_0 : P.sumLeaves 26 79523840 855 = 561456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77660) (lo := 0) (len := 855) (W := 561456) check rows elimOK (by decide) (by decide) cover77660 (by decide)
  decide +kernel

theorem c77660_1 : P.sumLeaves 26 79524695 169 = 888928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77660) (lo := 855) (len := 169) (W := 888928) check rows elimOK (by decide) (by decide) cover77660 (by decide)
  decide +kernel

theorem h77660 : P.leaf 36 77660 = 1450384 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(855, 561456), (169, 888928)]) (.cons c77660_0 (.cons c77660_1 (.nil))) (by decide) (by decide))

theorem cover77661 : P.CoversSplit 26 10 77661 0xfffa0000fffa55500000000000000000fffa0000fff8550055500000550055000000000000000000000000000000000000000000000000000000000000000000fffa0000fffa55500000000000000000fffa0000ff00550055500000550055000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 881, 929, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77661_0 : P.sumLeaves 26 79524864 855 = 2448108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77661) (lo := 0) (len := 855) (W := 2448108) check rows elimOK (by decide) (by decide) cover77661 (by decide)
  decide +kernel

theorem c77661_1 : P.sumLeaves 26 79525719 169 = 4026136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77661) (lo := 855) (len := 169) (W := 4026136) check rows elimOK (by decide) (by decide) cover77661 (by decide)
  decide +kernel

theorem h77661 : P.leaf 36 77661 = 6474244 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(855, 2448108), (169, 4026136)]) (.cons c77661_0 (.cons c77661_1 (.nil))) (by decide) (by decide))

theorem cover77663 : P.CoversSplit 26 10 77663 0xfffa0000fffa55500000000000000000fffa0000fff8550055500000550055005050505050505050505050505050505050505050505050005050505050005000fffa0000fffa55500000000000000000fffa0000ff00550055500000550055005050505050505050505050505050505050505050500050005050505050005000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77663_0 : P.sumLeaves 26 79526912 452 = 2873838 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77663) (lo := 0) (len := 452) (W := 2873838) check rows elimOK (by decide) (by decide) cover77663 (by decide)
  decide +kernel

theorem c77663_1 : P.sumLeaves 26 79527364 340 = 6708282 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77663) (lo := 452) (len := 340) (W := 6708282) check rows elimOK (by decide) (by decide) cover77663 (by decide)
  decide +kernel

theorem c77663_2 : P.sumLeaves 26 79527704 232 = 18244244 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77663) (lo := 792) (len := 232) (W := 18244244) check rows elimOK (by decide) (by decide) cover77663 (by decide)
  decide +kernel

theorem h77663 : P.leaf 36 77663 = 27826364 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(452, 2873838), (340, 6708282), (232, 18244244)]) (.cons c77663_0 (.cons c77663_1 (.cons c77663_2 (.nil)))) (by decide) (by decide))

theorem cover77694 : P.CoversSplit 26 10 77694 0xfffafffafffaaaaa0000000000000000fffafffafff8aa8855505550550000000000000000000000000000000000000000000000000000000000000000000000fffafffafffaaaaa0000000000000000fffafffaff00aa0055505550550000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 874, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77694_0 : P.sumLeaves 26 79558656 502 = 5796464 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77694) (lo := 0) (len := 502) (W := 5796464) check rows elimOK (by decide) (by decide) cover77694 (by decide)
  decide +kernel

theorem c77694_1 : P.sumLeaves 26 79559158 493 = 12053304 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77694) (lo := 502) (len := 493) (W := 12053304) check rows elimOK (by decide) (by decide) cover77694 (by decide)
  decide +kernel

theorem c77694_2 : P.sumLeaves 26 79559651 29 = 11042800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77694) (lo := 995) (len := 29) (W := 11042800) check rows elimOK (by decide) (by decide) cover77694 (by decide)
  decide +kernel

theorem h77694 : P.leaf 36 77694 = 28892568 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 5796464), (493, 12053304), (29, 11042800)]) (.cons c77694_0 (.cons c77694_1 (.cons c77694_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(77167, 720), (77182, 360), (77183, 360), (77292, 120), (77293, 360), (77295, 360), (77311, 120), (77640, 15), (77641, 180), (77643, 360), (77647, 120), (77659, 120), (77660, 90), (77661, 360), (77663, 360), (77694, 90)]

theorem segOK : checkSeg 20 perms 77167 77695 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 77167 77695 4095 19424700795 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 19424700795)
    (SegSum.cons (w := 720) h77167 (SegSum.cons (w := 360) h77182 (SegSum.cons (w := 360) h77183 (SegSum.cons (w := 120) h77292 (SegSum.cons (w := 360) h77293 (SegSum.cons (w := 360) h77295 (SegSum.cons (w := 120) h77311 (SegSum.cons (w := 15) h77640 (SegSum.cons (w := 180) h77641 (SegSum.cons (w := 360) h77643 (SegSum.cons (w := 120) h77647 (SegSum.cons (w := 120) h77659 (SegSum.cons (w := 90) h77660 (SegSum.cons (w := 360) h77661 (SegSum.cons (w := 360) h77663 (SegSum.cons (w := 90) h77694 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))) (by decide)

end RACert.S6N0.C0.S43
