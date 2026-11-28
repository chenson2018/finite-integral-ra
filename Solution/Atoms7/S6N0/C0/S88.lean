/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S88

open RACert RACert.Problem

theorem cover243519 : P.CoversSplit 26 10 243519 0xfffffffffffffffffffffffffffff0f0ffffffffffffccccffffaaaaff008000ffffffffffffffffffffa0a0ffffa0a0ffffffffffffccccffffa0a0ff008000fffffffffffffffffffffffffffff0f0ffffffffcc00cc00ffffaaaacc008000ffffffffffffffffffffa0a0ffffa0a0ffffffffcc00cc00ffffa0a0cc008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f243519 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (249363456 + i)

theorem c243519_0 : rowSum f243519 0 289 = 352307018 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243519) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243519 (by decide)
  decide +kernel

theorem c243519_1 : rowSum f243519 289 135 = 591365474 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243519) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243519 (by decide)
  decide +kernel

theorem c243519_2 : rowSum f243519 424 375 = 970103498 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243519) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243519 (by decide)
  decide +kernel

theorem c243519_3 : rowSum f243519 799 213 = 909014518 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243519) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243519 (by decide)
  decide +kernel

theorem c243519_4 : rowSum f243519 1012 12 = 131184660 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243519) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243519 (by decide)
  decide +kernel

theorem sum243519 : rowSum f243519 0 1024 = 2953975168 :=
  rowSum_append (F := f243519) (lo := 0) (n := 289) (m := 735) (A := 352307018) (B := 2601668150) c243519_0 (rowSum_append (F := f243519) (lo := 289) (n := 135) (m := 600) (A := 591365474) (B := 2010302676) c243519_1 (rowSum_append (F := f243519) (lo := 424) (n := 375) (m := 225) (A := 970103498) (B := 1040199178) c243519_2 (rowSum_append (F := f243519) (lo := 799) (n := 213) (m := 12) (A := 909014518) (B := 131184660) c243519_3 (c243519_4))))

theorem h243519 : P.leaf 36 243519 = 2953975168 :=
  leaf_weighted (k := 26) (d := 10) (H := 243519) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 243519) (by decide) (by decide +kernel)) sum243519

theorem cover359321 : P.CoversSplit 26 10 359321 0xffffffffaaaaaaaafffffafaaaaaaaaaffffffffaa80aa80fafafafaaa80aa80fffffafaaaaaaaaafafafafaaaaaaaaafffffafaaa80aa80fafafafaaa80aa80ffffffffaaaaaaaafffffafaaaaaaaaaffffffff88008800fafafafa880088000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 923, 979, 1273, 1658]) (by decide +kernel)

noncomputable def f359321 (i : ℕ) := rowWeight keep14 twice14 i * P.leaf 26 (367944704 + i)

theorem c359321_0 : rowSum f359321 0 436 = 116895720 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359321) (keep := keep14) (twice := twice14) check rows elimOK (by decide) (by decide) cover359321 (by decide)
  decide +kernel

theorem c359321_1 : rowSum f359321 436 409 = 251463704 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359321) (keep := keep14) (twice := twice14) check rows elimOK (by decide) (by decide) cover359321 (by decide)
  decide +kernel

theorem c359321_2 : rowSum f359321 845 179 = 198938772 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359321) (keep := keep14) (twice := twice14) check rows elimOK (by decide) (by decide) cover359321 (by decide)
  decide +kernel

theorem sum359321 : rowSum f359321 0 1024 = 567298196 :=
  rowSum_append (F := f359321) (lo := 0) (n := 436) (m := 588) (A := 116895720) (B := 450402476) c359321_0 (rowSum_append (F := f359321) (lo := 436) (n := 409) (m := 179) (A := 251463704) (B := 198938772) c359321_1 (c359321_2))

theorem h359321 : P.leaf 36 359321 = 567298196 :=
  leaf_weighted (k := 26) (d := 10) (H := 359321) (keep := keep14) (twice := twice14) rows (by decide) (by decide) (bal14) (invRow14 (H := 359321) (by decide) (by decide +kernel)) sum359321

theorem h243558 : P.leaf 36 243558 = 567298196 :=
  orient74 (v := 359321) (by decide) (by decide +kernel) h359321

theorem cover359325 : P.CoversSplit 26 10 359325 0xfffffffffffffffffffffafafffffafaffffffffffccffccfafafafafac8fac8fffffffffffffffffafafafafafafafaffffffffffccffccfafafafafac8fac8fffffffffffffffffffffafafffffafaffffffffccccccccfafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 923, 1273, 1658]) (by decide +kernel)

theorem c359325_0 : P.sumLeaves 26 367948800 400 = 90760644 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359325) (lo := 0) (len := 400) (W := 90760644) check rows elimOK (by decide) (by decide) cover359325 (by decide)
  decide +kernel

theorem c359325_1 : P.sumLeaves 26 367949200 100 = 203577199 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359325) (lo := 400) (len := 100) (W := 203577199) check rows elimOK (by decide) (by decide) cover359325 (by decide)
  decide +kernel

theorem c359325_2 : P.sumLeaves 26 367949300 126 = 144881103 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359325) (lo := 500) (len := 126) (W := 144881103) check rows elimOK (by decide) (by decide) cover359325 (by decide)
  decide +kernel

theorem c359325_3 : P.sumLeaves 26 367949426 112 = 184119676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359325) (lo := 626) (len := 112) (W := 184119676) check rows elimOK (by decide) (by decide) cover359325 (by decide)
  decide +kernel

theorem c359325_4 : P.sumLeaves 26 367949538 126 = 216370349 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359325) (lo := 738) (len := 126) (W := 216370349) check rows elimOK (by decide) (by decide) cover359325 (by decide)
  decide +kernel

theorem c359325_5 : P.sumLeaves 26 367949664 104 = 294271136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359325) (lo := 864) (len := 104) (W := 294271136) check rows elimOK (by decide) (by decide) cover359325 (by decide)
  decide +kernel

theorem c359325_6 : P.sumLeaves 26 367949768 56 = 297091888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359325) (lo := 968) (len := 56) (W := 297091888) check rows elimOK (by decide) (by decide) cover359325 (by decide)
  decide +kernel

theorem h359325 : P.leaf 36 359325 = 1431071995 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(400, 90760644), (100, 203577199), (126, 144881103), (112, 184119676), (126, 216370349), (104, 294271136), (56, 297091888)]) (.cons c359325_0 (.cons c359325_1 (.cons c359325_2 (.cons c359325_3 (.cons c359325_4 (.cons c359325_5 (.cons c359325_6 (.nil)))))))) (by decide) (by decide))

theorem h243559 : P.leaf 36 243559 = 1431071995 :=
  orient74 (v := 359325) (by decide) (by decide +kernel) h359325

theorem cover621306 : P.CoversSplit 26 10 621306 0xfffffffffffffafafffffffafffffafafffffffffff0fac0fffffffafff0fac0fffffafafffffafafafafafafafafafafffffafafff0fac0fafafafafaf0fac0fffffffffffffafafffffffafffffafaffffffffcc00c800fffffffacc00c8000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem c621306_0 : P.sumLeaves 26 636217344 408 = 113026359 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 621306) (lo := 0) (len := 408) (W := 113026359) check rows elimOK (by decide) (by decide) cover621306 (by decide)
  decide +kernel

theorem c621306_1 : P.sumLeaves 26 636217752 102 = 232063171 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 621306) (lo := 408) (len := 102) (W := 232063171) check rows elimOK (by decide) (by decide) cover621306 (by decide)
  decide +kernel

theorem c621306_2 : P.sumLeaves 26 636217854 136 = 105570325 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 621306) (lo := 510) (len := 136) (W := 105570325) check rows elimOK (by decide) (by decide) cover621306 (by decide)
  decide +kernel

theorem c621306_3 : P.sumLeaves 26 636217990 118 = 158187863 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 621306) (lo := 646) (len := 118) (W := 158187863) check rows elimOK (by decide) (by decide) cover621306 (by decide)
  decide +kernel

theorem c621306_4 : P.sumLeaves 26 636218108 122 = 174903206 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 621306) (lo := 764) (len := 122) (W := 174903206) check rows elimOK (by decide) (by decide) cover621306 (by decide)
  decide +kernel

theorem c621306_5 : P.sumLeaves 26 636218230 106 = 285315965 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 621306) (lo := 886) (len := 106) (W := 285315965) check rows elimOK (by decide) (by decide) cover621306 (by decide)
  decide +kernel

theorem c621306_6 : P.sumLeaves 26 636218336 32 = 140069470 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 621306) (lo := 992) (len := 32) (W := 140069470) check rows elimOK (by decide) (by decide) cover621306 (by decide)
  decide +kernel

theorem h621306 : P.leaf 36 621306 = 1209136359 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(408, 113026359), (102, 232063171), (136, 105570325), (118, 158187863), (122, 174903206), (106, 285315965), (32, 140069470)]) (.cons c621306_0 (.cons c621306_1 (.cons c621306_2 (.cons c621306_3 (.cons c621306_4 (.cons c621306_5 (.cons c621306_6 (.nil)))))))) (by decide) (by decide))

theorem h243566 : P.leaf 36 243566 = 1209136359 :=
  orient93 (v := 621306) (by decide) (by decide +kernel) h621306

def seg : List (ℕ × ℕ) := [(243519, 180), (243558, 120), (243559, 240), (243566, 720)]

theorem segOK : checkSeg 20 perms 243519 243567 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243519 243567 1260 1813826771040 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1813826771040)
    (SegSum.cons (w := 180) h243519 (SegSum.cons (w := 120) h243558 (SegSum.cons (w := 240) h243559 (SegSum.cons (w := 720) h243566 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S88
