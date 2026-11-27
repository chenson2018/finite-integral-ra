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

namespace RACert.S6N0.C0.S104

open RACert RACert.Problem

theorem cover242687 : P.CoversSplit 26 10 242687 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaffcc8888fffffafafffffafaffffaaaaffffaaaafffffafaffffc8c8ffffaaaaffcc8888fffffffffffffffffffffffffffffafaffccffccccccccccffccaa88cccc8888fffffafafffffafaffffaaaaffffaaaaffccfac8ccccc8c8ffccaa88cccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f242687 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (248511488 + i)

theorem c242687_0 : rowSum f242687 0 275 = 902608464 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242687) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242687 (by decide)
  decide +kernel

theorem c242687_1 : rowSum f242687 275 144 = 1518509388 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242687) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242687 (by decide)
  decide +kernel

theorem c242687_2 : rowSum f242687 419 367 = 1935593800 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242687) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242687 (by decide)
  decide +kernel

theorem c242687_3 : rowSum f242687 786 166 = 1974426483 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242687) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242687 (by decide)
  decide +kernel

theorem c242687_4 : rowSum f242687 952 72 = 507088448 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242687) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242687 (by decide)
  decide +kernel

theorem sum242687 : rowSum f242687 0 1024 = 6838226583 :=
  rowSum_append (F := f242687) (lo := 0) (n := 275) (m := 749) (A := 902608464) (B := 5935618119) c242687_0 (rowSum_append (F := f242687) (lo := 275) (n := 144) (m := 605) (A := 1518509388) (B := 4417108731) c242687_1 (rowSum_append (F := f242687) (lo := 419) (n := 367) (m := 238) (A := 1935593800) (B := 2481514931) c242687_2 (rowSum_append (F := f242687) (lo := 786) (n := 166) (m := 72) (A := 1974426483) (B := 507088448) c242687_3 (c242687_4))))

theorem h242687 : P.leaf 36 242687 = 6838226583 :=
  leaf_weighted (k := 26) (d := 10) (H := 242687) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 242687) (by decide) (by decide +kernel)) sum242687

theorem cover243511 : P.CoversSplit 26 10 243511 0xfffffffffffffffffffffffffffff0f0ffffffffffffccccffffaaaaff008000ffffffffffffffffffffa0a0ffffa0a0ffffffffffffccccffffa0a0ff008000fffffffffffffffffffffffffffff0f0ffffffffcc00cc00ffffaaaacc008000ffffffffffffffffffffa0a0ffffa0a0ffffffffcc00cc00ffffa0a0cc008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f243511 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (249355264 + i)

theorem c243511_0 : rowSum f243511 0 293 = 99347312 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243511) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover243511 (by decide)
  decide +kernel

theorem c243511_1 : rowSum f243511 293 245 = 415066369 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243511) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover243511 (by decide)
  decide +kernel

theorem c243511_2 : rowSum f243511 538 229 = 298608700 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243511) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover243511 (by decide)
  decide +kernel

theorem c243511_3 : rowSum f243511 767 187 = 427412216 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243511) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover243511 (by decide)
  decide +kernel

theorem c243511_4 : rowSum f243511 954 70 = 156598744 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243511) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover243511 (by decide)
  decide +kernel

theorem sum243511 : rowSum f243511 0 1024 = 1397033341 :=
  rowSum_append (F := f243511) (lo := 0) (n := 293) (m := 731) (A := 99347312) (B := 1297686029) c243511_0 (rowSum_append (F := f243511) (lo := 293) (n := 245) (m := 486) (A := 415066369) (B := 882619660) c243511_1 (rowSum_append (F := f243511) (lo := 538) (n := 229) (m := 257) (A := 298608700) (B := 584010960) c243511_2 (rowSum_append (F := f243511) (lo := 767) (n := 187) (m := 70) (A := 427412216) (B := 156598744) c243511_3 (c243511_4))))

theorem h243511 : P.leaf 36 243511 = 1397033341 :=
  leaf_weighted (k := 26) (d := 10) (H := 243511) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 243511) (by decide) (by decide +kernel)) sum243511

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
  leaf_weighted (k := 26) (d := 10) (H := 243519) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 243519) (by decide) (by decide +kernel)) sum243519

theorem cover243558 : P.CoversSplit 26 10 243558 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaff008800fffffffffffffffffafaa0a0fafaa0a0ffffffffffffccccfafaa0a0fa008000fffffffffffffffffffffffffffffafaffccffcccc00cc00ffccaa88cc008800fffffffffffffffffafaa0a0fafaa0a0ffccffcccc00cc00fac8a080c8008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 873, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243558_0 : P.sumLeaves 26 249403392 208 = 8052962 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 0) (len := 208) (W := 8052962) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem c243558_1 : P.sumLeaves 26 249403600 168 = 31087922 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 208) (len := 168) (W := 31087922) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem c243558_2 : P.sumLeaves 26 249403768 100 = 48284170 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 376) (len := 100) (W := 48284170) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem c243558_3 : P.sumLeaves 26 249403868 145 = 79321269 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 476) (len := 145) (W := 79321269) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem c243558_4 : P.sumLeaves 26 249404013 128 = 81655679 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 621) (len := 128) (W := 81655679) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem c243558_5 : P.sumLeaves 26 249404141 134 = 101381704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 749) (len := 134) (W := 101381704) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem c243558_6 : P.sumLeaves 26 249404275 100 = 100397662 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 883) (len := 100) (W := 100397662) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem c243558_7 : P.sumLeaves 26 249404375 41 = 117116828 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 983) (len := 41) (W := 117116828) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem h243558 : P.leaf 36 243558 = 567298196 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(208, 8052962), (168, 31087922), (100, 48284170), (145, 79321269), (128, 81655679), (134, 101381704), (100, 100397662), (41, 117116828)]) (.cons c243558_0 (.cons c243558_1 (.cons c243558_2 (.cons c243558_3 (.cons c243558_4 (.cons c243558_5 (.cons c243558_6 (.cons c243558_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(242687, 72), (243511, 360), (243519, 180), (243558, 120)]

theorem segOK : checkSeg 20 perms 242687 243559 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 242687 243559 732 1595075630496 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1595075630496)
    (SegSum.cons (w := 72) h242687 (SegSum.cons (w := 360) h243511 (SegSum.cons (w := 180) h243519 (SegSum.cons (w := 120) h243558 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S104
