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

namespace RACert.S6N0.C0.S76

open RACert RACert.Problem

theorem cover831453 : P.CoversSplit 26 10 831453 0xfffffffffffffffffffffafafffffafaffff0000ffcc0000ffff0000ffcc0000fffffffffffffffffffffafafffffafaffff0000ffcc0000ffff0000ffcc0000fffffffffffffffffffffafafffffafaffff0000ff000000ffff0000ff000000fffffffffffffffffffffafafffffafaffff0000ff000000ffff0000ff000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 881, 930, 1265, 1272, 1273]) (by decide +kernel)

theorem c831453_0 : P.sumLeaves 26 851407872 184 = 214805915 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831453) (lo := 0) (len := 184) (W := 214805915) check rows elimOK (by decide) (by decide) cover831453 (by decide)
  decide +kernel

theorem c831453_1 : P.sumLeaves 26 851408056 160 = 321381401 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831453) (lo := 184) (len := 160) (W := 321381401) check rows elimOK (by decide) (by decide) cover831453 (by decide)
  decide +kernel

theorem c831453_2 : P.sumLeaves 26 851408216 120 = 280327537 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831453) (lo := 344) (len := 120) (W := 280327537) check rows elimOK (by decide) (by decide) cover831453 (by decide)
  decide +kernel

theorem c831453_3 : P.sumLeaves 26 851408336 168 = 417361095 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831453) (lo := 464) (len := 168) (W := 417361095) check rows elimOK (by decide) (by decide) cover831453 (by decide)
  decide +kernel

theorem c831453_4 : P.sumLeaves 26 851408504 104 = 296829871 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831453) (lo := 632) (len := 104) (W := 296829871) check rows elimOK (by decide) (by decide) cover831453 (by decide)
  decide +kernel

theorem c831453_5 : P.sumLeaves 26 851408608 172 = 422610369 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831453) (lo := 736) (len := 172) (W := 422610369) check rows elimOK (by decide) (by decide) cover831453 (by decide)
  decide +kernel

theorem c831453_6 : P.sumLeaves 26 851408780 100 = 358881914 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831453) (lo := 908) (len := 100) (W := 358881914) check rows elimOK (by decide) (by decide) cover831453 (by decide)
  decide +kernel

theorem c831453_7 : P.sumLeaves 26 851408880 16 = 158037214 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831453) (lo := 1008) (len := 16) (W := 158037214) check rows elimOK (by decide) (by decide) cover831453 (by decide)
  decide +kernel

theorem h831453 : P.leaf 36 831453 = 2470235316 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(184, 214805915), (160, 321381401), (120, 280327537), (168, 417361095), (104, 296829871), (172, 422610369), (100, 358881914), (16, 158037214)]) (.cons c831453_0 (.cons c831453_1 (.cons c831453_2 (.cons c831453_3 (.cons c831453_4 (.cons c831453_5 (.cons c831453_6 (.cons c831453_7 (.nil))))))))) (by decide) (by decide))

theorem h122845 : P.leaf 36 122845 = 2470235316 :=
  orient84 (v := 831453) (by decide) (by decide +kernel) h831453

theorem cover122847 : P.CoversSplit 26 10 122847 0xfffffffffffffafafffffffffffffafafffffffffffffa00fafafafac8c8c800fffffafafffffafafafafafafafafafafffffafafffffa00fafafafac8c8c800fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafafafafafafafafffffafacc00c800fafafafac800c800 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f122847 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (125795328 + i)

theorem c122847_0 : rowSum f122847 0 292 = 765738274 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122847) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem c122847_1 : rowSum f122847 292 242 = 1198908536 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122847) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem c122847_2 : rowSum f122847 534 245 = 1343286300 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122847) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem c122847_3 : rowSum f122847 779 177 = 1369383154 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122847) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem c122847_4 : rowSum f122847 956 68 = 343459744 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122847) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem sum122847 : rowSum f122847 0 1024 = 5020776008 :=
  rowSum_append (F := f122847) (lo := 0) (n := 292) (m := 732) (A := 765738274) (B := 4255037734) c122847_0 (rowSum_append (F := f122847) (lo := 292) (n := 242) (m := 490) (A := 1198908536) (B := 3056129198) c122847_1 (rowSum_append (F := f122847) (lo := 534) (n := 245) (m := 245) (A := 1343286300) (B := 1712842898) c122847_2 (rowSum_append (F := f122847) (lo := 779) (n := 177) (m := 68) (A := 1369383154) (B := 343459744) c122847_3 (c122847_4))))

theorem h122847 : P.leaf 36 122847 = 5020776008 :=
  leaf_weighted (k := 26) (d := 10) (H := 122847) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 122847) (by decide) (by decide +kernel)) sum122847

theorem cover637307 : P.CoversSplit 26 10 637307 0xaaaaaaaaaaaaaaaaaaaaababaaaaaaaaaaaaaaaaaaaaaa88aaaaababaaaaaa88000000000000000000000a0a00000a0a000000000000000000000a0a00000a08aaaaaaaa88888888aaaaabab88888888aa88aa8888888888aa88ab8888888888000000000000000000000a0a00000808000000000000000000000a0800000808 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 930, 1322]) (by decide +kernel)

theorem c637307_0 : P.sumLeaves 26 652602368 501 = 213781267 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 637307) (lo := 0) (len := 501) (W := 213781267) check rows elimOK (by decide) (by decide) cover637307 (by decide)
  decide +kernel

theorem c637307_1 : P.sumLeaves 26 652602869 422 = 194773094 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 637307) (lo := 501) (len := 422) (W := 194773094) check rows elimOK (by decide) (by decide) cover637307 (by decide)
  decide +kernel

theorem c637307_2 : P.sumLeaves 26 652603291 101 = 249115622 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 637307) (lo := 923) (len := 101) (W := 249115622) check rows elimOK (by decide) (by decide) cover637307 (by decide)
  decide +kernel

theorem h637307 : P.leaf 36 637307 = 657669983 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(501, 213781267), (422, 194773094), (101, 249115622)]) (.cons c637307_0 (.cons c637307_1 (.cons c637307_2 (.nil)))) (by decide) (by decide))

theorem h122866 : P.leaf 36 122866 = 657669983 :=
  orient86 (v := 637307) (by decide) (by decide +kernel) h637307

theorem cover257005 : P.CoversSplit 26 10 257005 0xffffffffffffffffffffffffffffaaaaffffffffffffffccfffffafaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaffccaa88ffffffffffccffccffffffffffccaa88ffffffffffccffccfffffafaffccaa880000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [881, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c257005_0 : P.sumLeaves 26 263173120 378 = 123242906 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 257005) (lo := 0) (len := 378) (W := 123242906) check rows elimOK (by decide) (by decide) cover257005 (by decide)
  decide +kernel

theorem c257005_1 : P.sumLeaves 26 263173498 118 = 256630112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 257005) (lo := 378) (len := 118) (W := 256630112) check rows elimOK (by decide) (by decide) cover257005 (by decide)
  decide +kernel

theorem c257005_2 : P.sumLeaves 26 263173616 122 = 255542480 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 257005) (lo := 496) (len := 122) (W := 255542480) check rows elimOK (by decide) (by decide) cover257005 (by decide)
  decide +kernel

theorem c257005_3 : P.sumLeaves 26 263173738 112 = 223678300 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 257005) (lo := 618) (len := 112) (W := 223678300) check rows elimOK (by decide) (by decide) cover257005 (by decide)
  decide +kernel

theorem c257005_4 : P.sumLeaves 26 263173850 118 = 385222486 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 257005) (lo := 730) (len := 118) (W := 385222486) check rows elimOK (by decide) (by decide) cover257005 (by decide)
  decide +kernel

theorem c257005_5 : P.sumLeaves 26 263173968 104 = 350943564 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 257005) (lo := 848) (len := 104) (W := 350943564) check rows elimOK (by decide) (by decide) cover257005 (by decide)
  decide +kernel

theorem c257005_6 : P.sumLeaves 26 263174072 72 = 512378888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 257005) (lo := 952) (len := 72) (W := 512378888) check rows elimOK (by decide) (by decide) cover257005 (by decide)
  decide +kernel

theorem h257005 : P.leaf 36 257005 = 2107638736 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(378, 123242906), (118, 256630112), (122, 255542480), (112, 223678300), (118, 385222486), (104, 350943564), (72, 512378888)]) (.cons c257005_0 (.cons c257005_1 (.cons c257005_2 (.cons c257005_3 (.cons c257005_4 (.cons c257005_5 (.cons c257005_6 (.nil)))))))) (by decide) (by decide))

theorem h122867 : P.leaf 36 122867 = 2107638736 :=
  orient348 (v := 257005) (by decide) (by decide +kernel) h257005

def seg : List (ℕ × ℕ) := [(122845, 720), (122847, 360), (122866, 720), (122867, 720)]

theorem segOK : checkSeg 20 perms 122845 122870 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122845 122870 2520 5577071068080 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5577071068080)
    (SegSum.cons (w := 720) h122845 (SegSum.cons (w := 360) h122847 (SegSum.cons (w := 720) h122866 (SegSum.cons (w := 720) h122867 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S76
