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

namespace RACert.S6N0.C0.S36

open RACert RACert.Problem

theorem cover32736 : P.CoversSplit 26 10 32736 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h32736 : P.leaf 36 32736 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32736) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32736) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover32736 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover32737 : P.CoversSplit 26 10 32737 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h32737 : P.leaf 36 32737 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32737) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32737) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover32737 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover32739 : P.CoversSplit 26 10 32739 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h32739 : P.leaf 36 32739 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32739) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32739) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover32739 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover32741 : P.CoversSplit 26 10 32741 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h32741 : P.leaf 36 32741 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32741) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32741) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover32741 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover32743 : P.CoversSplit 26 10 32743 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h32743 : P.leaf 36 32743 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32743) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32743) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover32743 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover32751 : P.CoversSplit 26 10 32751 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h32751 : P.leaf 36 32751 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32751) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32751) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover32751 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96748 : P.CoversSplit 26 10 96748 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h96748 : P.leaf 36 96748 = 1738848 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96748) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96748) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover96748 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h32752 : P.leaf 36 32752 = 1738848 :=
  orient348 (v := 96748) (by decide) (by decide +kernel) h96748

theorem cover32753 : P.CoversSplit 26 10 32753 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00800000000000000000000fa000000fa0000000000000000000000fa000000fa080000000000000000000000000000000000000000f0c0f0c000000000f0c0f0c8000000000000000000000000000000000000000000000000000000000000fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979]) (by decide +kernel)

noncomputable def f32753 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (33539072 + i)

theorem c32753_0 : rowSum f32753 0 1024 = 61046772 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32753) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32753 (by decide)
  decide +kernel

theorem sum32753 : rowSum f32753 0 1024 = 61046772 :=
  c32753_0

theorem h32753 : P.leaf 36 32753 = 61046772 :=
  leaf_weighted (k := 26) (d := 10) (H := 32753) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 32753) (by decide) (by decide +kernel)) sum32753

theorem cover32755 : P.CoversSplit 26 10 32755 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00800000000000000000000fa000000fa0000000000000000000000fa000000fa080000000000000000000000000000000000000000f0c0f0c000000000f0c0f0c8000000000000000000000000000000000000000000000000000000000000fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979]) (by decide +kernel)

noncomputable def f32755 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (33541120 + i)

theorem c32755_0 : rowSum f32755 0 1024 = 129458992 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32755) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32755 (by decide)
  decide +kernel

theorem sum32755 : rowSum f32755 0 1024 = 129458992 :=
  c32755_0

theorem h32755 : P.leaf 36 32755 = 129458992 :=
  leaf_weighted (k := 26) (d := 10) (H := 32755) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 32755) (by decide) (by decide +kernel)) sum32755

theorem cover371163 : P.CoversSplit 26 10 371163 0xaaaaaaaaaaaaaaaaaaaaababaaaaabab00000000000000000000000000220022000000000000000000000a0a00000a0a0000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 881, 1665]) (by decide +kernel)

noncomputable def f371163 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (380070912 + i)

theorem c371163_0 : rowSum f371163 0 1024 = 115087146 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 371163) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover371163 (by decide)
  decide +kernel

theorem sum371163 : rowSum f371163 0 1024 = 115087146 :=
  c371163_0

theorem h371163 : P.leaf 36 371163 = 115087146 :=
  leaf_weighted (k := 26) (d := 10) (H := 371163) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 371163) (by decide) (by decide +kernel)) sum371163

theorem h32756 : P.leaf 36 32756 = 115087146 :=
  orient84 (v := 371163) (by decide) (by decide +kernel) h371163

theorem cover32757 : P.CoversSplit 26 10 32757 0xff00ff00ff00fa00ff00fa00ff00fa00ff00ff00ff00fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff00fa00fa00f000fa00f00000000000000000000000000000000000000000003300320000000000320032000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 929, 972, 979, 1265, 1273, 1315, 1658]) (by decide +kernel)

theorem c32757_0 : P.sumLeaves 26 33543168 747 = 87216562 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32757) (lo := 0) (len := 747) (W := 87216562) check rows elimOK (by decide) (by decide) cover32757 (by decide)
  decide +kernel

theorem c32757_1 : P.sumLeaves 26 33543915 224 = 191832624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32757) (lo := 747) (len := 224) (W := 191832624) check rows elimOK (by decide) (by decide) cover32757 (by decide)
  decide +kernel

theorem c32757_2 : P.sumLeaves 26 33544139 53 = 120909276 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32757) (lo := 971) (len := 53) (W := 120909276) check rows elimOK (by decide) (by decide) cover32757 (by decide)
  decide +kernel

theorem h32757 : P.leaf 36 32757 = 399958462 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(747, 87216562), (224, 191832624), (53, 120909276)]) (.cons c32757_0 (.cons c32757_1 (.cons c32757_2 (.nil)))) (by decide) (by decide))

theorem cover371199 : P.CoversSplit 26 10 371199 0xfffffffffffffffffffffefefffffefe00000000000000000000000000220022ffffffffffffffffaaaaaaaaaaaaaaaa0000000000000000000000000022002200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 881, 930, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f371199 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (380107776 + i)

theorem c371199_0 : rowSum f371199 0 941 = 371622104 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 371199) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover371199 (by decide)
  decide +kernel

theorem c371199_1 : rowSum f371199 941 83 = 468952240 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 371199) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover371199 (by decide)
  decide +kernel

theorem sum371199 : rowSum f371199 0 1024 = 840574344 :=
  rowSum_append (F := f371199) (lo := 0) (n := 941) (m := 83) (A := 371622104) (B := 468952240) c371199_0 (c371199_1)

theorem h371199 : P.leaf 36 371199 = 840574344 :=
  leaf_weighted (k := 26) (d := 10) (H := 371199) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 371199) (by decide) (by decide +kernel)) sum371199

theorem h32759 : P.leaf 36 32759 = 840574344 :=
  orient84 (v := 371199) (by decide) (by decide +kernel) h371199

theorem cover32764 : P.CoversSplit 26 10 32764 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f32764 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (33550336 + i)

theorem c32764_0 : rowSum f32764 0 410 = 146177522 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32764) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem c32764_1 : rowSum f32764 410 383 = 314433038 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32764) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem c32764_2 : rowSum f32764 793 230 = 490911620 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32764) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem c32764_3 : rowSum f32764 1023 1 = 9297188 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32764) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem sum32764 : rowSum f32764 0 1024 = 960819368 :=
  rowSum_append (F := f32764) (lo := 0) (n := 410) (m := 614) (A := 146177522) (B := 814641846) c32764_0 (rowSum_append (F := f32764) (lo := 410) (n := 383) (m := 231) (A := 314433038) (B := 500208808) c32764_1 (rowSum_append (F := f32764) (lo := 793) (n := 230) (m := 1) (A := 490911620) (B := 9297188) c32764_2 (c32764_3)))

theorem h32764 : P.leaf 36 32764 = 960819368 :=
  leaf_weighted (k := 26) (d := 10) (H := 32764) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 32764) (by decide) (by decide +kernel)) sum32764

theorem cover32765 : P.CoversSplit 26 10 32765 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [923, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f32765 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (33551360 + i)

theorem c32765_0 : rowSum f32765 0 410 = 377784388 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32765) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem c32765_1 : rowSum f32765 410 383 = 672665168 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32765) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem c32765_2 : rowSum f32765 793 230 = 995192308 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32765) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem c32765_3 : rowSum f32765 1023 1 = 13171336 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32765) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem sum32765 : rowSum f32765 0 1024 = 2058813200 :=
  rowSum_append (F := f32765) (lo := 0) (n := 410) (m := 614) (A := 377784388) (B := 1681028812) c32765_0 (rowSum_append (F := f32765) (lo := 410) (n := 383) (m := 231) (A := 672665168) (B := 1008363644) c32765_1 (rowSum_append (F := f32765) (lo := 793) (n := 230) (m := 1) (A := 995192308) (B := 13171336) c32765_2 (c32765_3)))

theorem h32765 : P.leaf 36 32765 = 2058813200 :=
  leaf_weighted (k := 26) (d := 10) (H := 32765) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 32765) (by decide) (by decide +kernel)) sum32765

theorem cover64511 : P.CoversSplit 26 10 64511 0xfffffffffffffac8ffffaaaaffffaa88ffffffffccccc8c8fac8aa88c8c88888fffffafafffffac8fafaaaaafafaaa88fffffafaccccc8c8fac8aa88c8c88888ffffffffffccfac8ffffaaaaffccaa88ffccffccccccc8c8fac8aa88c8c88888fffffafaffccfac8fafaaaaafac8aa88ffccfac8ccccc8c8fac8aa88c8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f64511 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (66059264 + i)

theorem c64511_0 : rowSum f64511 0 311 = 1047519977 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 64511) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover64511 (by decide)
  decide +kernel

theorem c64511_1 : rowSum f64511 311 155 = 1386999346 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 64511) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover64511 (by decide)
  decide +kernel

theorem c64511_2 : rowSum f64511 466 421 = 1550019924 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 64511) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover64511 (by decide)
  decide +kernel

theorem c64511_3 : rowSum f64511 887 137 = 776663360 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 64511) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover64511 (by decide)
  decide +kernel

theorem sum64511 : rowSum f64511 0 1024 = 4761202607 :=
  rowSum_append (F := f64511) (lo := 0) (n := 311) (m := 713) (A := 1047519977) (B := 3713682630) c64511_0 (rowSum_append (F := f64511) (lo := 311) (n := 155) (m := 558) (A := 1386999346) (B := 2326683284) c64511_1 (rowSum_append (F := f64511) (lo := 466) (n := 421) (m := 137) (A := 1550019924) (B := 776663360) c64511_2 (c64511_3)))

theorem h64511 : P.leaf 36 64511 = 4761202607 :=
  leaf_weighted (k := 26) (d := 10) (H := 64511) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 64511) (by decide) (by decide +kernel)) sum64511

theorem h32767 : P.leaf 36 32767 = 4761202607 :=
  orient80 (v := 64511) (by decide) (by decide +kernel) h64511

def seg : List (ℕ × ℕ) := [(32736, 90), (32737, 360), (32739, 180), (32741, 360), (32743, 360), (32751, 90), (32752, 180), (32753, 360), (32755, 180), (32756, 360), (32757, 720), (32759, 360), (32764, 180), (32765, 360), (32767, 180)]

theorem segOK : checkSeg 20 perms 32736 65520 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 32736 65520 4320 2448737385660 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2448737385660)
    (SegSum.cons (w := 90) h32736 (SegSum.cons (w := 360) h32737 (SegSum.cons (w := 180) h32739 (SegSum.cons (w := 360) h32741 (SegSum.cons (w := 360) h32743 (SegSum.cons (w := 90) h32751 (SegSum.cons (w := 180) h32752 (SegSum.cons (w := 360) h32753 (SegSum.cons (w := 180) h32755 (SegSum.cons (w := 360) h32756 (SegSum.cons (w := 720) h32757 (SegSum.cons (w := 360) h32759 (SegSum.cons (w := 180) h32764 (SegSum.cons (w := 360) h32765 (SegSum.cons (w := 180) h32767 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))) (by decide)

end RACert.S6N0.C0.S36
