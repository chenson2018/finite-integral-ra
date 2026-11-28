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

namespace RACert.S6N0.C0.S87

open RACert RACert.Problem

theorem cover242495 : P.CoversSplit 26 10 242495 0xfffffffffffffffffffffffffffff0f0ffffffffffffccccffffaaaaff008000fffffafafffffafaffffa0a0ffffa0a0fffffafaffffc8c8ffffa0a0ff008000fffffffffffffffffffffffffffff0f0ffccffcccc00cc00ffccaa88cc008000fffffafafffffafaffffa0a0ffffa0a0ffccfac8cc00c800ffcca080cc008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f242495 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (248314880 + i)

theorem c242495_0 : rowSum f242495 0 315 = 200753729 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242495) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem c242495_1 : rowSum f242495 315 136 = 339277260 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242495) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem c242495_2 : rowSum f242495 451 399 = 448351854 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242495) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem c242495_3 : rowSum f242495 850 174 = 411035076 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242495) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem sum242495 : rowSum f242495 0 1024 = 1399417919 :=
  rowSum_append (F := f242495) (lo := 0) (n := 315) (m := 709) (A := 200753729) (B := 1198664190) c242495_0 (rowSum_append (F := f242495) (lo := 315) (n := 136) (m := 573) (A := 339277260) (B := 859386930) c242495_1 (rowSum_append (F := f242495) (lo := 451) (n := 399) (m := 174) (A := 448351854) (B := 411035076) c242495_2 (c242495_3)))

theorem h242495 : P.leaf 36 242495 = 1399417919 :=
  leaf_weighted (k := 26) (d := 10) (H := 242495) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 242495) (by decide) (by decide +kernel)) sum242495

theorem cover621302 : P.CoversSplit 26 10 621302 0xfffffffffffffafafffffff0fffffaf0fffffffffffcfac8fffffff0fffcfac0fffffafafffffafafffff0f0fffff0f0fffffafafffcfac8fffff0f0fffcf0c0fffffffffffffafafffffff0fffffaf0ffccffccccccc8c8ffccffc0ccccc8c00000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 874, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

noncomputable def f621302 (i : ℕ) := rowWeight keep17 twice17 i * P.leaf 26 (636213248 + i)

theorem c621302_0 : rowSum f621302 0 491 = 357475521 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 621302) (keep := keep17) (twice := twice17) check rows elimOK (by decide) (by decide) cover621302 (by decide)
  decide +kernel

theorem c621302_1 : rowSum f621302 491 211 = 241129190 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 621302) (keep := keep17) (twice := twice17) check rows elimOK (by decide) (by decide) cover621302 (by decide)
  decide +kernel

theorem c621302_2 : rowSum f621302 702 200 = 456271673 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 621302) (keep := keep17) (twice := twice17) check rows elimOK (by decide) (by decide) cover621302 (by decide)
  decide +kernel

theorem c621302_3 : rowSum f621302 902 122 = 208813534 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 621302) (keep := keep17) (twice := twice17) check rows elimOK (by decide) (by decide) cover621302 (by decide)
  decide +kernel

theorem sum621302 : rowSum f621302 0 1024 = 1263689918 :=
  rowSum_append (F := f621302) (lo := 0) (n := 491) (m := 533) (A := 357475521) (B := 906214397) c621302_0 (rowSum_append (F := f621302) (lo := 491) (n := 211) (m := 322) (A := 241129190) (B := 665085207) c621302_1 (rowSum_append (F := f621302) (lo := 702) (n := 200) (m := 122) (A := 456271673) (B := 208813534) c621302_2 (c621302_3)))

theorem h621302 : P.leaf 36 621302 = 1263689918 :=
  leaf_weighted (k := 26) (d := 10) (H := 621302) (keep := keep17) (twice := twice17) rows (by decide) (by decide) (bal17) (invRow17 (H := 621302) (by decide) (by decide +kernel)) sum621302

theorem h242543 : P.leaf 36 242543 = 1263689918 :=
  orient93 (v := 621302) (by decide) (by decide +kernel) h621302

theorem cover613374 : P.CoversSplit 26 10 613374 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fffffffafffcfac8fffffafafffcfaf8fafafafafaf8faf8fffffafafffcfac8fafafafafaf8fac8ffffffffffccfac8fffffffaffccfac8ffffffffccccc8c8fffffffaccccc8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 922, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

noncomputable def f613374 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (628094976 + i)

theorem c613374_0 : rowSum f613374 0 397 = 621782224 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 613374) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover613374 (by decide)
  decide +kernel

theorem c613374_1 : rowSum f613374 397 113 = 852359102 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 613374) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover613374 (by decide)
  decide +kernel

theorem c613374_2 : rowSum f613374 510 464 = 972203163 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 613374) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover613374 (by decide)
  decide +kernel

theorem c613374_3 : rowSum f613374 974 50 = 306247934 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 613374) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover613374 (by decide)
  decide +kernel

theorem sum613374 : rowSum f613374 0 1024 = 2752592423 :=
  rowSum_append (F := f613374) (lo := 0) (n := 397) (m := 627) (A := 621782224) (B := 2130810199) c613374_0 (rowSum_append (F := f613374) (lo := 397) (n := 113) (m := 514) (A := 852359102) (B := 1278451097) c613374_1 (rowSum_append (F := f613374) (lo := 510) (n := 464) (m := 50) (A := 972203163) (B := 306247934) c613374_2 (c613374_3)))

theorem h613374 : P.leaf 36 613374 = 2752592423 :=
  leaf_weighted (k := 26) (d := 10) (H := 613374) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 613374) (by decide) (by decide +kernel)) sum613374

theorem h242559 : P.leaf 36 242559 = 2752592423 :=
  orient324 (v := 613374) (by decide) (by decide +kernel) h613374

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
  leaf_weighted (k := 26) (d := 10) (H := 242687) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 242687) (by decide) (by decide +kernel)) sum242687

theorem cover504623 : P.CoversSplit 26 10 504623 0xffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaff00aa00fffffafafffffafafafaaaaafafaaaaafffffafafffffafafafaaaaafa00aa00ffffffffffccffccffffffffffccffccffccffccff00ff00ffccaa88ff00aa00fffffafaffccfac8fafaaaaafac8aa88ffccfac8ff00fa00fac8aa88fa00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 930, 1658, 1665]) (by decide +kernel)

noncomputable def f504623 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (516733952 + i)

theorem c504623_0 : rowSum f504623 0 306 = 186201127 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 504623) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover504623 (by decide)
  decide +kernel

theorem c504623_1 : rowSum f504623 306 130 = 269166756 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 504623) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover504623 (by decide)
  decide +kernel

theorem c504623_2 : rowSum f504623 436 403 = 477573114 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 504623) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover504623 (by decide)
  decide +kernel

theorem c504623_3 : rowSum f504623 839 185 = 464092344 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 504623) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover504623 (by decide)
  decide +kernel

theorem sum504623 : rowSum f504623 0 1024 = 1397033341 :=
  rowSum_append (F := f504623) (lo := 0) (n := 306) (m := 718) (A := 186201127) (B := 1210832214) c504623_0 (rowSum_append (F := f504623) (lo := 306) (n := 130) (m := 588) (A := 269166756) (B := 941665458) c504623_1 (rowSum_append (F := f504623) (lo := 436) (n := 403) (m := 185) (A := 477573114) (B := 464092344) c504623_2 (c504623_3)))

theorem h504623 : P.leaf 36 504623 = 1397033341 :=
  leaf_weighted (k := 26) (d := 10) (H := 504623) (keep := keep8) (twice := twice8) rows (by decide) (by decide) (bal8) (invRow8 (H := 504623) (by decide) (by decide +kernel)) sum504623

theorem h243511 : P.leaf 36 243511 = 1397033341 :=
  orient348 (v := 504623) (by decide) (by decide +kernel) h504623

def seg : List (ℕ × ℕ) := [(242495, 360), (242543, 360), (242559, 360), (242687, 72), (243511, 360)]

theorem segOK : checkSeg 20 perms 242495 243519 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 242495 243519 1512 2944936410336 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2944936410336)
    (SegSum.cons (w := 360) h242495 (SegSum.cons (w := 360) h242543 (SegSum.cons (w := 360) h242559 (SegSum.cons (w := 72) h242687 (SegSum.cons (w := 360) h243511 (show SegSum (P.leaf 36) [] 0 from rfl)))))) (by decide)

end RACert.S6N0.C0.S87
