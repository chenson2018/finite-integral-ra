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

namespace RACert.S4N1.C0.S48

open RACert RACert.Problem

theorem cover7158 : P.CoversSplit 24 10 7158 0xffffffffafafa0a0ffffffffafafa0a0f0f0f0f00000aaaaf0f0f0f000000a0accffccff88888080cccccccc88888080c0f0c0f000008888c0c0c0c000000808ffffffffafafa0a0ffffffffafafa0a0f0f0ffff0000aaaaf0f0ffff00000a0a0000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 859, 879, 916, 1202, 1209, 1258, 1259, 1601]) (ps := [(12, [866], [859]), (14, [880], [859])]) (by decide +kernel)

theorem c7158_0 : P.sumLeaves 24 7329792 436 = 3243968 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7158) (lo := 0) (len := 436) (W := 3243968) check rows elimOK (by decide) (by decide) cover7158 (by decide)
  decide +kernel

theorem c7158_1 : P.sumLeaves 24 7330228 246 = 12549531 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7158) (lo := 436) (len := 246) (W := 12549531) check rows elimOK (by decide) (by decide) cover7158 (by decide)
  decide +kernel

theorem c7158_2 : P.sumLeaves 24 7330474 238 = 11082393 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7158) (lo := 682) (len := 238) (W := 11082393) check rows elimOK (by decide) (by decide) cover7158 (by decide)
  decide +kernel

theorem c7158_3 : P.sumLeaves 24 7330712 104 = 38018914 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7158) (lo := 920) (len := 104) (W := 38018914) check rows elimOK (by decide) (by decide) cover7158 (by decide)
  decide +kernel

theorem h7158 : P.leaf 34 7158 = 64894806 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(436, 3243968), (246, 12549531), (238, 11082393), (104, 38018914)]) (.cons c7158_0 (.cons c7158_1 (.cons c7158_2 (.cons c7158_3 (.nil))))) (by decide) (by decide))

theorem cover7159 : P.CoversSplit 24 10 7159 0xffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0ccffccff88888080cccccccc88888080ccffccff88888080cccccccc88888080ffffffffafafa0a0ffffffffafafa0a0ffffffffaaaaa0a0ffffffffaaaaa0a0ccffccff88888080cccccccc88888080cccccccc88888080cccccccc88888080 :=
  coversSplit check rows (by decide) (by decide) (xs := [859, 916, 1202, 1209, 1217, 1258, 1259, 1601, 1609]) (by decide +kernel)

theorem c7159_0 : P.sumLeaves 24 7330816 261 = 3697708 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7159) (lo := 0) (len := 261) (W := 3697708) check rows elimOK (by decide) (by decide) cover7159 (by decide)
  decide +kernel

theorem c7159_1 : P.sumLeaves 24 7331077 144 = 9821483 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7159) (lo := 261) (len := 144) (W := 9821483) check rows elimOK (by decide) (by decide) cover7159 (by decide)
  decide +kernel

theorem c7159_2 : P.sumLeaves 24 7331221 145 = 29674372 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7159) (lo := 405) (len := 145) (W := 29674372) check rows elimOK (by decide) (by decide) cover7159 (by decide)
  decide +kernel

theorem c7159_3 : P.sumLeaves 24 7331366 223 = 22837591 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7159) (lo := 550) (len := 223) (W := 22837591) check rows elimOK (by decide) (by decide) cover7159 (by decide)
  decide +kernel

theorem c7159_4 : P.sumLeaves 24 7331589 128 = 23445325 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7159) (lo := 773) (len := 128) (W := 23445325) check rows elimOK (by decide) (by decide) cover7159 (by decide)
  decide +kernel

theorem c7159_5 : P.sumLeaves 24 7331717 123 = 90913629 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7159) (lo := 901) (len := 123) (W := 90913629) check rows elimOK (by decide) (by decide) cover7159 (by decide)
  decide +kernel

theorem h7159 : P.leaf 34 7159 = 180390108 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(261, 3697708), (144, 9821483), (145, 29674372), (223, 22837591), (128, 23445325), (123, 90913629)]) (.cons c7159_0 (.cons c7159_1 (.cons c7159_2 (.cons c7159_3 (.cons c7159_4 (.cons c7159_5 (.nil))))))) (by decide) (by decide))

theorem cover7164 : P.CoversSplit 24 10 7164 0xffffffffaaaaaaaaffffffffaaaaaaaaf0f0f5f500000000f0f0f5f500000000cccccccc88888888cccccccc88888888c0c0c4c400000000c0c0c4c400000000ff00ff00aa00aa00ff33ff33aa22aa22f000f50000000000f030f531000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 859, 879, 916, 1202, 1259, 1601]) (by decide +kernel)

noncomputable def f7164 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7335936 + i)

theorem c7164_0 : rowSum f7164 0 702 = 32299717 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7164) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7164 (by decide)
  decide +kernel

theorem c7164_1 : rowSum f7164 702 322 = 51665322 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7164) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7164 (by decide)
  decide +kernel

theorem sum7164 : rowSum f7164 0 1024 = 83965039 :=
  rowSum_append (F := f7164) (lo := 0) (n := 702) (m := 322) (A := 32299717) (B := 51665322) c7164_0 (c7164_1)

theorem h7164 : P.leaf 34 7164 = 83965039 :=
  leaf_weighted (k := 24) (d := 10) (H := 7164) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 7164) (by decide) (by decide +kernel)) sum7164

theorem cover7165 : P.CoversSplit 24 10 7165 0xffffffffafafaaaaffffffffafafaaaaffffffff00000000ffffffff00000000ccffccff88888888cccccccc88888888ccffccff00000000cccccccc00000000ff00ff00af00aa00ff33ff33af23aa22ff00ff0000000000ff33ff33000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 859, 879, 916, 1202, 1209, 1258, 1259, 1601]) (by decide +kernel)

theorem c7165_0 : P.sumLeaves 24 7336960 495 = 27525080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7165) (lo := 0) (len := 495) (W := 27525080) check rows elimOK (by decide) (by decide) cover7165 (by decide)
  decide +kernel

theorem c7165_1 : P.sumLeaves 24 7337455 260 = 31461295 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7165) (lo := 495) (len := 260) (W := 31461295) check rows elimOK (by decide) (by decide) cover7165 (by decide)
  decide +kernel

theorem c7165_2 : P.sumLeaves 24 7337715 176 = 46619564 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7165) (lo := 755) (len := 176) (W := 46619564) check rows elimOK (by decide) (by decide) cover7165 (by decide)
  decide +kernel

theorem c7165_3 : P.sumLeaves 24 7337891 93 = 97590890 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7165) (lo := 931) (len := 93) (W := 97590890) check rows elimOK (by decide) (by decide) cover7165 (by decide)
  decide +kernel

theorem h7165 : P.leaf 34 7165 = 203196829 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(495, 27525080), (260, 31461295), (176, 46619564), (93, 97590890)]) (.cons c7165_0 (.cons c7165_1 (.cons c7165_2 (.cons c7165_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(7158, 48), (7159, 48), (7164, 24), (7165, 48)]

theorem segOK : checkSeg 16 perms 7158 7167 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7158 7167 168 23542284600 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 23542284600)
    (SegSum.cons (w := 48) h7158 (SegSum.cons (w := 48) h7159 (SegSum.cons (w := 24) h7164 (SegSum.cons (w := 48) h7165 (show SegSum (P.leaf 34) [] 0 from rfl))))) (by decide)

end RACert.S4N1.C0.S48
