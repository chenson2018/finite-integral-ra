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

namespace RACert.S6N0.C0.S132

open RACert RACert.Problem

theorem cover245631 : P.CoversSplit 26 10 245631 0xfffffffffffffffffffffffffffffafaffffffffffffffccffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaff00aa00fffffffffffffffffffffffffffffafaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245631_0 : P.sumLeaves 26 251526144 148 = 439401506 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245631) (lo := 0) (len := 148) (W := 439401506) check rows elimOK (by decide) (by decide) cover245631 (by decide)
  decide +kernel

theorem c245631_1 : P.sumLeaves 26 251526292 104 = 601430790 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245631) (lo := 148) (len := 104) (W := 601430790) check rows elimOK (by decide) (by decide) cover245631 (by decide)
  decide +kernel

theorem c245631_2 : P.sumLeaves 26 251526396 144 = 867297751 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245631) (lo := 252) (len := 144) (W := 867297751) check rows elimOK (by decide) (by decide) cover245631 (by decide)
  decide +kernel

theorem c245631_3 : P.sumLeaves 26 251526540 96 = 1110854956 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245631) (lo := 396) (len := 96) (W := 1110854956) check rows elimOK (by decide) (by decide) cover245631 (by decide)
  decide +kernel

theorem c245631_4 : P.sumLeaves 26 251526636 128 = 1051094504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245631) (lo := 492) (len := 128) (W := 1051094504) check rows elimOK (by decide) (by decide) cover245631 (by decide)
  decide +kernel

theorem c245631_5 : P.sumLeaves 26 251526764 112 = 1081611269 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245631) (lo := 620) (len := 112) (W := 1081611269) check rows elimOK (by decide) (by decide) cover245631 (by decide)
  decide +kernel

theorem c245631_6 : P.sumLeaves 26 251526876 128 = 1310056175 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245631) (lo := 732) (len := 128) (W := 1310056175) check rows elimOK (by decide) (by decide) cover245631 (by decide)
  decide +kernel

theorem c245631_7 : P.sumLeaves 26 251527004 100 = 1353587198 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245631) (lo := 860) (len := 100) (W := 1353587198) check rows elimOK (by decide) (by decide) cover245631 (by decide)
  decide +kernel

theorem c245631_8 : P.sumLeaves 26 251527104 64 = 1246572795 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245631) (lo := 960) (len := 64) (W := 1246572795) check rows elimOK (by decide) (by decide) cover245631 (by decide)
  decide +kernel

theorem h245631 : P.leaf 36 245631 = 9061906944 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 439401506), (104, 601430790), (144, 867297751), (96, 1110854956), (128, 1051094504), (112, 1081611269), (128, 1310056175), (100, 1353587198), (64, 1246572795)]) (.cons c245631_0 (.cons c245631_1 (.cons c245631_2 (.cons c245631_3 (.cons c245631_4 (.cons c245631_5 (.cons c245631_6 (.cons c245631_7 (.cons c245631_8 (.nil)))))))))) (by decide) (by decide))

theorem cover245687 : P.CoversSplit 26 10 245687 0xfffffffffffffffffffffffffffff0f0ffffffffffffffccffffaaaaffcca080ffffffffffffffffffffa0a0ffffa0a0ffffffffffffffccffffa0a0ffcca080fffffffffffffffffffffffffffff0f0ffffffffffccffccffffaaaaffcca080ffffffffffffffffffffa0a0ffffa0a0ffffffffffccffccffffa0a0ffcca080 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245687_0 : P.sumLeaves 26 251583488 145 = 84693977 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245687) (lo := 0) (len := 145) (W := 84693977) check rows elimOK (by decide) (by decide) cover245687 (by decide)
  decide +kernel

theorem c245687_1 : P.sumLeaves 26 251583633 108 = 136257710 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245687) (lo := 145) (len := 108) (W := 136257710) check rows elimOK (by decide) (by decide) cover245687 (by decide)
  decide +kernel

theorem c245687_2 : P.sumLeaves 26 251583741 129 = 340175774 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245687) (lo := 253) (len := 129) (W := 340175774) check rows elimOK (by decide) (by decide) cover245687 (by decide)
  decide +kernel

theorem c245687_3 : P.sumLeaves 26 251583870 104 = 501815339 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245687) (lo := 382) (len := 104) (W := 501815339) check rows elimOK (by decide) (by decide) cover245687 (by decide)
  decide +kernel

theorem c245687_4 : P.sumLeaves 26 251583974 129 = 464959749 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245687) (lo := 486) (len := 129) (W := 464959749) check rows elimOK (by decide) (by decide) cover245687 (by decide)
  decide +kernel

theorem c245687_5 : P.sumLeaves 26 251584103 120 = 372329732 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245687) (lo := 615) (len := 120) (W := 372329732) check rows elimOK (by decide) (by decide) cover245687 (by decide)
  decide +kernel

theorem c245687_6 : P.sumLeaves 26 251584223 125 = 522136302 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245687) (lo := 735) (len := 125) (W := 522136302) check rows elimOK (by decide) (by decide) cover245687 (by decide)
  decide +kernel

theorem c245687_7 : P.sumLeaves 26 251584348 104 = 641504652 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245687) (lo := 860) (len := 104) (W := 641504652) check rows elimOK (by decide) (by decide) cover245687 (by decide)
  decide +kernel

theorem c245687_8 : P.sumLeaves 26 251584452 60 = 594343238 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245687) (lo := 964) (len := 60) (W := 594343238) check rows elimOK (by decide) (by decide) cover245687 (by decide)
  decide +kernel

theorem h245687 : P.leaf 36 245687 = 3658216473 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(145, 84693977), (108, 136257710), (129, 340175774), (104, 501815339), (129, 464959749), (120, 372329732), (125, 522136302), (104, 641504652), (60, 594343238)]) (.cons c245687_0 (.cons c245687_1 (.cons c245687_2 (.cons c245687_3 (.cons c245687_4 (.cons c245687_5 (.cons c245687_6 (.cons c245687_7 (.cons c245687_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(245631, 120), (245687, 72)]

theorem segOK : checkSeg 20 perms 245631 245691 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 245631 245691 192 1350820419336 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1350820419336)
    (SegSum.cons (w := 120) h245631 (SegSum.cons (w := 72) h245687 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S132
