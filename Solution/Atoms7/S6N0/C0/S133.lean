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

namespace RACert.S6N0.C0.S133

open RACert RACert.Problem

theorem cover245691 : P.CoversSplit 26 10 245691 0xfffffffffffffffffffffffffffff0f0ffffffffffffffccffffaaaaffcca080ffffffffffffffffffffa0a0ffffa0a0ffffffffffffffccffffa0a0ffcca080fffffffffffffffffffffffffffff0f0ffffffffffccffccffffaaaaffcca080ffffffffffffffffffffa0a0ffffa0a0ffffffffffccffccffffa0a0ffcca080 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245691_0 : P.sumLeaves 26 251587584 145 = 76907121 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245691) (lo := 0) (len := 145) (W := 76907121) check rows elimOK (by decide) (by decide) cover245691 (by decide)
  decide +kernel

theorem c245691_1 : P.sumLeaves 26 251587729 108 = 128461602 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245691) (lo := 145) (len := 108) (W := 128461602) check rows elimOK (by decide) (by decide) cover245691 (by decide)
  decide +kernel

theorem c245691_2 : P.sumLeaves 26 251587837 129 = 274357272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245691) (lo := 253) (len := 129) (W := 274357272) check rows elimOK (by decide) (by decide) cover245691 (by decide)
  decide +kernel

theorem c245691_3 : P.sumLeaves 26 251587966 104 = 443484790 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245691) (lo := 382) (len := 104) (W := 443484790) check rows elimOK (by decide) (by decide) cover245691 (by decide)
  decide +kernel

theorem c245691_4 : P.sumLeaves 26 251588070 129 = 557014006 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245691) (lo := 486) (len := 129) (W := 557014006) check rows elimOK (by decide) (by decide) cover245691 (by decide)
  decide +kernel

theorem c245691_5 : P.sumLeaves 26 251588199 120 = 809563516 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245691) (lo := 615) (len := 120) (W := 809563516) check rows elimOK (by decide) (by decide) cover245691 (by decide)
  decide +kernel

theorem c245691_6 : P.sumLeaves 26 251588319 125 = 813514800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245691) (lo := 735) (len := 125) (W := 813514800) check rows elimOK (by decide) (by decide) cover245691 (by decide)
  decide +kernel

theorem c245691_7 : P.sumLeaves 26 251588444 104 = 978240330 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245691) (lo := 860) (len := 104) (W := 978240330) check rows elimOK (by decide) (by decide) cover245691 (by decide)
  decide +kernel

theorem c245691_8 : P.sumLeaves 26 251588548 60 = 805900490 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245691) (lo := 964) (len := 60) (W := 805900490) check rows elimOK (by decide) (by decide) cover245691 (by decide)
  decide +kernel

theorem h245691 : P.leaf 36 245691 = 4887443927 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(145, 76907121), (108, 128461602), (129, 274357272), (104, 443484790), (129, 557014006), (120, 809563516), (125, 813514800), (104, 978240330), (60, 805900490)]) (.cons c245691_0 (.cons c245691_1 (.cons c245691_2 (.cons c245691_3 (.cons c245691_4 (.cons c245691_5 (.cons c245691_6 (.cons c245691_7 (.cons c245691_8 (.nil)))))))))) (by decide) (by decide))

theorem cover245693 : P.CoversSplit 26 10 245693 0xfffffffffffffffffffffffffffff0f0ffffffffffffffccffffaaaaffcca080ffffffffffffffffffffa0a0ffffa0a0ffffffffffffffccffffa0a0ffcca080fffffffffffffffffffffffffffff0f0ffffffffff00ff00ffffaaaaff00a000ffffffffffffffffffffa0a0ffffa0a0ffffffffff00ff00ffffa0a0ff00a000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245693_0 : P.sumLeaves 26 251589632 158 = 93736748 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 0) (len := 158) (W := 93736748) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_1 : P.sumLeaves 26 251589790 131 = 146774370 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 158) (len := 131) (W := 146774370) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_2 : P.sumLeaves 26 251589921 127 = 430627889 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 289) (len := 127) (W := 430627889) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_3 : P.sumLeaves 26 251590048 103 = 751087225 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 416) (len := 103) (W := 751087225) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_4 : P.sumLeaves 26 251590151 128 = 341444583 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 519) (len := 128) (W := 341444583) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_5 : P.sumLeaves 26 251590279 114 = 429383332 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 647) (len := 114) (W := 429383332) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_6 : P.sumLeaves 26 251590393 125 = 644248869 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 761) (len := 125) (W := 644248869) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_7 : P.sumLeaves 26 251590518 104 = 838287936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 886) (len := 104) (W := 838287936) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_8 : P.sumLeaves 26 251590622 34 = 445344302 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 990) (len := 34) (W := 445344302) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem h245693 : P.leaf 36 245693 = 4120935254 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(158, 93736748), (131, 146774370), (127, 430627889), (103, 751087225), (128, 341444583), (114, 429383332), (125, 644248869), (104, 838287936), (34, 445344302)]) (.cons c245693_0 (.cons c245693_1 (.cons c245693_2 (.cons c245693_3 (.cons c245693_4 (.cons c245693_5 (.cons c245693_6 (.cons c245693_7 (.cons c245693_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(245691, 360), (245693, 720)]

theorem segOK : checkSeg 20 perms 245691 245695 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 245691 245695 1080 4726553196600 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4726553196600)
    (SegSum.cons (w := 360) h245691 (SegSum.cons (w := 720) h245693 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S133
