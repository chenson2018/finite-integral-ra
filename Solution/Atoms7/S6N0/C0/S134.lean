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

namespace RACert.S6N0.C0.S134

open RACert RACert.Problem

theorem cover245695 : P.CoversSplit 26 10 245695 0xfffffffffffffffffffffffffffff0f0ffffffffffffffccffffaaaaffcca080ffffffffffffffffffffa0a0ffffa0a0ffffffffffffffccffffa0a0ffcca080fffffffffffffffffffffffffffff0f0ffffffffffccffccffffaaaaffcca080ffffffffffffffffffffa0a0ffffa0a0ffffffffffccffccffffa0a0ffcca080 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245695_0 : P.sumLeaves 26 251591680 145 = 296281108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245695) (lo := 0) (len := 145) (W := 296281108) check rows elimOK (by decide) (by decide) cover245695 (by decide)
  decide +kernel

theorem c245695_1 : P.sumLeaves 26 251591825 108 = 476292845 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245695) (lo := 145) (len := 108) (W := 476292845) check rows elimOK (by decide) (by decide) cover245695 (by decide)
  decide +kernel

theorem c245695_2 : P.sumLeaves 26 251591933 129 = 555234057 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245695) (lo := 253) (len := 129) (W := 555234057) check rows elimOK (by decide) (by decide) cover245695 (by decide)
  decide +kernel

theorem c245695_3 : P.sumLeaves 26 251592062 104 = 830653074 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245695) (lo := 382) (len := 104) (W := 830653074) check rows elimOK (by decide) (by decide) cover245695 (by decide)
  decide +kernel

theorem c245695_4 : P.sumLeaves 26 251592166 129 = 836368199 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245695) (lo := 486) (len := 129) (W := 836368199) check rows elimOK (by decide) (by decide) cover245695 (by decide)
  decide +kernel

theorem c245695_5 : P.sumLeaves 26 251592295 120 = 864887242 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245695) (lo := 615) (len := 120) (W := 864887242) check rows elimOK (by decide) (by decide) cover245695 (by decide)
  decide +kernel

theorem c245695_6 : P.sumLeaves 26 251592415 125 = 940317106 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245695) (lo := 735) (len := 125) (W := 940317106) check rows elimOK (by decide) (by decide) cover245695 (by decide)
  decide +kernel

theorem c245695_7 : P.sumLeaves 26 251592540 104 = 1052052704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245695) (lo := 860) (len := 104) (W := 1052052704) check rows elimOK (by decide) (by decide) cover245695 (by decide)
  decide +kernel

theorem c245695_8 : P.sumLeaves 26 251592644 60 = 862544300 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245695) (lo := 964) (len := 60) (W := 862544300) check rows elimOK (by decide) (by decide) cover245695 (by decide)
  decide +kernel

theorem h245695 : P.leaf 36 245695 = 6714630635 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(145, 296281108), (108, 476292845), (129, 555234057), (104, 830653074), (129, 836368199), (120, 864887242), (125, 940317106), (104, 1052052704), (60, 862544300)]) (.cons c245695_0 (.cons c245695_1 (.cons c245695_2 (.cons c245695_3 (.cons c245695_4 (.cons c245695_5 (.cons c245695_6 (.cons c245695_7 (.cons c245695_8 (.nil)))))))))) (by decide) (by decide))

theorem cover245724 : P.CoversSplit 26 10 245724 0xfffffffffffffffffffffffffffffafaffffffffffffff00ffffaaaaffccaa00ffffffffffffffffffffaaaaffffaaaaffffffffffffff00ffffaaaaffccaa00fffffffffffffffffffffffffffffafaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245724_0 : P.sumLeaves 26 251621376 148 = 13441264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245724) (lo := 0) (len := 148) (W := 13441264) check rows elimOK (by decide) (by decide) cover245724 (by decide)
  decide +kernel

theorem c245724_1 : P.sumLeaves 26 251621524 104 = 24421616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245724) (lo := 148) (len := 104) (W := 24421616) check rows elimOK (by decide) (by decide) cover245724 (by decide)
  decide +kernel

theorem c245724_2 : P.sumLeaves 26 251621628 144 = 88120428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245724) (lo := 252) (len := 144) (W := 88120428) check rows elimOK (by decide) (by decide) cover245724 (by decide)
  decide +kernel

theorem c245724_3 : P.sumLeaves 26 251621772 96 = 214036692 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245724) (lo := 396) (len := 96) (W := 214036692) check rows elimOK (by decide) (by decide) cover245724 (by decide)
  decide +kernel

theorem c245724_4 : P.sumLeaves 26 251621868 128 = 156546604 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245724) (lo := 492) (len := 128) (W := 156546604) check rows elimOK (by decide) (by decide) cover245724 (by decide)
  decide +kernel

theorem c245724_5 : P.sumLeaves 26 251621996 112 = 194791036 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245724) (lo := 620) (len := 112) (W := 194791036) check rows elimOK (by decide) (by decide) cover245724 (by decide)
  decide +kernel

theorem c245724_6 : P.sumLeaves 26 251622108 128 = 246437048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245724) (lo := 732) (len := 128) (W := 246437048) check rows elimOK (by decide) (by decide) cover245724 (by decide)
  decide +kernel

theorem c245724_7 : P.sumLeaves 26 251622236 100 = 372666952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245724) (lo := 860) (len := 100) (W := 372666952) check rows elimOK (by decide) (by decide) cover245724 (by decide)
  decide +kernel

theorem c245724_8 : P.sumLeaves 26 251622336 64 = 405118600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245724) (lo := 960) (len := 64) (W := 405118600) check rows elimOK (by decide) (by decide) cover245724 (by decide)
  decide +kernel

theorem h245724 : P.leaf 36 245724 = 1715580240 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 13441264), (104, 24421616), (144, 88120428), (96, 214036692), (128, 156546604), (112, 194791036), (128, 246437048), (100, 372666952), (64, 405118600)]) (.cons c245724_0 (.cons c245724_1 (.cons c245724_2 (.cons c245724_3 (.cons c245724_4 (.cons c245724_5 (.cons c245724_6 (.cons c245724_7 (.cons c245724_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(245695, 360), (245724, 60)]

theorem segOK : checkSeg 20 perms 245695 245725 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 245695 245725 420 2520201843000 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2520201843000)
    (SegSum.cons (w := 360) h245695 (SegSum.cons (w := 60) h245724 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S134
