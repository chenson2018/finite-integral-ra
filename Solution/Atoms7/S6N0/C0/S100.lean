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

namespace RACert.S6N0.C0.S100

open RACert RACert.Problem

theorem cover241519 : P.CoversSplit 26 10 241519 0xffffffffffffffffffffffffffffaaaaffffffffffffffccffffaaaaff00aa00fffffffffffffffffafaaaaafafaaaaaffffffffffffffccfafaaaaafa00aa00ffffffffffffffffffffffffffffaaaaffffffffff00ff00ffffaaaaff00aa00fffffffffffffffffafaaaaafafaaaaaffffffffff00ff00fafaaaaafa00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c241519_0 : P.sumLeaves 26 247315456 158 = 82609154 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 0) (len := 158) (W := 82609154) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_1 : P.sumLeaves 26 247315614 128 = 185072936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 158) (len := 128) (W := 185072936) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_2 : P.sumLeaves 26 247315742 128 = 179160271 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 286) (len := 128) (W := 179160271) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_3 : P.sumLeaves 26 247315870 96 = 443557267 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 414) (len := 96) (W := 443557267) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_4 : P.sumLeaves 26 247315966 139 = 205198637 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 510) (len := 139) (W := 205198637) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_5 : P.sumLeaves 26 247316105 115 = 350277429 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 649) (len := 115) (W := 350277429) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_6 : P.sumLeaves 26 247316220 128 = 278601135 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 764) (len := 128) (W := 278601135) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_7 : P.sumLeaves 26 247316348 104 = 385425068 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 892) (len := 104) (W := 385425068) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_8 : P.sumLeaves 26 247316452 28 = 288750939 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 996) (len := 28) (W := 288750939) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem h241519 : P.leaf 36 241519 = 2398652836 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(158, 82609154), (128, 185072936), (128, 179160271), (96, 443557267), (139, 205198637), (115, 350277429), (128, 278601135), (104, 385425068), (28, 288750939)]) (.cons c241519_0 (.cons c241519_1 (.cons c241519_2 (.cons c241519_3 (.cons c241519_4 (.cons c241519_5 (.cons c241519_6 (.cons c241519_7 (.cons c241519_8 (.nil)))))))))) (by decide) (by decide))

theorem cover241534 : P.CoversSplit 26 10 241534 0xffffffffffffffffffffffffffffaaaaffffffffffffffccffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaff00aa00ffffffffffffffffffffffffffffaaaaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c241534_0 : P.sumLeaves 26 247330816 148 = 47577160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241534) (lo := 0) (len := 148) (W := 47577160) check rows elimOK (by decide) (by decide) cover241534 (by decide)
  decide +kernel

theorem c241534_1 : P.sumLeaves 26 247330964 104 = 72367656 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241534) (lo := 148) (len := 104) (W := 72367656) check rows elimOK (by decide) (by decide) cover241534 (by decide)
  decide +kernel

theorem c241534_2 : P.sumLeaves 26 247331068 148 = 198172731 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241534) (lo := 252) (len := 148) (W := 198172731) check rows elimOK (by decide) (by decide) cover241534 (by decide)
  decide +kernel

theorem c241534_3 : P.sumLeaves 26 247331216 96 = 380780229 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241534) (lo := 400) (len := 96) (W := 380780229) check rows elimOK (by decide) (by decide) cover241534 (by decide)
  decide +kernel

theorem c241534_4 : P.sumLeaves 26 247331312 128 = 283869215 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241534) (lo := 496) (len := 128) (W := 283869215) check rows elimOK (by decide) (by decide) cover241534 (by decide)
  decide +kernel

theorem c241534_5 : P.sumLeaves 26 247331440 112 = 214775203 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241534) (lo := 624) (len := 112) (W := 214775203) check rows elimOK (by decide) (by decide) cover241534 (by decide)
  decide +kernel

theorem c241534_6 : P.sumLeaves 26 247331552 128 = 347159476 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241534) (lo := 736) (len := 128) (W := 347159476) check rows elimOK (by decide) (by decide) cover241534 (by decide)
  decide +kernel

theorem c241534_7 : P.sumLeaves 26 247331680 104 = 400172504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241534) (lo := 864) (len := 104) (W := 400172504) check rows elimOK (by decide) (by decide) cover241534 (by decide)
  decide +kernel

theorem c241534_8 : P.sumLeaves 26 247331784 56 = 464574800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241534) (lo := 968) (len := 56) (W := 464574800) check rows elimOK (by decide) (by decide) cover241534 (by decide)
  decide +kernel

theorem h241534 : P.leaf 36 241534 = 2409448974 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 47577160), (104, 72367656), (148, 198172731), (96, 380780229), (128, 283869215), (112, 214775203), (128, 347159476), (104, 400172504), (56, 464574800)]) (.cons c241534_0 (.cons c241534_1 (.cons c241534_2 (.cons c241534_3 (.cons c241534_4 (.cons c241534_5 (.cons c241534_6 (.cons c241534_7 (.cons c241534_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(241519, 720), (241534, 180)]

theorem segOK : checkSeg 20 perms 241519 241535 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 241519 241535 900 2160730857240 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2160730857240)
    (SegSum.cons (w := 720) h241519 (SegSum.cons (w := 180) h241534 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S100
