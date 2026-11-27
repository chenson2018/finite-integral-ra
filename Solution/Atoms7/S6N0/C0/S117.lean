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

namespace RACert.S6N0.C0.S117

open RACert RACert.Problem

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

theorem cover241535 : P.CoversSplit 26 10 241535 0xffffffffffffffffffffffffffffaaaaffffffffffffffccffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaff00aa00ffffffffffffffffffffffffffffaaaaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c241535_0 : P.sumLeaves 26 247331840 148 = 192244615 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 0) (len := 148) (W := 192244615) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_1 : P.sumLeaves 26 247331988 104 = 279867689 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 148) (len := 104) (W := 279867689) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_2 : P.sumLeaves 26 247332092 148 = 426827545 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 252) (len := 148) (W := 426827545) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_3 : P.sumLeaves 26 247332240 96 = 559472627 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 400) (len := 96) (W := 559472627) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_4 : P.sumLeaves 26 247332336 128 = 527423275 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 496) (len := 128) (W := 527423275) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_5 : P.sumLeaves 26 247332464 112 = 503141651 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 624) (len := 112) (W := 503141651) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_6 : P.sumLeaves 26 247332576 128 = 637843577 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 736) (len := 128) (W := 637843577) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_7 : P.sumLeaves 26 247332704 104 = 621120108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 864) (len := 104) (W := 621120108) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_8 : P.sumLeaves 26 247332808 56 = 650130321 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 968) (len := 56) (W := 650130321) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem h241535 : P.leaf 36 241535 = 4398071408 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 192244615), (104, 279867689), (148, 426827545), (96, 559472627), (128, 527423275), (112, 503141651), (128, 637843577), (104, 621120108), (56, 650130321)]) (.cons c241535_0 (.cons c241535_1 (.cons c241535_2 (.cons c241535_3 (.cons c241535_4 (.cons c241535_5 (.cons c241535_6 (.cons c241535_7 (.cons c241535_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(241534, 180), (241535, 360)]

theorem segOK : checkSeg 20 perms 241534 241643 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 241534 241643 540 2017006522200 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2017006522200)
    (SegSum.cons (w := 180) h241534 (SegSum.cons (w := 360) h241535 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S117
