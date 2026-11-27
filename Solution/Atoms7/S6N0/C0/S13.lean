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

namespace RACert.S6N0.C0.S13

open RACert RACert.Problem

theorem cover7358 : P.CoversSplit 26 10 7358 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7358_0 : P.sumLeaves 26 7534592 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7358) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7358 (by decide)
  decide +kernel

theorem h7358 : P.leaf 36 7358 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7358_0 (.nil)) (by decide) (by decide))

theorem cover7359 : P.CoversSplit 26 10 7359 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7359_0 : P.sumLeaves 26 7535616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7359) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7359 (by decide)
  decide +kernel

theorem h7359 : P.leaf 36 7359 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7359_0 (.nil)) (by decide) (by decide))

theorem cover7368 : P.CoversSplit 26 10 7368 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7368_0 : P.sumLeaves 26 7544832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7368) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7368 (by decide)
  decide +kernel

theorem h7368 : P.leaf 36 7368 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7368_0 (.nil)) (by decide) (by decide))

theorem cover7369 : P.CoversSplit 26 10 7369 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7369_0 : P.sumLeaves 26 7545856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7369) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7369 (by decide)
  decide +kernel

theorem h7369 : P.leaf 36 7369 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7369_0 (.nil)) (by decide) (by decide))

theorem cover7370 : P.CoversSplit 26 10 7370 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7370_0 : P.sumLeaves 26 7546880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7370) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7370 (by decide)
  decide +kernel

theorem h7370 : P.leaf 36 7370 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7370_0 (.nil)) (by decide) (by decide))

theorem cover7371 : P.CoversSplit 26 10 7371 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7371_0 : P.sumLeaves 26 7547904 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7371) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7371 (by decide)
  decide +kernel

theorem h7371 : P.leaf 36 7371 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7371_0 (.nil)) (by decide) (by decide))

theorem cover7374 : P.CoversSplit 26 10 7374 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7374_0 : P.sumLeaves 26 7550976 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7374) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7374 (by decide)
  decide +kernel

theorem h7374 : P.leaf 36 7374 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7374_0 (.nil)) (by decide) (by decide))

theorem cover7375 : P.CoversSplit 26 10 7375 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7375_0 : P.sumLeaves 26 7552000 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7375) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7375 (by decide)
  decide +kernel

theorem h7375 : P.leaf 36 7375 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7375_0 (.nil)) (by decide) (by decide))

theorem cover7386 : P.CoversSplit 26 10 7386 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7386_0 : P.sumLeaves 26 7563264 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7386) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7386 (by decide)
  decide +kernel

theorem h7386 : P.leaf 36 7386 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7386_0 (.nil)) (by decide) (by decide))

theorem cover7387 : P.CoversSplit 26 10 7387 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7387_0 : P.sumLeaves 26 7564288 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7387) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7387 (by decide)
  decide +kernel

theorem h7387 : P.leaf 36 7387 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7387_0 (.nil)) (by decide) (by decide))

theorem cover7388 : P.CoversSplit 26 10 7388 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7388_0 : P.sumLeaves 26 7565312 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7388) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7388 (by decide)
  decide +kernel

theorem h7388 : P.leaf 36 7388 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7388_0 (.nil)) (by decide) (by decide))

theorem cover7389 : P.CoversSplit 26 10 7389 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7389_0 : P.sumLeaves 26 7566336 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7389) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7389 (by decide)
  decide +kernel

theorem h7389 : P.leaf 36 7389 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7389_0 (.nil)) (by decide) (by decide))

theorem cover7390 : P.CoversSplit 26 10 7390 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7390_0 : P.sumLeaves 26 7567360 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7390) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7390 (by decide)
  decide +kernel

theorem h7390 : P.leaf 36 7390 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7390_0 (.nil)) (by decide) (by decide))

theorem cover7391 : P.CoversSplit 26 10 7391 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7391_0 : P.sumLeaves 26 7568384 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7391) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7391 (by decide)
  decide +kernel

theorem h7391 : P.leaf 36 7391 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7391_0 (.nil)) (by decide) (by decide))

theorem cover7422 : P.CoversSplit 26 10 7422 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7422_0 : P.sumLeaves 26 7600128 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7422) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7422 (by decide)
  decide +kernel

theorem h7422 : P.leaf 36 7422 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7422_0 (.nil)) (by decide) (by decide))

theorem cover7423 : P.CoversSplit 26 10 7423 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7423_0 : P.sumLeaves 26 7601152 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7423) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7423 (by decide)
  decide +kernel

theorem h7423 : P.leaf 36 7423 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7423_0 (.nil)) (by decide) (by decide))

theorem cover7571 : P.CoversSplit 26 10 7571 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000400000000000000000000000000000000000000000100000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 489, 530, 538, 629, 636, 922, 930]) (by decide +kernel)

theorem c7571_0 : P.sumLeaves 26 7752704 1024 = 516852 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7571) (lo := 0) (len := 1024) (W := 516852) check rows elimOK (by decide) (by decide) cover7571 (by decide)
  decide +kernel

theorem h7571 : P.leaf 36 7571 = 516852 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 516852)]) (.cons c7571_0 (.nil)) (by decide) (by decide))

theorem cover7572 : P.CoversSplit 26 10 7572 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [537]) (by decide +kernel)

theorem c7572_0 : P.sumLeaves 26 7753728 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7572) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7572 (by decide)
  decide +kernel

theorem h7572 : P.leaf 36 7572 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7572_0 (.nil)) (by decide) (by decide))

theorem cover7573 : P.CoversSplit 26 10 7573 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [537]) (by decide +kernel)

theorem c7573_0 : P.sumLeaves 26 7754752 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7573) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7573 (by decide)
  decide +kernel

theorem h7573 : P.leaf 36 7573 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7573_0 (.nil)) (by decide) (by decide))

theorem cover7575 : P.CoversSplit 26 10 7575 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [537]) (by decide +kernel)

theorem c7575_0 : P.sumLeaves 26 7756800 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7575) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7575 (by decide)
  decide +kernel

theorem h7575 : P.leaf 36 7575 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7575_0 (.nil)) (by decide) (by decide))

theorem cover7580 : P.CoversSplit 26 10 7580 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c7580_0 : P.sumLeaves 26 7761920 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7580) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7580 (by decide)
  decide +kernel

theorem h7580 : P.leaf 36 7580 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7580_0 (.nil)) (by decide) (by decide))

theorem cover7581 : P.CoversSplit 26 10 7581 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c7581_0 : P.sumLeaves 26 7762944 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7581) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7581 (by decide)
  decide +kernel

theorem h7581 : P.leaf 36 7581 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7581_0 (.nil)) (by decide) (by decide))

theorem cover7583 : P.CoversSplit 26 10 7583 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c7583_0 : P.sumLeaves 26 7764992 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7583) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7583 (by decide)
  decide +kernel

theorem h7583 : P.leaf 36 7583 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7583_0 (.nil)) (by decide) (by decide))

theorem cover7588 : P.CoversSplit 26 10 7588 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c7588_0 : P.sumLeaves 26 7770112 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7588) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7588 (by decide)
  decide +kernel

theorem h7588 : P.leaf 36 7588 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7588_0 (.nil)) (by decide) (by decide))

theorem cover7589 : P.CoversSplit 26 10 7589 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c7589_0 : P.sumLeaves 26 7771136 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7589) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7589 (by decide)
  decide +kernel

theorem h7589 : P.leaf 36 7589 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7589_0 (.nil)) (by decide) (by decide))

theorem cover7590 : P.CoversSplit 26 10 7590 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c7590_0 : P.sumLeaves 26 7772160 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7590) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7590 (by decide)
  decide +kernel

theorem h7590 : P.leaf 36 7590 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7590_0 (.nil)) (by decide) (by decide))

theorem cover7591 : P.CoversSplit 26 10 7591 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c7591_0 : P.sumLeaves 26 7773184 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7591) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7591 (by decide)
  decide +kernel

theorem h7591 : P.leaf 36 7591 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7591_0 (.nil)) (by decide) (by decide))

theorem cover7592 : P.CoversSplit 26 10 7592 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7592_0 : P.sumLeaves 26 7774208 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7592) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7592 (by decide)
  decide +kernel

theorem h7592 : P.leaf 36 7592 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7592_0 (.nil)) (by decide) (by decide))

theorem cover7593 : P.CoversSplit 26 10 7593 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7593_0 : P.sumLeaves 26 7775232 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7593) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7593 (by decide)
  decide +kernel

theorem h7593 : P.leaf 36 7593 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7593_0 (.nil)) (by decide) (by decide))

theorem cover7594 : P.CoversSplit 26 10 7594 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7594_0 : P.sumLeaves 26 7776256 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7594) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7594 (by decide)
  decide +kernel

theorem h7594 : P.leaf 36 7594 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7594_0 (.nil)) (by decide) (by decide))

theorem cover7595 : P.CoversSplit 26 10 7595 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7595_0 : P.sumLeaves 26 7777280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7595) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7595 (by decide)
  decide +kernel

theorem h7595 : P.leaf 36 7595 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7595_0 (.nil)) (by decide) (by decide))

theorem cover7596 : P.CoversSplit 26 10 7596 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7596_0 : P.sumLeaves 26 7778304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7596) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7596 (by decide)
  decide +kernel

theorem h7596 : P.leaf 36 7596 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7596_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(7358, 360), (7359, 360), (7368, 180), (7369, 180), (7370, 720), (7371, 720), (7374, 360), (7375, 360), (7386, 360), (7387, 360), (7388, 360), (7389, 360), (7390, 720), (7391, 720), (7422, 180), (7423, 180), (7571, 45), (7572, 360), (7573, 720), (7575, 360), (7580, 180), (7581, 360), (7583, 180), (7588, 360), (7589, 360), (7590, 720), (7591, 720), (7592, 360), (7593, 360), (7594, 720), (7595, 720), (7596, 720)]

theorem segOK : checkSeg 20 perms 7358 7597 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 7358 7597 13725 23258340 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 23258340)
    (SegSum.cons (w := 360) h7358 (SegSum.cons (w := 360) h7359 (SegSum.cons (w := 180) h7368 (SegSum.cons (w := 180) h7369 (SegSum.cons (w := 720) h7370 (SegSum.cons (w := 720) h7371 (SegSum.cons (w := 360) h7374 (SegSum.cons (w := 360) h7375 (SegSum.cons (w := 360) h7386 (SegSum.cons (w := 360) h7387 (SegSum.cons (w := 360) h7388 (SegSum.cons (w := 360) h7389 (SegSum.cons (w := 720) h7390 (SegSum.cons (w := 720) h7391 (SegSum.cons (w := 180) h7422 (SegSum.cons (w := 180) h7423 (SegSum.cons (w := 45) h7571 (SegSum.cons (w := 360) h7572 (SegSum.cons (w := 720) h7573 (SegSum.cons (w := 360) h7575 (SegSum.cons (w := 180) h7580 (SegSum.cons (w := 360) h7581 (SegSum.cons (w := 180) h7583 (SegSum.cons (w := 360) h7588 (SegSum.cons (w := 360) h7589 (SegSum.cons (w := 720) h7590 (SegSum.cons (w := 720) h7591 (SegSum.cons (w := 360) h7592 (SegSum.cons (w := 360) h7593 (SegSum.cons (w := 720) h7594 (SegSum.cons (w := 720) h7595 (SegSum.cons (w := 720) h7596 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S13
