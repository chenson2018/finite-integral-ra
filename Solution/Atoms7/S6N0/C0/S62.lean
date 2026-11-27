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

namespace RACert.S6N0.C0.S62

open RACert RACert.Problem

theorem cover89559 : P.CoversSplit 26 10 89559 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89559_0 : P.sumLeaves 26 91708416 1024 = 5504977 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89559) (lo := 0) (len := 1024) (W := 5504977) check rows elimOK (by decide) (by decide) cover89559 (by decide)
  decide +kernel

theorem h89559 : P.leaf 36 89559 = 5504977 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5504977)]) (.cons c89559_0 (.nil)) (by decide) (by decide))

theorem cover89564 : P.CoversSplit 26 10 89564 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89564_0 : P.sumLeaves 26 91713536 1024 = 4869108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89564) (lo := 0) (len := 1024) (W := 4869108) check rows elimOK (by decide) (by decide) cover89564 (by decide)
  decide +kernel

theorem h89564 : P.leaf 36 89564 = 4869108 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4869108)]) (.cons c89564_0 (.nil)) (by decide) (by decide))

theorem cover89565 : P.CoversSplit 26 10 89565 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89565_0 : P.sumLeaves 26 91714560 1024 = 6104773 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89565) (lo := 0) (len := 1024) (W := 6104773) check rows elimOK (by decide) (by decide) cover89565 (by decide)
  decide +kernel

theorem h89565 : P.leaf 36 89565 = 6104773 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6104773)]) (.cons c89565_0 (.nil)) (by decide) (by decide))

theorem cover89567 : P.CoversSplit 26 10 89567 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89567_0 : P.sumLeaves 26 91716608 1024 = 8011129 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89567) (lo := 0) (len := 1024) (W := 8011129) check rows elimOK (by decide) (by decide) cover89567 (by decide)
  decide +kernel

theorem h89567 : P.leaf 36 89567 = 8011129 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8011129)]) (.cons c89567_0 (.nil)) (by decide) (by decide))

theorem cover89580 : P.CoversSplit 26 10 89580 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89580_0 : P.sumLeaves 26 91729920 1024 = 7114308 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89580) (lo := 0) (len := 1024) (W := 7114308) check rows elimOK (by decide) (by decide) cover89580 (by decide)
  decide +kernel

theorem h89580 : P.leaf 36 89580 = 7114308 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7114308)]) (.cons c89580_0 (.nil)) (by decide) (by decide))

theorem cover89581 : P.CoversSplit 26 10 89581 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89581_0 : P.sumLeaves 26 91730944 1024 = 7246938 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89581) (lo := 0) (len := 1024) (W := 7246938) check rows elimOK (by decide) (by decide) cover89581 (by decide)
  decide +kernel

theorem h89581 : P.leaf 36 89581 = 7246938 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7246938)]) (.cons c89581_0 (.nil)) (by decide) (by decide))

theorem cover89582 : P.CoversSplit 26 10 89582 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89582_0 : P.sumLeaves 26 91731968 1024 = 8130078 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89582) (lo := 0) (len := 1024) (W := 8130078) check rows elimOK (by decide) (by decide) cover89582 (by decide)
  decide +kernel

theorem h89582 : P.leaf 36 89582 = 8130078 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8130078)]) (.cons c89582_0 (.nil)) (by decide) (by decide))

theorem cover89583 : P.CoversSplit 26 10 89583 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89583_0 : P.sumLeaves 26 91732992 1024 = 8439249 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89583) (lo := 0) (len := 1024) (W := 8439249) check rows elimOK (by decide) (by decide) cover89583 (by decide)
  decide +kernel

theorem h89583 : P.leaf 36 89583 = 8439249 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8439249)]) (.cons c89583_0 (.nil)) (by decide) (by decide))

theorem cover89598 : P.CoversSplit 26 10 89598 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89598_0 : P.sumLeaves 26 91748352 1024 = 10934084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89598) (lo := 0) (len := 1024) (W := 10934084) check rows elimOK (by decide) (by decide) cover89598 (by decide)
  decide +kernel

theorem h89598 : P.leaf 36 89598 = 10934084 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10934084)]) (.cons c89598_0 (.nil)) (by decide) (by decide))

theorem cover89599 : P.CoversSplit 26 10 89599 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89599_0 : P.sumLeaves 26 91749376 1024 = 11570142 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89599) (lo := 0) (len := 1024) (W := 11570142) check rows elimOK (by decide) (by decide) cover89599 (by decide)
  decide +kernel

theorem h89599 : P.leaf 36 89599 = 11570142 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11570142)]) (.cons c89599_0 (.nil)) (by decide) (by decide))

theorem cover89726 : P.CoversSplit 26 10 89726 0xfffffffffffcfaf800000000000000000000000000000000000000000f0c0a080f0f0a0a0f0c0a080f0f0a0a0f0c0a080000000000000000000000000f0c0a0800000000ffccfac8000000000000000000000000ffccfac8000000000f0c0a080000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 587, 874, 979, 1315, 1658, 1665]) (by decide +kernel)

noncomputable def f89726 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91879424 + i)

theorem c89726_0 : rowSum f89726 0 1024 = 40706472 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89726) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89726 (by decide)
  decide +kernel

theorem sum89726 : rowSum f89726 0 1024 = 40706472 :=
  c89726_0

theorem h89726 : P.leaf 36 89726 = 40706472 :=
  leaf_weighted (k := 26) (d := 10) (H := 89726) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 89726) (by decide) (by decide +kernel)) sum89726

theorem cover89727 : P.CoversSplit 26 10 89727 0xfffffffffffcfaf800000000000000000000000000000000000000000f0c0a080f0f0a0a0f0c0a080f0f0a0a0f0c0a080000000000000000000000000f0c0a0800000000ffccfac8000000000000000000000000ffccfac8000000000f0c0a08000000000f0c0a08000000000f0c0a08000000000f0c0a08000000000f0c0a08 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 587, 979, 1315, 1658, 1665]) (by decide +kernel)

noncomputable def f89727 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91880448 + i)

theorem c89727_0 : rowSum f89727 0 988 = 48844996 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89727) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89727 (by decide)
  decide +kernel

theorem c89727_1 : rowSum f89727 988 36 = 24389200 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89727) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89727 (by decide)
  decide +kernel

theorem sum89727 : rowSum f89727 0 1024 = 73234196 :=
  rowSum_append (F := f89727) (lo := 0) (n := 988) (m := 36) (A := 48844996) (B := 24389200) c89727_0 (c89727_1)

theorem h89727 : P.leaf 36 89727 = 73234196 :=
  leaf_weighted (k := 26) (d := 10) (H := 89727) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 89727) (by decide) (by decide +kernel)) sum89727

theorem cover89812 : P.CoversSplit 26 10 89812 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 874, 922, 923, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89812_0 : P.sumLeaves 26 91967488 704 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89812) (lo := 0) (len := 704) (W := 0) check rows elimOK (by decide) (by decide) cover89812 (by decide)
  decide +kernel

theorem contract89812_1 : P.leaf 32 1437003 = 10336 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1437003) (ss := [(7, 1, 475), (2, 1, 482), (4, 1, 580), (3, 1, 409), (11, 1, 459), (29, 1, 587), (12, 1, 929), (13, 1, 461), (31, 1, 979), (28, 0, 1315), (30, 0, 1315), (26, 1, 481), (21, 1, 1658), (9, 1, 573), (20, 1, 1609)]) (ids := [3, 4, 6, 8, 12, 13, 14, 15, 16, 17, 20, 22, 23, 30, 31, 21, 25]) (cs := [1, 1, 1, 2, 3, 1, 4, 1, 5, 1, 1, 1, 6, 7, 8, 9, 10, 11, 1, 1, 12, 17, 13, 14, 1, 18, 0, 1, 0, 1, 15, 16]) (bs := [15, 2]) (W := 10336) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c89812_1 : P.sumLeaves 26 91968192 64 = 10336 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1437003) rows (by decide) (by decide)).symm.trans contract89812_1

theorem c89812_2 : P.sumLeaves 26 91968256 256 = 683776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89812) (lo := 768) (len := 256) (W := 683776) check rows elimOK (by decide) (by decide) cover89812 (by decide)
  decide +kernel

theorem h89812 : P.leaf 36 89812 = 694112 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(704, 0), (64, 10336), (256, 683776)]) (.cons c89812_0 (.cons c89812_1 (.cons c89812_2 (.nil)))) (by decide) (by decide))

theorem cover89813 : P.CoversSplit 26 10 89813 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 922, 923, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89813_0 : P.sumLeaves 26 91968512 1024 = 6571223 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89813) (lo := 0) (len := 1024) (W := 6571223) check rows elimOK (by decide) (by decide) cover89813 (by decide)
  decide +kernel

theorem h89813 : P.leaf 36 89813 = 6571223 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6571223)]) (.cons c89813_0 (.nil)) (by decide) (by decide))

theorem cover89814 : P.CoversSplit 26 10 89814 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000003300010000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 874, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89814_0 : P.sumLeaves 26 91969536 1024 = 13537989 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89814) (lo := 0) (len := 1024) (W := 13537989) check rows elimOK (by decide) (by decide) cover89814 (by decide)
  decide +kernel

theorem h89814 : P.leaf 36 89814 = 13537989 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13537989)]) (.cons c89814_0 (.nil)) (by decide) (by decide))

theorem cover89815 : P.CoversSplit 26 10 89815 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000003300010000000000330000000000000000000000000000000000000000000000010001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89815_0 : P.sumLeaves 26 91970560 1024 = 28272573 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89815) (lo := 0) (len := 1024) (W := 28272573) check rows elimOK (by decide) (by decide) cover89815 (by decide)
  decide +kernel

theorem h89815 : P.leaf 36 89815 = 28272573 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28272573)]) (.cons c89815_0 (.nil)) (by decide) (by decide))

theorem cover89818 : P.CoversSplit 26 10 89818 0xa0a00000a0a00000a0a00000a0a0000000000000000000000000000020200000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000020000000000000002000000000000000200000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 587, 874, 972, 979, 1315, 1665]) (by decide +kernel)

theorem c89818_0 : P.sumLeaves 26 91973632 1024 = 7346364 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89818) (lo := 0) (len := 1024) (W := 7346364) check rows elimOK (by decide) (by decide) cover89818 (by decide)
  decide +kernel

theorem h89818 : P.leaf 36 89818 = 7346364 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7346364)]) (.cons c89818_0 (.nil)) (by decide) (by decide))

theorem cover89819 : P.CoversSplit 26 10 89819 0xa0a00000a0a00000a0a00000a0a0000000000000000000000000000020200000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000020000000000000002000000000000000200000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 587, 972, 979, 1315, 1665]) (by decide +kernel)

theorem c89819_0 : P.sumLeaves 26 91974656 1024 = 27732640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89819) (lo := 0) (len := 1024) (W := 27732640) check rows elimOK (by decide) (by decide) cover89819 (by decide)
  decide +kernel

theorem h89819 : P.leaf 36 89819 = 27732640 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 27732640)]) (.cons c89819_0 (.nil)) (by decide) (by decide))

theorem cover89820 : P.CoversSplit 26 10 89820 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000050505050504050400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 874, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89820_0 : P.sumLeaves 26 91975680 1024 = 20914803 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89820) (lo := 0) (len := 1024) (W := 20914803) check rows elimOK (by decide) (by decide) cover89820 (by decide)
  decide +kernel

theorem h89820 : P.leaf 36 89820 = 20914803 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20914803)]) (.cons c89820_0 (.nil)) (by decide) (by decide))

theorem cover89821 : P.CoversSplit 26 10 89821 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000050505050504050400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89821_0 : P.sumLeaves 26 91976704 1024 = 48314406 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89821) (lo := 0) (len := 1024) (W := 48314406) check rows elimOK (by decide) (by decide) cover89821 (by decide)
  decide +kernel

theorem h89821 : P.leaf 36 89821 = 48314406 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 48314406)]) (.cons c89821_0 (.nil)) (by decide) (by decide))

theorem cover89822 : P.CoversSplit 26 10 89822 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000050505050504050400000000000000000000000000000000000000000000000000000000330001000000000033000100000000003300010000000000300000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89822_0 : P.sumLeaves 26 91977728 1020 = 60696676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89822) (lo := 0) (len := 1020) (W := 60696676) check rows elimOK (by decide) (by decide) cover89822 (by decide)
  decide +kernel

theorem c89822_1 : P.sumLeaves 26 91978748 4 = 8192360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89822) (lo := 1020) (len := 4) (W := 8192360) check rows elimOK (by decide) (by decide) cover89822 (by decide)
  decide +kernel

theorem h89822 : P.leaf 36 89822 = 68889036 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1020, 60696676), (4, 8192360)]) (.cons c89822_0 (.cons c89822_1 (.nil))) (by decide) (by decide))

theorem cover89823 : P.CoversSplit 26 10 89823 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000050505050504050400000000000000000000000000000000000000000000000000000000330001000000000033000100000000003300010000000000300000000000000001000100000000000000000000000000010001000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89823_0 : P.sumLeaves 26 91978752 1016 = 114250005 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89823) (lo := 0) (len := 1016) (W := 114250005) check rows elimOK (by decide) (by decide) cover89823 (by decide)
  decide +kernel

theorem c89823_1 : P.sumLeaves 26 91979768 8 = 22929276 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89823) (lo := 1016) (len := 8) (W := 22929276) check rows elimOK (by decide) (by decide) cover89823 (by decide)
  decide +kernel

theorem h89823 : P.leaf 36 89823 = 137179281 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1016, 114250005), (8, 22929276)]) (.cons c89823_0 (.cons c89823_1 (.nil))) (by decide) (by decide))

theorem cover89829 : P.CoversSplit 26 10 89829 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 922, 923, 972, 979, 1266, 1315]) (by decide +kernel)

theorem c89829_0 : P.sumLeaves 26 91984896 1024 = 3146904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89829) (lo := 0) (len := 1024) (W := 3146904) check rows elimOK (by decide) (by decide) cover89829 (by decide)
  decide +kernel

theorem h89829 : P.leaf 36 89829 = 3146904 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3146904)]) (.cons c89829_0 (.nil)) (by decide) (by decide))

theorem cover89830 : P.CoversSplit 26 10 89830 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000330030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 524, 587, 874, 922, 972, 979, 1266, 1315]) (by decide +kernel)

theorem c89830_0 : P.sumLeaves 26 91985920 1024 = 15411503 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89830) (lo := 0) (len := 1024) (W := 15411503) check rows elimOK (by decide) (by decide) cover89830 (by decide)
  decide +kernel

theorem h89830 : P.leaf 36 89830 = 15411503 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15411503)]) (.cons c89830_0 (.nil)) (by decide) (by decide))

theorem cover89831 : P.CoversSplit 26 10 89831 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000330030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 922, 972, 979, 1266, 1315]) (by decide +kernel)

theorem c89831_0 : P.sumLeaves 26 91986944 1024 = 25516864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89831) (lo := 0) (len := 1024) (W := 25516864) check rows elimOK (by decide) (by decide) cover89831 (by decide)
  decide +kernel

theorem h89831 : P.leaf 36 89831 = 25516864 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 25516864)]) (.cons c89831_0 (.nil)) (by decide) (by decide))

theorem cover89834 : P.CoversSplit 26 10 89834 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300030000000000030003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 524, 874, 972, 979, 1266, 1665]) (by decide +kernel)

theorem c89834_0 : P.sumLeaves 26 91990016 1024 = 28594340 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89834) (lo := 0) (len := 1024) (W := 28594340) check rows elimOK (by decide) (by decide) cover89834 (by decide)
  decide +kernel

theorem h89834 : P.leaf 36 89834 = 28594340 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28594340)]) (.cons c89834_0 (.nil)) (by decide) (by decide))

theorem cover89835 : P.CoversSplit 26 10 89835 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000030303000000000000000000000000000000000000000000000000000000000000000000000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1266, 1322, 1658, 1665]) (by decide +kernel)

theorem c89835_0 : P.sumLeaves 26 91991040 1024 = 66533892 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89835) (lo := 0) (len := 1024) (W := 66533892) check rows elimOK (by decide) (by decide) cover89835 (by decide)
  decide +kernel

theorem h89835 : P.leaf 36 89835 = 66533892 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 66533892)]) (.cons c89835_0 (.nil)) (by decide) (by decide))

theorem cover89836 : P.CoversSplit 26 10 89836 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [524, 874, 922, 923, 972, 979, 1266, 1315]) (by decide +kernel)

theorem c89836_0 : P.sumLeaves 26 91992064 1008 = 8443944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89836) (lo := 0) (len := 1008) (W := 8443944) check rows elimOK (by decide) (by decide) cover89836 (by decide)
  decide +kernel

theorem c89836_1 : P.sumLeaves 26 91993072 16 = 3718752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89836) (lo := 1008) (len := 16) (W := 3718752) check rows elimOK (by decide) (by decide) cover89836 (by decide)
  decide +kernel

theorem h89836 : P.leaf 36 89836 = 12162696 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1008, 8443944), (16, 3718752)]) (.cons c89836_0 (.cons c89836_1 (.nil))) (by decide) (by decide))

theorem cover89837 : P.CoversSplit 26 10 89837 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000030303000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89837_0 : P.sumLeaves 26 91993088 1002 = 16336104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89837) (lo := 0) (len := 1002) (W := 16336104) check rows elimOK (by decide) (by decide) cover89837 (by decide)
  decide +kernel

theorem c89837_1 : P.sumLeaves 26 91994090 22 = 7351616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89837) (lo := 1002) (len := 22) (W := 7351616) check rows elimOK (by decide) (by decide) cover89837 (by decide)
  decide +kernel

theorem h89837 : P.leaf 36 89837 = 23687720 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1002, 16336104), (22, 7351616)]) (.cons c89837_0 (.cons c89837_1 (.nil))) (by decide) (by decide))

theorem cover89838 : P.CoversSplit 26 10 89838 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000330032000000000033003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [524, 874, 922, 972, 979, 1266, 1315, 1665]) (by decide +kernel)

theorem c89838_0 : P.sumLeaves 26 91994112 994 = 48087297 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89838) (lo := 0) (len := 994) (W := 48087297) check rows elimOK (by decide) (by decide) cover89838 (by decide)
  decide +kernel

theorem c89838_1 : P.sumLeaves 26 91995106 30 = 35888600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89838) (lo := 994) (len := 30) (W := 35888600) check rows elimOK (by decide) (by decide) cover89838 (by decide)
  decide +kernel

theorem h89838 : P.leaf 36 89838 = 83975897 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(994, 48087297), (30, 35888600)]) (.cons c89838_0 (.cons c89838_1 (.nil))) (by decide) (by decide))

theorem cover89839 : P.CoversSplit 26 10 89839 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000030303000000000000000000000000000000000000000000000000000000000000000000000000000330032000000000033003200000000003300320000000000300030000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89839_0 : P.sumLeaves 26 91995136 975 = 70518694 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89839) (lo := 0) (len := 975) (W := 70518694) check rows elimOK (by decide) (by decide) cover89839 (by decide)
  decide +kernel

theorem c89839_1 : P.sumLeaves 26 91996111 49 = 74466197 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89839) (lo := 975) (len := 49) (W := 74466197) check rows elimOK (by decide) (by decide) cover89839 (by decide)
  decide +kernel

theorem h89839 : P.leaf 36 89839 = 144984891 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(975, 70518694), (49, 74466197)]) (.cons c89839_0 (.cons c89839_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(89559, 90), (89564, 360), (89565, 720), (89567, 360), (89580, 360), (89581, 360), (89582, 720), (89583, 720), (89598, 360), (89599, 360), (89726, 120), (89727, 120), (89812, 720), (89813, 720), (89814, 720), (89815, 720), (89818, 720), (89819, 720), (89820, 720), (89821, 720), (89822, 720), (89823, 720), (89829, 360), (89830, 720), (89831, 720), (89834, 720), (89835, 720), (89836, 720), (89837, 720), (89838, 720), (89839, 720)]

theorem segOK : checkSeg 20 perms 89559 89844 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 89559 89844 17970 596965586370 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 596965586370)
    (SegSum.cons (w := 90) h89559 (SegSum.cons (w := 360) h89564 (SegSum.cons (w := 720) h89565 (SegSum.cons (w := 360) h89567 (SegSum.cons (w := 360) h89580 (SegSum.cons (w := 360) h89581 (SegSum.cons (w := 720) h89582 (SegSum.cons (w := 720) h89583 (SegSum.cons (w := 360) h89598 (SegSum.cons (w := 360) h89599 (SegSum.cons (w := 120) h89726 (SegSum.cons (w := 120) h89727 (SegSum.cons (w := 720) h89812 (SegSum.cons (w := 720) h89813 (SegSum.cons (w := 720) h89814 (SegSum.cons (w := 720) h89815 (SegSum.cons (w := 720) h89818 (SegSum.cons (w := 720) h89819 (SegSum.cons (w := 720) h89820 (SegSum.cons (w := 720) h89821 (SegSum.cons (w := 720) h89822 (SegSum.cons (w := 720) h89823 (SegSum.cons (w := 360) h89829 (SegSum.cons (w := 720) h89830 (SegSum.cons (w := 720) h89831 (SegSum.cons (w := 720) h89834 (SegSum.cons (w := 720) h89835 (SegSum.cons (w := 720) h89836 (SegSum.cons (w := 720) h89837 (SegSum.cons (w := 720) h89838 (SegSum.cons (w := 720) h89839 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S62
