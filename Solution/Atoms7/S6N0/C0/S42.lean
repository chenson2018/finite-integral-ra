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

namespace RACert.S6N0.C0.S42

open RACert RACert.Problem

theorem cover76983 : P.CoversSplit 26 10 76983 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000cc00cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300330000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 881, 972, 1315, 1658, 2008]) (by decide +kernel)

theorem c76983_0 : P.sumLeaves 26 78830592 1024 = 52390304 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 76983) (lo := 0) (len := 1024) (W := 52390304) check rows elimOK (by decide) (by decide) cover76983 (by decide)
  decide +kernel

theorem h76983 : P.leaf 36 76983 = 52390304 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 52390304)]) (.cons c76983_0 (.nil)) (by decide) (by decide))

theorem cover76984 : P.CoversSplit 26 10 76984 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100210000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 538, 587, 629, 636, 881, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c76984_0 : P.sumLeaves 26 78831616 1024 = 23983 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 76984) (lo := 0) (len := 1024) (W := 23983) check rows elimOK (by decide) (by decide) cover76984 (by decide)
  decide +kernel

theorem h76984 : P.leaf 36 76984 = 23983 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23983)]) (.cons c76984_0 (.nil)) (by decide) (by decide))

theorem cover76985 : P.CoversSplit 26 10 76985 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100210000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 538, 587, 629, 636, 881, 972, 1315, 1658]) (by decide +kernel)

theorem c76985_0 : P.sumLeaves 26 78832640 1024 = 30223 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 76985) (lo := 0) (len := 1024) (W := 30223) check rows elimOK (by decide) (by decide) cover76985 (by decide)
  decide +kernel

theorem h76985 : P.leaf 36 76985 = 30223 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 30223)]) (.cons c76985_0 (.nil)) (by decide) (by decide))

theorem cover76987 : P.CoversSplit 26 10 76987 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100210000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 538, 587, 629, 636, 881, 972, 1315, 1658]) (by decide +kernel)

theorem c76987_0 : P.sumLeaves 26 78834688 1024 = 43049 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 76987) (lo := 0) (len := 1024) (W := 43049) check rows elimOK (by decide) (by decide) cover76987 (by decide)
  decide +kernel

theorem h76987 : P.leaf 36 76987 = 43049 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 43049)]) (.cons c76987_0 (.nil)) (by decide) (by decide))

theorem cover76991 : P.CoversSplit 26 10 76991 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100210000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 587, 629, 636, 881, 972, 1315, 1658]) (by decide +kernel)

theorem c76991_0 : P.sumLeaves 26 78838784 1024 = 65523 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 76991) (lo := 0) (len := 1024) (W := 65523) check rows elimOK (by decide) (by decide) cover76991 (by decide)
  decide +kernel

theorem h76991 : P.leaf 36 76991 = 65523 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 65523)]) (.cons c76991_0 (.nil)) (by decide) (by decide))

theorem cover77000 : P.CoversSplit 26 10 77000 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 481, 482, 530, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77000_0 : P.sumLeaves 26 78848000 1024 = 64 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77000) (lo := 0) (len := 1024) (W := 64) check rows elimOK (by decide) (by decide) cover77000 (by decide)
  decide +kernel

theorem h77000 : P.leaf 36 77000 = 64 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 64)]) (.cons c77000_0 (.nil)) (by decide) (by decide))

theorem cover77001 : P.CoversSplit 26 10 77001 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 481, 482, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77001_0 : P.sumLeaves 26 78849024 1024 = 1024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77001) (lo := 0) (len := 1024) (W := 1024) check rows elimOK (by decide) (by decide) cover77001 (by decide)
  decide +kernel

theorem h77001 : P.leaf 36 77001 = 1024 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1024)]) (.cons c77001_0 (.nil)) (by decide) (by decide))

theorem cover77002 : P.CoversSplit 26 10 77002 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 524, 530, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77002_0 : P.sumLeaves 26 78850048 1024 = 512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77002) (lo := 0) (len := 1024) (W := 512) check rows elimOK (by decide) (by decide) cover77002 (by decide)
  decide +kernel

theorem h77002 : P.leaf 36 77002 = 512 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 512)]) (.cons c77002_0 (.nil)) (by decide) (by decide))

theorem cover77003 : P.CoversSplit 26 10 77003 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 524, 530, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77003_0 : P.sumLeaves 26 78851072 1024 = 4096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77003) (lo := 0) (len := 1024) (W := 4096) check rows elimOK (by decide) (by decide) cover77003 (by decide)
  decide +kernel

theorem h77003 : P.leaf 36 77003 = 4096 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4096)]) (.cons c77003_0 (.nil)) (by decide) (by decide))

theorem cover77006 : P.CoversSplit 26 10 77006 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 524, 530, 531, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77006_0 : P.sumLeaves 26 78854144 1024 = 2352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77006) (lo := 0) (len := 1024) (W := 2352) check rows elimOK (by decide) (by decide) cover77006 (by decide)
  decide +kernel

theorem h77006 : P.leaf 36 77006 = 2352 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2352)]) (.cons c77006_0 (.nil)) (by decide) (by decide))

theorem cover77007 : P.CoversSplit 26 10 77007 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 524, 530, 531, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77007_0 : P.sumLeaves 26 78855168 1024 = 25952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77007) (lo := 0) (len := 1024) (W := 25952) check rows elimOK (by decide) (by decide) cover77007 (by decide)
  decide +kernel

theorem h77007 : P.leaf 36 77007 = 25952 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 25952)]) (.cons c77007_0 (.nil)) (by decide) (by decide))

theorem cover77018 : P.CoversSplit 26 10 77018 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 530, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77018_0 : P.sumLeaves 26 78866432 1024 = 8192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77018) (lo := 0) (len := 1024) (W := 8192) check rows elimOK (by decide) (by decide) cover77018 (by decide)
  decide +kernel

theorem h77018 : P.leaf 36 77018 = 8192 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8192)]) (.cons c77018_0 (.nil)) (by decide) (by decide))

theorem cover77019 : P.CoversSplit 26 10 77019 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77019_0 : P.sumLeaves 26 78867456 1024 = 32768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77019) (lo := 0) (len := 1024) (W := 32768) check rows elimOK (by decide) (by decide) cover77019 (by decide)
  decide +kernel

theorem h77019 : P.leaf 36 77019 = 32768 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 32768)]) (.cons c77019_0 (.nil)) (by decide) (by decide))

theorem cover77020 : P.CoversSplit 26 10 77020 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 475, 530, 531, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77020_0 : P.sumLeaves 26 78868480 1024 = 6656 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77020) (lo := 0) (len := 1024) (W := 6656) check rows elimOK (by decide) (by decide) cover77020 (by decide)
  decide +kernel

theorem h77020 : P.leaf 36 77020 = 6656 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6656)]) (.cons c77020_0 (.nil)) (by decide) (by decide))

theorem cover77021 : P.CoversSplit 26 10 77021 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 475, 530, 531, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77021_0 : P.sumLeaves 26 78869504 1024 = 24064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77021) (lo := 0) (len := 1024) (W := 24064) check rows elimOK (by decide) (by decide) cover77021 (by decide)
  decide +kernel

theorem h77021 : P.leaf 36 77021 = 24064 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 24064)]) (.cons c77021_0 (.nil)) (by decide) (by decide))

theorem cover77022 : P.CoversSplit 26 10 77022 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77022_0 : P.sumLeaves 26 78870528 1024 = 21504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77022) (lo := 0) (len := 1024) (W := 21504) check rows elimOK (by decide) (by decide) cover77022 (by decide)
  decide +kernel

theorem h77022 : P.leaf 36 77022 = 21504 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 21504)]) (.cons c77022_0 (.nil)) (by decide) (by decide))

theorem cover77023 : P.CoversSplit 26 10 77023 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77023_0 : P.sumLeaves 26 78871552 1024 = 88256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77023) (lo := 0) (len := 1024) (W := 88256) check rows elimOK (by decide) (by decide) cover77023 (by decide)
  decide +kernel

theorem h77023 : P.leaf 36 77023 = 88256 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 88256)]) (.cons c77023_0 (.nil)) (by decide) (by decide))

theorem cover77054 : P.CoversSplit 26 10 77054 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 881, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77054_0 : P.sumLeaves 26 78903296 1024 = 66376 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77054) (lo := 0) (len := 1024) (W := 66376) check rows elimOK (by decide) (by decide) cover77054 (by decide)
  decide +kernel

theorem h77054 : P.leaf 36 77054 = 66376 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 66376)]) (.cons c77054_0 (.nil)) (by decide) (by decide))

theorem cover77055 : P.CoversSplit 26 10 77055 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 881, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77055_0 : P.sumLeaves 26 78904320 1024 = 264640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77055) (lo := 0) (len := 1024) (W := 264640) check rows elimOK (by decide) (by decide) cover77055 (by decide)
  decide +kernel

theorem h77055 : P.leaf 36 77055 = 264640 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 264640)]) (.cons c77055_0 (.nil)) (by decide) (by decide))

theorem cover77128 : P.CoversSplit 26 10 77128 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000500000000000000000000000000000000000000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 530, 579, 629, 636, 972, 979, 1322, 1665]) (by decide +kernel)

theorem c77128_0 : P.sumLeaves 26 78979072 1024 = 23983 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77128) (lo := 0) (len := 1024) (W := 23983) check rows elimOK (by decide) (by decide) cover77128 (by decide)
  decide +kernel

theorem h77128 : P.leaf 36 77128 = 23983 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23983)]) (.cons c77128_0 (.nil)) (by decide) (by decide))

theorem cover77129 : P.CoversSplit 26 10 77129 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 482, 530, 579, 629, 636, 972, 979, 1322, 1665]) (by decide +kernel)

theorem c77129_0 : P.sumLeaves 26 78980096 1024 = 1024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77129) (lo := 0) (len := 1024) (W := 1024) check rows elimOK (by decide) (by decide) cover77129 (by decide)
  decide +kernel

theorem h77129 : P.leaf 36 77129 = 1024 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1024)]) (.cons c77129_0 (.nil)) (by decide) (by decide))

theorem cover77131 : P.CoversSplit 26 10 77131 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 523, 530, 579, 629, 636, 972, 979, 1322, 1665]) (by decide +kernel)

theorem c77131_0 : P.sumLeaves 26 78982144 1024 = 8192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77131) (lo := 0) (len := 1024) (W := 8192) check rows elimOK (by decide) (by decide) cover77131 (by decide)
  decide +kernel

theorem h77131 : P.leaf 36 77131 = 8192 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8192)]) (.cons c77131_0 (.nil)) (by decide) (by decide))

theorem cover77132 : P.CoversSplit 26 10 77132 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77132_0 : P.sumLeaves 26 78983168 1024 = 848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77132) (lo := 0) (len := 1024) (W := 848) check rows elimOK (by decide) (by decide) cover77132 (by decide)
  decide +kernel

theorem h77132 : P.leaf 36 77132 = 848 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 848)]) (.cons c77132_0 (.nil)) (by decide) (by decide))

theorem cover77133 : P.CoversSplit 26 10 77133 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77133_0 : P.sumLeaves 26 78984192 1024 = 9656 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77133) (lo := 0) (len := 1024) (W := 9656) check rows elimOK (by decide) (by decide) cover77133 (by decide)
  decide +kernel

theorem h77133 : P.leaf 36 77133 = 9656 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9656)]) (.cons c77133_0 (.nil)) (by decide) (by decide))

theorem cover77135 : P.CoversSplit 26 10 77135 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77135_0 : P.sumLeaves 26 78986240 1024 = 101656 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77135) (lo := 0) (len := 1024) (W := 101656) check rows elimOK (by decide) (by decide) cover77135 (by decide)
  decide +kernel

theorem h77135 : P.leaf 36 77135 = 101656 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 101656)]) (.cons c77135_0 (.nil)) (by decide) (by decide))

theorem cover77147 : P.CoversSplit 26 10 77147 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000500000000000000000000000000000000000000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 530, 579, 629, 636, 972, 979, 1322, 1665]) (by decide +kernel)

theorem c77147_0 : P.sumLeaves 26 78998528 1024 = 68768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77147) (lo := 0) (len := 1024) (W := 68768) check rows elimOK (by decide) (by decide) cover77147 (by decide)
  decide +kernel

theorem h77147 : P.leaf 36 77147 = 68768 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 68768)]) (.cons c77147_0 (.nil)) (by decide) (by decide))

theorem cover77148 : P.CoversSplit 26 10 77148 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77148_0 : P.sumLeaves 26 78999552 1024 = 13120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77148) (lo := 0) (len := 1024) (W := 13120) check rows elimOK (by decide) (by decide) cover77148 (by decide)
  decide +kernel

theorem h77148 : P.leaf 36 77148 = 13120 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13120)]) (.cons c77148_0 (.nil)) (by decide) (by decide))

theorem cover77149 : P.CoversSplit 26 10 77149 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77149_0 : P.sumLeaves 26 79000576 1024 = 96184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77149) (lo := 0) (len := 1024) (W := 96184) check rows elimOK (by decide) (by decide) cover77149 (by decide)
  decide +kernel

theorem h77149 : P.leaf 36 77149 = 96184 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 96184)]) (.cons c77149_0 (.nil)) (by decide) (by decide))

theorem cover77151 : P.CoversSplit 26 10 77151 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77151_0 : P.sumLeaves 26 79002624 1024 = 630212 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77151) (lo := 0) (len := 1024) (W := 630212) check rows elimOK (by decide) (by decide) cover77151 (by decide)
  decide +kernel

theorem h77151 : P.leaf 36 77151 = 630212 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 630212)]) (.cons c77151_0 (.nil)) (by decide) (by decide))

theorem cover77164 : P.CoversSplit 26 10 77164 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77164_0 : P.sumLeaves 26 79015936 1024 = 6784 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77164) (lo := 0) (len := 1024) (W := 6784) check rows elimOK (by decide) (by decide) cover77164 (by decide)
  decide +kernel

theorem h77164 : P.leaf 36 77164 = 6784 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6784)]) (.cons c77164_0 (.nil)) (by decide) (by decide))

theorem cover77165 : P.CoversSplit 26 10 77165 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77165_0 : P.sumLeaves 26 79016960 1024 = 34712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77165) (lo := 0) (len := 1024) (W := 34712) check rows elimOK (by decide) (by decide) cover77165 (by decide)
  decide +kernel

theorem h77165 : P.leaf 36 77165 = 34712 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34712)]) (.cons c77165_0 (.nil)) (by decide) (by decide))

theorem cover77166 : P.CoversSplit 26 10 77166 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77166_0 : P.sumLeaves 26 79017984 1024 = 75888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77166) (lo := 0) (len := 1024) (W := 75888) check rows elimOK (by decide) (by decide) cover77166 (by decide)
  decide +kernel

theorem h77166 : P.leaf 36 77166 = 75888 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 75888)]) (.cons c77166_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(76983, 6), (76984, 60), (76985, 180), (76987, 180), (76991, 60), (77000, 180), (77001, 180), (77002, 720), (77003, 720), (77006, 360), (77007, 360), (77018, 360), (77019, 360), (77020, 360), (77021, 360), (77022, 720), (77023, 720), (77054, 180), (77055, 180), (77128, 60), (77129, 360), (77131, 360), (77132, 360), (77133, 720), (77135, 360), (77147, 120), (77148, 360), (77149, 720), (77151, 360), (77164, 360), (77165, 360), (77166, 720)]

theorem segOK : checkSeg 20 perms 76983 77167 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 76983 77167 11466 938311644 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 938311644)
    (SegSum.cons (w := 6) h76983 (SegSum.cons (w := 60) h76984 (SegSum.cons (w := 180) h76985 (SegSum.cons (w := 180) h76987 (SegSum.cons (w := 60) h76991 (SegSum.cons (w := 180) h77000 (SegSum.cons (w := 180) h77001 (SegSum.cons (w := 720) h77002 (SegSum.cons (w := 720) h77003 (SegSum.cons (w := 360) h77006 (SegSum.cons (w := 360) h77007 (SegSum.cons (w := 360) h77018 (SegSum.cons (w := 360) h77019 (SegSum.cons (w := 360) h77020 (SegSum.cons (w := 360) h77021 (SegSum.cons (w := 720) h77022 (SegSum.cons (w := 720) h77023 (SegSum.cons (w := 180) h77054 (SegSum.cons (w := 180) h77055 (SegSum.cons (w := 60) h77128 (SegSum.cons (w := 360) h77129 (SegSum.cons (w := 360) h77131 (SegSum.cons (w := 360) h77132 (SegSum.cons (w := 720) h77133 (SegSum.cons (w := 360) h77135 (SegSum.cons (w := 120) h77147 (SegSum.cons (w := 360) h77148 (SegSum.cons (w := 720) h77149 (SegSum.cons (w := 360) h77151 (SegSum.cons (w := 360) h77164 (SegSum.cons (w := 360) h77165 (SegSum.cons (w := 720) h77166 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S42
