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

namespace RACert.S4N1.C0.S44

open RACert RACert.Problem

theorem cover6966 : P.CoversSplit 24 10 6966 0xffffffffa5a5a0a0ffffffffa5a5a0a0a0a0a0a000000000a0a0a0a000000000cc33cc3380008000cc00cc008000800080208020000000008000800000000000ffffffffa5a5a0a0ffffffffa5a5a0a0a0a0ffff0000a0a0a0a0ffff000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 529, 572, 859, 1202, 1209, 1258, 1259, 1601]) (ps := [(5, [524], [517]), (8, [531], [517, 1217]), (14, [880], [859])]) (by decide +kernel)

noncomputable def f6966 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (7133184 + i)

theorem c6966_0 : rowSum f6966 0 683 = 1464662 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6966) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover6966 (by decide)
  decide +kernel

theorem c6966_1 : rowSum f6966 683 341 = 9749860 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6966) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover6966 (by decide)
  decide +kernel

theorem sum6966 : rowSum f6966 0 1024 = 11214522 :=
  rowSum_append (F := f6966) (lo := 0) (n := 683) (m := 341) (A := 1464662) (B := 9749860) c6966_0 (c6966_1)

theorem h6966 : P.leaf 34 6966 = 11214522 :=
  leaf_weighted (k := 24) (d := 10) (H := 6966) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 6966) (by decide) (by decide +kernel)) sum6966

theorem cover6967 : P.CoversSplit 24 10 6967 0xffffffffa5a5a0a0ffffffffa5a5a0a0ffffffff00000000ffffffff00000000cc33cc3380008000cc00cc0080008000cc33cc3300000000cc00cc0000000000ffffffffa5a5a0a0ffffffffa5a5a0a0ffffffffa5a5a0a0ffffffffa5a5a0a00000000000000000cc00cc0080008000cc33cc3380008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 572, 859, 1202, 1209, 1217, 1258, 1259, 1601, 1609]) (ps := [(8, [531], [1217])]) (by decide +kernel)

noncomputable def f6967 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (7134208 + i)

theorem c6967_0 : rowSum f6967 0 415 = 878552 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6967) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover6967 (by decide)
  decide +kernel

theorem c6967_1 : rowSum f6967 415 392 = 5570047 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6967) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover6967 (by decide)
  decide +kernel

theorem c6967_2 : rowSum f6967 807 217 = 24175319 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6967) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover6967 (by decide)
  decide +kernel

theorem sum6967 : rowSum f6967 0 1024 = 30623918 :=
  rowSum_append (F := f6967) (lo := 0) (n := 415) (m := 609) (A := 878552) (B := 29745366) c6967_0 (rowSum_append (F := f6967) (lo := 415) (n := 392) (m := 217) (A := 5570047) (B := 24175319) c6967_1 (c6967_2))

theorem h6967 : P.leaf 34 6967 = 30623918 :=
  leaf_weighted (k := 24) (d := 10) (H := 6967) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 6967) (by decide) (by decide +kernel)) sum6967

theorem cover6972 : P.CoversSplit 24 10 6972 0xfca9fca9a0a0a0a0fca9fca9a0a0a0a0a0a0a4a100000000a0a0a4a100000000cc00cc0080008000cc00cc008000800080008400000000008000840000000000cc00cc0080008000cc21cc2180208020800084000000000080208421000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 529, 572, 859, 916, 1202, 1258, 1259, 1601]) (by decide +kernel)

noncomputable def f6972 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (7139328 + i)

theorem c6972_0 : rowSum f6972 0 1024 = 14681908 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6972) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover6972 (by decide)
  decide +kernel

theorem sum6972 : rowSum f6972 0 1024 = 14681908 :=
  c6972_0

theorem h6972 : P.leaf 34 6972 = 14681908 :=
  leaf_weighted (k := 24) (d := 10) (H := 6972) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 6972) (by decide) (by decide +kernel)) sum6972

theorem cover6973 : P.CoversSplit 24 10 6973 0xffffffffa5a5a0a0ffffffffa5a5a0a0ffffffff00000000ffffffff00000000cc33cc3380008000cc00cc0080008000cc33cc3300000000cc00cc0000000000cc00cc0084008000cc33cc3384218020cc00cc0000000000cc33cc33000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 529, 572, 916, 1202, 1209, 1258, 1259, 1601]) (by decide +kernel)

noncomputable def f6973 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (7140352 + i)

theorem c6973_0 : rowSum f6973 0 817 = 6702873 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6973) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover6973 (by decide)
  decide +kernel

theorem c6973_1 : rowSum f6973 817 207 = 27600355 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6973) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover6973 (by decide)
  decide +kernel

theorem sum6973 : rowSum f6973 0 1024 = 34303228 :=
  rowSum_append (F := f6973) (lo := 0) (n := 817) (m := 207) (A := 6702873) (B := 27600355) c6973_0 (c6973_1)

theorem h6973 : P.leaf 34 6973 = 34303228 :=
  leaf_weighted (k := 24) (d := 10) (H := 6973) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 6973) (by decide) (by decide +kernel)) sum6973

theorem cover6975 : P.CoversSplit 24 10 6975 0xffffffffa5a5a0a0ffffffffa5a5a0a0ffffffff0000a0a0ffffffff0000a0a0cc33cc3380008000cc00cc0080008000cc33cc3300008000cc00cc0000008000ffffffffa5a5a0a0ffffffffa5a5a0a0ffffffffa5a5a0a0ffffffffa5a5a0a00000000000000000cc00cc0080008000cc33cc3380008000cc00cc0080008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 572, 1202, 1209, 1217, 1258, 1259, 1601, 1609]) (by decide +kernel)

noncomputable def f6975 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7142400 + i)

theorem c6975_0 : rowSum f6975 0 427 = 2558800 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6975) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6975 (by decide)
  decide +kernel

theorem c6975_1 : rowSum f6975 427 506 = 24120312 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6975) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6975 (by decide)
  decide +kernel

theorem c6975_2 : rowSum f6975 933 91 = 49070386 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6975) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6975 (by decide)
  decide +kernel

theorem sum6975 : rowSum f6975 0 1024 = 75749498 :=
  rowSum_append (F := f6975) (lo := 0) (n := 427) (m := 597) (A := 2558800) (B := 73190698) c6975_0 (rowSum_append (F := f6975) (lo := 427) (n := 506) (m := 91) (A := 24120312) (B := 49070386) c6975_1 (c6975_2))

theorem h6975 : P.leaf 34 6975 = 75749498 :=
  leaf_weighted (k := 24) (d := 10) (H := 6975) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6975) (by decide) (by decide +kernel)) sum6975

theorem cover7010 : P.CoversSplit 24 10 7010 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 566, 859, 879, 916, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c7010_0 : P.sumLeaves 24 7178240 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7010) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover7010 (by decide)
  decide +kernel

theorem contract7010_1 : P.leaf 30 112167 = 22416 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 112167) (ss := [(2, 1, 453), (5, 1, 453), (3, 1, 409), (6, 1, 478), (12, 1, 460), (30, 19, 523), (19, 1, 529), (14, 1, 923), (8, 1, 586), (18, 1, 923), (31, 1, 1210), (26, 1, 515), (17, 1, 1273)]) (ids := [2, 5, 7, 8, 9, 11, 13, 14, 18, 19, 21, 23, 25, 26, 27, 20, 22]) (cs := [1, 1, 2, 1, 1, 3, 1, 4, 5, 6, 1, 7, 1, 8, 9, 1, 1, 1, 10, 11, 17, 12, 18, 13, 1, 14, 15, 16, 1, 1]) (bs := [15, 2]) (W := 22416) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7010_1 : P.sumLeaves 24 7178688 64 = 22416 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 112167) rows (by decide) (by decide)).symm.trans contract7010_1

theorem c7010_2 : P.sumLeaves 24 7178752 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7010) (lo := 512) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover7010 (by decide)
  decide +kernel

theorem contract7010_3 : P.leaf 30 112173 = 17744 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 112173) (ss := [(2, 1, 453), (5, 1, 453), (3, 1, 409), (6, 1, 478), (12, 1, 460), (30, 1, 523), (4, 1, 565), (28, 1, 859), (26, 1, 515), (31, 1, 859), (14, 1, 880), (17, 1, 880), (19, 1, 1273)]) (ids := [5, 6, 7, 8, 9, 11, 13, 14, 16, 18, 19, 21, 23, 25, 27, 20, 22]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 1, 7, 1, 8, 9, 1, 10, 1, 11, 12, 17, 13, 18, 14, 1, 15, 1, 16, 1, 1]) (bs := [15, 2]) (W := 17744) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7010_3 : P.sumLeaves 24 7179072 64 = 17744 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 112173) rows (by decide) (by decide)).symm.trans contract7010_3

theorem c7010_4 : P.sumLeaves 24 7179136 128 = 99936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7010) (lo := 896) (len := 128) (W := 99936) check rows elimOK (by decide) (by decide) cover7010 (by decide)
  decide +kernel

theorem h7010 : P.leaf 34 7010 = 140096 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 22416), (320, 0), (64, 17744), (128, 99936)]) (.cons c7010_0 (.cons c7010_1 (.cons c7010_2 (.cons c7010_3 (.cons c7010_4 (.nil)))))) (by decide) (by decide))

theorem cover7011 : P.CoversSplit 24 10 7011 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 523, 572, 916, 1202, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c7011_0 : P.sumLeaves 24 7179264 1024 = 3790938 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7011) (lo := 0) (len := 1024) (W := 3790938) check rows elimOK (by decide) (by decide) cover7011 (by decide)
  decide +kernel

theorem h7011 : P.leaf 34 7011 = 3790938 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3790938)]) (.cons c7011_0 (.nil)) (by decide) (by decide))

theorem cover7012 : P.CoversSplit 24 10 7012 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 524, 572, 859, 879, 916, 1202, 1209, 1210, 1259, 1308]) (by decide +kernel)

theorem c7012_0 : P.sumLeaves 24 7180288 1024 = 153752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7012) (lo := 0) (len := 1024) (W := 153752) check rows elimOK (by decide) (by decide) cover7012 (by decide)
  decide +kernel

theorem h7012 : P.leaf 34 7012 = 153752 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 153752)]) (.cons c7012_0 (.nil)) (by decide) (by decide))

theorem cover7013 : P.CoversSplit 24 10 7013 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 524, 572, 859, 879, 916, 1202, 1209, 1210, 1251, 1258, 1259, 1308]) (by decide +kernel)

theorem c7013_0 : P.sumLeaves 24 7181312 1024 = 1113976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7013) (lo := 0) (len := 1024) (W := 1113976) check rows elimOK (by decide) (by decide) cover7013 (by decide)
  decide +kernel

theorem h7013 : P.leaf 34 7013 = 1113976 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1113976)]) (.cons c7013_0 (.nil)) (by decide) (by decide))

theorem cover7014 : P.CoversSplit 24 10 7014 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 524, 566, 859, 879, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c7014_0 : P.sumLeaves 24 7182336 1024 = 3116636 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7014) (lo := 0) (len := 1024) (W := 3116636) check rows elimOK (by decide) (by decide) cover7014 (by decide)
  decide +kernel

theorem h7014 : P.leaf 34 7014 = 3116636 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3116636)]) (.cons c7014_0 (.nil)) (by decide) (by decide))

theorem cover7015 : P.CoversSplit 24 10 7015 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 524, 566, 859, 1202, 1209, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c7015_0 : P.sumLeaves 24 7183360 1024 = 11705430 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7015) (lo := 0) (len := 1024) (W := 11705430) check rows elimOK (by decide) (by decide) cover7015 (by decide)
  decide +kernel

theorem h7015 : P.leaf 34 7015 = 11705430 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11705430)]) (.cons c7015_0 (.nil)) (by decide) (by decide))

theorem cover7016 : P.CoversSplit 24 10 7016 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 523, 565, 572, 859, 879, 916, 1202, 1209, 1210, 1259, 1308]) (by decide +kernel)

theorem c7016_0 : P.sumLeaves 24 7184384 1024 = 96816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7016) (lo := 0) (len := 1024) (W := 96816) check rows elimOK (by decide) (by decide) cover7016 (by decide)
  decide +kernel

theorem h7016 : P.leaf 34 7016 = 96816 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 96816)]) (.cons c7016_0 (.nil)) (by decide) (by decide))

theorem cover7017 : P.CoversSplit 24 10 7017 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 572, 879, 916, 1202, 1209, 1210, 1258, 1259, 1308]) (by decide +kernel)

theorem c7017_0 : P.sumLeaves 24 7185408 1024 = 716292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7017) (lo := 0) (len := 1024) (W := 716292) check rows elimOK (by decide) (by decide) cover7017 (by decide)
  decide +kernel

theorem h7017 : P.leaf 34 7017 = 716292 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 716292)]) (.cons c7017_0 (.nil)) (by decide) (by decide))

theorem cover7018 : P.CoversSplit 24 10 7018 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 859, 879, 916, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c7018_0 : P.sumLeaves 24 7186432 1024 = 1285016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7018) (lo := 0) (len := 1024) (W := 1285016) check rows elimOK (by decide) (by decide) cover7018 (by decide)
  decide +kernel

theorem h7018 : P.leaf 34 7018 = 1285016 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1285016)]) (.cons c7018_0 (.nil)) (by decide) (by decide))

theorem cover7019 : P.CoversSplit 24 10 7019 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 523, 572, 916, 1202, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c7019_0 : P.sumLeaves 24 7187456 1024 = 7996456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7019) (lo := 0) (len := 1024) (W := 7996456) check rows elimOK (by decide) (by decide) cover7019 (by decide)
  decide +kernel

theorem h7019 : P.leaf 34 7019 = 7996456 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7996456)]) (.cons c7019_0 (.nil)) (by decide) (by decide))

theorem cover7020 : P.CoversSplit 24 10 7020 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 572, 859, 879, 916, 1202, 1209, 1210, 1259, 1308]) (by decide +kernel)

theorem c7020_0 : P.sumLeaves 24 7188480 1024 = 840292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7020) (lo := 0) (len := 1024) (W := 840292) check rows elimOK (by decide) (by decide) cover7020 (by decide)
  decide +kernel

theorem h7020 : P.leaf 34 7020 = 840292 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 840292)]) (.cons c7020_0 (.nil)) (by decide) (by decide))

theorem cover7021 : P.CoversSplit 24 10 7021 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 879, 916, 1202, 1209, 1210, 1251, 1258, 1259, 1308]) (by decide +kernel)

theorem c7021_0 : P.sumLeaves 24 7189504 1024 = 4814414 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7021) (lo := 0) (len := 1024) (W := 4814414) check rows elimOK (by decide) (by decide) cover7021 (by decide)
  decide +kernel

theorem h7021 : P.leaf 34 7021 = 4814414 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4814414)]) (.cons c7021_0 (.nil)) (by decide) (by decide))

theorem cover7022 : P.CoversSplit 24 10 7022 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 859, 879, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c7022_0 : P.sumLeaves 24 7190528 1024 = 6410120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7022) (lo := 0) (len := 1024) (W := 6410120) check rows elimOK (by decide) (by decide) cover7022 (by decide)
  decide +kernel

theorem h7022 : P.leaf 34 7022 = 6410120 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6410120)]) (.cons c7022_0 (.nil)) (by decide) (by decide))

theorem cover7023 : P.CoversSplit 24 10 7023 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1202, 1209, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c7023_0 : P.sumLeaves 24 7191552 1024 = 22866596 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7023) (lo := 0) (len := 1024) (W := 22866596) check rows elimOK (by decide) (by decide) cover7023 (by decide)
  decide +kernel

theorem h7023 : P.leaf 34 7023 = 22866596 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 22866596)]) (.cons c7023_0 (.nil)) (by decide) (by decide))

theorem cover7027 : P.CoversSplit 24 10 7027 0xffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000ffffffffafafa0a0ffffffffafafa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 859, 916, 1202, 1209, 1217, 1258, 1259, 1308, 1601, 1609]) (ps := [(8, [586], [1609])]) (by decide +kernel)

theorem c7027_0 : P.sumLeaves 24 7195648 527 = 2293240 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7027) (lo := 0) (len := 527) (W := 2293240) check rows elimOK (by decide) (by decide) cover7027 (by decide)
  decide +kernel

theorem c7027_1 : P.sumLeaves 24 7196175 297 = 2057919 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7027) (lo := 527) (len := 297) (W := 2057919) check rows elimOK (by decide) (by decide) cover7027 (by decide)
  decide +kernel

theorem c7027_2 : P.sumLeaves 24 7196472 128 = 6721213 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7027) (lo := 824) (len := 128) (W := 6721213) check rows elimOK (by decide) (by decide) cover7027 (by decide)
  decide +kernel

theorem c7027_3 : P.sumLeaves 24 7196600 72 = 11961316 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7027) (lo := 952) (len := 72) (W := 11961316) check rows elimOK (by decide) (by decide) cover7027 (by decide)
  decide +kernel

theorem h7027 : P.leaf 34 7027 = 23033688 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(527, 2293240), (297, 2057919), (128, 6721213), (72, 11961316)]) (.cons c7027_0 (.cons c7027_1 (.cons c7027_2 (.cons c7027_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(6966, 24), (6967, 24), (6972, 12), (6973, 24), (6975, 12), (7010, 24), (7011, 48), (7012, 48), (7013, 48), (7014, 48), (7015, 48), (7016, 48), (7017, 48), (7018, 48), (7019, 48), (7020, 48), (7021, 48), (7022, 48), (7023, 48), (7027, 24)]

theorem segOK : checkSeg 16 perms 6966 7028 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6966 7028 768 6584270952 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 6584270952)
    (SegSum.cons (w := 24) h6966 (SegSum.cons (w := 24) h6967 (SegSum.cons (w := 12) h6972 (SegSum.cons (w := 24) h6973 (SegSum.cons (w := 12) h6975 (SegSum.cons (w := 24) h7010 (SegSum.cons (w := 48) h7011 (SegSum.cons (w := 48) h7012 (SegSum.cons (w := 48) h7013 (SegSum.cons (w := 48) h7014 (SegSum.cons (w := 48) h7015 (SegSum.cons (w := 48) h7016 (SegSum.cons (w := 48) h7017 (SegSum.cons (w := 48) h7018 (SegSum.cons (w := 48) h7019 (SegSum.cons (w := 48) h7020 (SegSum.cons (w := 48) h7021 (SegSum.cons (w := 48) h7022 (SegSum.cons (w := 48) h7023 (SegSum.cons (w := 24) h7027 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S44
