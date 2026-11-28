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

namespace RACert.S4N1.C0.S39

open RACert RACert.Problem

theorem cover6972 : P.CoversSplit 24 10 6972 0xfca9fca9a0a0a0a0fca9fca9a0a0a0a0a0a0a4a100000000a0a0a4a100000000cc00cc0080008000cc00cc008000800080008400000000008000840000000000cc00cc0080008000cc21cc2180208020800084000000000080208421000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 529, 572, 859, 916, 1202, 1258, 1259, 1601]) (by decide +kernel)

noncomputable def f6972 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (7139328 + i)

theorem c6972_0 : rowSum f6972 0 1024 = 14681908 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6972) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover6972 (by decide)
  decide +kernel

theorem sum6972 : rowSum f6972 0 1024 = 14681908 :=
  c6972_0

theorem h6972 : P.leaf 34 6972 = 14681908 :=
  leaf_weighted (k := 24) (d := 10) (H := 6972) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 6972) (by decide) (by decide +kernel)) sum6972

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
  leaf_weighted (k := 24) (d := 10) (H := 6973) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 6973) (by decide) (by decide +kernel)) sum6973

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
  leaf_weighted (k := 24) (d := 10) (H := 6975) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 6975) (by decide) (by decide +kernel)) sum6975

theorem cover51339 : P.CoversSplit 24 10 51339 0xaa00000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 517, 522, 528, 536, 573, 859, 865, 879, 915, 916, 921]) (by decide +kernel)

theorem h51339 : P.leaf 34 51339 = 140096 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 51339) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 51339) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 51339) (weight := rowWeight keep5 twice5) (xs := [383, 511, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover51339 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7010 : P.leaf 34 7010 = 140096 :=
  orient25 (v := 51339) (by decide) (by decide +kernel) h51339

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

theorem h7012 : P.leaf 34 7012 = 153752 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7012) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7012) (weight := fun _ => 1) (xs := [507, 511, 895, 1019, 1023]) check rows elimOK (by decide) (by decide) cover7012 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7013 : P.CoversSplit 24 10 7013 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 524, 572, 859, 879, 916, 1202, 1209, 1210, 1251, 1258, 1259, 1308]) (by decide +kernel)

theorem h7013 : P.leaf 34 7013 = 1113976 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7013) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7013) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover7013 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7014 : P.CoversSplit 24 10 7014 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 524, 566, 859, 879, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem h7014 : P.leaf 34 7014 = 3116636 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7014) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7014) (weight := fun _ => 1) (xs := [497, 499, 501, 503, 505, 507, 509, 511, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover7014 (by decide) (by decide) (by decide +kernel)
  decide +kernel

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

theorem h7016 : P.leaf 34 7016 = 96816 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7016) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7016) (weight := fun _ => 1) (xs := [507, 511, 895, 1019, 1023]) check rows elimOK (by decide) (by decide) cover7016 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7017 : P.CoversSplit 24 10 7017 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 572, 879, 916, 1202, 1209, 1210, 1258, 1259, 1308]) (by decide +kernel)

theorem h7017 : P.leaf 34 7017 = 716292 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7017) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7017) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover7017 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7018 : P.CoversSplit 24 10 7018 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 859, 879, 916, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem h7018 : P.leaf 34 7018 = 1285016 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7018) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7018) (weight := fun _ => 1) (xs := [497, 499, 501, 503, 505, 507, 509, 511, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover7018 (by decide) (by decide) (by decide +kernel)
  decide +kernel

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

theorem h7020 : P.leaf 34 7020 = 840292 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7020) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7020) (weight := fun _ => 1) (xs := [507, 511, 895, 1019, 1023]) check rows elimOK (by decide) (by decide) cover7020 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7021 : P.CoversSplit 24 10 7021 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 879, 916, 1202, 1209, 1210, 1251, 1258, 1259, 1308]) (by decide +kernel)

theorem h7021 : P.leaf 34 7021 = 4814414 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7021) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7021) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover7021 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7022 : P.CoversSplit 24 10 7022 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 859, 879, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem h7022 : P.leaf 34 7022 = 6410120 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7022) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7022) (weight := fun _ => 1) (xs := [497, 499, 501, 503, 505, 507, 509, 511, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover7022 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7023 : P.CoversSplit 24 10 7023 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1202, 1209, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c7023_0 : P.sumLeaves 24 7191552 1024 = 22866596 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7023) (lo := 0) (len := 1024) (W := 22866596) check rows elimOK (by decide) (by decide) cover7023 (by decide)
  decide +kernel

theorem h7023 : P.leaf 34 7023 = 22866596 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 22866596)]) (.cons c7023_0 (.nil)) (by decide) (by decide))

theorem cover18207 : P.CoversSplit 24 10 18207 0xfffffffff0000a00fffffffff0000a00ffffffff00000000ffff0000000000008888888880000800220022002000020088888888000000002200000000000000fffffffff0000a00ffff0000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 523, 529, 572, 872, 909, 1202, 1217, 1251, 1259, 1264, 1308, 1601, 1609]) (ps := [(8, [615], [1217, 1266]), (14, [965], [1609])]) (by decide +kernel)

noncomputable def f18207 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (18643968 + i)

theorem c18207_0 : rowSum f18207 0 957 = 15466874 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 18207) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover18207 (by decide)
  decide +kernel

theorem c18207_1 : rowSum f18207 957 67 = 7566814 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 18207) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover18207 (by decide)
  decide +kernel

theorem sum18207 : rowSum f18207 0 1024 = 23033688 :=
  rowSum_append (F := f18207) (lo := 0) (n := 957) (m := 67) (A := 15466874) (B := 7566814) c18207_0 (c18207_1)

theorem h18207 : P.leaf 34 18207 = 23033688 :=
  leaf_weighted (k := 24) (d := 10) (H := 18207) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 18207) (by decide) (by decide +kernel)) sum18207

theorem h7027 : P.leaf 34 7027 = 23033688 :=
  orient4 (v := 18207) (by decide) (by decide +kernel) h18207

theorem cover25827 : P.CoversSplit 24 10 25827 0xf0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 522, 573, 858, 865, 1202, 1210, 1259]) (by decide +kernel)

theorem c25827_0 : P.sumLeaves 24 26446848 1024 = 2271996 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 25827) (lo := 0) (len := 1024) (W := 2271996) check rows elimOK (by decide) (by decide) cover25827 (by decide)
  decide +kernel

theorem h25827 : P.leaf 34 25827 = 2271996 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2271996)]) (.cons c25827_0 (.nil)) (by decide) (by decide))

theorem h7028 : P.leaf 34 7028 = 2271996 :=
  orient32 (v := 25827) (by decide) (by decide +kernel) h25827

theorem cover18223 : P.CoversSplit 24 10 18223 0xfffffffffa000000fffffffffa00000088888c8c000000008888000000000000cccccccc88000000330033002200000088888c8c00000000000000000000000088888888880000000000000000000000888888880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 860, 872, 916, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem c18223_0 : P.sumLeaves 24 18660352 948 = 9090083 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18223) (lo := 0) (len := 948) (W := 9090083) check rows elimOK (by decide) (by decide) cover18223 (by decide)
  decide +kernel

theorem c18223_1 : P.sumLeaves 24 18661300 76 = 14582452 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18223) (lo := 948) (len := 76) (W := 14582452) check rows elimOK (by decide) (by decide) cover18223 (by decide)
  decide +kernel

theorem h18223 : P.leaf 34 18223 = 23672535 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(948, 9090083), (76, 14582452)]) (.cons c18223_0 (.cons c18223_1 (.nil))) (by decide) (by decide))

theorem h7029 : P.leaf 34 7029 = 23672535 :=
  orient4 (v := 18223) (by decide) (by decide +kernel) h18223

theorem cover35755 : P.CoversSplit 24 10 35755 0xfffffffff0f0a0a0fffffffff0f0a0a0ffffffff00000000ffff000000000000cccccccc80008000ff00ff00a000a000cccccccc00000000ff00000000000000fffffffff0f0a0a00000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 859, 915, 916, 1202, 1209, 1217, 1251, 1258, 1308, 1601]) (ps := [(8, [615], [1217]), (14, [965], [1272]), (19, [965], [1264])]) (by decide +kernel)

theorem c35755_0 : P.sumLeaves 24 36613120 747 = 6361982 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 35755) (lo := 0) (len := 747) (W := 6361982) check rows elimOK (by decide) (by decide) cover35755 (by decide)
  decide +kernel

theorem c35755_1 : P.sumLeaves 24 36613867 206 = 11304999 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 35755) (lo := 747) (len := 206) (W := 11304999) check rows elimOK (by decide) (by decide) cover35755 (by decide)
  decide +kernel

theorem c35755_2 : P.sumLeaves 24 36614073 71 = 14646108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 35755) (lo := 953) (len := 71) (W := 14646108) check rows elimOK (by decide) (by decide) cover35755 (by decide)
  decide +kernel

theorem h35755 : P.leaf 34 35755 = 32313089 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(747, 6361982), (206, 11304999), (71, 14646108)]) (.cons c35755_0 (.cons c35755_1 (.cons c35755_2 (.nil)))) (by decide) (by decide))

theorem h7030 : P.leaf 34 7030 = 32313089 :=
  orient24 (v := 35755) (by decide) (by decide +kernel) h35755

theorem cover18239 : P.CoversSplit 24 10 18239 0xfffffffffa000000fffffffffa000000ffffffff00000000ffff000000000000cccccccc880000003300330022000000cccccccc000000003300000000000000fffffffffa000000ffff0000fa000000ffffffff00000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 529, 572, 860, 872, 909, 916, 1202, 1210, 1217, 1251, 1264, 1308, 1601, 1609]) (ps := [(8, [615], [1217]), (14, [965], [1609])]) (by decide +kernel)

theorem c18239_0 : P.sumLeaves 24 18676736 500 = 5715901 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18239) (lo := 0) (len := 500) (W := 5715901) check rows elimOK (by decide) (by decide) cover18239 (by decide)
  decide +kernel

theorem c18239_1 : P.sumLeaves 24 18677236 384 = 18949053 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18239) (lo := 500) (len := 384) (W := 18949053) check rows elimOK (by decide) (by decide) cover18239 (by decide)
  decide +kernel

theorem c18239_2 : P.sumLeaves 24 18677620 140 = 53627329 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18239) (lo := 884) (len := 140) (W := 53627329) check rows elimOK (by decide) (by decide) cover18239 (by decide)
  decide +kernel

theorem h18239 : P.leaf 34 18239 = 78292283 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(500, 5715901), (384, 18949053), (140, 53627329)]) (.cons c18239_0 (.cons c18239_1 (.cons c18239_2 (.nil)))) (by decide) (by decide))

theorem h7031 : P.leaf 34 7031 = 78292283 :=
  orient4 (v := 18239) (by decide) (by decide +kernel) h18239

def seg : List (ℕ × ℕ) := [(6972, 12), (6973, 24), (6975, 12), (7010, 24), (7011, 48), (7012, 48), (7013, 48), (7014, 48), (7015, 48), (7016, 48), (7017, 48), (7018, 48), (7019, 48), (7020, 48), (7021, 48), (7022, 48), (7023, 48), (7027, 24), (7028, 48), (7029, 48), (7030, 48), (7031, 48)]

theorem segOK : checkSeg 16 perms 6972 7032 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6972 7032 912 12134543736 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 12134543736)
    (SegSum.cons (w := 12) h6972 (SegSum.cons (w := 24) h6973 (SegSum.cons (w := 12) h6975 (SegSum.cons (w := 24) h7010 (SegSum.cons (w := 48) h7011 (SegSum.cons (w := 48) h7012 (SegSum.cons (w := 48) h7013 (SegSum.cons (w := 48) h7014 (SegSum.cons (w := 48) h7015 (SegSum.cons (w := 48) h7016 (SegSum.cons (w := 48) h7017 (SegSum.cons (w := 48) h7018 (SegSum.cons (w := 48) h7019 (SegSum.cons (w := 48) h7020 (SegSum.cons (w := 48) h7021 (SegSum.cons (w := 48) h7022 (SegSum.cons (w := 48) h7023 (SegSum.cons (w := 24) h7027 (SegSum.cons (w := 48) h7028 (SegSum.cons (w := 48) h7029 (SegSum.cons (w := 48) h7030 (SegSum.cons (w := 48) h7031 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S39
