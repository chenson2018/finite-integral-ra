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

namespace RACert.S4N1.C0.S54

open RACert RACert.Problem

theorem cover7924 : P.CoversSplit 24 10 7924 0xfffffffffafa00000000000000000000fffffffffafa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 573, 1210, 1259, 1264]) (by decide +kernel)

theorem c7924_0 : P.sumLeaves 24 8114176 1024 = 5231144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7924) (lo := 0) (len := 1024) (W := 5231144) check rows elimOK (by decide) (by decide) cover7924 (by decide)
  decide +kernel

theorem h7924 : P.leaf 34 7924 = 5231144 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5231144)]) (.cons c7924_0 (.nil)) (by decide) (by decide))

theorem cover7925 : P.CoversSplit 24 10 7925 0xffffffffffff00000000000000000000ffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 573, 1209, 1210, 1259, 1264]) (by decide +kernel)

theorem c7925_0 : P.sumLeaves 24 8115200 1024 = 25222704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7925) (lo := 0) (len := 1024) (W := 25222704) check rows elimOK (by decide) (by decide) cover7925 (by decide)
  decide +kernel

theorem h7925 : P.leaf 34 7925 = 25222704 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 25222704)]) (.cons c7925_0 (.nil)) (by decide) (by decide))

theorem cover7926 : P.CoversSplit 24 10 7926 0xffffffffffff00000000000000000000ffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 573, 916, 1209, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c7926_0 : P.sumLeaves 24 8116224 1012 = 19684786 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7926) (lo := 0) (len := 1012) (W := 19684786) check rows elimOK (by decide) (by decide) cover7926 (by decide)
  decide +kernel

theorem c7926_1 : P.sumLeaves 24 8117236 12 = 7123952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7926) (lo := 1012) (len := 12) (W := 7123952) check rows elimOK (by decide) (by decide) cover7926 (by decide)
  decide +kernel

theorem h7926 : P.leaf 34 7926 = 26808738 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1012, 19684786), (12, 7123952)]) (.cons c7926_0 (.cons c7926_1 (.nil))) (by decide) (by decide))

theorem cover7927 : P.CoversSplit 24 10 7927 0xffffffffffff00000000000000000000ffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 573, 916, 1209, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c7927_0 : P.sumLeaves 24 8117248 1012 = 30535564 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7927) (lo := 0) (len := 1012) (W := 30535564) check rows elimOK (by decide) (by decide) cover7927 (by decide)
  decide +kernel

theorem c7927_1 : P.sumLeaves 24 8118260 12 = 12445504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7927) (lo := 1012) (len := 12) (W := 12445504) check rows elimOK (by decide) (by decide) cover7927 (by decide)
  decide +kernel

theorem h7927 : P.leaf 34 7927 = 42981068 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1012, 30535564), (12, 12445504)]) (.cons c7927_0 (.cons c7927_1 (.nil))) (by decide) (by decide))

theorem cover7932 : P.CoversSplit 24 10 7932 0xfffffffffafa00000000000000000000fffffffffafa000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 573, 916, 1210, 1259, 1264, 1308]) (by decide +kernel)

noncomputable def f7932 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (8122368 + i)

theorem c7932_0 : rowSum f7932 0 1024 = 28835658 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7932) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover7932 (by decide)
  decide +kernel

theorem sum7932 : rowSum f7932 0 1024 = 28835658 :=
  c7932_0

theorem h7932 : P.leaf 34 7932 = 28835658 :=
  leaf_weighted (k := 24) (d := 10) (H := 7932) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 7932) (by decide) (by decide +kernel)) sum7932

theorem cover7933 : P.CoversSplit 24 10 7933 0xffffffffffff00000000000000000000ffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 573, 916, 1209, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

noncomputable def f7933 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (8123392 + i)

theorem c7933_0 : rowSum f7933 0 1024 = 38904925 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7933) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover7933 (by decide)
  decide +kernel

theorem sum7933 : rowSum f7933 0 1024 = 38904925 :=
  c7933_0

theorem h7933 : P.leaf 34 7933 = 38904925 :=
  leaf_weighted (k := 24) (d := 10) (H := 7933) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 7933) (by decide) (by decide +kernel)) sum7933

theorem cover7934 : P.CoversSplit 24 10 7934 0xffffffffffff00000000000000000000ffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 916, 1209, 1210, 1217, 1258, 1259, 1264, 1308]) (by decide +kernel)

noncomputable def f7934 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (8124416 + i)

theorem c7934_0 : rowSum f7934 0 1024 = 62437892 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7934) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover7934 (by decide)
  decide +kernel

theorem sum7934 : rowSum f7934 0 1024 = 62437892 :=
  c7934_0

theorem h7934 : P.leaf 34 7934 = 62437892 :=
  leaf_weighted (k := 24) (d := 10) (H := 7934) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 7934) (by decide) (by decide +kernel)) sum7934

theorem cover7935 : P.CoversSplit 24 10 7935 0xffffffffffff00000000000000000000ffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 916, 1209, 1210, 1217, 1258, 1259, 1264, 1308]) (by decide +kernel)

noncomputable def f7935 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (8125440 + i)

theorem c7935_0 : rowSum f7935 0 1024 = 62437892 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7935) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover7935 (by decide)
  decide +kernel

theorem sum7935 : rowSum f7935 0 1024 = 62437892 :=
  c7935_0

theorem h7935 : P.leaf 34 7935 = 62437892 :=
  leaf_weighted (k := 24) (d := 10) (H := 7935) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 7935) (by decide) (by decide +kernel)) sum7935

theorem cover8052 : P.CoversSplit 24 10 8052 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc00c8008000cc33cc33c8328020cc00cc00c8008000cc33cc33c82080200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 572, 916, 1209, 1210, 1601]) (ps := [(8, [1217], [572]), (14, [1217], [916])]) (by decide +kernel)

noncomputable def f8052 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8245248 + i)

theorem c8052_0 : rowSum f8052 0 801 = 1717068 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8052) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8052 (by decide)
  decide +kernel

theorem c8052_1 : rowSum f8052 801 201 = 6381814 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8052) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8052 (by decide)
  decide +kernel

theorem c8052_2 : rowSum f8052 1002 22 = 1967366 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8052) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8052 (by decide)
  decide +kernel

theorem sum8052 : rowSum f8052 0 1024 = 10066248 :=
  rowSum_append (F := f8052) (lo := 0) (n := 801) (m := 223) (A := 1717068) (B := 8349180) c8052_0 (rowSum_append (F := f8052) (lo := 801) (n := 201) (m := 22) (A := 6381814) (B := 1967366) c8052_1 (c8052_2))

theorem h8052 : P.leaf 34 8052 = 10066248 :=
  leaf_weighted (k := 24) (d := 10) (H := 8052) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 8052) (by decide) (by decide +kernel)) sum8052

theorem cover8053 : P.CoversSplit 24 10 8053 0xffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000cc00cc00cc008000cc33cc33cc338020cc00cc00c8008000cc33cc33c82080200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 572, 916, 1209, 1210, 1217, 1258, 1601]) (ps := [(8, [1217], [572]), (14, [1217], [916])]) (by decide +kernel)

noncomputable def f8053 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8246272 + i)

theorem c8053_0 : rowSum f8053 0 757 = 9744497 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8053) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8053 (by decide)
  decide +kernel

theorem c8053_1 : rowSum f8053 757 190 = 35752658 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8053) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8053 (by decide)
  decide +kernel

theorem c8053_2 : rowSum f8053 947 77 = 47284066 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8053) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8053 (by decide)
  decide +kernel

theorem sum8053 : rowSum f8053 0 1024 = 92781221 :=
  rowSum_append (F := f8053) (lo := 0) (n := 757) (m := 267) (A := 9744497) (B := 83036724) c8053_0 (rowSum_append (F := f8053) (lo := 757) (n := 190) (m := 77) (A := 35752658) (B := 47284066) c8053_1 (c8053_2))

theorem h8053 : P.leaf 34 8053 = 92781221 :=
  leaf_weighted (k := 24) (d := 10) (H := 8053) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 8053) (by decide) (by decide +kernel)) sum8053

theorem cover8054 : P.CoversSplit 24 10 8054 0xffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000ffffffffffffa0a0ffffffffffffa0a0fffffffffafaa0a0fffffffffafaa0a00000000000000000cc00cc0080008000cc33cc3380008000cc00cc0080008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

noncomputable def f8054 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8247296 + i)

theorem c8054_0 : rowSum f8054 0 403 = 6229706 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8054) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8054 (by decide)
  decide +kernel

theorem c8054_1 : rowSum f8054 403 344 = 19023086 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8054) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8054 (by decide)
  decide +kernel

theorem c8054_2 : rowSum f8054 747 196 = 51428091 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8054) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8054 (by decide)
  decide +kernel

theorem c8054_3 : rowSum f8054 943 81 = 67266628 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8054) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8054 (by decide)
  decide +kernel

theorem sum8054 : rowSum f8054 0 1024 = 143947511 :=
  rowSum_append (F := f8054) (lo := 0) (n := 403) (m := 621) (A := 6229706) (B := 137717805) c8054_0 (rowSum_append (F := f8054) (lo := 403) (n := 344) (m := 277) (A := 19023086) (B := 118694719) c8054_1 (rowSum_append (F := f8054) (lo := 747) (n := 196) (m := 81) (A := 51428091) (B := 67266628) c8054_2 (c8054_3)))

theorem h8054 : P.leaf 34 8054 = 143947511 :=
  leaf_weighted (k := 24) (d := 10) (H := 8054) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 8054) (by decide) (by decide +kernel)) sum8054

def seg : List (ℕ × ℕ) := [(7924, 48), (7925, 48), (7926, 48), (7927, 48), (7932, 24), (7933, 24), (7934, 24), (7935, 24), (8052, 24), (8053, 24), (8054, 24)]

theorem segOK : checkSeg 16 perms 7924 8055 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7924 8055 360 15357567720 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 15357567720)
    (SegSum.cons (w := 48) h7924 (SegSum.cons (w := 48) h7925 (SegSum.cons (w := 48) h7926 (SegSum.cons (w := 48) h7927 (SegSum.cons (w := 24) h7932 (SegSum.cons (w := 24) h7933 (SegSum.cons (w := 24) h7934 (SegSum.cons (w := 24) h7935 (SegSum.cons (w := 24) h8052 (SegSum.cons (w := 24) h8053 (SegSum.cons (w := 24) h8054 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))) (by decide)

end RACert.S4N1.C0.S54
