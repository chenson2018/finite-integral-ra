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

namespace RACert.S4N1.C0.S15

open RACert RACert.Problem

theorem cover1928 : P.CoversSplit 24 10 1928 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [509]) (by decide +kernel)

theorem h1928 : P.leaf 34 1928 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1928) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1928) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1928 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1929 : P.CoversSplit 24 10 1929 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 474, 515, 517, 522, 528, 565, 915, 1209, 1609]) (ps := [(14, [874, 929], [860, 1266])]) (by decide +kernel)

theorem h1929 : P.leaf 34 1929 = 20912 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1929) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1929) (weight := fun _ => 1) (xs := [507, 511, 895, 1019, 1023]) check rows elimOK (by decide) (by decide) cover1929 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1930 : P.CoversSplit 24 10 1930 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [509]) (by decide +kernel)

theorem h1930 : P.leaf 34 1930 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1930) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1930) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1930 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16989 : P.CoversSplit 24 10 16989 0xc000c00000000000c000c00000000000800000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000c000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 523, 536, 565, 572, 573, 578, 859, 871, 916, 1210, 1259]) (ps := [(8, [622], [1266])]) (by decide +kernel)

theorem h16989 : P.leaf 34 16989 = 286720 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 16989) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16989) (weight := fun _ => 1) (xs := [494, 495, 510, 511, 831, 895, 942, 943, 958, 959, 1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover16989 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1931 : P.leaf 34 1931 = 286720 :=
  orient24 (v := 16989) (by decide) (by decide +kernel) h16989

theorem cover3426 : P.CoversSplit 24 10 3426 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 572, 858, 865, 915, 1209, 1266]) (by decide +kernel)

theorem h3426 : P.leaf 34 3426 = 11832 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3426) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3426) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover3426 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1932 : P.leaf 34 1932 = 11832 :=
  orient25 (v := 3426) (by decide) (by decide +kernel) h3426

theorem cover1933 : P.CoversSplit 24 10 1933 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000220000000000000000000000000000002000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 528, 860, 915, 1209, 1609]) (ps := [(14, [923], [1266])]) (by decide +kernel)

theorem h1933 : P.leaf 34 1933 = 207936 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1933) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1933) (weight := fun _ => 1) (xs := [507, 511, 565, 689, 693, 895, 1019, 1023]) check rows elimOK (by decide) (by decide) cover1933 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3427 : P.CoversSplit 24 10 3427 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 565, 572, 858, 865, 915, 916, 1209, 1266]) (by decide +kernel)

theorem h3427 : P.leaf 34 3427 = 146544 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3427) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3427) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover3427 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1934 : P.leaf 34 1934 = 146544 :=
  orient25 (v := 3427) (by decide) (by decide +kernel) h3427

theorem cover1935 : P.CoversSplit 24 10 1935 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000008800000000000000000000000000000080000000000000aaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000008800000000000000000000000000000080000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 517, 522, 528, 860, 916, 1209, 1258, 1259]) (ps := [(16, [566], [1258])]) (by decide +kernel)

theorem h1935 : P.leaf 34 1935 = 2046344 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1935) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1935) (weight := fun _ => 1) (xs := [55, 179, 183, 373, 375, 381, 383, 497, 499, 501, 503, 505, 507, 509, 511, 567, 691, 695, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1935 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16927 : P.CoversSplit 24 10 16927 0x8000800000000000800080000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000080008000000000000000000000000000800080000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 517, 523, 524, 528, 573, 578, 859, 916, 1210, 1259]) (by decide +kernel)

theorem h16927 : P.leaf 34 16927 = 353586 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 16927) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 16927) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16927) (weight := rowWeight keep1 twice1) (xs := [303, 319, 367, 383, 495, 511, 831, 895, 943, 959, 1007, 1023]) check rows elimOK (by decide) (by decide) cover16927 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1939 : P.leaf 34 1939 = 353586 :=
  orient24 (v := 16927) (by decide) (by decide +kernel) h16927

theorem cover16942 : P.CoversSplit 24 10 16942 0x8000000000000000800000000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 529, 572, 859, 860, 879, 916]) (by decide +kernel)

theorem h16942 : P.leaf 34 16942 = 55840 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 16942) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16942) (weight := fun _ => 1) (xs := [831, 895, 959, 1023]) check rows elimOK (by decide) (by decide) cover16942 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1940 : P.leaf 34 1940 = 55840 :=
  orient24 (v := 16942) (by decide) (by decide +kernel) h16942

theorem cover16958 : P.CoversSplit 24 10 16958 0xc000c00000000000c000c00000000000c000c00000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000c000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 524, 529, 572, 573, 578, 859, 871, 916, 1251, 1259]) (ps := [(14, [880], [1266])]) (by decide +kernel)

theorem h16958 : P.leaf 34 16958 = 480812 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 16958) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16958) (weight := fun _ => 1) (xs := [494, 495, 510, 511, 830, 831, 878, 879, 894, 895, 942, 943, 958, 959, 1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover16958 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1941 : P.leaf 34 1941 = 480812 :=
  orient24 (v := 16958) (by decide) (by decide +kernel) h16958

theorem cover16943 : P.CoversSplit 24 10 16943 0xcc00c80088000000cc00c800880000008c000000000000008c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 529, 572, 859, 872, 879, 916, 1202, 1210]) (by decide +kernel)

theorem h16943 : P.leaf 34 16943 = 805796 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 16943) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16943) (weight := fun _ => 1) (xs := [826, 827, 831, 890, 891, 895, 923, 927, 939, 942, 943, 954, 955, 958, 959, 987, 991, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover16943 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1942 : P.leaf 34 1942 = 805796 :=
  orient24 (v := 16943) (by decide) (by decide +kernel) h16943

theorem cover16959 : P.CoversSplit 24 10 16959 0xcc00cc0088000000cc00cc0088000000cc00cc0000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 529, 572, 573, 578, 872, 916, 1202, 1210, 1217, 1251, 1259, 1308]) (ps := [(14, [958], [1266])]) (by decide +kernel)

theorem c16959_0 : P.sumLeaves 24 17366016 1024 = 2781088 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 16959) (lo := 0) (len := 1024) (W := 2781088) check rows elimOK (by decide) (by decide) cover16959 (by decide)
  decide +kernel

theorem h16959 : P.leaf 34 16959 = 2781088 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2781088)]) (.cons c16959_0 (.nil)) (by decide) (by decide))

theorem h1943 : P.leaf 34 1943 = 2781088 :=
  orient24 (v := 16959) (by decide) (by decide +kernel) h16959

theorem cover1944 : P.CoversSplit 24 10 1944 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [509]) (by decide +kernel)

theorem h1944 : P.leaf 34 1944 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1944) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1944) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1944 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16990 : P.CoversSplit 24 10 16990 0xc000c00000000000c000c00000000000800000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000c000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 523, 536, 565, 572, 573, 578, 859, 871, 916, 1210, 1259]) (ps := [(8, [622], [1266])]) (by decide +kernel)

theorem h16990 : P.leaf 34 16990 = 354864 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 16990) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16990) (weight := fun _ => 1) (xs := [494, 495, 510, 511, 831, 895, 942, 943, 958, 959, 1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover16990 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1945 : P.leaf 34 1945 = 354864 :=
  orient24 (v := 16990) (by decide) (by decide +kernel) h16990

theorem cover1946 : P.CoversSplit 24 10 1946 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [509]) (by decide +kernel)

theorem h1946 : P.leaf 34 1946 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1946) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1946) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1946 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16991 : P.CoversSplit 24 10 16991 0xc000c00000000000c000c00000000000800000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000c000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 523, 536, 565, 572, 573, 578, 859, 871, 916, 1210, 1259]) (ps := [(8, [622], [1266])]) (by decide +kernel)

theorem h16991 : P.leaf 34 16991 = 1091392 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 16991) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16991) (weight := fun _ => 1) (xs := [494, 495, 510, 511, 831, 895, 942, 943, 958, 959, 1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover16991 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1947 : P.leaf 34 1947 = 1091392 :=
  orient24 (v := 16991) (by decide) (by decide +kernel) h16991

theorem cover17006 : P.CoversSplit 24 10 17006 0x8000800000000000800080000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 572, 859, 871, 879, 916, 921, 1210, 1259]) (ps := [(14, [874], [1266])]) (by decide +kernel)

theorem h17006 : P.leaf 34 17006 = 234440 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17006) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17006) (weight := fun _ => 1) (xs := [495, 511, 831, 895, 943, 959, 1007, 1023]) check rows elimOK (by decide) (by decide) cover17006 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1948 : P.leaf 34 1948 = 234440 :=
  orient24 (v := 17006) (by decide) (by decide +kernel) h17006

theorem cover17022 : P.CoversSplit 24 10 17022 0xc000c00000000000c000c00000000000c000c00000000000c000c000000000000000000000000000000000000000000000000000000000000000000000000000c000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 573, 578, 859, 860, 871, 916, 1259]) (ps := [(8, [622], [1266])]) (by decide +kernel)

theorem h17022 : P.leaf 34 17022 = 2054128 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17022) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17022) (weight := fun _ => 1) (xs := [494, 495, 510, 511, 814, 815, 830, 831, 878, 879, 894, 895, 942, 943, 958, 959, 1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover17022 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1949 : P.leaf 34 1949 = 2054128 :=
  orient24 (v := 17022) (by decide) (by decide +kernel) h17022

theorem cover3939 : P.CoversSplit 24 10 3939 0xff000000fe0000000000000000000000ff000000fe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 515, 523, 565, 572, 915, 921, 1217, 1258, 1308]) (by decide +kernel)

theorem c3939_0 : P.sumLeaves 24 4033536 1024 = 2556660 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3939) (lo := 0) (len := 1024) (W := 2556660) check rows elimOK (by decide) (by decide) cover3939 (by decide)
  decide +kernel

theorem h3939 : P.leaf 34 3939 = 2556660 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2556660)]) (.cons c3939_0 (.nil)) (by decide) (by decide))

theorem h1950 : P.leaf 34 1950 = 2556660 :=
  orient25 (v := 3939) (by decide) (by decide +kernel) h3939

theorem cover17023 : P.CoversSplit 24 10 17023 0xcc00cc0088000000cc00cc0088000000cc00cc0088000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 573, 578, 859, 916, 1202, 1210, 1259, 1308]) (ps := [(8, [622], [1266])]) (by decide +kernel)

theorem c17023_0 : P.sumLeaves 24 17431552 1024 = 8991730 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17023) (lo := 0) (len := 1024) (W := 8991730) check rows elimOK (by decide) (by decide) cover17023 (by decide)
  decide +kernel

theorem h17023 : P.leaf 34 17023 = 8991730 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8991730)]) (.cons c17023_0 (.nil)) (by decide) (by decide))

theorem h1951 : P.leaf 34 1951 = 8991730 :=
  orient24 (v := 17023) (by decide) (by decide +kernel) h17023

theorem cover2980 : P.CoversSplit 24 10 2980 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 508, 515, 517, 522, 524, 566, 859, 879, 916, 1202, 1210, 1308]) (by decide +kernel)

theorem h2980 : P.leaf 34 2980 = 31040 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2980) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2980) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover2980 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1956 : P.leaf 34 1956 = 31040 :=
  orient4 (v := 2980) (by decide) (by decide +kernel) h2980

theorem cover1957 : P.CoversSplit 24 10 1957 0xcc000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [468, 473, 475, 515, 517, 522, 566, 860, 872, 915, 916, 1209, 1251, 1308]) (by decide +kernel)

theorem h1957 : P.leaf 34 1957 = 257384 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1957) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1957) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1957 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1958 : P.CoversSplit 24 10 1958 0xaaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 468, 515, 522, 524, 566, 860, 872, 916, 1202, 1258]) (by decide +kernel)

theorem h1958 : P.leaf 34 1958 = 547192 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1958) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1958) (weight := fun _ => 1) (xs := [497, 499, 501, 503, 505, 507, 509, 511, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1958 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1959 : P.CoversSplit 24 10 1959 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [468, 515, 517, 522, 524, 566, 860, 872, 915, 916, 1209, 1251, 1258, 1259, 1308]) (by decide +kernel)

theorem c1959_0 : P.sumLeaves 24 2006016 1024 = 1981552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1959) (lo := 0) (len := 1024) (W := 1981552) check rows elimOK (by decide) (by decide) cover1959 (by decide)
  decide +kernel

theorem h1959 : P.leaf 34 1959 = 1981552 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1981552)]) (.cons c1959_0 (.nil)) (by decide) (by decide))

theorem cover17100 : P.CoversSplit 24 10 17100 0x8000800000000000800080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 472, 473, 516, 536, 573, 859, 879]) (ps := [(14, [874], [1266])]) (by decide +kernel)

theorem h17100 : P.leaf 34 17100 = 28394 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 17100) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 17100) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17100) (weight := rowWeight keep1 twice1) (xs := [943, 959, 1007, 1023]) check rows elimOK (by decide) (by decide) cover17100 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1960 : P.leaf 34 1960 = 28394 :=
  orient24 (v := 17100) (by decide) (by decide +kernel) h17100

theorem cover1961 : P.CoversSplit 24 10 1961 0xcc000000000000000000000000000000800000000000000000000000000000000000000000000000003300000000000000000000000000000020000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 565, 860, 872, 915, 1209, 1251, 1308, 1609]) (ps := [(14, [874], [860])]) (by decide +kernel)

theorem h1961 : P.leaf 34 1961 = 277302 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1961) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1961) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 565, 688, 689, 692, 693, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1961 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17101 : P.CoversSplit 24 10 17101 0xc000c00000000000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 536, 573, 859, 860, 871, 879]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem h17101 : P.leaf 34 17101 = 242720 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17101) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17101) (weight := fun _ => 1) (xs := [942, 943, 958, 959, 1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover17101 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1962 : P.leaf 34 1962 = 242720 :=
  orient24 (v := 17101) (by decide) (by decide +kernel) h17101

theorem cover17117 : P.CoversSplit 24 10 17117 0xf000f00000000000f000f00000000000a000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000c000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 859, 860, 867, 871, 916, 921, 1210, 1259]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem h17117 : P.leaf 34 17117 = 1307760 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17117) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17117) (weight := fun _ => 1) (xs := [494, 495, 510, 511, 829, 831, 893, 895, 940, 941, 942, 943, 956, 957, 958, 959, 1004, 1005, 1006, 1007, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover17117 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1963 : P.leaf 34 1963 = 1307760 :=
  orient24 (v := 17117) (by decide) (by decide +kernel) h17117

theorem cover1964 : P.CoversSplit 24 10 1964 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000220000000000000000000000000000002000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 860, 872, 915, 1202, 1259, 1308]) (by decide +kernel)

theorem h1964 : P.leaf 34 1964 = 153545 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1964) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1964) (weight := fun _ => 1) (xs := [507, 511, 565, 689, 693, 895, 1019, 1023]) check rows elimOK (by decide) (by decide) cover1964 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1965 : P.CoversSplit 24 10 1965 0xcc000000000000000000000000000000800000000000000000000000000000000000000000000000003300000000000000000000000000000020000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 860, 872, 915, 1209, 1251, 1308, 1609]) (by decide +kernel)

theorem h1965 : P.leaf 34 1965 = 1326904 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1965) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1965) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 565, 688, 689, 692, 693, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1965 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1966 : P.CoversSplit 24 10 1966 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 860, 872, 916, 1202, 1258, 1259, 1308]) (ps := [(16, [468], [1258])]) (by decide +kernel)

theorem h1966 : P.leaf 34 1966 = 1532240 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1966) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1966) (weight := fun _ => 1) (xs := [497, 499, 501, 503, 505, 507, 509, 511, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1966 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(1928, 48), (1929, 48), (1930, 48), (1931, 48), (1932, 48), (1933, 48), (1934, 48), (1935, 48), (1939, 12), (1940, 48), (1941, 48), (1942, 48), (1943, 48), (1944, 48), (1945, 48), (1946, 48), (1947, 48), (1948, 48), (1949, 48), (1950, 48), (1951, 48), (1956, 48), (1957, 48), (1958, 48), (1959, 48), (1960, 24), (1961, 24), (1962, 48), (1963, 48), (1964, 48), (1965, 48), (1966, 48)]

theorem segOK : checkSeg 16 perms 1928 1967 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1928 1967 1452 1427933736 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1427933736)
    (SegSum.cons (w := 48) h1928 (SegSum.cons (w := 48) h1929 (SegSum.cons (w := 48) h1930 (SegSum.cons (w := 48) h1931 (SegSum.cons (w := 48) h1932 (SegSum.cons (w := 48) h1933 (SegSum.cons (w := 48) h1934 (SegSum.cons (w := 48) h1935 (SegSum.cons (w := 12) h1939 (SegSum.cons (w := 48) h1940 (SegSum.cons (w := 48) h1941 (SegSum.cons (w := 48) h1942 (SegSum.cons (w := 48) h1943 (SegSum.cons (w := 48) h1944 (SegSum.cons (w := 48) h1945 (SegSum.cons (w := 48) h1946 (SegSum.cons (w := 48) h1947 (SegSum.cons (w := 48) h1948 (SegSum.cons (w := 48) h1949 (SegSum.cons (w := 48) h1950 (SegSum.cons (w := 48) h1951 (SegSum.cons (w := 48) h1956 (SegSum.cons (w := 48) h1957 (SegSum.cons (w := 48) h1958 (SegSum.cons (w := 48) h1959 (SegSum.cons (w := 24) h1960 (SegSum.cons (w := 24) h1961 (SegSum.cons (w := 48) h1962 (SegSum.cons (w := 48) h1963 (SegSum.cons (w := 48) h1964 (SegSum.cons (w := 48) h1965 (SegSum.cons (w := 48) h1966 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S15
