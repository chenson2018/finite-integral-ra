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

namespace RACert.S4N1.C0.S55

open RACert RACert.Problem

theorem cover8055 : P.CoversSplit 24 10 8055 0xffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000ffffffffffffa0a0ffffffffffffa0a0fffffffffafaa0a0fffffffffafaa0a00000000000000000cc00cc0080008000cc33cc3380008000cc00cc0080008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

noncomputable def f8055 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8248320 + i)

theorem c8055_0 : rowSum f8055 0 403 = 11865478 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8055) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8055 (by decide)
  decide +kernel

theorem c8055_1 : rowSum f8055 403 344 = 31132050 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8055) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8055 (by decide)
  decide +kernel

theorem c8055_2 : rowSum f8055 747 196 = 104730246 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8055) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8055 (by decide)
  decide +kernel

theorem c8055_3 : rowSum f8055 943 81 = 111341073 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8055) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8055 (by decide)
  decide +kernel

theorem sum8055 : rowSum f8055 0 1024 = 259068847 :=
  rowSum_append (F := f8055) (lo := 0) (n := 403) (m := 621) (A := 11865478) (B := 247203369) c8055_0 (rowSum_append (F := f8055) (lo := 403) (n := 344) (m := 277) (A := 31132050) (B := 216071319) c8055_1 (rowSum_append (F := f8055) (lo := 747) (n := 196) (m := 81) (A := 104730246) (B := 111341073) c8055_2 (c8055_3)))

theorem h8055 : P.leaf 34 8055 = 259068847 :=
  leaf_weighted (k := 24) (d := 10) (H := 8055) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 8055) (by decide) (by decide +kernel)) sum8055

theorem cover8056 : P.CoversSplit 24 10 8056 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc00c8008000cc00cc00c8008000cc00cc00c8008000fffffffff8a8a0a0000000000000000000000000000000000000000000000000cc00000080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 572, 916, 1209, 1210, 1601]) (ps := [(5, [565], [572]), (8, [586, 1217], [572, 1609]), (14, [923, 1217], [916])]) (by decide +kernel)

noncomputable def f8056 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8249344 + i)

theorem c8056_0 : rowSum f8056 0 787 = 2472356 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8056) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8056 (by decide)
  decide +kernel

theorem c8056_1 : rowSum f8056 787 205 = 8163900 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8056) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8056 (by decide)
  decide +kernel

theorem c8056_2 : rowSum f8056 992 32 = 5608832 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8056) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8056 (by decide)
  decide +kernel

theorem sum8056 : rowSum f8056 0 1024 = 16245088 :=
  rowSum_append (F := f8056) (lo := 0) (n := 787) (m := 237) (A := 2472356) (B := 13772732) c8056_0 (rowSum_append (F := f8056) (lo := 787) (n := 205) (m := 32) (A := 8163900) (B := 5608832) c8056_1 (c8056_2))

theorem h8056 : P.leaf 34 8056 = 16245088 :=
  leaf_weighted (k := 24) (d := 10) (H := 8056) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 8056) (by decide) (by decide +kernel)) sum8056

theorem cover8057 : P.CoversSplit 24 10 8057 0xffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000cc00cc00cc008000cc00cc00cc008000cc00cc00c8008000fffffffff8a8a0a0000000000000000000000000000000000000000000000000cc00000080000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 572, 916, 1209, 1210, 1217, 1258, 1601]) (ps := [(5, [523], [572]), (8, [586, 1217], [572, 1609]), (14, [923, 1217], [916])]) (by decide +kernel)

noncomputable def f8057 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8250368 + i)

theorem c8057_0 : rowSum f8057 0 746 = 4199428 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8057) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8057 (by decide)
  decide +kernel

theorem c8057_1 : rowSum f8057 746 193 = 16592876 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8057) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8057 (by decide)
  decide +kernel

theorem c8057_2 : rowSum f8057 939 85 = 27023592 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8057) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8057 (by decide)
  decide +kernel

theorem sum8057 : rowSum f8057 0 1024 = 47815896 :=
  rowSum_append (F := f8057) (lo := 0) (n := 746) (m := 278) (A := 4199428) (B := 43616468) c8057_0 (rowSum_append (F := f8057) (lo := 746) (n := 193) (m := 85) (A := 16592876) (B := 27023592) c8057_1 (c8057_2))

theorem h8057 : P.leaf 34 8057 = 47815896 :=
  leaf_weighted (k := 24) (d := 10) (H := 8057) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 8057) (by decide) (by decide +kernel)) sum8057

theorem cover8058 : P.CoversSplit 24 10 8058 0xffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000ffffffffffffa0a0ffffffffffffa0a0fffffffffafaa0a0fffffffffafaa0a000000000000000000000000000000000cc33cc3380008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 916, 1209, 1210, 1217, 1258, 1601, 1609]) (ps := [(8, [586], [1609])]) (by decide +kernel)

noncomputable def f8058 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8251392 + i)

theorem c8058_0 : rowSum f8058 0 417 = 2251896 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8058) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8058 (by decide)
  decide +kernel

theorem c8058_1 : rowSum f8058 417 356 = 7590720 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8058) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8058 (by decide)
  decide +kernel

theorem c8058_2 : rowSum f8058 773 181 = 17147792 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8058) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8058 (by decide)
  decide +kernel

theorem c8058_3 : rowSum f8058 954 70 = 19023420 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8058) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8058 (by decide)
  decide +kernel

theorem sum8058 : rowSum f8058 0 1024 = 46013828 :=
  rowSum_append (F := f8058) (lo := 0) (n := 417) (m := 607) (A := 2251896) (B := 43761932) c8058_0 (rowSum_append (F := f8058) (lo := 417) (n := 356) (m := 251) (A := 7590720) (B := 36171212) c8058_1 (rowSum_append (F := f8058) (lo := 773) (n := 181) (m := 70) (A := 17147792) (B := 19023420) c8058_2 (c8058_3)))

theorem h8058 : P.leaf 34 8058 = 46013828 :=
  leaf_weighted (k := 24) (d := 10) (H := 8058) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 8058) (by decide) (by decide +kernel)) sum8058

theorem cover8059 : P.CoversSplit 24 10 8059 0xffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000ffffffffffffa0a0ffffffffffffa0a0fffffffffafaa0a0fffffffffafaa0a000000000000000000000000000000000cc33cc3380008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 916, 1209, 1210, 1217, 1258, 1601, 1609]) (ps := [(8, [586], [1609])]) (by decide +kernel)

noncomputable def f8059 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8252416 + i)

theorem c8059_0 : rowSum f8059 0 417 = 4862582 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8059) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8059 (by decide)
  decide +kernel

theorem c8059_1 : rowSum f8059 417 356 = 17342166 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8059) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8059 (by decide)
  decide +kernel

theorem c8059_2 : rowSum f8059 773 181 = 48255265 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8059) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8059 (by decide)
  decide +kernel

theorem c8059_3 : rowSum f8059 954 70 = 41991328 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8059) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8059 (by decide)
  decide +kernel

theorem sum8059 : rowSum f8059 0 1024 = 112451341 :=
  rowSum_append (F := f8059) (lo := 0) (n := 417) (m := 607) (A := 4862582) (B := 107588759) c8059_0 (rowSum_append (F := f8059) (lo := 417) (n := 356) (m := 251) (A := 17342166) (B := 90246593) c8059_1 (rowSum_append (F := f8059) (lo := 773) (n := 181) (m := 70) (A := 48255265) (B := 41991328) c8059_2 (c8059_3)))

theorem h8059 : P.leaf 34 8059 = 112451341 :=
  leaf_weighted (k := 24) (d := 10) (H := 8059) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 8059) (by decide) (by decide +kernel)) sum8059

def seg : List (ℕ × ℕ) := [(8055, 24), (8056, 24), (8057, 24), (8058, 24), (8059, 24)]

theorem segOK : checkSeg 16 perms 8055 8060 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8055 8060 120 11558280000 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 11558280000)
    (SegSum.cons (w := 24) h8055 (SegSum.cons (w := 24) h8056 (SegSum.cons (w := 24) h8057 (SegSum.cons (w := 24) h8058 (SegSum.cons (w := 24) h8059 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S55
