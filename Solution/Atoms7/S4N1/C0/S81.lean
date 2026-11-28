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

namespace RACert.S4N1.C0.S81

open RACert RACert.Problem

theorem cover24543 : P.CoversSplit 24 10 24543 0xfffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0cccccccc80008000cc00cc0080008000cccccccc80008000cc00cc0080008000fffffffff0f0a0a0fffffffff0f0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0cccccccc80008000cc00cc0080008000cc00cc0080008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [1609], [1266]), (14, [1217], [1266])]) (by decide +kernel)

def k24543 : ℕ := 0x8aef000000000000ffff8aef0000000000000000000000000000000000000000ffffffff8aef0000ffffffffffff8aef00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def t24543 : ℕ := 0x8ae000000000000ffff08ae0000000000000000000000000000000000000000ffffffff08ae0000ffffffffffff08ae00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000

noncomputable def f24543 (i : ℕ) := rowWeight k24543 t24543 i * P.leaf 24 (25132032 + i)

theorem contract24543_0 : P.leaf 30 392688 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (29, 1, 1259), (8, 0, 1266), (5, 1, 622), (14, 0, 1266), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24543_0 : rowSum f24543 0 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k24543) (twice := t24543) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 392688) rows (by decide) (by decide)).symm.trans contract24543_0)

theorem contract24543_1 : P.leaf 30 392689 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (8, 0, 1266), (5, 1, 622), (14, 0, 1266), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24543_1 : rowSum f24543 64 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k24543) (twice := t24543) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 392689) rows (by decide) (by decide)).symm.trans contract24543_1)

theorem c24543_2 : rowSum f24543 128 128 = 22230300 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24543) (keep := k24543) (twice := t24543) check rows elimOK (by decide) (by decide) cover24543 (by decide)
  decide +kernel

theorem contract24543_3 : P.leaf 30 392692 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (14, 0, 1266), (5, 1, 433), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24543_3 : rowSum f24543 256 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k24543) (twice := t24543) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 392692) rows (by decide) (by decide)).symm.trans contract24543_3)

theorem contract24543_4 : P.leaf 30 392693 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (14, 0, 1266), (5, 1, 433), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24543_4 : rowSum f24543 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k24543) (twice := t24543) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 392693) rows (by decide) (by decide)).symm.trans contract24543_4)

theorem c24543_5 : rowSum f24543 384 318 = 183991641 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24543) (keep := k24543) (twice := t24543) check rows elimOK (by decide) (by decide) cover24543 (by decide)
  decide +kernel

theorem c24543_6 : rowSum f24543 702 322 = 214096700 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24543) (keep := k24543) (twice := t24543) check rows elimOK (by decide) (by decide) cover24543 (by decide)
  decide +kernel

theorem sum24543 : rowSum f24543 0 1024 = 420318641 :=
  rowSum_append (F := f24543) (lo := 0) (n := 64) (m := 960) (A := 0) (B := 420318641) c24543_0 (rowSum_append (F := f24543) (lo := 64) (n := 64) (m := 896) (A := 0) (B := 420318641) c24543_1 (rowSum_append (F := f24543) (lo := 128) (n := 128) (m := 768) (A := 22230300) (B := 398088341) c24543_2 (rowSum_append (F := f24543) (lo := 256) (n := 64) (m := 704) (A := 0) (B := 398088341) c24543_3 (rowSum_append (F := f24543) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 398088341) c24543_4 (rowSum_append (F := f24543) (lo := 384) (n := 318) (m := 322) (A := 183991641) (B := 214096700) c24543_5 (c24543_6))))))

theorem h24543 : P.leaf 34 24543 = 420318641 :=
  leaf_weighted (k := 24) (d := 10) (H := 24543) (keep := k24543) (twice := t24543) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow5 (H := 24543) (by decide) (by decide +kernel)) sum24543

theorem cover60782 : P.CoversSplit 24 10 60782 0xfffffffffefafafafffffffffefafafafffffffffefafafafffffffffefafafaeee0eee0eee0eae00000000000000000eee0eee0eee0eae00000000000000000cc00cc00cc00c800cc33cc33cc32c832cc00cc00c800c800cc33cc33c820c8200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 572, 858, 865, 915, 1217, 1601]) (ps := [(8, [1217], [572]), (14, [1217], [915])]) (by decide +kernel)

noncomputable def f60782 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (62240768 + i)

theorem c60782_0 : rowSum f60782 0 743 = 32014484 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60782) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover60782 (by decide)
  decide +kernel

theorem c60782_1 : rowSum f60782 743 186 = 66104572 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60782) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover60782 (by decide)
  decide +kernel

theorem c60782_2 : rowSum f60782 929 95 = 70779298 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60782) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover60782 (by decide)
  decide +kernel

theorem sum60782 : rowSum f60782 0 1024 = 168898354 :=
  rowSum_append (F := f60782) (lo := 0) (n := 743) (m := 281) (A := 32014484) (B := 136883870) c60782_0 (rowSum_append (F := f60782) (lo := 743) (n := 186) (m := 95) (A := 66104572) (B := 70779298) c60782_1 (c60782_2))

theorem h60782 : P.leaf 34 60782 = 168898354 :=
  leaf_weighted (k := 24) (d := 10) (H := 60782) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 60782) (by decide) (by decide +kernel)) sum60782

theorem h24556 : P.leaf 34 24556 = 168898354 :=
  orient5 (v := 60782) (by decide) (by decide +kernel) h60782

theorem cover60783 : P.CoversSplit 24 10 60783 0xfffffffffefafafafffffffffefafafafffffffffefafafafffffffffefafafaffecffecfee8fae80000000000000000ffecffecfee8fae80000000000000000cc00cc00cc00c800cc33cc33cc32c832cc00cc00c800c800cc33cc33c820c8200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 572, 858, 865, 915, 1217, 1601]) (ps := [(8, [1217], [572]), (14, [1217], [915])]) (by decide +kernel)

noncomputable def f60783 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (62241792 + i)

theorem c60783_0 : rowSum f60783 0 725 = 49272888 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60783) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover60783 (by decide)
  decide +kernel

theorem c60783_1 : rowSum f60783 725 178 = 100574190 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60783) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover60783 (by decide)
  decide +kernel

theorem c60783_2 : rowSum f60783 903 121 = 115638668 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60783) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover60783 (by decide)
  decide +kernel

theorem sum60783 : rowSum f60783 0 1024 = 265485746 :=
  rowSum_append (F := f60783) (lo := 0) (n := 725) (m := 299) (A := 49272888) (B := 216212858) c60783_0 (rowSum_append (F := f60783) (lo := 725) (n := 178) (m := 121) (A := 100574190) (B := 115638668) c60783_1 (c60783_2))

theorem h60783 : P.leaf 34 60783 = 265485746 :=
  leaf_weighted (k := 24) (d := 10) (H := 60783) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 60783) (by decide) (by decide +kernel)) sum60783

theorem h24557 : P.leaf 34 24557 = 265485746 :=
  orient5 (v := 60783) (by decide) (by decide +kernel) h60783

theorem cover24558 : P.CoversSplit 24 10 24558 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888fffffffffafaaaaa0000000000000000fffffffffafaaaaa00330033003200220000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24558_0 : P.sumLeaves 24 25147392 491 = 44449524 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24558) (lo := 0) (len := 491) (W := 44449524) check rows elimOK (by decide) (by decide) cover24558 (by decide)
  decide +kernel

theorem c24558_1 : P.sumLeaves 24 25147883 228 = 45732498 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24558) (lo := 491) (len := 228) (W := 45732498) check rows elimOK (by decide) (by decide) cover24558 (by decide)
  decide +kernel

theorem c24558_2 : P.sumLeaves 24 25148111 148 = 57172411 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24558) (lo := 719) (len := 148) (W := 57172411) check rows elimOK (by decide) (by decide) cover24558 (by decide)
  decide +kernel

theorem c24558_3 : P.sumLeaves 24 25148259 120 = 123723385 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24558) (lo := 867) (len := 120) (W := 123723385) check rows elimOK (by decide) (by decide) cover24558 (by decide)
  decide +kernel

theorem c24558_4 : P.sumLeaves 24 25148379 37 = 99435660 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24558) (lo := 987) (len := 37) (W := 99435660) check rows elimOK (by decide) (by decide) cover24558 (by decide)
  decide +kernel

theorem h24558 : P.leaf 34 24558 = 370513478 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(491, 44449524), (228, 45732498), (148, 57172411), (120, 123723385), (37, 99435660)]) (.cons c24558_0 (.cons c24558_1 (.cons c24558_2 (.cons c24558_3 (.cons c24558_4 (.nil)))))) (by decide) (by decide))

theorem cover24559 : P.CoversSplit 24 10 24559 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888fffffffffafaaaaa0000000000000000fffffffffafaaaaa00330033003200220000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24559_0 : P.sumLeaves 24 25148416 491 = 65887033 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24559) (lo := 0) (len := 491) (W := 65887033) check rows elimOK (by decide) (by decide) cover24559 (by decide)
  decide +kernel

theorem c24559_1 : P.sumLeaves 24 25148907 228 = 77946663 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24559) (lo := 491) (len := 228) (W := 77946663) check rows elimOK (by decide) (by decide) cover24559 (by decide)
  decide +kernel

theorem c24559_2 : P.sumLeaves 24 25149135 148 = 97004138 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24559) (lo := 719) (len := 148) (W := 97004138) check rows elimOK (by decide) (by decide) cover24559 (by decide)
  decide +kernel

theorem c24559_3 : P.sumLeaves 24 25149283 120 = 177480291 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24559) (lo := 867) (len := 120) (W := 177480291) check rows elimOK (by decide) (by decide) cover24559 (by decide)
  decide +kernel

theorem c24559_4 : P.sumLeaves 24 25149403 37 = 138626286 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24559) (lo := 987) (len := 37) (W := 138626286) check rows elimOK (by decide) (by decide) cover24559 (by decide)
  decide +kernel

theorem h24559 : P.leaf 34 24559 = 556944411 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(491, 65887033), (228, 77946663), (148, 97004138), (120, 177480291), (37, 138626286)]) (.cons c24559_0 (.cons c24559_1 (.cons c24559_2 (.cons c24559_3 (.cons c24559_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24543, 24), (24556, 24), (24557, 24), (24558, 48), (24559, 48)]

theorem segOK : checkSeg 16 perms 24543 24574 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24543 24574 168 65030844456 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 65030844456)
    (SegSum.cons (w := 24) h24543 (SegSum.cons (w := 24) h24556 (SegSum.cons (w := 24) h24557 (SegSum.cons (w := 48) h24558 (SegSum.cons (w := 48) h24559 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S81
