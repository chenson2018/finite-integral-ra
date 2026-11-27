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

namespace RACert.S6N0.C0.S3

open RACert RACert.Problem

theorem cover1537 : P.CoversSplit 26 10 1537 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1537_0 : P.sumLeaves 26 1573888 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1537) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1537 (by decide)
  decide +kernel

theorem h1537 : P.leaf 36 1537 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1537_0 (.nil)) (by decide) (by decide))

theorem cover1539 : P.CoversSplit 26 10 1539 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1539_0 : P.sumLeaves 26 1575936 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1539) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1539 (by decide)
  decide +kernel

theorem h1539 : P.leaf 36 1539 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1539_0 (.nil)) (by decide) (by decide))

theorem cover1541 : P.CoversSplit 26 10 1541 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c1541_0 : P.sumLeaves 26 1577984 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1541) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1541 (by decide)
  decide +kernel

theorem h1541 : P.leaf 36 1541 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1541_0 (.nil)) (by decide) (by decide))

theorem cover1543 : P.CoversSplit 26 10 1543 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c1543_0 : P.sumLeaves 26 1580032 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1543) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1543 (by decide)
  decide +kernel

theorem h1543 : P.leaf 36 1543 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1543_0 (.nil)) (by decide) (by decide))

theorem cover1551 : P.CoversSplit 26 10 1551 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c1551_0 : P.sumLeaves 26 1588224 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1551) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1551 (by decide)
  decide +kernel

theorem h1551 : P.leaf 36 1551 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1551_0 (.nil)) (by decide) (by decide))

theorem cover1555 : P.CoversSplit 26 10 1555 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1555_0 : P.sumLeaves 26 1592320 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1555) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1555 (by decide)
  decide +kernel

theorem h1555 : P.leaf 36 1555 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1555_0 (.nil)) (by decide) (by decide))

theorem cover1556 : P.CoversSplit 26 10 1556 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c1556_0 : P.sumLeaves 26 1593344 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1556) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1556 (by decide)
  decide +kernel

theorem h1556 : P.leaf 36 1556 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1556_0 (.nil)) (by decide) (by decide))

theorem cover1557 : P.CoversSplit 26 10 1557 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1557_0 : P.sumLeaves 26 1594368 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1557) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1557 (by decide)
  decide +kernel

theorem h1557 : P.leaf 36 1557 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1557_0 (.nil)) (by decide) (by decide))

theorem cover1559 : P.CoversSplit 26 10 1559 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1559_0 : P.sumLeaves 26 1596416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1559) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1559 (by decide)
  decide +kernel

theorem h1559 : P.leaf 36 1559 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1559_0 (.nil)) (by decide) (by decide))

theorem cover1564 : P.CoversSplit 26 10 1564 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c1564_0 : P.sumLeaves 26 1601536 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1564) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1564 (by decide)
  decide +kernel

theorem h1564 : P.leaf 36 1564 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1564_0 (.nil)) (by decide) (by decide))

theorem cover1565 : P.CoversSplit 26 10 1565 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1565_0 : P.sumLeaves 26 1602560 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1565) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1565 (by decide)
  decide +kernel

theorem h1565 : P.leaf 36 1565 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1565_0 (.nil)) (by decide) (by decide))

theorem cover1567 : P.CoversSplit 26 10 1567 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1567_0 : P.sumLeaves 26 1604608 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1567) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1567 (by decide)
  decide +kernel

theorem h1567 : P.leaf 36 1567 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1567_0 (.nil)) (by decide) (by decide))

theorem cover1572 : P.CoversSplit 26 10 1572 0xc0000c0000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000030000300000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 489, 538, 622, 881, 922, 972, 979, 1265]) (by decide +kernel)

theorem c1572_0 : P.sumLeaves 26 1609728 1024 = 1284 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1572) (lo := 0) (len := 1024) (W := 1284) check rows elimOK (by decide) (by decide) cover1572 (by decide)
  decide +kernel

theorem h1572 : P.leaf 36 1572 = 1284 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1284)]) (.cons c1572_0 (.nil)) (by decide) (by decide))

theorem cover1573 : P.CoversSplit 26 10 1573 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1573_0 : P.sumLeaves 26 1610752 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1573) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1573 (by decide)
  decide +kernel

theorem h1573 : P.leaf 36 1573 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1573_0 (.nil)) (by decide) (by decide))

theorem cover1574 : P.CoversSplit 26 10 1574 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c1574_0 : P.sumLeaves 26 1611776 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1574) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1574 (by decide)
  decide +kernel

theorem h1574 : P.leaf 36 1574 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1574_0 (.nil)) (by decide) (by decide))

theorem cover1575 : P.CoversSplit 26 10 1575 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1575_0 : P.sumLeaves 26 1612800 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1575) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1575 (by decide)
  decide +kernel

theorem h1575 : P.leaf 36 1575 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1575_0 (.nil)) (by decide) (by decide))

theorem cover1576 : P.CoversSplit 26 10 1576 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem c1576_0 : P.sumLeaves 26 1613824 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1576) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1576 (by decide)
  decide +kernel

theorem h1576 : P.leaf 36 1576 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1576_0 (.nil)) (by decide) (by decide))

theorem cover1577 : P.CoversSplit 26 10 1577 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem c1577_0 : P.sumLeaves 26 1614848 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1577) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1577 (by decide)
  decide +kernel

theorem h1577 : P.leaf 36 1577 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1577_0 (.nil)) (by decide) (by decide))

theorem cover1578 : P.CoversSplit 26 10 1578 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1578_0 : P.sumLeaves 26 1615872 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1578) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1578 (by decide)
  decide +kernel

theorem h1578 : P.leaf 36 1578 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1578_0 (.nil)) (by decide) (by decide))

theorem cover1579 : P.CoversSplit 26 10 1579 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1579_0 : P.sumLeaves 26 1616896 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1579) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1579 (by decide)
  decide +kernel

theorem h1579 : P.leaf 36 1579 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1579_0 (.nil)) (by decide) (by decide))

theorem cover1580 : P.CoversSplit 26 10 1580 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1580_0 : P.sumLeaves 26 1617920 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1580) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1580 (by decide)
  decide +kernel

theorem h1580 : P.leaf 36 1580 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1580_0 (.nil)) (by decide) (by decide))

theorem cover1581 : P.CoversSplit 26 10 1581 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1581_0 : P.sumLeaves 26 1618944 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1581) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1581 (by decide)
  decide +kernel

theorem h1581 : P.leaf 36 1581 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1581_0 (.nil)) (by decide) (by decide))

theorem cover1582 : P.CoversSplit 26 10 1582 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1582_0 : P.sumLeaves 26 1619968 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1582) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1582 (by decide)
  decide +kernel

theorem h1582 : P.leaf 36 1582 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1582_0 (.nil)) (by decide) (by decide))

theorem cover1583 : P.CoversSplit 26 10 1583 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1583_0 : P.sumLeaves 26 1620992 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1583) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1583 (by decide)
  decide +kernel

theorem h1583 : P.leaf 36 1583 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1583_0 (.nil)) (by decide) (by decide))

theorem cover1590 : P.CoversSplit 26 10 1590 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c1590_0 : P.sumLeaves 26 1628160 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1590) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1590 (by decide)
  decide +kernel

theorem h1590 : P.leaf 36 1590 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1590_0 (.nil)) (by decide) (by decide))

theorem cover1591 : P.CoversSplit 26 10 1591 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1591_0 : P.sumLeaves 26 1629184 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1591) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1591 (by decide)
  decide +kernel

theorem h1591 : P.leaf 36 1591 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1591_0 (.nil)) (by decide) (by decide))

theorem cover1594 : P.CoversSplit 26 10 1594 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1594_0 : P.sumLeaves 26 1632256 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1594) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1594 (by decide)
  decide +kernel

theorem h1594 : P.leaf 36 1594 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1594_0 (.nil)) (by decide) (by decide))

theorem cover1595 : P.CoversSplit 26 10 1595 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem c1595_0 : P.sumLeaves 26 1633280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1595) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1595 (by decide)
  decide +kernel

theorem h1595 : P.leaf 36 1595 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1595_0 (.nil)) (by decide) (by decide))

theorem cover1596 : P.CoversSplit 26 10 1596 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1596_0 : P.sumLeaves 26 1634304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1596) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1596 (by decide)
  decide +kernel

theorem h1596 : P.leaf 36 1596 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1596_0 (.nil)) (by decide) (by decide))

theorem cover1597 : P.CoversSplit 26 10 1597 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem c1597_0 : P.sumLeaves 26 1635328 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1597) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1597 (by decide)
  decide +kernel

theorem h1597 : P.leaf 36 1597 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1597_0 (.nil)) (by decide) (by decide))

theorem cover1598 : P.CoversSplit 26 10 1598 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1598_0 : P.sumLeaves 26 1636352 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1598) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1598 (by decide)
  decide +kernel

theorem h1598 : P.leaf 36 1598 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1598_0 (.nil)) (by decide) (by decide))

theorem cover1599 : P.CoversSplit 26 10 1599 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem c1599_0 : P.sumLeaves 26 1637376 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1599) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1599 (by decide)
  decide +kernel

theorem h1599 : P.leaf 36 1599 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1599_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1537, 180), (1539, 180), (1541, 360), (1543, 360), (1551, 90), (1555, 60), (1556, 360), (1557, 720), (1559, 360), (1564, 180), (1565, 360), (1567, 180), (1572, 180), (1573, 360), (1574, 720), (1575, 720), (1576, 360), (1577, 360), (1578, 720), (1579, 720), (1580, 720), (1581, 720), (1582, 720), (1583, 720), (1590, 360), (1591, 360), (1594, 360), (1595, 360), (1596, 720), (1597, 720), (1598, 720), (1599, 720)]

theorem segOK : checkSeg 20 perms 1537 1644 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 1537 1644 14730 231120 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 231120)
    (SegSum.cons (w := 180) h1537 (SegSum.cons (w := 180) h1539 (SegSum.cons (w := 360) h1541 (SegSum.cons (w := 360) h1543 (SegSum.cons (w := 90) h1551 (SegSum.cons (w := 60) h1555 (SegSum.cons (w := 360) h1556 (SegSum.cons (w := 720) h1557 (SegSum.cons (w := 360) h1559 (SegSum.cons (w := 180) h1564 (SegSum.cons (w := 360) h1565 (SegSum.cons (w := 180) h1567 (SegSum.cons (w := 180) h1572 (SegSum.cons (w := 360) h1573 (SegSum.cons (w := 720) h1574 (SegSum.cons (w := 720) h1575 (SegSum.cons (w := 360) h1576 (SegSum.cons (w := 360) h1577 (SegSum.cons (w := 720) h1578 (SegSum.cons (w := 720) h1579 (SegSum.cons (w := 720) h1580 (SegSum.cons (w := 720) h1581 (SegSum.cons (w := 720) h1582 (SegSum.cons (w := 720) h1583 (SegSum.cons (w := 360) h1590 (SegSum.cons (w := 360) h1591 (SegSum.cons (w := 360) h1594 (SegSum.cons (w := 360) h1595 (SegSum.cons (w := 720) h1596 (SegSum.cons (w := 720) h1597 (SegSum.cons (w := 720) h1598 (SegSum.cons (w := 720) h1599 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S3
