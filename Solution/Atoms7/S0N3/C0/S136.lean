/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C0

open RACert RACert.Problem

namespace S136

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(1044838, 24), (1044839, 24), (1044840, 12), (1044841, 24), (1044842, 24), (1044843, 24), (1044844, 24), (1044845, 24), (1044846, 24), (1044847, 24), (1044851, 24), (1044852, 24), (1044853, 24), (1044854, 24), (1044855, 24), (1044856, 24), (1044857, 24), (1044858, 24), (1044859, 24), (1044860, 24), (1044861, 24), (1044862, 24), (1044863, 24), (1044931, 12), (1044935, 24), (1044943, 12), (1044945, 24), (1044946, 24), (1044947, 24), (1044949, 24), (1044950, 24), (1044951, 24), (1044953, 24), (1044954, 24), (1044955, 24), (1044956, 12), (1044957, 24), (1044958, 24), (1044959, 24), (1044976, 12)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(1044838, 2838), (1044839, 4044), (1044840, 942), (1044841, 1406), (1044842, 1876), (1044843, 2809), (1044844, 3768), (1044845, 3952), (1044846, 5064), (1044847, 9740), (1044851, 1655), (1044852, 2658), (1044853, 3625), (1044854, 3681), (1044855, 5081), (1044856, 2111), (1044857, 2759), (1044858, 2719), (1044859, 4156), (1044860, 5568), (1044861, 6170), (1044862, 6154), (1044863, 12235), (1044931, 1284), (1044935, 2162), (1044943, 2250), (1044945, 2900), (1044946, 2187), (1044947, 5835), (1044949, 5832), (1044950, 4934), (1044951, 8714), (1044953, 6086), (1044954, 4463), (1044955, 8943), (1044956, 8388), (1044957, 10318), (1044958, 8814), (1044959, 22818), (1044976, 760)]

theorem l1044838 : P.leaf 18 1044838 = 2838 := by decide +kernel

theorem l1044839 : P.leaf 18 1044839 = 4044 := by decide +kernel

theorem l1044840 : P.leaf 18 1044840 = 942 := by decide +kernel

theorem l1044841 : P.leaf 18 1044841 = 1406 := by decide +kernel

theorem l1044842 : P.leaf 18 1044842 = 1876 := by decide +kernel

theorem l1044843 : P.leaf 18 1044843 = 2809 := by decide +kernel

theorem l1044844 : P.leaf 18 1044844 = 3768 := by decide +kernel

theorem l1044845 : P.leaf 18 1044845 = 3952 := by decide +kernel

theorem l1044846 : P.leaf 18 1044846 = 5064 := by decide +kernel

theorem l1044847 : P.leaf 18 1044847 = 9740 := by decide +kernel

theorem l1044851 : P.leaf 18 1044851 = 1655 := by decide +kernel

theorem l1044852 : P.leaf 18 1044852 = 2658 := by decide +kernel

theorem l1044853 : P.leaf 18 1044853 = 3625 := by decide +kernel

theorem l1044854 : P.leaf 18 1044854 = 3681 := by decide +kernel

theorem l1044855 : P.leaf 18 1044855 = 5081 := by decide +kernel

theorem l1044856 : P.leaf 18 1044856 = 2111 := by decide +kernel

theorem l1044857 : P.leaf 18 1044857 = 2759 := by decide +kernel

theorem l1044858 : P.leaf 18 1044858 = 2719 := by decide +kernel

theorem l1044859 : P.leaf 18 1044859 = 4156 := by decide +kernel

theorem l1044860 : P.leaf 18 1044860 = 5568 := by decide +kernel

theorem l1044861 : P.leaf 18 1044861 = 6170 := by decide +kernel

theorem l1044862 : P.leaf 18 1044862 = 6154 := by decide +kernel

theorem l1044863 : P.leaf 18 1044863 = 12235 := by decide +kernel

theorem l1044931 : P.leaf 18 1044931 = 1284 := by decide +kernel

theorem l1044935 : P.leaf 18 1044935 = 2162 := by decide +kernel

theorem l1044943 : P.leaf 18 1044943 = 2250 := by decide +kernel

theorem l1044945 : P.leaf 18 1044945 = 2900 := by decide +kernel

theorem l1044946 : P.leaf 18 1044946 = 2187 := by decide +kernel

theorem l1044947 : P.leaf 18 1044947 = 5835 := by decide +kernel

theorem l1044949 : P.leaf 18 1044949 = 5832 := by decide +kernel

theorem l1044950 : P.leaf 18 1044950 = 4934 := by decide +kernel

theorem l1044951 : P.leaf 18 1044951 = 8714 := by decide +kernel

theorem l1044953 : P.leaf 18 1044953 = 6086 := by decide +kernel

theorem l1044954 : P.leaf 18 1044954 = 4463 := by decide +kernel

theorem l1044955 : P.leaf 18 1044955 = 8943 := by decide +kernel

theorem l1044956 : P.leaf 18 1044956 = 8388 := by decide +kernel

theorem l1044957 : P.leaf 18 1044957 = 10318 := by decide +kernel

theorem l1044958 : P.leaf 18 1044958 = 8814 := by decide +kernel

theorem l1044959 : P.leaf 18 1044959 = 22818 := by decide +kernel

theorem l1044976 : P.leaf 18 1044976 = 760 := by decide +kernel

theorem segOK : checkSeg 20 perms 1044838 1044977 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 4677288 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 1044838 1044977 900 4677288 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l1044838 (.cons l1044839 (.cons l1044840 (.cons l1044841 (.cons l1044842 (.cons l1044843 (.cons l1044844 (.cons l1044845 (.cons l1044846 (.cons l1044847 (.cons l1044851 (.cons l1044852 (.cons l1044853 (.cons l1044854 (.cons l1044855 (.cons l1044856 (.cons l1044857 (.cons l1044858 (.cons l1044859 (.cons l1044860 (.cons l1044861 (.cons l1044862 (.cons l1044863 (.cons l1044931 (.cons l1044935 (.cons l1044943 (.cons l1044945 (.cons l1044946 (.cons l1044947 (.cons l1044949 (.cons l1044950 (.cons l1044951 (.cons l1044953 (.cons l1044954 (.cons l1044955 (.cons l1044956 (.cons l1044957 (.cons l1044958 (.cons l1044959 (.cons l1044976 (.nil))))))))))))))))))))))))))))))))))))))))))

end S136

end RACert.S0N3.C0
