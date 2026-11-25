/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S3N1.C0.Defs
public import Solution.Atoms6.S3N1.C0.K0
public import Solution.Atoms6.S3N1.C0.K1
public import Solution.Atoms6.S3N1.C0.K2
public import Solution.Atoms6.S3N1.C0.K3
public import Solution.Atoms6.S3N1.C0.K4
public import Solution.Atoms6.S3N1.C0.K5
public import Solution.Atoms6.S3N1.C0.K6
public import Solution.Atoms6.S3N1.C0.K7
public import Solution.Atoms6.S3N1.C0.K8
public import Solution.Atoms6.S3N1.C0.K9
public import Solution.Atoms6.S3N1.C0.K10
public import Solution.Atoms6.S3N1.C0.K11
public import Solution.Atoms6.S3N1.C0.K12
public import Solution.Atoms6.S3N1.C0.K13
public import Solution.Atoms6.S3N1.C0.K14
public import Solution.Atoms6.S3N1.C0.K15
public import Solution.Atoms6.S3N1.C0.K16
public import Solution.Atoms6.S3N1.C0.K17
public import Solution.Atoms6.S3N1.C0.K18
public import Solution.Atoms6.S3N1.C0.K19
public import Solution.Atoms6.S3N1.C0.K20
public import Solution.Atoms6.S3N1.C0.K21
public import Solution.Atoms6.S3N1.C0.K22
public import Solution.Atoms6.S3N1.C0.K23
public import Solution.Atoms6.S3N1.C0.K24
public import Solution.Atoms6.S3N1.C0.K25
public import Solution.Atoms6.S3N1.C0.K26
public import Solution.Atoms6.S3N1.C0.K27
public import Solution.Atoms6.S3N1.C0.K28
public import Solution.Atoms6.S3N1.C0.K29
public import Solution.Atoms6.S3N1.C0.K30
public import Solution.Atoms6.S3N1.C0.K31
public import Solution.Atoms6.S3N1.C0.K32
public import Solution.Atoms6.S3N1.C0.K33
public import Solution.Atoms6.S3N1.C0.K34
public import Solution.Atoms6.S3N1.C0.K35
public import Solution.Atoms6.S3N1.C0.K36
public import Solution.Atoms6.S3N1.C0.K37
public import Solution.Atoms6.S3N1.C0.K38
public import Solution.Atoms6.S3N1.C0.K39
public import Solution.Atoms6.S3N1.C0.K40
public import Solution.Atoms6.S3N1.C0.K41
public import Solution.Atoms6.S3N1.C0.K42
public import Solution.Atoms6.S3N1.C0.K43
public import Solution.Atoms6.S3N1.C0.K44
public import Solution.Atoms6.S3N1.C0.K45
public import Solution.Atoms6.S3N1.C0.K46
public import Solution.Atoms6.S3N1.C0.K47
public import Solution.Atoms6.S3N1.C0.K48
public import Solution.Atoms6.S3N1.C0.K49
public import Solution.Atoms6.S3N1.C0.K50
public import Solution.Atoms6.S3N1.C0.K51
public import Solution.Atoms6.S3N1.C0.K52
public import Solution.Atoms6.S3N1.C0.K53
public import Solution.Atoms6.S3N1.C0.K54
public import Solution.Atoms6.S3N1.C0.K55
public import Solution.Atoms6.S3N1.C0.K56
public import Solution.Atoms6.S3N1.C0.K57
public import Solution.Atoms6.S3N1.C0.K58
public import Solution.Atoms6.S3N1.C0.K59
public import Solution.Atoms6.S3N1.C0.K60
public import Solution.Atoms6.S3N1.C0.K61
public import Solution.Atoms6.S3N1.C0.K62
public import Solution.Atoms6.S3N1.C0.K63

/-! Generated certificate (see `certgen`): symmetry class 0 of type (3, 1). -/

set_option linter.style.longLine false
set_option maxRecDepth 100000

@[expose] public section

namespace RACert.S3N1.C0

open RACert RACert.Problem

theorem total : P.sumLeaves 20 0 1024 = 11044515 :=
  sumLeaves_of_chunks (cs := [(16, 4194), (16, 10150), (16, 7120), (16, 18044), (16, 13498), (16, 31009), (16, 22409), (16, 63067), (16, 7120), (16, 18044), (16, 17952), (16, 51812), (16, 22409), (16, 63067), (16, 68408), (16, 264020), (16, 17474), (16, 87426), (16, 26880), (16, 148946), (16, 115812), (16, 504320), (16, 161844), (16, 620396), (16, 26880), (16, 148946), (16, 117317), (16, 344796), (16, 161844), (16, 620396), (16, 298991), (16, 805683), (16, 4990), (16, 20126), (16, 9852), (16, 32939), (16, 18341), (16, 50276), (16, 29171), (16, 91836), (16, 9852), (16, 32939), (16, 41336), (16, 134092), (16, 29171), (16, 91836), (16, 105261), (16, 385878), (16, 20756), (16, 117672), (16, 32982), (16, 230858), (16, 142576), (16, 548000), (16, 195687), (16, 689535), (16, 32982), (16, 230858), (16, 141293), (16, 567764), (16, 195687), (16, 689535), (16, 320315), (16, 909845)])
    (.cons K0.total (.cons K16.total (.cons K32.total (.cons K48.total (.cons K64.total (.cons K80.total (.cons K96.total (.cons K112.total (.cons K128.total (.cons K144.total (.cons K160.total (.cons K176.total (.cons K192.total (.cons K208.total (.cons K224.total (.cons K240.total (.cons K256.total (.cons K272.total (.cons K288.total (.cons K304.total (.cons K320.total (.cons K336.total (.cons K352.total (.cons K368.total (.cons K384.total (.cons K400.total (.cons K416.total (.cons K432.total (.cons K448.total (.cons K464.total (.cons K480.total (.cons K496.total (.cons K512.total (.cons K528.total (.cons K544.total (.cons K560.total (.cons K576.total (.cons K592.total (.cons K608.total (.cons K624.total (.cons K640.total (.cons K656.total (.cons K672.total (.cons K688.total (.cons K704.total (.cons K720.total (.cons K736.total (.cons K752.total (.cons K768.total (.cons K784.total (.cons K800.total (.cons K816.total (.cons K832.total (.cons K848.total (.cons K864.total (.cons K880.total (.cons K896.total (.cons K912.total (.cons K928.total (.cons K944.total (.cons K960.total (.cons K976.total (.cons K992.total (.cons K1008.total (.nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 3 1 [0, 1, 2, 3, 4, 5] = 11044515 :=
  fixCountL_of_total (P := P) check rows (by decide +kernel) (by decide +kernel) total

end RACert.S3N1.C0
