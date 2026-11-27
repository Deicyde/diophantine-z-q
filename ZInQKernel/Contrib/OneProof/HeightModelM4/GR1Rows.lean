import ZInQKernel.Contrib.OneProof.HeightModelM3.GR1Rows
import ZInQKernel.Contrib.OneProof.HeightModelM4.Wedge

/-! # The GR1 rows, with the wedge identity proved

`HeightModelM2.IsGR1StableHeightGlobal` takes the lattice `globalDetLattice` of global sections of
`ε*Ω^g`. `Wedge.lean` proves that the Hodge line carries the natural action of `𝒪_S(V)` through
restriction to the generic point, that this action multiplies one factor of a wedge by a lift of
`c` (`germEtaField_smul_wedge`), and that `detSec V W` and `globalDetLattice` are submodules for it
(`detSecSubmodule`, `globalDetLatticeSubmodule`). The rows over that predicate give the bundle's
fields (`HeightModelM2.gaudronRemondThm14GR1Global_iff`,
`HeightModelM2.gaudronRemondSec9LowerGR1WeakGlobal_iff`); this file restates the two
implications. -/

namespace ZInQ.HeightModelM4

/-- The field `gaudronRemondThm14GR1` from Thm 1.4 over GR1's own model and lattice. -/
theorem gaudronRemondThm14GR1_of_global_wedge
    (h : ZInQ.HeightModelM2.GaudronRemondThm14GR1Global) :
    ZInQ.HeightModelM.GaudronRemondThm14GR1 :=
  ZInQ.HeightModelM2.gaudronRemondThm14GR1Global_iff.mp h

/-- The field `gaudronRemondSec9LowerGR1Weak` from the weak Cor. 8.4 over GR1's own model and
lattice. -/
theorem gaudronRemondSec9LowerGR1Weak_of_global_wedge
    (h : ZInQ.HeightModelM2.GaudronRemondSec9LowerGR1WeakGlobal) :
    ZInQ.HeightModelM.GaudronRemondSec9LowerGR1Weak :=
  ZInQ.HeightModelM2.gaudronRemondSec9LowerGR1WeakGlobal_iff.mp h

end ZInQ.HeightModelM4
