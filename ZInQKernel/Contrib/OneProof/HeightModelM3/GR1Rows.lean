import ZInQKernel.Contrib.OneProof.HeightModelM2.GR1Rows
import ZInQKernel.Contrib.OneProof.HeightModelM3.Spans
import ZInQKernel.Contrib.OneProof.HeightModelM3.StalkInjective

/-! # The GR1 rows, with the readings of `HeightModelM2` closed

`HeightModelM2.IsGR1StableHeightGlobal` asks for a commutative semi-abelian model and takes the
lattice `globalDetLattice` of global sections of `ε*Ω^g`. Its three readings are now theorems, up
to the two readings listed in this directory's README: the stalks of `e*Ω¹` inject into the
generic fibre (`stalkToGeneric_injective`, `mem_globalOmega_iff`), `secOmega` is an
`𝒪_S(V)`-module and the generating wedges of `detSec` are closed under one-factor multiplication
(`germEta_smul_mem_secOmega`, `smul_wedge_mem_detSec`), and the wedges of images of `θ` are all
wedges (`theta_surjective`, `map_comap_secOmega`). The rows over
that predicate give the bundle's fields (`HeightModelM2.gaudronRemondThm14GR1Global_iff`,
`HeightModelM2.gaudronRemondSec9LowerGR1WeakGlobal_iff`); this file restates the two
implications. -/

namespace ZInQ.HeightModelM3

/-- The field `gaudronRemondThm14GR1` from Thm 1.4 over GR1's own model and lattice. -/
theorem gaudronRemondThm14GR1_of_global
    (h : ZInQ.HeightModelM2.GaudronRemondThm14GR1Global) :
    ZInQ.HeightModelM.GaudronRemondThm14GR1 :=
  ZInQ.HeightModelM2.gaudronRemondThm14GR1Global_iff.mp h

/-- The field `gaudronRemondSec9LowerGR1Weak` from the weak Cor. 8.4 over GR1's own model and
lattice. -/
theorem gaudronRemondSec9LowerGR1Weak_of_global
    (h : ZInQ.HeightModelM2.GaudronRemondSec9LowerGR1WeakGlobal) :
    ZInQ.HeightModelM.GaudronRemondSec9LowerGR1Weak :=
  ZInQ.HeightModelM2.gaudronRemondSec9LowerGR1WeakGlobal_iff.mp h

end ZInQ.HeightModelM3
