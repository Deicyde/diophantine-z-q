import ZInQKernel.Contrib.RLeaf.T36Torsion
import ZInQKernel.Contrib.RLeaf.T37GoodReduction

/-!
# rleaf-elliptic: the glue target `BelyiX1` proved outright

`X1Belyi.belyiX1_of_leaves : TorsionStructure → GoodReductionUnramified → BelyiX1`
(ZInQKernel/HDecomp/ModCurves/X1Belyi.lean) derives `LeafModCurves.BelyiX1` (`j/1728` is a Belyi
function on `K_N = ℚ(j)(x(P))`, and `[K_N : ℚ(j)] ≤ N²`) from the leaves T36 and T37. Both are now
theorems (`ZInQ.RLeaf.t36_torsionStructure`, `ZInQ.RLeaf.T37.t37_goodReductionUnramified`), so
`BelyiX1` holds with no hypotheses. The bundle field `X1Leaves` keeps three open fields
(`curve` T38, `constants` T39, `cusp` T40); `x1Leaves_of` packages the two proved ones.
-/

namespace ZInQ.RLeaf

/-- **`LeafModCurves.BelyiX1`, proved** (from T36 and T37). -/
theorem belyiX1 : LeafModCurves.BelyiX1 :=
  X1Belyi.belyiX1_of_leaves t36_torsionStructure T37.t37_goodReductionUnramified

/-- The x1-belyi bundle with T36 and T37 discharged: only T38, T39, T40 remain. -/
theorem x1Leaves_of (hC : X1Belyi.CurveOfFunctionFieldQ) (hK : X1Belyi.X1ConstantField)
    (hR : X1Belyi.X1RationalCusp) : X1Belyi.X1Leaves :=
  ⟨t36_torsionStructure, T37.t37_goodReductionUnramified, hC, hK, hR⟩

/-- `X1ModelExists` from T38, T39, T40 alone (T36 discharged). -/
theorem x1ModelExists_of (hC : X1Belyi.CurveOfFunctionFieldQ) (hK : X1Belyi.X1ConstantField)
    (hR : X1Belyi.X1RationalCusp) : LeafModCurves.X1ModelExists :=
  X1Belyi.x1ModelExists_of_leaves t36_torsionStructure hC hK hR

end ZInQ.RLeaf

#print axioms ZInQ.RLeaf.belyiX1
#print axioms ZInQ.RLeaf.x1Leaves_of
#print axioms ZInQ.RLeaf.x1ModelExists_of
