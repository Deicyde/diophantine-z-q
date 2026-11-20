import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Parametrization
import ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint
import ZInQKernel.Contrib.CloudB3W17bReduced.Port.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.Group.Smooth

/-! On the fixed projective model the group object is the missing algebraic
step: properness, smoothness and geometric integrality then follow. On the
spot (c), tex 1785–1787. -/

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj PkgI3 WeierstrassCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme

namespace ZInQ.Manuscript.RC.J0Cusps

/-- The fixed projective target regarded as a scheme over the rationals. -/
abbrev projectiveTarget (E : WeierstrassCurve ℚ) : Over (Spec (.of ℚ)) :=
  Over.mk (PreparedParam.projectiveOverQ E)

/-- The abelian variety attached to a scheme group law on the fixed model.
This uses geometric reducedness over the perfect ground field, smoothness
of group schemes, and geometric connectedness from a rational section. -/
def projectiveAbVar (E : WeierstrassCurve ℚ) [GrpObj (projectiveTarget E)] : AbVar ℚ := by
  let X := projectiveTarget E
  haveI : IsIntegral X.left := isIntegral_proj E
  letI : IsProper X.hom := by
    change IsProper (PreparedParam.projectiveOverQ E)
    unfold PreparedParam.projectiveOverQ
    have := isProper_proj E
    infer_instance
  letI : GeometricallyReduced X.hom := geometricallyReduced_of_isReduced _
  letI : Smooth X.hom := by
    letI : GrpObj (Over.mk X.hom) := ‹GrpObj (projectiveTarget E)›
    exact smooth_of_grpObj X.hom
  letI : GeometricallyConnected X.hom :=
    geometricallyConnected_of_connectedSpace_of_section X.hom (η[X]).left (Over.w (η[X]))
  letI : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  exact ⟨X⟩


end ZInQ.Manuscript.RC.J0Cusps
