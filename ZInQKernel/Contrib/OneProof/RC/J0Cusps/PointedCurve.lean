import ZInQKernel.HDecomp.ModCurves.Defs
import ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Basic

/-! A rational section supplies geometric connectedness of the integral
source. The same pointed curve goes into both Jacobian APIs.
Tex 1781–1787, 2937–2939; on the spot (c). -/

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace ZInQ.Manuscript.RC.J0Cusps

variable {K : Type} [Field K]

/-- Turn a section of the structure morphism into the Jacobian API's point. -/
def rationalPoint {X : Over (Spec (.of K))} (b : Spec (.of K) ⟶ X.left)
    (hb : b ≫ X.hom = 𝟙 _) : 𝟙_ (Over (Spec (.of K))) ⟶ X :=
  Over.homMk b hb

theorem isCurve_of_point (X : Over (Spec (.of K))) [IsIntegral X.left]
    [IsProper X.hom] [SmoothOfRelativeDimension 1 X.hom]
    (b : 𝟙_ (Over (Spec (.of K))) ⟶ X) : LeafModCurves.IsCurve X :=
  ⟨inferInstance, inferInstance,
    geometricallyConnected_of_connectedSpace_of_section X.hom b.left (Over.w b)⟩

/-- The same scheme as a curve in the represented Picard package. -/
def pointedSourceCurve (X : Over (Spec (.of K))) [IsIntegral X.left]
    [IsProper X.hom] [SmoothOfRelativeDimension 1 X.hom] (b : 𝟙_ (Over (Spec (.of K))) ⟶ X) :
    Curve K := by
  letI : GeometricallyConnected X.hom := (isCurve_of_point X b).geomConnected
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  letI : GeometricallyIntegral X.hom := TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  exact ⟨X⟩

/-- Select the Jacobian and its pointed morphism together. The existence
input is the existing Jacobian theorem; it does not depend on this curve or
on the choice of any map out of it. -/
def basedJacobian (hExists : LeafModCurves.JacobianExists K)
    (X : Over (Spec (.of K))) [IsIntegral X.left]
    [IsProper X.hom] [SmoothOfRelativeDimension 1 X.hom] (b : 𝟙_ (Over (Spec (.of K))) ⟶ X) :
    {p : Σ J : PkgI3.AbVar K, X ⟶ J.X // LeafModCurves.IsJacobian X b p.1 p.2} :=
  let h := hExists X (isCurve_of_point X b) b
  ⟨⟨h.choose, h.choose_spec.choose⟩, h.choose_spec.choose_spec⟩


end ZInQ.Manuscript.RC.J0Cusps
