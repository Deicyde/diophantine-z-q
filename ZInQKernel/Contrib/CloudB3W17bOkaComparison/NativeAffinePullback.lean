import ZInQKernel.Contrib.CloudB3W17Hodge.Bridge
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.StructureSheaf

/-!
# Affine Γ-to-Oka pullback for the actual algebraic étale source chart

The chart is the exact LocalEtaleCoordinates datum used by the unchanged
native Hodge atlas.  Every regular section is analytically evaluated on its
inverse, and these evaluations form one actual ring homomorphism into OkaRing,
not only a family of scalar functions.  This is the affine input to Oka's
Γ–Spec/analytification universal property; no algebraic F witness is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (z : ComplexPoint X)

/-- The ACTUAL chosen algebraic étale coordinate datum, not arbitrary strong coordinates. -/
abbrev actualEtaleDatum := ComplexPoint.localEtaleCoordinates X d z

/-- The native inverse chart's actual open Euclidean target. -/
def actualEtaleChartOpen : Opens (Fin d → ℂ) :=
  ⟨(ComplexPoint.coordinateNeighborhoodChart X d z).target,
    (ComplexPoint.coordinateNeighborhoodChart X d z).open_target⟩

/-- A chart point, as an actual complex point of the genuine affine neighbourhood V. -/
def actualEtaleChartPoint (w : Fin d → ℂ) :
    ComplexPoint (ComplexPoint.openScheme X (actualEtaleDatum X d z).neighborhood) :=
  (ComplexPoint.openHomeomorph X (actualEtaleDatum X d z).neighborhood).symm
    ((ComplexPoint.coordinateNeighborhoodChart X d z).symm w)

/-- Every Γ(V,⊤) evaluation along the actual native inverse chart is analytic. -/
theorem analyticAt_actualEtaleChart_eval
    (s : Γ((actualEtaleDatum X d z).neighborhood.toScheme, ⊤))
    {w : Fin d → ℂ} (hw : w ∈ actualEtaleChartOpen X d z) :
    AnalyticAt ℂ (fun v => (actualEtaleDatum X d z).pointAlgHomHomeomorph
      (actualEtaleChartPoint X d z v) s) w :=
  (actualEtaleDatum X d z).analyticAt_ambientProjectionChart_symm_pointAlgHom_apply
    (ComplexPoint.pointInCoordinateNeighborhood X d z) hw s

/-- The affine regular ring maps into the genuine Oka ring of this actual chart. -/
def actualEtaleGammaPullback :
    Γ((actualEtaleDatum X d z).neighborhood.toScheme, ⊤) →+*
      OkaRing (actualEtaleChartOpen X d z) where
  toFun s := OkaRing.mk
    (fun w => (actualEtaleDatum X d z).pointAlgHomHomeomorph
      (actualEtaleChartPoint X d z w.1) s)
    (okaAnalytic_restrict (fun _ hw => analyticAt_actualEtaleChart_eval X d z s hw))
  map_one' := by
    apply OkaRing.ext
    funext w
    exact map_one _
  map_mul' s t := by
    apply OkaRing.ext
    funext w
    exact map_mul _ s t
  map_zero' := by
    apply OkaRing.ext
    funext w
    exact map_zero _
  map_add' s t := by
    apply OkaRing.ext
    funext w
    exact map_add _ s t

/-- The Γ-to-Oka map has the original point value on every representative. -/
theorem actualEtaleGammaPullback_eval
    (s : Γ((actualEtaleDatum X d z).neighborhood.toScheme, ⊤))
    (w : actualEtaleChartOpen X d z) :
    OkaRing.evalHom w.2 (actualEtaleGammaPullback X d z s) =
      Point.evaluate ⊤ s (actualEtaleChartPoint X d z w.1) :=
  (actualEtaleDatum X d z).pointAlgHomHomeomorph_apply _ s

end ZInQ.Contrib.CloudB3W17bOkaComparison
