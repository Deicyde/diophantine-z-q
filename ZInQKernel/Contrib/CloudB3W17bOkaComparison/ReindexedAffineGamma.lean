import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffineGammaCoordinates
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.OpenAnalyticMap

/-!
# The actual native affine-chart Γ map into a genuine Oka source's global sections

This reindexes only Euclidean coordinates along the genuine continuous linear
ULift equivalence.  The original affine scheme and its regular ring are unchanged.
The codomain is the actual global-section ring of the open Oka source, not a
substitute ring or a compatibility premise.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- Genuine finite-coordinate relabelling, preserving the complex-linear structure. -/
def affineCoordinateULift (d : ℕ) : (Fin d → ℂ) ≃L[ℂ] (ULift.{0} (Fin d) → ℂ) :=
  ((LinearEquiv.funCongrLeft ℂ ℂ (Equiv.ulift (α := Fin d)).symm).toContinuousLinearEquiv).symm

@[simp]
theorem affineCoordinateULift_symm_apply (d : ℕ) (v : ULift.{0} (Fin d) → ℂ) (i : Fin d) :
    (affineCoordinateULift d).symm v i = v (ULift.up i) := rfl

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (z : ComplexPoint X)

/-- The actual inverse-chart open in Oka's own ULift-indexed Euclidean coordinates. -/
def actualEtaleOkaOpen : Opens (ULift.{0} (Fin d) → ℂ) :=
  (affineCoordinateULift d).opensCongr (actualEtaleChartOpen X d z)

/-- The genuine open Oka source of the native affine inverse chart. -/
abbrev actualEtaleOkaSource : AnalyticSpace := euclideanOpen d (actualEtaleOkaOpen X d z)

/-- The same regular-ring pullback in Oka's ULift coordinate convention. -/
def actualEtaleOkaRingPullback :
    Γ((actualEtaleDatum X d z).neighborhood.toScheme, ⊤) →+*
      OkaRing (actualEtaleOkaOpen X d z) :=
  (OkaRing.congr (affineCoordinateULift d) (actualEtaleChartOpen X d z)).toRingHom.comp
    (actualEtaleGammaPullback X d z)

/-- Complex constants are unchanged by the native Γ map and genuine coordinate relabelling. -/
theorem actualEtaleOkaRingPullback_C (c : ℂ) :
    actualEtaleOkaRingPullback X d z
      ((actualEtaleDatum X d z).coordinateRingHomOnOpen (MvPolynomial.C c)) =
        algebraMap ℂ (OkaRing (actualEtaleOkaOpen X d z)) c :=
  (congrArg (fun s => OkaRing.congr (affineCoordinateULift d) (actualEtaleChartOpen X d z) s)
    (actualEtaleGammaPullback_C X d z c)).trans
    ((OkaRing.congr (affineCoordinateULift d) (actualEtaleChartOpen X d z)).commutes c)

/-- The ACTUAL Γ(V,⊤) → Γ(Oka-open-source,⊤) map required by Γ–Spec. -/
def actualEtaleOkaGlobalPullback :
    Γ((actualEtaleDatum X d z).neighborhood.toScheme, ⊤) →+*
      (actualEtaleOkaSource X d z).presheaf.obj (op ⊤) :=
  ((_root_.complexAffineSpace d).presheaf.map
    (homOfLE (Opens.isOpenEmbedding_obj_top (actualEtaleOkaOpen X d z)).le).op).hom.comp
      (actualEtaleOkaRingPullback X d z)

/-- The actual global-section pullback is over the genuine complex constants. -/
theorem actualEtaleOkaGlobalPullback_C (c : ℂ) :
    actualEtaleOkaGlobalPullback X d z
      ((actualEtaleDatum X d z).coordinateRingHomOnOpen (MvPolynomial.C c)) =
        (actualEtaleOkaSource X d z).algebraMap c := by
  exact (congrArg ((_root_.complexAffineSpace d).presheaf.map
    (homOfLE (Opens.isOpenEmbedding_obj_top (actualEtaleOkaOpen X d z)).le).op).hom
      (actualEtaleOkaRingPullback_C X d z c)).trans rfl

/-- The true value before restriction is the original inverse-chart point's regular value. -/
theorem actualEtaleOkaRingPullback_eval
    (s : Γ((actualEtaleDatum X d z).neighborhood.toScheme, ⊤))
    (w : actualEtaleOkaOpen X d z) :
    OkaRing.evalHom (U := actualEtaleOkaOpen X d z) w.2 (actualEtaleOkaRingPullback X d z s) =
      Point.evaluate ⊤ s (actualEtaleChartPoint X d z ((affineCoordinateULift d).symm w.1)) :=
  (actualEtaleDatum X d z).pointAlgHomHomeomorph_apply _ s

end ZInQ.Contrib.CloudB3W17bOkaComparison
