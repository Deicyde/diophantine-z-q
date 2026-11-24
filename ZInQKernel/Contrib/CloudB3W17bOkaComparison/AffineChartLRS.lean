import ZInQKernel.Contrib.CloudB3W17bOkaComparison.ReindexedAffineGamma
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.ULiftBase
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytification.OverSpec

/-!
# The actual affine-chart morphism of locally ringed spaces over Oka's complex base

The morphism comes from the proved Γ(V,⊤) pullback on the actual inverse of
Hodge's algebraic étale chart.  V is the original affine open subscheme.  Its
structure morphism is only re-expressed along the genuine Spec(ULift ℂ) base
isomorphism.  No algebraic point-map witness or compatibility premise is used.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic
open scoped Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (z : ComplexPoint X)

/-- The actual affine neighbourhood selected by the canonical algebraic étale coordinates. -/
abbrev actualEtaleNativeScheme : Over (Spec (CommRingCat.of ℂ)) :=
  ComplexPoint.openScheme X (actualEtaleDatum X d z).neighborhood

local instance actualEtaleIsAffine : IsAffine (actualEtaleNativeScheme X d z).left :=
  (actualEtaleDatum X d z).isAffine

/-- The complex structure map on the actual regular coordinate algebra. -/
def actualEtaleNativeConst : ℂ →+* Γ((actualEtaleNativeScheme X d z).left, ⊤) :=
  (actualEtaleDatum X d z).coordinateRingHomOnOpen.comp MvPolynomial.C

/-- The actual algebraic affine identification respects the genuine complex structure morphism. -/
theorem actualEtaleToSpecΓ_over :
    (actualEtaleNativeScheme X d z).left.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (actualEtaleNativeConst X d z)) =
        (actualEtaleNativeScheme X d z).hom := by
  let D := actualEtaleDatum X d z
  letI := D.coordinateRingComplexAlgebra
  exact D.toSpecΓ_over

/-- The same original affine scheme identification, expressed over Oka's lifted complex base. -/
theorem actualEtaleFromSpecΓ_overULift :
    (asIso (actualEtaleNativeScheme X d z).left.toSpecΓ).inv ≫
      (overULift (actualEtaleNativeScheme X d z)).hom =
        Spec.map (CommRingCat.ofHom (uliftAlgMap (actualEtaleNativeConst X d z))) := by
  let V := actualEtaleNativeScheme X d z
  let e := asIso V.left.toSpecΓ
  have h : e.hom ≫ Spec.map (CommRingCat.ofHom (actualEtaleNativeConst X d z)) = V.hom :=
    actualEtaleToSpecΓ_over X d z
  have hi : e.inv ≫ V.hom = Spec.map (CommRingCat.ofHom (actualEtaleNativeConst X d z)) :=
    (Iso.inv_comp_eq e).2 h.symm
  change e.inv ≫ (V.hom ≫ complexULiftBaseIso.hom) = _
  calc
    e.inv ≫ (V.hom ≫ complexULiftBaseIso.hom) =
        (e.inv ≫ V.hom) ≫ complexULiftBaseIso.hom := (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom (actualEtaleNativeConst X d z)) ≫
        complexULiftBaseIso.hom := congrArg (fun m => m ≫ complexULiftBaseIso.hom) hi
    _ = Spec.map (CommRingCat.ofHom (uliftAlgMap (actualEtaleNativeConst X d z))) := by
      rw [complexULiftBaseIso, ← Spec.map_comp]
      rfl

/-- Γ–Spec is functorial in the coefficient map, written with explicit ring homomorphisms. -/
theorem toSpecAlg_comp {R S : Type} [CommRing R] [CommRing S]
    (Y : LocallyRingedSpace) (a : S →+* Y.presheaf.obj (op ⊤)) (b : R →+* S) :
    Y.toSpecOfAlgMap a ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom b) =
      Y.toSpecOfAlgMap (a.comp b) :=
  (Category.assoc _ _ _).trans (congrArg (fun m => Y.toΓSpec ≫ m)
    (Spec.locallyRingedSpaceMap_comp (CommRingCat.ofHom b) (CommRingCat.ofHom a)).symm)

/-- Actual complex-constant compatibility of the regular Γ pullback. -/
theorem actualEtaleOkaGlobalPullback_comp_const :
    (actualEtaleOkaGlobalPullback X d z).comp (uliftAlgMap (actualEtaleNativeConst X d z)) =
      uliftAlgMap (actualEtaleOkaSource X d z).algebraMap :=
  RingHom.ext fun c => actualEtaleOkaGlobalPullback_C X d z c.down

/-- The actual morphism of locally ringed spaces from the native inverse-chart Oka source to V. -/
def affineChartToNativeLRS :
    (actualEtaleOkaSource X d z).toLocallyRingedSpace ⟶
      (actualEtaleNativeScheme X d z).left.toLocallyRingedSpace :=
  (actualEtaleOkaSource X d z).toLocallyRingedSpace.toSpecOfAlgMap
    (actualEtaleOkaGlobalPullback X d z) ≫
      (asIso (actualEtaleNativeScheme X d z).left.toSpecΓ).inv.toLRSHom

/-- The constructed actual LRS morphism is over Oka's actual Spec(ULift ℂ) base. -/
theorem affineChartToNativeLRS_comp_base :
    affineChartToNativeLRS X d z ≫ (overULift (actualEtaleNativeScheme X d z)).hom.toLRSHom =
      (actualEtaleOkaSource X d z).toSpecℂ := by
  have h := congrArg Scheme.Hom.toLRSHom (actualEtaleFromSpecΓ_overULift X d z)
  change ((actualEtaleOkaSource X d z).toLocallyRingedSpace.toSpecOfAlgMap
    (actualEtaleOkaGlobalPullback X d z) ≫
      (asIso (actualEtaleNativeScheme X d z).left.toSpecΓ).inv.toLRSHom) ≫
      (overULift (actualEtaleNativeScheme X d z)).hom.toLRSHom = _
  calc
    _ = (actualEtaleOkaSource X d z).toLocallyRingedSpace.toSpecOfAlgMap
        (actualEtaleOkaGlobalPullback X d z) ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom (uliftAlgMap (actualEtaleNativeConst X d z))) :=
      (Category.assoc _ _ _).trans (congrArg (fun m =>
        (actualEtaleOkaSource X d z).toLocallyRingedSpace.toSpecOfAlgMap
          (actualEtaleOkaGlobalPullback X d z) ≫ m) h)
    _ = (actualEtaleOkaSource X d z).toLocallyRingedSpace.toSpecOfAlgMap
        ((actualEtaleOkaGlobalPullback X d z).comp
          (uliftAlgMap (actualEtaleNativeConst X d z))) := toSpecAlg_comp _ _ _
    _ = (actualEtaleOkaSource X d z).toSpecℂ :=
      congrArg (actualEtaleOkaSource X d z).toLocallyRingedSpace.toSpecOfAlgMap
        (actualEtaleOkaGlobalPullback_comp_const X d z)

/-- The actual LRS morphism, bundled over the exact complex base used by Oka. -/
def affineChartOverLRS :
    AnalyticSpace.toOverSpec.obj (actualEtaleOkaSource X d z) ⟶
      Over.mk (overULift (actualEtaleNativeScheme X d z)).hom.toLRSHom :=
  Over.homMk (affineChartToNativeLRS X d z) (affineChartToNativeLRS_comp_base X d z)

end ZInQ.Contrib.CloudB3W17bOkaComparison
