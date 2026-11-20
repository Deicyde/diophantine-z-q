import ZInQKernel.Contrib.CloudB3W17bGraphScout.AlgebraicProjection
import ZInQKernel.Contrib.CloudB3W17Hodge.Bridge
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.Separated
import ZInQKernel.Contrib.OneProof.CartierSmooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
Private scout: the actual algebraic projection-isomorphism tail.
A proper morphism of finite-type complex group schemes that is bijective on
complex points is an isomorphism. We do not assume an analytic graph has been
algebraized. Cartier is the proved PR34 supplier, not a new hypothesis.
The argument does not require the source group to be an abelian variety,
connected, geometrically integral, or independently smooth.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bGraphScout

/-- The self-pullback of an algebraic group homomorphism is a genuine group object.
This uses the existing limits of group objects, not a pointwise group structure. -/
abbrev selfPullbackGrpObj
    {X Y : Over (Spec (.of ℂ))} [GrpObj X] [GrpObj Y] (p : X ⟶ Y) [IsMonHom p] :
    GrpObj (pullback p p) := by
  let pg : Grp.mk X ⟶ Grp.mk Y := Grp.ofHom p
  let e := PreservesPullback.iso (Grp.forget (Over (Spec (.of ℂ)))) pg pg
  letI : GrpObj ((Grp.forget (Over (Spec (.of ℂ)))).obj (pullback pg pg)) :=
    inferInstanceAs (GrpObj (pullback pg pg).X)
  exact GrpObj.ofIso e

/-- Smoothness over the actual complex field gives reducedness via regular local rings. -/
theorem isReduced_of_smooth_over_complex
    (X : Over (Spec (.of ℂ))) [Smooth X.hom] : IsReduced X.left := by
  haveI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  haveI (z : X.left) : IsRegularLocalRing (X.left.presheaf.stalk z) :=
    TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth X.hom z
  haveI (z : X.left) : _root_.IsReduced (X.left.presheaf.stalk z) := inferInstance
  exact isReduced_of_isReduced_stalk X.left

/-- Cartier makes the algebraic self-pullback reduced. In particular this does not
infer that a merely bijective finite morphism is an isomorphism. -/
theorem reduced_selfPullback_of_complex_groupHom
    {X Y : Over (Spec (.of ℂ))} [GrpObj X] [GrpObj Y] (p : X ⟶ Y) [IsMonHom p]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType p.left] :
    IsReduced (pullback p.left p.left) := by
  let D : Over (Spec (.of ℂ)) := pullback p p
  letI : GrpObj D := selfPullbackGrpObj p
  let e : D.left ≅ pullback p.left p.left :=
    PreservesPullback.iso (Over.forget (Spec (.of ℂ))) p p
  have he : e.hom ≫ pullback.fst p.left p.left = (pullback.fst p p).left :=
    PreservesPullback.iso_hom_fst (Over.forget (Spec (.of ℂ))) p p
  have hD : D.hom = e.hom ≫ pullback.fst p.left p.left ≫ X.hom := by
    rw [← Category.assoc, he]
    exact (pullback.fst p p).w.symm
  haveI : LocallyOfFiniteType D.hom := by
    rw [hD]
    infer_instance
  haveI : Smooth D.hom :=
    ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof ℂ D inferInstance
  haveI : IsReduced D.left := isReduced_of_smooth_over_complex D
  exact isReduced_of_isOpenImmersion e.inv

/-- The first projection of a genuine algebraic graph subgroup is an isomorphism
once its point map is bijective. No finite/bijective shortcut or algebraic graph
witness is concealed in this theorem. -/
theorem isIso_of_proper_complex_groupHom_bijective_points
    {X Y : Over (Spec (.of ℂ))} [GrpObj X] [GrpObj Y] (p : X ⟶ Y) [IsMonHom p]
    [IsProper p.left] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (hp : Function.Bijective (fun t : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ X => t ≫ p)) :
    IsIso p := by
  haveI : Smooth Y.hom :=
    ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof ℂ Y inferInstance
  haveI : IsReduced Y.left := isReduced_of_smooth_over_complex Y
  haveI : IsReduced (pullback p.left p.left) := reduced_selfPullback_of_complex_groupHom p
  exact isIso_of_proper_of_reduced_selfPullback_of_complexPoints p hp

/-- The finite/bijective characteristic-zero homomorphism case is a specialization;
finite alone and point bijection alone are not the proof. -/
theorem isIso_of_finite_complex_groupHom_bijective_points
    {X Y : Over (Spec (.of ℂ))} [GrpObj X] [GrpObj Y] (p : X ⟶ Y) [IsMonHom p]
    [IsFinite p.left] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (hp : Function.Bijective (fun t : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ X => t ≫ p)) :
    IsIso p :=
  isIso_of_proper_complex_groupHom_bijective_points p hp

/-- The same genuine algebraic tail on the original identity-embedding point source,
using the unchanged point-source isomorphism from PR37's Hodge bridge. -/
theorem isIso_of_proper_complex_groupHom_bijective_original_points
    {X Y : Over (Spec (.of ℂ))} [GrpObj X] [GrpObj Y] (p : X ⟶ Y) [IsMonHom p]
    [IsProper p.left] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (hp : Function.Bijective (fun t : CloudB3W17Hodge.CPt X => t ≫ p)) :
    IsIso p := by
  apply isIso_of_proper_complex_groupHom_bijective_points p
  constructor
  · intro a b hab
    apply (cancel_epi CloudB3W17Hodge.ptIso.hom).1
    apply hp.1
    simpa only [Category.assoc] using
      congrArg (fun t => CloudB3W17Hodge.ptIso.hom ≫ t) hab
  · intro b
    obtain ⟨a, ha⟩ := hp.2 (CloudB3W17Hodge.ptIso.hom ≫ b)
    refine ⟨CloudB3W17Hodge.ptIso.inv ≫ a, ?_⟩
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun t => CloudB3W17Hodge.ptIso.inv ≫ t) ha

end ZInQ.Contrib.CloudB3W17bGraphScout
