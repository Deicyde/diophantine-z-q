/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Additive finite-stage consumer of an ACTUAL ordinary-residue augmentation.
Every field map and the original R→R/m inclusion are preserved as scheme
morphisms. No stage inclusion/injectivity, model, properness, hdesc or
quotient is assumed. This does not construct a henselization or a MODEL.
All previously frozen nineteen Lane5 files remain unchanged.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.ResiduePoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.OrdinaryStages

/-- The actual structure morphism of the given finite étale stage. -/
def stageBase (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R B))

/-- The actual κ(R)-point obtained from the stage's ORIGINAL augmentation. -/
def stagePoint {R B : Type u} [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]
    (aug : B →ₐ[R] IsLocalRing.ResidueField R) :
    Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom aug.toRingHom)

/-- It lies over the original quotient map, not over a strict residue field. -/
@[reassoc]
theorem stagePoint_comp {R B : Type u} [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]
    (aug : B →ₐ[R] IsLocalRing.ResidueField R) :
    stagePoint aug ≫ stageBase R B = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
  unfold stagePoint stageBase
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact (aug.commutes r).trans (RingHom.congr_fun (IsLocalRing.ResidueField.algebraMap_eq R) r)

/-- The refined affine neighbourhood and its original residue point, with
    the whole special-fibre isomorphism and faithful flatness PROVED below.
    This is constructed data, not an assumed effective descended model. -/
structure StageRefinement (R B : Type u) [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]
    (aug : B →ₐ[R] IsLocalRing.ResidueField R) where
  V : (Spec (CommRingCat.of B)).Opens
  affine : IsAffineOpen V
  etale : Etale (V.ι ≫ stageBase R B)
  surjective : Surjective (V.ι ≫ stageBase R B)
  quasiCompact : QuasiCompact (V.ι ≫ stageBase R B)
  wholeFibre : IsIso ((V.ι ≫ stageBase R B).fiberToSpecResidueField (IsLocalRing.closedPoint R))
  faithfullyFlat : (PointedRefinement.affineStructureMap (V.ι ≫ stageBase R B)).FaithfullyFlat
  point : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ V.toScheme
  point_inclusion : point ≫ V.ι = stagePoint aug
  point_base : point ≫ (V.ι ≫ stageBase R B) = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

/-- Every ACTUAL finite étale stage augmentation has a refined affine étale
    faithfully-flat neighbourhood with entire special fibre Spec κ(R).
    No injectivity of its stage map or of a transition is used. -/
theorem exists_stageRefinement {R B : Type u} [CommRing R] [IsLocalRing R] [CommRing B]
    [Algebra R B] [Algebra.Etale R B] (aug : B →ₐ[R] IsLocalRing.ResidueField R) :
    Nonempty (StageRefinement R B aug) := by
  haveI : Etale (stageBase R B) := by
    rw [stageBase, HasRingHomProperty.Spec_iff (P := @Etale)]
    change (algebraMap R B).Etale
    exact RingHom.etale_algebraMap.mpr inferInstance
  obtain ⟨V, hV, hE, hS, hQ, hF, hFF, x, hinc, hbase⟩ :=
    PointedRefinement.exists_affine_refinement_from_original_residue
      (stageBase R B) (stagePoint aug) (stagePoint_comp aug)
  exact ⟨⟨V, hV, hE, hS, hQ, hF, hFF, x, hinc, hbase⟩⟩

/-- Raw stage transitions retain their compatible ordinary-residue point.
    This does not assert that a simultaneous choice of affine shrinks is
    already a filtered diagram or a model-descent theorem. -/
@[reassoc]
theorem stagePoint_natural
    {R B C : Type u} [CommRing R] [IsLocalRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (t : B →ₐ[R] C)
    (b : B →ₐ[R] IsLocalRing.ResidueField R) (c : C →ₐ[R] IsLocalRing.ResidueField R)
    (ht : c.comp t = b) :
    stagePoint c ≫ Spec.map (CommRingCat.ofHom t.toRingHom) = stagePoint b := by
  unfold stagePoint
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg AlgHom.toRingHom ht

#print axioms stagePoint_comp
#print axioms exists_stageRefinement
#print axioms stagePoint_natural

end ZInQ.Contrib.CloudR2NOS.GoodDescent.OrdinaryStages
