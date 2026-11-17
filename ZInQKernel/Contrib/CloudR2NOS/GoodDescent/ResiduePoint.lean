/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

New canonical residue-point adapter (2026-11-14). This identifies the
SCHEME residue field at the local closed point with the ORIGINAL R/m,
with its actual ring map and Spec morphism. It is not a henselization,
inertia-field or DVR constructor, and changes no frozen definition.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.AffinePointedCover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.PointedRefinement

/-- The actual residue-field isomorphism from the local stalk isomorphism. -/
def localResidueIso (R : Type u) [CommRing R] [IsLocalRing R] :
    (Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R) ≅
      CommRingCat.of (IsLocalRing.ResidueField R) :=
  (IsLocalRing.ResidueField.mapEquiv
    (stalkClosedPointIso (CommRingCat.of R)).commRingCatIsoToRingEquiv).toCommRingCatIso

/-- Its Spec map preserves the ORIGINAL R→R/m ring map exactly. -/
@[reassoc]
theorem localResidueIso_spec_comp (R : Type u) [CommRing R] [IsLocalRing R] :
    Spec.map (localResidueIso R).inv ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) =
      (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R) := by
  rw [Scheme.fromSpecResidueField, ← Spec_stalkClosedPointIso,
    ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  ext r
  rfl

/-- The two canonical Spec maps are genuinely inverse morphisms. -/
@[reassoc (attr := simp)]
theorem localResidueIso_spec_hom_inv (R : Type u) [CommRing R] [IsLocalRing R] :
    Spec.map (localResidueIso R).hom ≫ Spec.map (localResidueIso R).inv =
      𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField R))) := by
  rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]

/-- Full refinement with the point given over the ORIGINAL quotient R/m.
    All the point's field embeddings and its original-base map are retained;
    the scheme-residue-field difference is actually transported, not ignored. -/
theorem exists_affine_refinement_from_original_residue
    {R : Type u} [CommRing R] [IsLocalRing R] {U : Scheme.{u}}
    (p : U ⟶ Spec (CommRingCat.of R)) [Etale p]
    (x : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ U)
    (hx : x ≫ p = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ V : U.Opens, IsAffineOpen V ∧ Etale (V.ι ≫ p) ∧ Surjective (V.ι ≫ p) ∧
      QuasiCompact (V.ι ≫ p) ∧ IsIso ((V.ι ≫ p).fiberToSpecResidueField (IsLocalRing.closedPoint R)) ∧
      (affineStructureMap (V.ι ≫ p)).FaithfullyFlat ∧
      ∃ x' : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ V.toScheme,
        x' ≫ V.ι = x ∧ x' ≫ (V.ι ≫ p) = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
  let a := Spec.map (localResidueIso R).inv
  let b := Spec.map (localResidueIso R).hom
  have hab : b ≫ a = 𝟙 _ := localResidueIso_spec_hom_inv R
  let x₁ := a ≫ x
  have hx₁ : x₁ ≫ p =
      (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R) := by
    rw [Category.assoc, hx]
    exact localResidueIso_spec_comp R
  obtain ⟨V, hV, hE, hS, hQ, hI, hF, x₁', hinc, hover⟩ :=
    exists_affine_etale_faithfullyFlat_refinement p x₁ hx₁
  let x' := b ≫ x₁'
  have hinc' : x' ≫ V.ι = x := by
    change (b ≫ x₁') ≫ V.ι = x
    rw [Category.assoc, hinc, ← Category.assoc, hab, Category.id_comp]
  have hover' : x' ≫ (V.ι ≫ p) = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
    rw [← Category.assoc, hinc', hx]
  exact ⟨V, hV, hE, hS, hQ, hI, hF, x', hinc', hover'⟩

#print axioms localResidueIso_spec_comp
#print axioms exists_affine_refinement_from_original_residue

end ZInQ.Contrib.CloudR2NOS.GoodDescent.PointedRefinement
