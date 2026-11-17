/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_of_isSeparable_of_henselianLocalRing
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_HenselianLocalRing_of_moduleFinite_of_isLocalRing
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_of_isSeparable_of_henselianLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (k' : Type u) [Field k'] [Algebra (IsLocalRing.ResidueField R) k']
    [FiniteDimensional (IsLocalRing.ResidueField R) k'] [Algebra.IsSeparable (IsLocalRing.ResidueField R) k']
    (x₀ : Spec (CommRingCat.of k') ⟶ X)
    (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom
      ((algebraMap (IsLocalRing.ResidueField R) k').comp (IsLocalRing.residue R)))) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : HenselianLocalRing R')
      (φ : k' ≃ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R')
      (s : Spec (CommRingCat.of R') ⟶ X),
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' ∧
      s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ∧
      Spec.map (CommRingCat.ofHom (algebraMap R' (IsLocalRing.ResidueField R'))) ≫ s =
        Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom) ≫ x₀ := by
  obtain ⟨R', i1, i2, i3, i4, i5, i6, i7, i8, hmap, ⟨φ⟩⟩ :=
    IsDiscreteValuationRing.exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv R k'
  haveI i9 : HenselianLocalRing R' := HenselianLocalRing.of_moduleFinite_of_isLocalRing (R := R) (S := R')

  have hring : (algebraMap R' (IsLocalRing.ResidueField R')).comp (algebraMap R R') =
      φ.toRingEquiv.toRingHom.comp ((algebraMap (IsLocalRing.ResidueField R) k').comp (IsLocalRing.residue R)) := by
    ext r
    show algebraMap R' (IsLocalRing.ResidueField R') (algebraMap R R' r) =
      φ (algebraMap (IsLocalRing.ResidueField R) k' (IsLocalRing.residue R r))
    rw [AlgEquiv.commutes, IsLocalRing.ResidueField.algebraMap_residue]
    rfl
  have hcomm : (Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom) ≫ x₀) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R' (IsLocalRing.ResidueField R'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [Category.assoc, hx₀, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hring]
  have hx₀' : pullback.lift _ _ hcomm ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
      Spec.map (CommRingCat.ofHom (algebraMap R' (IsLocalRing.ResidueField R'))) := pullback.lift_snd _ _ _

  obtain ⟨s', hs'₁, hs'₂⟩ :=
    AlgebraicGeometry.Smooth.exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) _ hx₀'
  have h₁ : (s' ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs'₁, Category.id_comp]
  have h₂ : Spec.map (CommRingCat.ofHom (algebraMap R' (IsLocalRing.ResidueField R'))) ≫
      (s' ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) =
        Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom) ≫ x₀ := by
    rw [← Category.assoc, hs'₂]
    exact pullback.lift_fst _ _ _
  exact ⟨R', i1, i2, i3, i4, i5, i6, i7, i8, i9, φ, _, hmap, h₁, h₂⟩
