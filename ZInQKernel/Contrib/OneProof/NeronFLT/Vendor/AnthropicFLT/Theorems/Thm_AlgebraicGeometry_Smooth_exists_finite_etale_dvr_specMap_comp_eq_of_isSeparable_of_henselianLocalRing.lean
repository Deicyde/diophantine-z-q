/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_of_isSeparable_of_henselianLocalRing
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_of_isSeparable_of_henselianLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Smooth.exists_finite_etale_dvr_specMap_comp_eq_of_isSeparable_of_henselianLocalRing
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
        Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom) ≫ x₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_of_isSeparable_of_henselianLocalRing.solution
