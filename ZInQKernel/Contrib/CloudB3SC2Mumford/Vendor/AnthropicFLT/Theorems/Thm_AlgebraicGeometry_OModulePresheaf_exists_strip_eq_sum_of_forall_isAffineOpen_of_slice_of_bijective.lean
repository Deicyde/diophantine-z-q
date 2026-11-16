/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [IsSeparated fY]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (iY : Y ⟶ P) (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒱 : Y.OrderedAffineCover)
    (e : ∀ (U : X.affineOpens) (σ : 𝒱.Idx 1), Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (he : ∀ U : X.affineOpens, ∀ ρ : 𝒱.Idx (1 + 1),
      ∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
            ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j)))).op).hom (e U (𝒱.face ρ j)) = 0)
    (hcompat : ∀ (U U' : X.affineOpens) (hle : U'.1 ≤ U.1),
      ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
          ((TopologicalSpace.Opens.map p₁.base).monotone (hle)) : p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e U σ) - e U' σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U'.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j)))
    (hslice : ∀ U : X.affineOpens, x₀ ⁻¹ᵁ U.1 = ⊤ →
      ∃ g : ∀ i : 𝒱.Idx 0, Γ(Y, iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i)),
      ∀ σ : 𝒱.Idx (0 + 1), (iY.app (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).hom (e U σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map iY.base).monotone (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j))))).op).hom (g (𝒱.face σ j))) :
    ∀ U : X.affineOpens, ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), e U σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective.solution
