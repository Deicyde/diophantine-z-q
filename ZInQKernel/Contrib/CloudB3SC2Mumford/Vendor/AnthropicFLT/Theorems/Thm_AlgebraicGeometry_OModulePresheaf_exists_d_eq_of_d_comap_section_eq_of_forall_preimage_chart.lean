/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart
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
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart
    {R : Type u} [CommRing R] {X P : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R)) [IsSeparated πX]
    (p : P ⟶ X) [IsSeparated (p ≫ πX)]
    (s : X ⟶ P) [IsAffineHom s] (hs : s ≫ p = 𝟙 X)
    (hp : ∀ U : X.Opens, IsAffineOpen U → Function.Surjective (p.app U).hom)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p ≫ πX)).d 𝒲 1 c = 0)
    (hcU : ∀ i : 𝒲.ι, ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i)),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left :
            𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i) ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i))
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)))
    (hcs : ∃ b : (OModulePresheaf.unit πX).cochain (𝒲.comap s) 0,
      (OModulePresheaf.unit πX).d (𝒲.comap s) 0 b = fun t =>
        (X.presheaf.map (homOfLE (𝒲.comap_inter_le s t)).op).hom ((s.app (𝒲.inter t)).hom (c t))) :
    ∃ b : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 0, (OModulePresheaf.unit (p ≫ πX)).d 𝒲 0 b = c := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart.solution
