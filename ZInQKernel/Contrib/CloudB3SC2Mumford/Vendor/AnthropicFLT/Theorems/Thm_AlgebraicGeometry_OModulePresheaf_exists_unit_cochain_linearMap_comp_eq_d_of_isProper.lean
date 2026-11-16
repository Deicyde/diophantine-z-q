/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_unit_cochain_linearMap_comp_eq_d_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent) (K : P.OrderedAffineCover) :
    ∃ (Y : Scheme.{u}) (q' : Y ⟶ Spec (CommRingCat.of A)) (_ : IsProper q') (K' : Y.OrderedAffineCover)
      (L : ∀ j : ℕ, F.cochain K j →ₗ[A] (OModulePresheaf.unit q').cochain K' j)
      (Q : ∀ j : ℕ, (OModulePresheaf.unit q').cochain K' j →ₗ[A] F.cochain K j),
      (∀ (j : ℕ) (x : F.cochain K j), Q j (L j x) = x) ∧
      (∀ (j : ℕ) (x : F.cochain K j), (OModulePresheaf.unit q').d K' j (L j x) = L (j + 1) (F.d K j x)) ∧
      (∀ (j : ℕ) (y : (OModulePresheaf.unit q').cochain K' j),
        F.d K j (Q j y) = Q (j + 1) ((OModulePresheaf.unit q').d K' j y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.solution
