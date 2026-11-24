/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.Leray.exists_hom_relHPresheaf_zero
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    (K' : V'.OrderedAffineCover) :
    ∃ φ : OModulePresheaf.Hom (OModulePresheaf.Leray.relHPresheaf p πZ K' 0)
        (OModulePresheaf.Leray.pullOpen p πZ (⊤ : V'.Opens)),
      (∀ U : Z.Opens, Function.Bijective (φ.app U)) ∧
      ∀ (U : Z.Opens) (x : LinearMap.ker (OModulePresheaf.Leray.relAltd p πZ K' U 0)),
        OModulePresheaf.Leray.relAug p πZ K' U (φ.app U (Submodule.Quotient.mk x)) = x.1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero.solution
