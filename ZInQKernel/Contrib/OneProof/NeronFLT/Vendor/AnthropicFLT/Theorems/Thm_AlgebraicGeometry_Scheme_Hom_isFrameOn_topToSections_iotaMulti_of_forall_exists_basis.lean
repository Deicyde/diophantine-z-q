/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFrameOn_topToSections_iotaMulti_of_forall_exists_basis
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isFrameOn_topToSections_iotaMulti_of_forall_exists_basis

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.Scheme.Hom.isFrameOn_topToSections_iotaMulti_of_forall_exists_basis
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ)
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := f.sectionsAlgebra U
    ∀ (η : Fin d → Ω[Γ(X, U)⁄A]),
      (∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
        letI := f.sectionsAlgebra W
        letI : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
        ∀ [IsScalarTower A Γ(X, U) Γ(X, W)],
          ∃ b : Module.Basis (Fin d) Γ(X, W) (Ω[Γ(X, W)⁄A]),
            ∀ i, b i = KaehlerDifferential.map A A Γ(X, U) Γ(X, W) (η i)) →
      Scheme.Modules.IsFrameOn (f.topToSections d U (exteriorPower.ιMulti Γ(X, U) d η)) U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_isFrameOn_topToSections_iotaMulti_of_forall_exists_basis.solution
