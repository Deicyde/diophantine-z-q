/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Presentation.finite_H_of_ses {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} {D : ProjSpaceCech.GradedModule R n}
    (σ : ProjSpaceCech.GradedModule.Presentation D) (i : ℕ)
    (hF : Module.Finite R (ProjSpaceCech.GradedModule.H σ.F i)) (hK : Module.Finite R (ProjSpaceCech.GradedModule.H σ.ker (i + 1))) :
    Module.Finite R (ProjSpaceCech.GradedModule.H D i) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses.solution
