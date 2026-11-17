/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_subsingleton_H_of_ses. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_Presentation_subsingleton_H_of_ses

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Presentation.subsingleton_H_of_ses {R : Type u} [CommRing R] {n : ℕ} {D : ProjSpaceCech.GradedModule R n}
    (σ : ProjSpaceCech.GradedModule.Presentation D) (i : ℕ)
    (hF : Subsingleton (ProjSpaceCech.GradedModule.H σ.F i)) (hK : Subsingleton (ProjSpaceCech.GradedModule.H σ.ker (i + 1))) :
    Subsingleton (ProjSpaceCech.GradedModule.H D i) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_Presentation_subsingleton_H_of_ses.solution
