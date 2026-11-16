/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ProjSpaceCech_GradedModule_finite_cohomology_FD
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_nonempty_HEquiv_FD
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Theorems.Thm_ProjSpaceCech_Twist_finite_cohomology
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
namespace P2MW.S_ProjSpaceCech_GradedModule_finite_cohomology_FD

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function MvPolynomial

theorem solution (R : Type u) [CommRing R] (n : ℕ) (d₀ : ℤ) (i : ℕ) :
    Module.Finite R (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.FD R n d₀) i) :=
  by
  obtain ⟨e⟩ := ProjSpaceCech.GradedModule.nonempty_HEquiv_FD R n d₀ i
  haveI := ProjSpaceCech.Twist.finite_cohomology R n d₀ i
  exact Module.Finite.equiv e

end
