/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ProjSpaceCech_Twist_finite_cohomology
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_Twist_finite_cohomology

set_option autoImplicit false

universe u

theorem ProjSpaceCech.Twist.finite_cohomology (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (i : ℕ) :
    Module.Finite R (ProjSpaceCech.Twist.H R n d i) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_Twist_finite_cohomology.solution
