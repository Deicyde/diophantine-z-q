/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_ideal_pow_le_of_forall_le_radical
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_ideal_pow_le_of_forall_le_radical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_forall_ideal_pow_le_of_forall_le_radical
    {X : Scheme.{u}} [IsNoetherian X] (𝓙₁ 𝓙₂ : X.IdealSheafData)
    (h : ∀ U : X.affineOpens, 𝓙₁.ideal U ≤ (𝓙₂.ideal U).radical) :
    ∃ t : ℕ, ∀ U : X.affineOpens, 𝓙₁.ideal U ^ t ≤ 𝓙₂.ideal U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_ideal_pow_le_of_forall_le_radical.solution
