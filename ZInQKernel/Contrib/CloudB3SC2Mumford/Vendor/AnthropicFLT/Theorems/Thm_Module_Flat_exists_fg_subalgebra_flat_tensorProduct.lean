/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Module_Flat_exists_fg_subalgebra_flat_tensorProduct
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open TensorProduct

theorem Module.Flat.exists_fg_subalgebra_flat_tensorProduct
    {R₀ R B₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀]
    [Algebra R₀ R] [Algebra R₀ B₀] [Algebra.FinitePresentation R₀ B₀]
    [Module.Flat R (R ⊗[R₀] B₀)] (s : Finset R) :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧ (↑s : Set R) ⊆ R₁ ∧ Module.Flat R₁ (R₁ ⊗[R₀] B₀) := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.solution
