/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

theorem IsLocalRing.exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff
    {A₀ : Type u} [CommRing A₀] {R : Type u} [CommRing R] [IsLocalRing R] [Algebra A₀ R]
    (T : Subalgebra A₀ R) [IsNoetherianRing ↥T] :
    ∃ S : Subalgebra A₀ R,
      (S : Set R) = {x : R | ∃ t ∈ T, ∃ u ∈ T, u ∉ IsLocalRing.maximalIdeal R ∧ x * u = t} ∧
      IsNoetherianRing ↥S ∧ IsLocalRing ↥S ∧ ∀ x : ↥S, IsUnit x ↔ IsUnit (x : R) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff.solution
