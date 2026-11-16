/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Subalgebra_exists_algHom_localizationAway_forall_apply_eq_coe_of_fg
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_Subalgebra_exists_algHom_localizationAway_forall_apply_eq_coe_of_fg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

theorem Subalgebra.exists_algHom_localizationAway_forall_apply_eq_coe_of_fg
    {R : Type u} [CommRing R] [IsNoetherianRing R] (𝔭 : Ideal R) [𝔭.IsPrime]
    (T : Subalgebra R (Localization.AtPrime 𝔭)) (hT : T.FG) :
    ∃ (r : R) (_ : r ∉ 𝔭) (ψ : ↥T →ₐ[R] Localization.Away r),
      ∀ (π : Localization.Away r →ₐ[R] Localization.AtPrime 𝔭) (x : ↥T),
        π (ψ x) = (x : Localization.AtPrime 𝔭) := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_exists_algHom_localizationAway_forall_apply_eq_coe_of_fg.solution
