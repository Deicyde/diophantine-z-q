/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AdicCompletion_isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AdicCompletion_isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

theorem AdicCompletion.isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal
    {C : Type*} [CommRing C] [IsNoetherianRing C] (𝔫 : Ideal C) [𝔫.IsMaximal] :
    IsNoetherianRing (AdicCompletion 𝔫 C) ∧
    ∃ _ : IsLocalRing (AdicCompletion 𝔫 C),
      IsLocalRing.maximalIdeal (AdicCompletion 𝔫 C) = 𝔫.map (algebraMap C (AdicCompletion 𝔫 C)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (AdicCompletion 𝔫 C)) (AdicCompletion 𝔫 C) ∧
      (IsLocalRing.maximalIdeal (AdicCompletion 𝔫 C)).comap (algebraMap C (AdicCompletion 𝔫 C)) = 𝔫 ∧
      Function.Surjective ((IsLocalRing.residue (AdicCompletion 𝔫 C)).comp (algebraMap C (AdicCompletion 𝔫 C))) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal.solution
