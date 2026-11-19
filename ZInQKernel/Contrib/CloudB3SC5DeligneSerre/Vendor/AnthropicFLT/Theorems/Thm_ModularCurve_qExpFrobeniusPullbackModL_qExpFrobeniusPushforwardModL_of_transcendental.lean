/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental (git blob ccb5f8dbaaf2a55e4ffdc18a72dc59401a5ee244, sha256 4c254b37bad5ead5a70978f9539fd0300ea0537bb9a04a9b3533f91b8162488b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpFrobeniusModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hF : ∃ x : ModularCurve.qExpFunctionFieldC K Γ, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ))
    (y : AlgebraicCurve.Pic0 K (ModularCurve.qExpFunctionFieldC K Γ)) :
    ModularCurve.qExpFrobeniusPullbackModL K Γ ℓ (ModularCurve.qExpFrobeniusPushforwardModL K Γ ℓ y) =
      ℓ • y := by
  revert K ℓ Γ hF y
  exact @_root_.P2MW.S_ModularCurve_qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental.solution
