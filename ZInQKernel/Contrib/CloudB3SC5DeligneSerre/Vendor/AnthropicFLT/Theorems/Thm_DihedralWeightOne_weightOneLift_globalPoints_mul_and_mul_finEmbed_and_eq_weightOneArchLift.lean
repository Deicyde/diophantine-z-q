/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DihedralWeightOne_weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift (git blob b01adc25363a529bd981f7ab9d80af980e193f70, sha256 1aa6be41f501ae275ca75857cad4ea8bb756f859fb263613663e595e6131bce5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalNewvector_AdelicSpanCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AdelicDock_LocalEmbedding
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DihedralWeightOne_weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm DihedralWeightOne IsDedekindDomain
open scoped MatrixGroups ModularForm

theorem DihedralWeightOne.weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift
    {N : ℕ} (hN : N ≠ 0) (f : UpperHalfPlane → ℂ)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma1 N → f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = f) :
    (∀ (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ),
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f (globalPoints (𝓞 ℚ) ℚ γ * x) =
          weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f x) ∧
    (∀ u ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) =
          weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f x) ∧
    ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 →
      LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f h = weightOneArchLift f (LanglandsTunnell.ratArchGL2 h) := by
  revert N hN f hf
  exact @_root_.P2MW.S_DihedralWeightOne_weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift.solution
