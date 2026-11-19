/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn (git blob 36eebdd77843ca5e396f4815cf4faa0caa41861c, sha256 eeebeb6b1ef6eb70103b9db332af5d3d747bb5e5b9a4b01c901fdb021745f7f6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel Topology

theorem AutomorphicForm.continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn
    (F : Type) [Field F] [NumberField F]
    {X : Type*} [TopologicalSpace X] (U : Set X) (_hU : IsOpen U)
    (f : X → AdelicGL2 (𝓞 F) F → ℂ) (Φ : X → AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F → ℂ)
    (_hΦ : ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => Φ p.1 p.2.1 p.2.2)
      (U ×ˢ ((adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) ×ˢ
        {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))})))
    (_hf : ∀ x ∈ U, ∀ b ∈ adelicBorel (𝓞 F) F, ∀ k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      f x (b * k) = Φ x b k) :
    ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) (U ×ˢ Set.univ) := by
  revert F X U _hU f Φ _hΦ _hf
  exact @_root_.P2MW.S_AutomorphicForm_continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn.solution
