/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact (git blob e25854285e5763eaed0bb517306c7a126a5b7c47, sha256 2358671ad779d19b3cd4043f916580d5dbc8ebfd65fd22b513871f866bf4498a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel Topology

theorem AutomorphicForm.continuousOn_of_isInducedSection_of_continuousOn_maximalCompact
    (F : Type) [Field F] [NumberField F]
    {X : Type*} [TopologicalSpace X] (U : Set X) (_hU : IsOpen U)
    (χ₁ χ₂ : X → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
    (_hχ₁ : ContinuousOn (fun p : X × (AdeleRing (𝓞 F) F)ˣ => ((χ₁ p.1 p.2 : ℂˣ) : ℂ)) (U ×ˢ Set.univ))
    (_hχ₂ : ContinuousOn (fun p : X × (AdeleRing (𝓞 F) F)ˣ => ((χ₂ p.1 p.2 : ℂˣ) : ℂ)) (U ×ˢ Set.univ))
    (f : X → AdelicGL2 (𝓞 F) F → ℂ)
    (_hf : ∀ x ∈ U, IsInducedSection (𝓞 F) F (χ₁ x) (χ₂ x) (f x))
    (_hfK : ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2)
      (U ×ˢ {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))})) :
    ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) (U ×ˢ Set.univ) := by
  revert F X U _hU χ₁ χ₂ _hχ₁ _hχ₂ f _hf _hfK
  exact @_root_.P2MW.S_AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact.solution
