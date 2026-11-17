/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap (git blob 337423cd15f8c660c0b9bbb1e0c2c5f1bd93c644, sha256 00cdcbba92a0902742777b8b19e45b19db8d69a123ff07baed807082c0ea6bd3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap (F : Type) [Field F]
    [NumberField F] {c u d₁ d₂ C : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) :
    IsCompact (AutomorphicForm.WindowedSiegel.centreCutSiegelSet F c u d₁ d₂ ∩
      {g | ∀ w : NumberField.InfinitePlace F,
        AutomorphicForm.WindowedSiegel.localHeight (NumberField.AdelicLevel.archComponent F w
          (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F g)) ≤ C}) := by
  revert F c u d₁ d₂ C hc hd₁
  exact @_root_.P2MW.S_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap.solution
