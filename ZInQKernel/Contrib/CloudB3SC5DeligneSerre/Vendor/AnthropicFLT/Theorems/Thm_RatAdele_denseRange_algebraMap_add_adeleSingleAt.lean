/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_RatAdele_denseRange_algebraMap_add_adeleSingleAt (git blob 6d3bbcc6ce8cfd587550dd5eb86298e2529c5ecd, sha256 20f88ec7bd1e9b19fa8df49800564901478893d6072b75e4198981bb56444294).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_RatAdele_denseRange_algebraMap_add_adeleSingleAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem RatAdele.denseRange_algebraMap_add_adeleSingleAt
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    DenseRange fun qy : ℚ × v.adicCompletion ℚ =>
      algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) qy.1 +
        NumberField.StandardAddChar.adeleSingleAt ℚ v qy.2 := by
  revert v
  exact @_root_.P2MW.S_RatAdele_denseRange_algebraMap_add_adeleSingleAt.solution
