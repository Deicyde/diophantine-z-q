/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_denseRange_algebraMap_add_adeleSingleAt (git blob 1267545ffc0b51a8e9195e89e0af948c46fd919f, sha256 8c2afbea5bab32a87c0b27ee8410322a2ff684c222472f935bfbd647d98677ba).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_denseRange_algebraMap_add_adeleSingleAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem NumberField.denseRange_algebraMap_add_adeleSingleAt (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    DenseRange fun qy : K × v.adicCompletion K =>
      algebraMap K (NumberField.AdeleRing (NumberField.RingOfIntegers K) K) qy.1 +
        NumberField.StandardAddChar.adeleSingleAt K v qy.2 := by
  revert K v
  exact @_root_.P2MW.S_NumberField_denseRange_algebraMap_add_adeleSingleAt.solution
