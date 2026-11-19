/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin (git blob 2c22a94bf3d568dc97dbff48a5d71ff96505e288, sha256 f030a0a78436a629d3d21908053256210209b21ac37e9b1bbecef78f52753f4c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (O : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ O) (hO : O ≠ ⊤) :
    IsPrincipalIdealRing O := by
  revert K F x O hK hO
  exact @_root_.P2MW.S_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin.solution
