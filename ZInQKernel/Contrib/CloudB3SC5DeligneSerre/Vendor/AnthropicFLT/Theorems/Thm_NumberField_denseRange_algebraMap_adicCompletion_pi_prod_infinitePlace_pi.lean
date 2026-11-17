/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi (git blob e96808b378c2d48f80aad014de121145abd9acd3, sha256 2aba5abb471b65c872b06ef13132f35042f50794103ed9f02597c3c9c17a2193).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
theorem NumberField.denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi {K : Type*} [Field K] [NumberField K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    DenseRange (fun x : K =>
      ((fun v : S => algebraMap K (v.1.adicCompletion K) x),
       (fun w : NumberField.InfinitePlace K => algebraMap K w.Completion x))) := by
  revert K S
  exact @_root_.P2MW.S_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi.solution
