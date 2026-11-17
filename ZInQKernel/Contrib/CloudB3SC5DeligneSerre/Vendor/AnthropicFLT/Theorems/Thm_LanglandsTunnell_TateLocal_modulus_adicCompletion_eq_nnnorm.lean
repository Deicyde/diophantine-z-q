/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm (git blob b9f656664c0292745df470dbb18f2ecdf5bf66e9, sha256 b66303f62d898c6d468ed16536fff7128b37ad7ce9f079a131e1ea5c1b5dedd1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm (K : Type) [Field K]
    [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :
    modulus x = ‖x‖₊ := by
  revert K v x
  exact @_root_.P2MW.S_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm.solution
