/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta (git blob 9ac17dbea20d6684f220f837d16762b891788100, sha256 adeea128ce672b917969969641c8d73b015287565cbaaf4cc543968c2f868861).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
    (K : Type) [Field K] [NumberField K] (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (NumberField.dedekindZeta K s) := by
  revert K s hs
  exact @_root_.P2MW.S_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta.solution
