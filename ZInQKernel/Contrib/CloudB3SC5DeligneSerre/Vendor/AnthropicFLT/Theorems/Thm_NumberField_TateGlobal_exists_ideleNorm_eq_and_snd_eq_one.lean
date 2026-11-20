/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one (git blob 27d596896b52454e39e05d556364f4f4df5a5655, sha256 a384617ca0bf81385420099abb0f7af6a986af56b08660a1158f7c839f1c920e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField open NumberField.TateGlobal hiding ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one

theorem NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one
    (K : Type) [Field K] [NumberField K] (r : ℝ) (hr : 0 < r) :
    ∃ z : (AdeleRing (𝓞 K) K)ˣ, ((z : AdeleRing (𝓞 K) K)).2 = 1 ∧ ideleNorm K z = r := by
  revert K r hr
  exact @_root_.P2MW.S_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one.solution
