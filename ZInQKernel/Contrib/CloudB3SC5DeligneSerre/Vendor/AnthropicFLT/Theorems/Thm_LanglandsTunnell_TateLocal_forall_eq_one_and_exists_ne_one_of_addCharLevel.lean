/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel (git blob ec799cde5bfdf6ddce11f784eab402e4fe329435, sha256 bf3b1832fbf0ab5062ed789a2382f1e8270a4fd7ca8fb49dd8fdc0ed052398a4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (ψ : AddChar (v.adicCompletion K) ℂ)
    (hψk : ∃ k : ℤ, ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp k → ψ x = 1) (hψ : ψ ≠ 1) :
    (∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel ψ) → ψ x = 1) ∧
      ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel ψ + 1) ∧ ψ x ≠ 1 := by
  revert K v ψ hψk hψ
  exact @_root_.P2MW.S_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel.solution
