/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_BrauerNesbitt_exists_linearEquiv_of_span_range_eq_top_of_trace_eq (git blob 18b5094a8fa5ce8281a52365ae1ee90547535e19, sha256 a15a3b9d05f0c553cf74c0708bff08c55d1997203c47c321551a7e235bba8ba5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_BrauerNesbitt_exists_linearEquiv_of_span_range_eq_top_of_trace_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem BrauerNesbitt.exists_linearEquiv_of_span_range_eq_top_of_trace_eq {k : Type*} {G : Type*}
  {V₁ : Type*} {V₂ : Type*} [Field k] [Monoid G] [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
  [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂] (ρ₁ : Representation k G V₁)
  (ρ₂ : Representation k G V₂) [Nontrivial V₁] (hspan₁ : Submodule.span k (Set.range ⇑ρ₁) = ⊤)
  (hspan₂ : Submodule.span k (Set.range ⇑ρ₂) = ⊤)
  (htr : ∀ (g : G), (LinearMap.trace k V₁) (ρ₁ g) = (LinearMap.trace k V₂) (ρ₂ g)) :
  ∃ e : V₁ ≃ₗ[k] V₂, ∀ (g : G) (v : V₁), e ((ρ₁ g) v) = (ρ₂ g) (e v) := by
  revert k G V₁ V₂ ρ₁ ρ₂ hspan₁ hspan₂ htr
  exact @_root_.P2MW.S_BrauerNesbitt_exists_linearEquiv_of_span_range_eq_top_of_trace_eq.solution
