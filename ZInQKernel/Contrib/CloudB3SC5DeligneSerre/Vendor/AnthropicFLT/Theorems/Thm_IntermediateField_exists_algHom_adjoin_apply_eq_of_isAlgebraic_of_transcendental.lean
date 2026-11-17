/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IntermediateField_exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental (git blob 877b16931c914bb48ef2455c8bcf72abfb713c08, sha256 59a00d501b3e45914f2c1b12b057fd23ea01f1dd845a041bf2cac56c9b6d5c23).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_IntermediateField_exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem IntermediateField.exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental
    (K : Type*) {L L' : Type*} [Field K] [Field L] [Algebra K L] [Field L'] [Algebra K L']
    (G : Set L) (h1 : (1 : L) ∈ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (θ : L → L') (hθ : ∀ x ∈ G, ∀ y ∈ G, θ (x * y) = θ x * θ y)
    (hlin : ∀ c : L →₀ K, (↑c.support : Set L) ⊆ G →
      (c.sum fun x r => r • x) = 0 → (c.sum fun x r => r • θ x) = 0)
    (F : IntermediateField K L) (hF : F = IntermediateField.adjoin K G)
    (x₀ : F) (hx₀G : (x₀ : L) ∈ G) (hx₀ : Transcendental K (θ x₀))
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x₀} : Set F)) F) :
    ∃ Θ : F →ₐ[K] L', ∀ x : F, (x : L) ∈ G → Θ x = θ x := by
  revert K L L' G h1 hmul θ hθ hlin F hF x₀ hx₀G hx₀ halg
  exact @_root_.P2MW.S_IntermediateField_exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental.solution
