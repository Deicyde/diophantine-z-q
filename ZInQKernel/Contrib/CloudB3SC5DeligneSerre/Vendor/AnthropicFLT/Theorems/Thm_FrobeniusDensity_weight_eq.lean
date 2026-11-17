/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FrobeniusDensity_weight_eq (git blob e35b096c8f047e2aeb6f5ce8a06735ebf329a9ef, sha256 c9f571b73e3463bd470b597403c55cc3d69b3115f26adcf6830e40b8f1c874fd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Set.Card
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_weight_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped Classical in
theorem FrobeniusDensity.weight_eq {G : Type*} [Group G] [Finite G] (σ τ : G) :
    ∑ f ∈ (orderOf σ).divisors,
        (ArithmeticFunction.moebius (orderOf σ / f)) *
          ((f : ℤ) * ({x : G ⧸ Subgroup.zpowers (σ ^ (orderOf σ / f)) | τ • x = x}.ncard : ℤ))
      = ({g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard : ℤ) := by
  revert G σ τ
  exact @_root_.P2MW.S_FrobeniusDensity_weight_eq.solution
