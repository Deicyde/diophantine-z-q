/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_of_orderMap (git blob 75a0fba0bc9e4a34a7329a7fd4a4730e99133796, sha256 30b74a608d5ddb7ec06af5eadc55a4487455a560fa7ec1d779f9966f647a9020).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_of_orderMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AlgebraicCurve.Place.exists_of_orderMap {K F : Type*} [Field K] [Field F] [Algebra K F]
    (μ : F → WithTop ℤ) (h_top : ∀ x, μ x = ⊤ ↔ x = 0)
    (h_mul : ∀ x y, μ (x * y) = μ x + μ y) (h_add : ∀ x y, min (μ x) (μ y) ≤ μ (x + y))
    (h_const : ∀ c : K, c ≠ 0 → μ (algebraMap K F c) = 0) (h_nontriv : ∃ x, 0 < μ x ∧ μ x ≠ ⊤) :
    ∃ (P : AlgebraicCurve.Place K F) (e : ℕ), 0 < e ∧
      (∀ x, x ∈ P.toValuationSubring ↔ 0 ≤ μ x) ∧
      ∀ x, x ≠ 0 → μ x = (((e : ℤ) * P.ord x : ℤ) : WithTop ℤ) := by
  revert K F μ h_top h_mul h_add h_const h_nontriv
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_of_orderMap.solution
