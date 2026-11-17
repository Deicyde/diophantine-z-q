/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_exists_valuation_mul_eq_one_of_finrank_le_card (git blob 2dcd14cd4cc3fb928f1c2cd4f046148262d3ea7e, sha256 58a5c4053df4eaffa81359db6acb24fbd3b5cde66f65e758fa35ef5615919fcc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_exists_valuation_mul_eq_one_of_finrank_le_card

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.exists_valuation_mul_eq_one_of_finrank_le_card
    {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F']
    (O : ValuationSubring F) {ι : Type*} [Fintype ι] (O' : ι → ValuationSubring F')
    (hinj : Function.Injective O') (hO' : ∀ i, (O' i).comap (algebraMap F F') = O)
    (hcard : Module.finrank F F' ≤ Fintype.card ι) (i : ι) (g : F') (hg : g ≠ 0) :
    ∃ h : F, (O' i).valuation (algebraMap F F' h * g) = 1 := by
  revert F F' O ι O' hinj hO' hcard i g hg
  exact @_root_.P2MW.S_ValuationSubring_exists_valuation_mul_eq_one_of_finrank_le_card.solution
