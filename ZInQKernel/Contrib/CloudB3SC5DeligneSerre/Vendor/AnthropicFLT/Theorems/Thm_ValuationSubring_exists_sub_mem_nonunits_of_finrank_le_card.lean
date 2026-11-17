/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_exists_sub_mem_nonunits_of_finrank_le_card (git blob b41cafddc6215d67c2c7bc6c9a4b9789393c0048, sha256 86bff7847b6631ade779df3011b2513141eebc1780ff43898e8d7164f2605d0b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_exists_sub_mem_nonunits_of_finrank_le_card

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.exists_sub_mem_nonunits_of_finrank_le_card
    {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F']
    (O : ValuationSubring F) {ι : Type*} [Fintype ι] (O' : ι → ValuationSubring F')
    (hinj : Function.Injective O') (hO' : ∀ i, (O' i).comap (algebraMap F F') = O)
    (hcard : Module.finrank F F' ≤ Fintype.card ι) (i : ι) (x : F') (hx : x ∈ O' i) :
    ∃ y ∈ O, x - algebraMap F F' y ∈ (O' i).nonunits := by
  revert F F' O ι O' hinj hO' hcard i x hx
  exact @_root_.P2MW.S_ValuationSubring_exists_sub_mem_nonunits_of_finrank_le_card.solution
