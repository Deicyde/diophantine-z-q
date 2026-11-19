/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MeasureTheory_Measure_exists_eq_prod_of_forall_map_add_left (git blob 6023d9de4edd04a42e6e08dcdd538f652148a02f, sha256 52f3588e9d2fd8f6b0322825f6a5ebb0a80da72d26cbd50aa5b9e95f966d02f9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MeasureTheory_Measure_exists_eq_prod_of_forall_map_add_left

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open MeasureTheory
theorem MeasureTheory.Measure.exists_eq_prod_of_forall_map_add_left
    {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure]
    {Y : Type*} [MeasurableSpace Y] (ρ : MeasureTheory.Measure (G × Y))
    (hinv : ∀ a : G, ρ.map (fun p : G × Y => (a + p.1, p.2)) = ρ)
    (hfin : ∃ B : ℕ → Set Y, (∀ n, MeasurableSet (B n)) ∧ (⋃ n, B n) = Set.univ ∧
      ∀ n (K : Set G), IsCompact K → ρ (K ×ˢ B n) < ⊤) :
    ∃ σ : MeasureTheory.Measure Y, MeasureTheory.SigmaFinite σ ∧ ρ = μ.prod σ := by
  revert G μ Y ρ hinv hfin
  exact @_root_.P2MW.S_MeasureTheory_Measure_exists_eq_prod_of_forall_map_add_left.solution
