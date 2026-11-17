/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PowerSeries_exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem (git blob bc7d9b8eb12215f1c2df9cccfcb87d407f4f36bc, sha256 6617ca80f786d68043bb510161cb3fa6b3476cdcac382b3da83abbbbb3ec5a7d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_PowerSeries_exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem PowerSeries.exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem
    {E : Type*} [Field E] [CharZero E] (ι : AlgebraicClosure ℚ →+* E)
    (V : Submodule E (PowerSeries E))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (A : PowerSeries (AlgebraicClosure ℚ)) (hA : ∀ n : ℕ, PowerSeries.coeff n A ∈ K)
    (hV : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      A.map (ι.comp (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ∈ V) :
    ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (r : Fin n → PowerSeries ℚ),
      (∀ i, (r i).map (algebraMap ℚ E) ∈ V) ∧
        A.map ι = ∑ i, ι (c i) • (r i).map (algebraMap ℚ E) := by
  revert E ι V K A hA hV
  exact @_root_.P2MW.S_PowerSeries_exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem.solution
