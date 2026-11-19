/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ContinuousMap_ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero (git blob df8dc832a4a2b82a578b78265b593bb2194ab329, sha256 1cc76aab5a38a093d0e47541078676d433d16fea44d2ef37211b76a442ef7576).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.RCLike.Lemmas
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ContinuousMap_ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory

theorem ContinuousMap.ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (A : StarSubalgebra ℂ C(X, ℂ)) (hA : A.SeparatesPoints)
    (β : C(X, ℂ))
    (h : ∀ f ∈ A, ∫ x, f x * β x ∂μ = 0) :
    (β : X → ℂ) =ᵐ[μ] 0 := by
  revert X μ A hA β h
  exact @_root_.P2MW.S_ContinuousMap_ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero.solution
