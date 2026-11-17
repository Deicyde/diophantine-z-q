/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Complex_locallyIntegrableOn_of_simplePoles (git blob aa8b9f154255521dc9ee5632a1c436a84835b871, sha256 e02cf2ae8223bd91d4fe00c7a75218bbc472cb020d8dcc84ee81c13d94e57836).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_Complex_locallyIntegrableOn_of_simplePoles

open MeasureTheory Filter Metric Set
open scoped Topology

namespace SimplePolesLocInt

theorem integrableOn_const_div (c : ℂ) (r : ℝ) :
    IntegrableOn (fun x : ℂ => c / x) (ball 0 r) := by
  have hd : 1 ≤ Module.finrank ℝ ℂ := by rw [Complex.finrank_real_complex]; norm_num
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) hd (C := ‖c‖) (α := 1) ?_ ?_ ?_
  · rw [Complex.finrank_real_complex]; norm_num
  · refine Eventually.of_forall fun x => le_of_eq ?_
    rw [norm_div, Real.rpow_neg_one, div_eq_mul_inv]
  · exact (measurable_const.div measurable_id).aestronglyMeasurable

theorem integrableOn_const_div_sub (c a : ℂ) (r : ℝ) :
    IntegrableOn (fun z : ℂ => c / (z - a)) (ball a r) := by
  have hT := (measurePreserving_add_right (volume : Measure ℂ) a).integrableOn_comp_preimage
    (measurableEmbedding_addRight a) (f := fun z : ℂ => c / (z - a)) (s := ball a r)
  rw [← hT]
  have hpre : (fun x : ℂ => x + a) ⁻¹' ball a r = ball 0 r := by
    ext x
    simp only [mem_preimage, mem_ball_iff_norm, add_sub_cancel_right, sub_zero]
  rw [hpre]
  simp only [Function.comp_def, add_sub_cancel_right]
  exact integrableOn_const_div c r

theorem main
    (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z) :
    LocallyIntegrableOn F U := by
  intro a ha
  obtain ⟨g, hg, hev⟩ := hloc a ha

  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.mem_nhds_iff.1 hg.eventually_analyticAt

  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε₂, hε₂, hball₂⟩ := hev
  set r : ℝ := min ε₁ ε₂ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr₁ : r < ε₁ := by
    have := min_le_left ε₁ ε₂; rw [hr]; linarith
  have hr₂ : r < ε₂ := by
    have := min_le_right ε₁ ε₂; rw [hr]; linarith
  refine ⟨ball a r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a hr0), ?_⟩

  have hgc : ContinuousOn g (closedBall a r) := fun z hz =>
    (hball₁ (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz) hr₁)) :
      AnalyticAt ℂ g z).continuousAt.continuousWithinAt
  have hgi : IntegrableOn g (ball a r) :=
    (hgc.integrableOn_compact (isCompact_closedBall a r)).mono_set ball_subset_closedBall
  have hmodel : IntegrableOn (fun z => c a / (z - a) + g z) (ball a r) :=
    (integrableOn_const_div_sub (c a) a r).add hgi

  refine hmodel.congr_fun_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
  filter_upwards [(Set.finite_singleton a).countable.ae_notMem volume] with z hza hz
  rw [mem_singleton_iff] at hza
  exact (hball₂ (mem_ball.1 (ball_subset_ball hr₂.le hz)) hza).symm

end SimplePolesLocInt

open Complex MeasureTheory in
open scoped Topology in
theorem solution
    (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z) :
    LocallyIntegrableOn F U :=
  SimplePolesLocInt.main U hU F c hloc
