/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_UpperHalfPlane_qExpansion_prod (git blob 9f0f2ea852474620c7dd2f89a8a70fff6a867c65, sha256 7f6b62d8beaeac8380d6a18043560dee8235985d92903d00c36fa5d4ff810dd3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_UpperHalfPlane_qExpansion_prod

set_option autoImplicit false

noncomputable section

open Complex Filter Function UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass

open scoped Real MatrixGroups Topology Manifold

theorem solution {h : ℝ} {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ} (hF : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction h (F i)) 0) : qExpansion h (∏ i ∈ s, F i) = ∏ i ∈ s, qExpansion h (F i) := by
  suffices H : qExpansion h (∏ i ∈ s, F i) = ∏ i ∈ s, qExpansion h (F i) ∧
      AnalyticAt ℂ (cuspFunction h (∏ i ∈ s, F i)) 0 from H.1
  induction s using Finset.cons_induction with
  | empty =>
    have h1 : cuspFunction h (1 : ℍ → ℂ) = 1 := by
      ext q
      rcases eq_or_ne q 0 with rfl | hq
      · simp [cuspFunction, Periodic.cuspFunction]
        exact Filter.Tendsto.limUnder_eq tendsto_const_nhds
      · simp [cuspFunction, Periodic.cuspFunction_eq_of_nonzero h _ hq]
    refine ⟨by simpa using qExpansion_one h, ?_⟩
    rw [Finset.prod_empty, h1]
    exact analyticAt_const
  | cons a s ha ih =>
    have hFa : AnalyticAt ℂ (cuspFunction h (F a)) 0 := hF a (Finset.mem_cons_self a s)
    obtain ⟨ih1, ih2⟩ := ih fun i hi ↦ hF i (Finset.mem_cons_of_mem hi)
    rw [Finset.prod_cons, Finset.prod_cons, qExpansion_mul hFa ih2, ih1]
    refine ⟨rfl, ?_⟩
    rw [cuspFunction_mul hFa.continuousAt ih2.continuousAt]
    exact hFa.mul ih2

end
