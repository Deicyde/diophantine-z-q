/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex (git blob 2f15303b425371c6290f760d05deb661e92e3403, sha256 ae25a372fac69a17c11699c9c4b684c087031450ee4b9fbefe6c9370ab463379).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    (ρ : Place ℂ F → ℝ) (γ : Place ℂ F → ℂ → Place ℂ F) (t : Place ℂ F → F)
    (hρ : ∀ v, 0 < ρ v) (h₀ : ∀ v, γ v 0 = v)
    (ht : ∀ v, ∀ z ∈ Metric.ball (0 : ℂ) (ρ v), (γ v z).ord (t v - algebraMap ℂ F z) = 1)
    (hγ : ∀ v, ∀ f : F, f ≠ 0 → ∀ z ∈ Metric.ball (0 : ℂ) (ρ v),
        MeromorphicAt (fun u : ℂ => (γ v u).evalAt f) z ∧
        meromorphicOrderAt (fun u : ℂ => (γ v u).evalAt f) z = ((γ v z).ord f : WithTop ℤ) ∧
        (0 ≤ (γ v z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ v u).evalAt f) z)) :
    ∃ (S : Finset (Place ℂ F)) (r : Place ℂ F → ℝ), (∀ v ∈ S, 0 ≤ r v ∧ r v < ρ v) ∧
      ∀ w : Place ℂ F, ∃ v ∈ S, ∃ z : ℂ, ‖z‖ ≤ r v ∧ γ v z = w := by
  revert F hfg ρ γ t hρ h₀ ht hγ
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.solution
