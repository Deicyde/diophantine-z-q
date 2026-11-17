/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MeasureTheory_Measure_exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer (git blob 5131904e87acfc54a4dd7a13285d1021f67611b9, sha256 b947d887e81f5443e8b02f012075a00655a6e400b4ff8eb423c21a5156aba7a1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MeasureTheory_Measure_exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.Measure.exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
    [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L]
    (μL : Measure L) [μL.IsHaarMeasure]
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [MulAction L X] [ContinuousSMul L X] [MulAction.IsPretransitive L X]
    (x₀ : X) (hx₀ : IsCompact (MulAction.stabilizer L x₀ : Set L))
    (σ : Measure X) [IsFiniteMeasureOnCompacts σ]
    (hσ : ∀ g : L, σ.map (fun x : X => g • x) = σ) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ σ = c • μL.map (fun g : L => g • x₀) := by
  revert L μL X x₀ hx₀ σ hσ
  exact @_root_.P2MW.S_MeasureTheory_Measure_exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer.solution
