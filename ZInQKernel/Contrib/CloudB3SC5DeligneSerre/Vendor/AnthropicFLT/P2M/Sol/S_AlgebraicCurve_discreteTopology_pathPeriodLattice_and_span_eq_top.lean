/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_discreteTopology_pathPeriodLattice_and_span_eq_top (git blob 24174302cacc981628950ab0f8eebfe57cc4fb11, sha256 1ab56aaa30857da2084389a17095d840a67215ffcfd53654e1d3f8e31f40ad5e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_span_real_pathPeriodLattice_eq_top
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_finset_card_le_span_eq_pathPeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_discreteTopology_pathPeriodLattice_and_span_eq_top.AlgebraicCurve
end P2MW.S_AlgebraicCurve_discreteTopology_pathPeriodLattice_and_span_eq_top.AlgebraicCurve

namespace P2MW.S_AlgebraicCurve_discreteTopology_pathPeriodLattice_and_span_eq_top

set_option autoImplicit false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_discreteTopology_pathPeriodLattice_and_span_eq_top.AlgebraicCurve
open scoped Manifold ContDiff

noncomputable section

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place IsCurveOver HasCanonicalDivisor genus Place.evalAt regularDifferentials pathPeriodLattice span_real_pathPeriodLattice_eq_top exists_finset_card_le_span_eq_pathPeriodLattice)
namespace PeriodLatticeIsLatticeProof
open _root_.AlgebraicCurve

section LinearAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem span_real_coe_span_int (s : Set E) :
    Submodule.span ℝ ((Submodule.span ℤ s : Submodule ℤ E) : Set E) = Submodule.span ℝ s :=
  Submodule.span_span_of_tower ℤ ℝ s

theorem linearIndependent_of_card_le_of_span_eq_top [FiniteDimensional ℝ E] (s : Finset E)
    (hcard : s.card ≤ Module.finrank ℝ E)
    (hspan : Submodule.span ℝ (s : Set E) = ⊤) :
    LinearIndependent ℝ (Subtype.val : ↥(s : Set E) → E) := by
  classical
  have hrange : Set.range (Subtype.val : ↥(s : Set E) → E) = (s : Set E) := Subtype.range_coe
  refine linearIndependent_of_top_le_span_of_card_le_finrank ?_ ?_
  · rw [hrange, hspan]
  · simpa [Fintype.card_coe] using hcard

theorem discreteTopology_of_span_eq_of_card_le_of_span_eq_top [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) (s : Finset E)
    (hcard : s.card ≤ Module.finrank ℝ E) (hs : Submodule.span ℤ (s : Set E) = L)
    (hspan : Submodule.span ℝ (L : Set E) = ⊤) : DiscreteTopology L := by
  classical

  have hspan' : Submodule.span ℝ (s : Set E) = ⊤ := by
    rw [← span_real_coe_span_int, hs, hspan]

  have hli := linearIndependent_of_card_le_of_span_eq_top s hcard hspan'
  have hrange : Set.range (Subtype.val : ↥(s : Set E) → E) = (s : Set E) := Subtype.range_coe
  let B : Module.Basis ↥(s : Set E) ℝ E :=
    Module.Basis.mk hli (by rw [hrange, hspan'])
  have hB : Set.range B = (s : Set E) := by
    rw [Module.Basis.coe_mk, hrange]

  have hL : L = Submodule.span ℤ (Set.range B) := by rw [hB, hs]
  rw [hL]
  infer_instance

end LinearAlgebra

theorem finrank_real_fin_fun_complex (n : ℕ) : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
  rw [finrank_real_of_complex, Module.finrank_fin_fun]

end AlgebraicCurve.PeriodLatticeIsLatticeProof

end

open AlgebraicCurve.PeriodLatticeIsLatticeProof in

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F)) :
    DiscreteTopology ↥(pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ]))) ∧
      Submodule.span ℝ (pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])) : Set (Fin n → ℂ)) = ⊤ := by
  classical

  have hspan : Submodule.span ℝ (pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])) : Set (Fin n → ℂ)) = ⊤ :=
    span_real_pathPeriodLattice_eq_top F hfg hF b

  obtain ⟨s, hcard, hs⟩ := exists_finset_card_le_span_eq_pathPeriodLattice F hfg hF b

  refine ⟨?_, hspan⟩
  exact discreteTopology_of_span_eq_of_card_le_of_span_eq_top _ s
    (by rw [finrank_real_fin_fun_complex]; exact hcard) hs hspan
