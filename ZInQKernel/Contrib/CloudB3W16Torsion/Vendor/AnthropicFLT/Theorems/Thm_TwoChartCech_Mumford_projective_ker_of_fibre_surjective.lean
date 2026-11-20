/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_TwoChartCech_Mumford_projective_ker_of_fibre_surjective. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Finrank
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_TwoChartCech_Mumford_projective_ker_of_fibre_surjective

set_option backward.isDefEq.respectTransparency false

universe u

open scoped TensorProduct

theorem TwoChartCech.Mumford.projective_ker_of_fibre_surjective
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {C0 C1 : Type u} [AddCommGroup C0] [Module A C0] [AddCommGroup C1] [Module A C1]
    [Module.Flat A C0] [Module.Flat A C1] (d : C0 →ₗ[A] C1)
    [Module.Finite A (LinearMap.ker d)] [Module.Finite A (C1 ⧸ LinearMap.range d)]
    (hH1 : ∀ (K : Type u) [Field K] [Algebra A K], Function.Surjective (d.baseChange K)) :
    Module.Projective A (LinearMap.ker d) ∧
      (∀ (A' : Type u) [CommRing A'] [Algebra A A'], Function.Bijective (TwoChartCech.kerBaseChangeHom d A')) ∧
      ∀ (K : Type u) [Field K] [Algebra A K],
        Module.finrank K (K ⊗[A] LinearMap.ker d) = Module.finrank K (LinearMap.ker (d.baseChange K)) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_Mumford_projective_ker_of_fibre_surjective.solution
