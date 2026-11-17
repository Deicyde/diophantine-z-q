/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_TwoChartCech_Mumford_projective_K0. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_MumfordTruncation
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_TwoChartCech_Mumford_finite_K0
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_TwoChartCech_Mumford_flat_K0
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.FinitePresentation
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_TwoChartCech_Mumford_projective_K0

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

open TwoChartCech.Mumford in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Module.Projective R (TwoChartCech.Mumford.K0 d) := by
  haveI := TwoChartCech.Mumford.finite_K0 d
  haveI := TwoChartCech.Mumford.flat_K0 d
  haveI : Module.FinitePresentation R (K0 d) := Module.finitePresentation_of_finite R _
  exact Module.Flat.projective_of_finitePresentation

end
