/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_TwoChartCech_projective_ker_of_isReduced_of_kerMapBaseChange_bijective. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Nilpotent.Defs
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_TwoChartCech_projective_ker_of_isReduced_of_kerMapBaseChange_bijective

set_option backward.isDefEq.respectTransparency false

universe u

open scoped TensorProduct

theorem TwoChartCech.projective_ker_of_isReduced_of_kerMapBaseChange_bijective
    {R : Type u} [CommRing R] [IsReduced R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0]
    [AddCommGroup C1] [Module R C1] {d : C0 →ₗ[R] C1}
    (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (ι0 : G.C0 →ₗ[R] C0) (ι1 : G.C1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ G.d)
    (hG : ∀ (A : Type u) [CommRing A] [Algebra R A],
      Function.Bijective (TwoChartCech.kerMapBaseChange G.d d ι0 ι1 comm A))
    {n : ℕ} (hH0 : ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
      (LinearMap.ker (d.baseChange 𝔭.asIdeal.ResidueField)) = n) :
    Module.Projective R (LinearMap.ker d) ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A], Function.Bijective (TwoChartCech.kerBaseChangeHom d A)) ∧
      ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
          (𝔭.asIdeal.ResidueField ⊗[R] LinearMap.ker d) = n := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_projective_ker_of_isReduced_of_kerMapBaseChange_bijective.solution
