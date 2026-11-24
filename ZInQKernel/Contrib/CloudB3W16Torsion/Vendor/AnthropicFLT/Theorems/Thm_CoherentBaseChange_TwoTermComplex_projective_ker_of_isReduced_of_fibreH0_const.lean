/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Nilpotent.Defs
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const

set_option backward.isDefEq.respectTransparency false

universe u v w

open scoped TensorProduct
open CoherentBaseChange

theorem CoherentBaseChange.TwoTermComplex.projective_ker_of_isReduced_of_fibreH0_const
    {R : Type u} [CommRing R] [IsReduced R] (G : TwoTermComplex.{u, v} R) {c : ℕ}
    (h0 : ∀ 𝔭 : PrimeSpectrum R, G.fibreH0 𝔭 = c) :
    Module.Projective R (LinearMap.ker G.d) ∧
      (∀ (A : Type w) [CommRing A] [Algebra R A], Function.Bijective (G.kerBaseChangeHom A)) ∧
      ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
        (𝔭.asIdeal.ResidueField ⊗[R] LinearMap.ker G.d) = c := by p2m_exact_reverting @_root_.P2MW.S_CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const.solution
