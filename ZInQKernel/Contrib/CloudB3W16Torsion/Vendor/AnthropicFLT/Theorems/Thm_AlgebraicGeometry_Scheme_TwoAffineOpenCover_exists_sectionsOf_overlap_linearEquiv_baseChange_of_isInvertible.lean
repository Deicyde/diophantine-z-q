/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option autoImplicit false

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    letI : Algebra (𝒱.cover c).A0 (𝒱.cover c).A01 := (𝒱.cover c).ρ0.toRingHom.toAlgebra
    letI : Algebra (𝒱.cover c).A1 (𝒱.cover c).A01 := (𝒱.cover c).ρ1.toRingHom.toAlgebra
    ∃ (rbc0 : (𝒱.cover c).A01 ⊗[(𝒱.cover c).A0] (𝒱.sectionsOf c M).M0 ≃ₗ[(𝒱.cover c).A01]
                (𝒱.sectionsOf c M).M01)
      (rbc1 : (𝒱.cover c).A01 ⊗[(𝒱.cover c).A1] (𝒱.sectionsOf c M).M1 ≃ₗ[(𝒱.cover c).A01]
                (𝒱.sectionsOf c M).M01),
      (∀ m, rbc0 ((1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A0] m) = (𝒱.sectionsOf c M).r0 m) ∧
      (∀ m, rbc1 ((1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A1] m) = (𝒱.sectionsOf c M).r1 m) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible.solution
