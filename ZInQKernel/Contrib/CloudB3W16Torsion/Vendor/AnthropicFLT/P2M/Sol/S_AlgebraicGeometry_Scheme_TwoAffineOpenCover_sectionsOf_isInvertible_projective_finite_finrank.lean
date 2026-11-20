/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 16000000

noncomputable section

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Module.Projective (𝒱.cover c).A0 (𝒱.sectionsOf c M).M0 ∧
    Module.Finite (𝒱.cover c).A0 (𝒱.sectionsOf c M).M0 ∧
    (∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A0 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A0] (𝒱.sectionsOf c M).M0) = 1) ∧
    Module.Projective (𝒱.cover c).A1 (𝒱.sectionsOf c M).M1 ∧
    Module.Finite (𝒱.cover c).A1 (𝒱.sectionsOf c M).M1 ∧
    (∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A1 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A1] (𝒱.sectionsOf c M).M1) = 1) ∧
    Module.Projective (𝒱.cover c).A01 (𝒱.sectionsOf c M).M01 ∧
    Module.Finite (𝒱.cover c).A01 (𝒱.sectionsOf c M).M01 ∧
    (∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A01 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A01] (𝒱.sectionsOf c M).M01) = 1) := by
  refine ⟨
    Scheme.Modules.projective_sections_of_locallyTrivial M hM.1 ⟨𝒱.U0, 𝒱.isAffineOpen_U0⟩,
    Scheme.Modules.finite_sections_of_locallyTrivial M hM.1 ⟨𝒱.U0, 𝒱.isAffineOpen_U0⟩,
    fun K fK algK =>
      @Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial
        X M hM.1 ⟨𝒱.U0, 𝒱.isAffineOpen_U0⟩ K fK algK,
    Scheme.Modules.projective_sections_of_locallyTrivial M hM.1 ⟨𝒱.U1, 𝒱.isAffineOpen_U1⟩,
    Scheme.Modules.finite_sections_of_locallyTrivial M hM.1 ⟨𝒱.U1, 𝒱.isAffineOpen_U1⟩,
    fun K fK algK =>
      @Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial
        X M hM.1 ⟨𝒱.U1, 𝒱.isAffineOpen_U1⟩ K fK algK,
    Scheme.Modules.projective_sections_of_locallyTrivial M hM.1 ⟨𝒱.U0 ⊓ 𝒱.U1, 𝒱.isAffineOpen_inf⟩,
    Scheme.Modules.finite_sections_of_locallyTrivial M hM.1 ⟨𝒱.U0 ⊓ 𝒱.U1, 𝒱.isAffineOpen_inf⟩,
    fun K fK algK =>
      @Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial
        X M hM.1 ⟨𝒱.U0 ⊓ 𝒱.U1, 𝒱.isAffineOpen_inf⟩ K fK algK⟩

end
