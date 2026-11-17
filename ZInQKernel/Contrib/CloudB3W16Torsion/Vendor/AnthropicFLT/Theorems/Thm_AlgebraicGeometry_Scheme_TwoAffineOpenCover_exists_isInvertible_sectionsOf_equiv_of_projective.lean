/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_isInvertible_sectionsOf_equiv_of_projective
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (P0 : Type u) [AddCommGroup P0] [Module (𝒱.cover c).A0 P0]
    [Module.Projective (𝒱.cover c).A0 P0] [Module.Finite (𝒱.cover c).A0 P0]
    (P1 : Type u) [AddCommGroup P1] [Module (𝒱.cover c).A1 P1]
    [Module.Projective (𝒱.cover c).A1 P1] [Module.Finite (𝒱.cover c).A1 P1]
    (hrk0 : ∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A0 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A0] P0) = 1)
    (hrk1 : ∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A1 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A1] P1) = 1)
    (σ : letI : Algebra (𝒱.cover c).A0 (𝒱.cover c).A01 := (𝒱.cover c).ρ0.toRingHom.toAlgebra
         letI : Algebra (𝒱.cover c).A1 (𝒱.cover c).A01 := (𝒱.cover c).ρ1.toRingHom.toAlgebra
         ((𝒱.cover c).A01 ⊗[(𝒱.cover c).A0] P0) ≃ₗ[(𝒱.cover c).A01]
           ((𝒱.cover c).A01 ⊗[(𝒱.cover c).A1] P1)) :
    letI : Algebra (𝒱.cover c).A0 (𝒱.cover c).A01 := (𝒱.cover c).ρ0.toRingHom.toAlgebra
    letI : Algebra (𝒱.cover c).A1 (𝒱.cover c).A01 := (𝒱.cover c).ρ1.toRingHom.toAlgebra
    ∃ (L : X.Modules), Scheme.Modules.IsInvertible L ∧
      ∃ (e0 : (𝒱.sectionsOf c L).M0 ≃ₗ[(𝒱.cover c).A0] P0)
        (e1 : (𝒱.sectionsOf c L).M1 ≃ₗ[(𝒱.cover c).A1] P1)
        (e01 : (𝒱.sectionsOf c L).M01 ≃ₗ[(𝒱.cover c).A01]
          ((𝒱.cover c).A01 ⊗[(𝒱.cover c).A0] P0)),
        (∀ m, e01 ((𝒱.sectionsOf c L).r0 m) = (1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A0] e0 m) ∧
        (∀ m, σ (e01 ((𝒱.sectionsOf c L).r1 m)) = (1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A1] e1 m) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.solution
