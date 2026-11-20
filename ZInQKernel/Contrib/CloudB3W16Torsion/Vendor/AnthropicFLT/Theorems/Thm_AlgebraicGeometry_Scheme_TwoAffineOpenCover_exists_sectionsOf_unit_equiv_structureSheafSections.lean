/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_unit_equiv_structureSheafSections
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) :
    ∃ (e0 : (𝒱.sectionsOf c (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 ≃ₗ[R]
          (𝒱.structureSheafSections c).H0)
      (e1 : (𝒱.sectionsOf c (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 ≃ₗ[R]
          (𝒱.structureSheafSections c).H1),
      (∀ x, ((e0 x : (𝒱.structureSheafSections c).M0 × (𝒱.structureSheafSections c).M1)) = x.1) ∧
      (∀ y : (𝒱.sectionsOf c (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M01,
          e1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk (show (𝒱.structureSheafSections c).M01 from y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections.solution
