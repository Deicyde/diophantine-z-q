/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    {R : Type u} [CommRing R] {X X' : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of R)) (x' : X' ⟶ Spec (CommRingCat.of R))
    (φ : X ≅ X') (hφ : φ.hom ≫ x' = x) (𝒱' : X'.TwoAffineOpenCover) (M' : X'.Modules) (M : X.Modules)
    (e : M ≅ (Scheme.Modules.pullback φ.hom).obj M') :
    ∃ 𝒱 : X.TwoAffineOpenCover, 𝒱.U0 = φ.hom ⁻¹ᵁ 𝒱'.U0 ∧ 𝒱.U1 = φ.hom ⁻¹ᵁ 𝒱'.U1 ∧
      Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[R] (𝒱'.sectionsOf x' M').H0) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[R] (𝒱'.sectionsOf x' M').H1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso.solution
