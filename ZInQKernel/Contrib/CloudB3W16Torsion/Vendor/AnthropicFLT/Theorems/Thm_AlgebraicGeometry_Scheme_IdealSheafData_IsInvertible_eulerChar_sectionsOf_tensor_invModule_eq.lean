/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.IsCartierFLT.eulerChar_sectionsOf_tensor_invModule_eq
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x]
    {I : X.IdealSheafData} (hI : I.IsCartierFLT) {r : ℕ}
    (hZ : IsFinite (I.subschemeι ≫ x))
    (hdeg : ∀ t : Spec (CommRingCat.of k), (I.subschemeι ≫ x).finrank t = r)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (𝒱 : X.TwoAffineOpenCover) :
    (Module.finrank k (𝒱.sectionsOf x (L ⊗ I.invModule)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf x (L ⊗ I.invModule)).H1
      = (Module.finrank k (𝒱.sectionsOf x L).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x L).H1 + r := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq.solution
