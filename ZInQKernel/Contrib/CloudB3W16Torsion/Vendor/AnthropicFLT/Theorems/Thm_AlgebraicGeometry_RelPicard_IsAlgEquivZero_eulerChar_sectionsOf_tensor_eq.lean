/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.RelPicard.IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq
    {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k)) [IsProper a]
    (𝒱 : A.TwoAffineOpenCover) (L M : A.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (h0 : RelPicard.IsAlgEquivZero a L) :
    (Module.finrank k (𝒱.sectionsOf a (L ⊗ M)).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf a (L ⊗ M)).H1
      = (Module.finrank k (𝒱.sectionsOf a M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf a M).H1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq.solution
