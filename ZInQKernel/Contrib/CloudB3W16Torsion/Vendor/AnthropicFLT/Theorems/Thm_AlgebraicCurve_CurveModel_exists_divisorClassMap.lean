/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicCurve_CurveModel_exists_divisorClassMap. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_CurveModel_exists_divisorClassMap

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.exists_divisorClassMap
    {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [Algebra k F] [IsCurveOver k F] (M : CurveModel k F) :
    ∃ cl : M.C.Modules → Pic k F,
      (∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') → cl L = cl L') ∧
      (∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
        cl (L ⊗ L') = cl L + cl L') ∧
      cl (𝟙_ M.C.Modules) = 0 ∧
      (∀ (P : {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) (n : ℕ),
        cl (((P.1.ker) ^ n).invModule) =
            QuotientAddGroup.mk (n • Finsupp.single (M.pointEquivPlace P) (1 : ℤ)) ∧
          cl (((P.1.ker) ^ n).module) =
            QuotientAddGroup.mk (-(n • Finsupp.single (M.pointEquivPlace P) (1 : ℤ)))) ∧
      (∀ (𝒱 : M.C.TwoAffineOpenCover) (L : M.C.Modules), Scheme.Modules.IsInvertible L →
        ∀ D : Divisor k F, QuotientAddGroup.mk D = cl L →
          Module.Finite k (𝒱.sectionsOf M.toBase L).H0 ∧ Module.Finite k (𝒱.sectionsOf M.toBase L).H1 ∧
          Module.finrank k (𝒱.sectionsOf M.toBase L).H0 = ell D ∧
          ((Module.finrank k (𝒱.sectionsOf M.toBase L).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf M.toBase L).H1) -
            ((Module.finrank k (𝒱.sectionsOf M.toBase (𝟙_ M.C.Modules)).H0 : ℤ) -
              Module.finrank k (𝒱.sectionsOf M.toBase (𝟙_ M.C.Modules)).H1) = Divisor.degree D) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.solution
