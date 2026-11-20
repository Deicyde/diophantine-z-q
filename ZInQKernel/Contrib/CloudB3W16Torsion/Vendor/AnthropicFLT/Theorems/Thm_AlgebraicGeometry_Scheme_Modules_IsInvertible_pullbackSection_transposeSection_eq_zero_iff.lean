/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.pullbackSection_transposeSection_eq_zero_iff
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) {X M : Y.Modules} (hX : Scheme.Modules.IsInvertible X) (φ : X ⟶ M)
    (s : 𝟙_ Y.Modules ⟶ M ⊗ Scheme.Modules.fltDual X)
    (hs : (ihom.ev X).app (𝟙_ Y.Modules) ≫ s = φ ▷ Scheme.Modules.fltDual X) :
    Scheme.Modules.pullbackSectionFLT g s = 0 ↔ (Scheme.Modules.pullback g).map φ = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff.solution
