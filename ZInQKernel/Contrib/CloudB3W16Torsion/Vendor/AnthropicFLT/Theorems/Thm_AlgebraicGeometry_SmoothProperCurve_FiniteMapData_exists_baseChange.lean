/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.FiniteMapData.exists_baseChange
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    ∃ 𝔉' : SmoothProperCurve.FiniteMapData (baseChange R c R') (sectionBaseChange R' ε),
      𝔉'.U = (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U ∧ 𝔉'.V = (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.V ∧
        𝔉'.m = 𝔉.m ∧
        (IsLocalRing R → Module.Finite R R' → 𝔉.LevelSetsGenericallyEtale → 𝔉'.LevelSetsGenericallyEtale) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange.solution
