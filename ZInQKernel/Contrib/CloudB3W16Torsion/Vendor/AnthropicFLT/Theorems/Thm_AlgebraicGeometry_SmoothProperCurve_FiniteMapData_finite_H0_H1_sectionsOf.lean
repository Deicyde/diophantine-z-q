/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_sectionsOf. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.RingTheory.Noetherian.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_sectionsOf

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.FiniteMapData.finite_H0_H1_sectionsOf
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    Module.Finite R (𝔉.twoAffineOpenCover.sectionsOf c M).H0 ∧
      Module.Finite R (𝔉.twoAffineOpenCover.sectionsOf c M).H1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_sectionsOf.solution
