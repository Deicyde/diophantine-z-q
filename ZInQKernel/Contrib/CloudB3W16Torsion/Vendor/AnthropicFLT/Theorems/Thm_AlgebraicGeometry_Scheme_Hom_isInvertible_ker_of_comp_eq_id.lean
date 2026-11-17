/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id
    {X T : Scheme.{u}} {p : X ⟶ T} [IsSeparated p] [SmoothOfRelativeDimension 1 p]
    (σ : T ⟶ X) (hσ : σ ≫ p = 𝟙 T) : σ.ker.IsCartierFLT := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id.solution
