/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension
    {k : Type u} [Field k] {F : Scheme.{u}} (g : F ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    (hg : SmoothOfRelativeDimension n g)
    (m : ℕ) (U : (Spec (CommRingCat.of k)).Opens) (W : F.Opens) (hW : IsAffineOpen W)
    (w : F) (hw : w ∈ W) (e : W ≤ g ⁻¹ᵁ U)
    (hm : (g.appLE U W e).hom.IsStandardSmoothOfRelativeDimension m) : m = n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension.solution
