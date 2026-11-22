/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk
    {T Y : Scheme.{u}} [IsLocallyNoetherian T]
    (hT : ∀ x : T, IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x))
    [IsAffine Y] (V : T.Opens) (hV : ∀ x : T, ringKrullDim (T.presheaf.stalk x) ≤ 1 → x ∈ V)
    (v : (V : Scheme.{u}) ⟶ Y) :
    ∃! φ : T ⟶ Y, V.ι ≫ φ = v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.solution
