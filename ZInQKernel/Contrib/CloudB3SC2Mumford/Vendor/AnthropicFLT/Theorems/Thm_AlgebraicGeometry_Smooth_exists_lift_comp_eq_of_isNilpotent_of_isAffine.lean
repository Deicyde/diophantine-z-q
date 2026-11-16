/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isNilpotent_of_isAffine
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isNilpotent_of_isAffine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.exists_lift_comp_eq_of_isNilpotent_of_isAffine
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [Smooth f]
    {C : Type u} [CommRing C] (J : Ideal C) (hJ : IsNilpotent J)
    (t : Spec (CommRingCat.of C) ⟶ S) (x₀ : Spec (CommRingCat.of (C ⧸ J)) ⟶ X)
    (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ t) :
    ∃ x : Spec (CommRingCat.of C) ⟶ X, x ≫ f = t ∧ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ x = x₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isNilpotent_of_isAffine.solution
