/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.SmoothOfRelativeDimension.nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (n : ℕ) [SmoothOfRelativeDimension n f] (y : Y)
    [Algebra R (Y.presheaf.stalk y)]
    (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) :
    Nonempty (Module.Basis (Fin n) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄R])) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq.solution
