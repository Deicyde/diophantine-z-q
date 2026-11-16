/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_isIso_of_isPullback_of_isIso_of_isNilpotent_ker
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isIso_of_isPullback_of_isIso_of_isNilpotent_ker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isIso_of_isPullback_of_isIso_of_isNilpotent_ker
    (T' T : Type u) [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {X Y X₀ Y₀ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of T')) (q : Y ⟶ Spec (CommRingCat.of T'))
    [Flat p] [LocallyOfFinitePresentation p] [Flat q] [LocallyOfFinitePresentation q]
    (φ : X ⟶ Y) (hφ : φ ≫ q = p)
    (p₀ : X₀ ⟶ Spec (CommRingCat.of T)) (q₀ : Y₀ ⟶ Spec (CommRingCat.of T))
    (gX : X₀ ⟶ X) (hX : IsPullback gX p₀ p (Spec.map (CommRingCat.ofHom π)))
    (gY : Y₀ ⟶ Y) (hY : IsPullback gY q₀ q (Spec.map (CommRingCat.ofHom π)))
    (φ₀ : X₀ ⟶ Y₀) (hφ₀ : φ₀ ≫ gY = gX ≫ φ) (hφ₀q : φ₀ ≫ q₀ = p₀) [IsIso φ₀] :
    IsIso φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_of_isPullback_of_isIso_of_isNilpotent_ker.solution
