/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective
    {S S₀ X X₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i] [Surjective i]
    {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : X₀ ⟶ X} (hg : IsPullback g f₀ f i) :
    IsClosedImmersion g ∧ Surjective g ∧ (IsSeparated f₀ → IsSeparated f) ∧
      (UniversallyClosed f₀ → UniversallyClosed f) ∧
      (IsProper f₀ → LocallyOfFiniteType f → IsProper f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective.solution
