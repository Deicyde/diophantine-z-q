/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift
    {S Y' A B U : Scheme.{u}} (f' : Y' ⟶ S)
    (jA : A ⟶ Y') (jB : B ⟶ Y') [IsOpenImmersion jA] [IsOpenImmersion jB]
    (hcov : Set.range jA.base ∪ Set.range jB.base = Set.univ)
    (fA : A ⟶ S) (fB : B ⟶ S) (hA : jA ≫ f' = fA) (hB : jB ≫ f' = fB) [IsSeparated fA] [IsSeparated fB]
    (uA : U ⟶ A) (uB : U ⟶ B) (hsq : IsPullback uA uB jA jB)
    (hΓ : IsClosedImmersion
      (pullback.lift uA uB (by rw [← hA, ← hB, ← Category.assoc, hsq.w, Category.assoc]) : U ⟶ pullback fA fB)) :
    IsSeparated f' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift.solution
