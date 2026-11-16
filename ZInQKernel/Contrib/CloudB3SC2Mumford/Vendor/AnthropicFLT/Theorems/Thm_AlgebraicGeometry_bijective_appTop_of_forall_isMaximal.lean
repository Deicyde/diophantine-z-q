/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.bijective_appTop_of_forall_isMaximal
    {X : Scheme.{u}} {R : CommRingCat.{u}} (q : X ⟶ Spec R) [CompactSpace X] [QuasiSeparatedSpace X]
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      Function.Bijective (pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime P))))).appTop) :
    Function.Bijective q.appTop := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal.solution
