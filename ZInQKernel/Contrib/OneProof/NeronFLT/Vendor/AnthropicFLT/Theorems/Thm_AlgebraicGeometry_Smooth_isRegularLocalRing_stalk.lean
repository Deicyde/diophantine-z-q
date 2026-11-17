/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
[port] name clash with declarations already in the kernel: renamed `isRegularLocalRing_stalk` → `isRegularLocalRing_stalk_nflt`.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_nflt
    {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    [Smooth f] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk.solution
