/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_equation_tateBase_iff (git blob 1aa7f2b047ad2a906b89b26fdabc57c78aad4250, sha256 d2a15c45660dc49f3c7f7ebfe8f86e7a7647eaa6ddca02f585bfb9c131f6ddb3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateSlots
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_equation_tateBase_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve
theorem ModularCurve.equation_tateBase_iff (K : Type*) [CommRing K] (p : ℕ) [NeZero p] (x y : LaurentSeries K) : (tateBase K p).toAffine.Equation x y ↔ y ^ 2 + x * y = x ^ 3 + qExpand K p (laurentOfInt K tateA4) * x + qExpand K p (laurentOfInt K tateA6) := by
  revert K p x y
  exact @_root_.P2MW.S_ModularCurve_equation_tateBase_iff.solution
