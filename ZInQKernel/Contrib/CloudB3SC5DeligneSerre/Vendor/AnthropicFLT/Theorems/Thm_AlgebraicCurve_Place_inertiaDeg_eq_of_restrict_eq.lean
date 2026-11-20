/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq (git blob e10da8d780d2c9597fdae63a570e797fc3183c7d, sha256 7386faba6b34fe7d348f38143bd2f4323a2464d4b7839e7ce133a5d4f55285cb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import Mathlib.FieldTheory.Galois.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Place.inertiaDeg_eq_of_restrict_eq {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [IsGalois F' M] (W W' : Place K M)
    (h : W'.restrict F' = W.restrict F') :
    W'.inertiaDeg F' = W.inertiaDeg F' := by
  revert K F' M W W' h
  exact @_root_.P2MW.S_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq.solution
