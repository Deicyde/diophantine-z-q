/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FunctionFieldPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate
theorem P2M.Dup.WeierstrassCurve.Affine.CoordinateRing.exists_eq_XYIdeal {K : Type*} [Field K] {W : Affine K} [IsAlgClosed K] {P : Ideal W.CoordinateRing} (hP : P ≠ ⊥) [P.IsPrime] : ∃ a b : K, W.Equation a b ∧ P = XYIdeal W a (C b) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.solution
#p2m_type_eq_warn P2M.Dup.WeierstrassCurve.Affine.CoordinateRing.exists_eq_XYIdeal WeierstrassCurve.Affine.CoordinateRing.exists_eq_XYIdeal
