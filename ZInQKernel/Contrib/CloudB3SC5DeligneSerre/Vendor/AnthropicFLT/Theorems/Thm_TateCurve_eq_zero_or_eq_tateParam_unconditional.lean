/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_TateCurve_eq_zero_or_eq_tateParam_unconditional (git blob 73bd2970940f48f2eae5016df10658e26fe4144c, sha256 78474343babe9871ee2d53d830a68a6105fad5c3bda4249604826cc5d2411d96).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_XMultAlignment
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_TateCurve_eq_zero_or_eq_tateParam_unconditional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open WeierstrassCurve.Affine TateCurve
open scoped NNReal
theorem TateCurve.eq_zero_or_eq_tateParam_unconditional {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] [IsAlgClosed K] {q ζ t : K} {p : ℕ} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hp : p.Prime) (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q) (R : (curve q).toAffine.Point) (hR : p • R = 0) : R = 0 ∨ ∃ i j : ℕ, i < p ∧ j < p ∧ ¬(i = 0 ∧ j = 0) ∧ ∃ hns : (curve q).toAffine.Nonsingular (pointX q (ζ ^ i * t ^ j)) (pointY q (ζ ^ i * t ^ j)), R = Point.some (pointX q (ζ ^ i * t ^ j)) (pointY q (ζ ^ i * t ^ j)) hns := by
  revert K q ζ t p hq0 hq hp hp5 hζ ht R hR
  exact @_root_.P2MW.S_TateCurve_eq_zero_or_eq_tateParam_unconditional.solution
