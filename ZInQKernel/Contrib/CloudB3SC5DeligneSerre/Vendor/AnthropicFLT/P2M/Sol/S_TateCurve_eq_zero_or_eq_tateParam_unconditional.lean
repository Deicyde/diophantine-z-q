/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_TateCurve_eq_zero_or_eq_tateParam_unconditional (git blob 7360a943cf988f3d83e3372a07704c88253c8278, sha256 9af9b3f3d2c1f7fed6963650c7607dd27a001aa2131c612e6e5366a62bd3665d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_eq_zero_or_eq_tateParam_of_prime_nsmul_eq_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_symAddHyps_unconditional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_TateCurve_eq_zero_or_eq_tateParam_unconditional

open WeierstrassCurve.Affine TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] [DecidableEq K] [IsAlgClosed K] {q ζ t : K} {p : ℕ}
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    (R : (curve q).toAffine.Point) (hR : p • R = 0) :
    R = 0 ∨ ∃ i j : ℕ, i < p ∧ j < p ∧ ¬(i = 0 ∧ j = 0) ∧
      ∃ hns : (curve q).toAffine.Nonsingular (pointX q (ζ ^ i * t ^ j))
        (pointY q (ζ ^ i * t ^ j)),
        R = Point.some (pointX q (ζ ^ i * t ^ j)) (pointY q (ζ ^ i * t ^ j)) hns :=
  TateCurve.eq_zero_or_eq_tateParam_of_prime_nsmul_eq_zero
    (TateCurve.symAddHyps_unconditional hq0 hq) hq0 hq hp hp5 hζ ht R hR
