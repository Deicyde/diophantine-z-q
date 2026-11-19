/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UnramifiedWhittaker_tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval (git blob 7d36f662dff47561303aeaa6b29e3495172d4762, sha256 e8713599af84c6d938d45f93ad73db1fd4b5cd85b8ef99adc05133779805d0e4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UnramifiedWhittaker_tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Polynomial UnramifiedWhittaker

theorem UnramifiedWhittaker.tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval
    (N lam om lam' om' : ℂ) (hN : N ≠ 0) (y : ℂ)
    (hsum : Summable fun m : ℕ =>
      heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m) :
    (∑' m : ℕ, heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m) *
        (LanglandsTunnell.RankinSelberg.rsEulerPoly lam (N * om) lam' (N * om') 0).eval (y / N ^ 2) =
      1 - om * om' * (y / N) ^ 2 := by
  revert N lam om lam' om' hN y hsum
  exact @_root_.P2MW.S_UnramifiedWhittaker_tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval.solution
