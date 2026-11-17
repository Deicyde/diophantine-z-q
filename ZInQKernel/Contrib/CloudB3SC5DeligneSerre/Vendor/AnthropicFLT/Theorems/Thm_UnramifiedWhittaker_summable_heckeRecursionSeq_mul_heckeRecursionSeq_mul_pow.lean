/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UnramifiedWhittaker_summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow (git blob 888a61c8baa415d578fbe706d6da0f284d7d354d, sha256 a6098ed62a268f0205fbdbffa0b7890395601555129ee5969c2909ad2705bf60).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UnramifiedWhittaker_summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Polynomial UnramifiedWhittaker

theorem UnramifiedWhittaker.summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow
    (N lam om lam' om' : ℂ) (hN : N ≠ 0) (y : ℂ)
    (hy : ‖y‖ * (max 1 (‖lam‖ + ‖N * om‖)) * (max 1 (‖lam'‖ + ‖N * om'‖)) < ‖N‖ ^ 2) :
    Summable fun m : ℕ =>
      heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m := by
  revert N lam om lam' om' hN y hy
  exact @_root_.P2MW.S_UnramifiedWhittaker_summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow.solution
