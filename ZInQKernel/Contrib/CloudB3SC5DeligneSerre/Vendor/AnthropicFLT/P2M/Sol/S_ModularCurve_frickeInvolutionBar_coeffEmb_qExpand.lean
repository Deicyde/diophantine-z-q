/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand (git blob b2442b9f7b2be4edbf20841d4cbb67430dd40bc1, sha256 be32ab80376e9b9152ff6f7309dbbc9e4a3d2023a6fc80a5ed7f9a0b4397192c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (a b : ℕ) (hab : a * b = N) [NeZero a] [NeZero b] :
    frickeInvolutionBar N ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ a jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro b hab))⟩ = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro_left a hab))⟩ := by
  rw [frickeInvolutionBar_def]
  refine (geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (frickeInvolutionFull N)
    ⟨qExpand ℚ a jq, jqd_mem_full N (Dvd.intro b hab)⟩).trans (Subtype.ext ?_)
  change coeffEmb (AlgebraicClosure ℚ) ((frickeInvolutionFull N ⟨qExpand ℚ a jq, _⟩ : modularFunctionFieldFull N) :
    LaurentSeries ℚ) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq)
  rw [h a b hab ‹NeZero a› ‹NeZero b›]
