/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_mem_regularDiffs_iff (git blob 9f0ac5809d9f61e811a7f500ad51c4a232a80cc8, sha256 dd5723e39d4dc4470b47a78c793148d3aa2228ff899d4134a0f56d91fd5a1682).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Differentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_mem_regularDiffs_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem AlgebraicCurve.mem_regularDiffs_iff {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (ω : Ω[F⁄K]) :
    ω ∈ AlgebraicCurve.regularDiffs K F ↔ AlgebraicCurve.IsRegularDiff K F ω := by
  revert K F x ω
  exact @_root_.P2MW.S_AlgebraicCurve_mem_regularDiffs_iff.solution
