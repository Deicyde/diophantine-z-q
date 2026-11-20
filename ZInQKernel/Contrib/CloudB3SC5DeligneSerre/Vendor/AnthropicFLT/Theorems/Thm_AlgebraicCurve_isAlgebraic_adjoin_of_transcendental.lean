/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental (git blob c053b2178eb78dc871a1b22841a74a17dabb13b9, sha256 fa7c0fcc37425fe3e5113a979f329007b752292afc95b3739425471eb1508ae1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.Algebraic.Defs
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AlgebraicCurve.isAlgebraic_adjoin_of_transcendental {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] {t : F} (ht : Transcendental K t) :
    Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F := by
  revert K F x t ht
  exact @_root_.P2MW.S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.solution
