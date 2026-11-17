/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact (git blob 8189b290eecf9c0587bc6409f3f5751cff1ff802, sha256 076a8c9185c3be3f01bee573a01c310673490cd364c3c9adbc6587c321f1f9ca).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.AdeleRing
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact
    (F : Type) [Field F] [NumberField F]
    {C : Set (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)} (hC : IsCompact C) :
    {ξ : F | algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ξ ∈ C}.Finite := by
  revert F C hC
  exact @_root_.P2MW.S_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact.solution
