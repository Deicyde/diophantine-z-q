/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Subalgebra_isIntegrallyClosed_adjoin_singleton_of_transcendental (git blob e79a4cb7572d2bb0e89f25803cab00e4c8ddac66, sha256 fecc665e4c3e151cab16b8a1757a78fc7cd5aa53c0f106ac3c6c9cfc45e3be2b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Subalgebra_isIntegrallyClosed_adjoin_singleton_of_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Subalgebra.isIntegrallyClosed_adjoin_singleton_of_transcendental
    {L : Type*} [Field L] {F : Type*} [CommRing F] [IsDomain F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) :
    IsIntegrallyClosed (Algebra.adjoin L ({x} : Set F)) := by
  revert L F x hxL
  exact @_root_.P2MW.S_Subalgebra_isIntegrallyClosed_adjoin_singleton_of_transcendental.solution
