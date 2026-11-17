/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CommRing_infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int (git blob 366041423aac6f188fab7c108b392aa260f4b82b, sha256 55a85f84f610ab47d022fe88c59e48170a6437b08df7a49a55870c01c97b7b73).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CommRing_infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] [Module.Finite ℤ R] :
    {ℓ : ℕ | ℓ.Prime ∧ Nonempty (R →+* ZMod ℓ)}.Infinite := by
  revert R
  exact @_root_.P2MW.S_CommRing_infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int.solution
