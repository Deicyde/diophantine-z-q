/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_finite_integralClosure_adjoin_singleton_of_isAlgClosed (git blob 7011b1b8c33306ecfa93b2760f9ba596044be202, sha256 b6304496b24c22f8f4b215d3236c315d24f1c43b61b1cdd5b5d843e9ae45379f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_finite_integralClosure_adjoin_singleton_of_isAlgClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Algebra.finite_integralClosure_adjoin_singleton_of_isAlgClosed
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] (x : F)
    (hx : Transcendental k x)
    (hfd : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    Module.Finite (Algebra.adjoin k ({x} : Set F))
      (integralClosure (Algebra.adjoin k ({x} : Set F)) F) := by
  revert k F x hx hfd
  exact @_root_.P2MW.S_Algebra_finite_integralClosure_adjoin_singleton_of_isAlgClosed.solution
