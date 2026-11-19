/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_Mathlib_RingTheory_Ideal_Quotient_Basic (git blob 46e759b3bee767fb616aefb8f99994173bc11bb2, sha256 545124ce8ae648b585e28e786176e0875d6bced4c4d0f3da5de5fc5ca95c322e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

section

variable {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]

theorem Ideal.Quotient.out_sub (x : R) : (Ideal.Quotient.mk I x).out - x ∈ I := by
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]

end
