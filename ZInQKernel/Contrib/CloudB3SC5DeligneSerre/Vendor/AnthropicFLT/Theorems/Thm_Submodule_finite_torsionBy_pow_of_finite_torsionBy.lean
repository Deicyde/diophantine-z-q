/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Submodule_finite_torsionBy_pow_of_finite_torsionBy (git blob 27d8926e871beda0d6840a0c46d2bbe1497e1093, sha256 00e3599821f726664f8790f100634e8fb627810c7f5f0784dfd41e047bbe1eb0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Submodule_finite_torsionBy_pow_of_finite_torsionBy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Submodule.finite_torsionBy_pow_of_finite_torsionBy
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a : R)
    (h : Finite (Submodule.torsionBy R M a)) (k : ℕ) :
    Finite (Submodule.torsionBy R M (a ^ k)) := by
  revert R M a h k
  exact @_root_.P2MW.S_Submodule_finite_torsionBy_pow_of_finite_torsionBy.solution
