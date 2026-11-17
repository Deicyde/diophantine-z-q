/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one (git blob c3587511a0867169e8c423f06c850b0ceb0034ee, sha256 a26f373e04e7c908761d163b319b001ed2f7ea592dd5fa5616e84b286c089595).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (q m : ℕ)
    (hA : A.LiesOverPrime q) (hσ : A.IsFrobeniusAt σ q) (hm : m.Coprime q)
    (ζ : L) (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ q := by
  revert K L A σ q m hA hσ hm ζ hζ
  exact @_root_.P2MW.S_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one.solution
