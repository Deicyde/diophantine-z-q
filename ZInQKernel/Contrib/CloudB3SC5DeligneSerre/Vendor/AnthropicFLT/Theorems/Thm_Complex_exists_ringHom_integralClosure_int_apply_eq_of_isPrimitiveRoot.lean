/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Complex_exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot (git blob 940f04a9a21b7e83870033d772dd623ed0ab9c39, sha256 a2eebc6d30f69b53f2e47d9ee1267b4cdcef677d63d8f7685f189d82d052353c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Complex_exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Complex.exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot
    (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ) [NeZero M] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    ∃ φ : integralClosure ℤ ℂ →+* K,
      ∀ z : integralClosure ℤ ℂ,
        (z : ℂ) = Complex.exp (2 * Real.pi * Complex.I / M) → φ z = ζ := by
  revert ℓ M hℓM K ζ hζ
  exact @_root_.P2MW.S_Complex_exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot.solution
