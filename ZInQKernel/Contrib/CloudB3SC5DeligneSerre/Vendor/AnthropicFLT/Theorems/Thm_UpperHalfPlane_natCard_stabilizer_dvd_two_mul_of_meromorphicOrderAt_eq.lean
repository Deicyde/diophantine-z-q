/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq (git blob e7642c5282d95307c56c7d285923fd0a844ef7cd, sha256 31abd024f2d5176790a5c3d45ff2ec6fb288c26570dfe18fcc58940158ea46a1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups

theorem UpperHalfPlane.natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq
    (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ) (hF : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (τ : ℍ) (n : ℤ)
    (hn : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = n) :
    (Nat.card (MulAction.stabilizer Γ τ) : ℤ) ∣ 2 * n := by
  revert Γ F hF τ n hn
  exact @_root_.P2MW.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq.solution
