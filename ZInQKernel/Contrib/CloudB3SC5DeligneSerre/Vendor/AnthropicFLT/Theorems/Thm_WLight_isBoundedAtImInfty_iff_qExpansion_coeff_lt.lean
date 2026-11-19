/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WLight_isBoundedAtImInfty_iff_qExpansion_coeff_lt (git blob 7ac847f0746fd0db3d0ee3055b3398101a09f300, sha256 069f727b00ea2a7a8c25797991ff770ec007bd0c583888307db72584c8e015b3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation
import Mathlib.FieldTheory.IntermediateField.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WLight_isBoundedAtImInfty_iff_qExpansion_coeff_lt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem WLight.isBoundedAtImInfty_iff_qExpansion_coeff_lt (N : ℕ) [NeZero N] {F : ℍ → ℂ} {M : ℕ}
    (hFhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hFper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) N)
    (hFbd : IsBoundedAtImInfty (F * ModularForm.discriminant ^ M)) :
    IsBoundedAtImInfty F ↔
      ∀ n < N * M,
        (UpperHalfPlane.qExpansion N (F * ModularForm.discriminant ^ M)).coeff n = 0 := by
  revert N F M hFhol hFper hFbd
  exact @_root_.P2MW.S_WLight_isBoundedAtImInfty_iff_qExpansion_coeff_lt.solution
