/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UpperHalfPlane_linearIndependent_complex_of_qExpansion_coeff_mem (git blob 6ad778fbbe8ad43fbe109ec25a397a3c8bce12cc, sha256 b433c3fcde9ef6d47ca0333ff5f3c67386e51d1d004569293bf681e1b51ad043).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.FieldTheory.IntermediateField.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UpperHalfPlane_linearIndependent_complex_of_qExpansion_coeff_mem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped Manifold

theorem UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ ℂ) {ι : Type*} (f : ι → UpperHalfPlane → ℂ)
    (hf : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i) ∧ ∃ m : ℕ,
      Function.Periodic ((f i * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
      UpperHalfPlane.IsBoundedAtImInfty (f i * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (f i * ModularForm.discriminant ^ m)).coeff n ∈ K)
    (hli : LinearIndependent ↥K f) : LinearIndependent ℂ f := by
  revert N K ι f hf hli
  exact @_root_.P2MW.S_UpperHalfPlane_linearIndependent_complex_of_qExpansion_coeff_mem.solution
