/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WLight_span_inter_rational_of_twist_stable (git blob fb8f903332df7420e49cf69acf2e8f606be5c076, sha256 988858bc3b531f4cfd8ee7b520a8bfc9fcba1338f441a2e940e5003de403c6c1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WLight_span_inter_rational_of_twist_stable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open Complex UpperHalfPlane Function
open scoped Topology Manifold ModularForm

theorem WLight.span_inter_rational_of_twist_stable (K : IntermediateField ℚ ℂ)
    (M : Submodule ↥K (ℍ → ℂ))
    (hflat : ∀ s : Finset (ℍ → ℂ), (↑s : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) →
      LinearIndependent ↥K (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) →
      LinearIndependent ℂ (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)))
    (V : Submodule ℂ (ℍ → ℂ))
    (hVle : V ≤ Submodule.span ℂ (M : Set (ℍ → ℂ)))
    (hstab : ∀ (σ : ℂ ≃ₐ[↥K] ℂ) (v : ℍ → ℂ), v ∈ V →
      ∃ (s : Finset (ℍ → ℂ)) (c : (ℍ → ℂ) → ℂ), (↑s : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) ∧
        v = ∑ w ∈ s, c w • w ∧ (∑ w ∈ s, σ (c w) • w) ∈ V)
    (G1 : ∀ c : ℂ, (∀ σ : ℂ ≃ₐ[↥K] ℂ, σ c = c) → ∃ a : ↥K, algebraMap ↥K ℂ a = c)
    {v : ℍ → ℂ} (hv : v ∈ V) :
    v ∈ Submodule.span ℂ {y : ℍ → ℂ | y ∈ V ∧ y ∈ M} := by
  revert K M hflat V hVle hstab G1 v hv
  exact @_root_.P2MW.S_WLight_span_inter_rational_of_twist_stable.solution
