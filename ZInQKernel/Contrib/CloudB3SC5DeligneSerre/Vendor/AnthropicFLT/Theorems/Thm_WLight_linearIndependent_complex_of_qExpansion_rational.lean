/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WLight_linearIndependent_complex_of_qExpansion_rational (git blob 23c1be0d3d1d7ccc6832502a50565415101609b0, sha256 31ed482599b73977cad2c6b422fbb374c853f520ac765d6826f3855e400a04d5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WLight_linearIndependent_complex_of_qExpansion_rational

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open Complex UpperHalfPlane Function
open scoped Topology Manifold ModularForm

theorem WLight.linearIndependent_complex_of_qExpansion_rational (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ ℂ) (s : Finset (ℍ → ℂ)) (m : ℕ)
    (hdata : ∀ f ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧
      Function.Periodic ((f * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (f * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (f * ModularForm.discriminant ^ m)).coeff n ∈ K)
    (hind : LinearIndependent ↥K (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ))) :
    LinearIndependent ℂ (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) := by
  revert N K s m hdata hind
  exact @_root_.P2MW.S_WLight_linearIndependent_complex_of_qExpansion_rational.solution
