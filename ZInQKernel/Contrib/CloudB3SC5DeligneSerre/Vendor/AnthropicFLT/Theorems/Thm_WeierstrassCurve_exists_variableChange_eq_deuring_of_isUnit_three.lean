/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_exists_variableChange_eq_deuring_of_isUnit_three (git blob d7d05b836885e7d6dda8a8a079224d9473c40445, sha256 55267f2f298666998e73b7435a61646d7a5bb37d5d70e34b180199487bf470b1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_variableChange_eq_deuring_of_isUnit_three

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem WeierstrassCurve.exists_variableChange_eq_deuring_of_isUnit_three
    {M : Type u} [Field M] [DecidableEq M] (A : ValuationSubring M) (h3 : IsUnit (3 : A))
    (E : WeierstrassCurve M) [E.IsElliptic] (hj : E.j ∈ A)
    {x₀ y₀ : M} (hP : E.toAffine.Nonsingular x₀ y₀) (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0)
    {c : M} (hc : c ^ 3 = 2 * y₀ + E.a₁ * x₀ + E.a₃) :
    ∃ (α : A) (κ : VariableChange M),
      IsUnit (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve A).Δ ∧
      (κ.u : M) = c ∧ κ.r = x₀ ∧
      κ.s = (3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄ - E.a₁ * y₀) / (2 * y₀ + E.a₁ * x₀ + E.a₃) ∧
      κ.t = y₀ ∧
      κ • E = (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve A).map A.subtype := by
  revert M A h3 E hj x₀ y₀ hP h3P c hc
  exact @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_eq_deuring_of_isUnit_three.solution
