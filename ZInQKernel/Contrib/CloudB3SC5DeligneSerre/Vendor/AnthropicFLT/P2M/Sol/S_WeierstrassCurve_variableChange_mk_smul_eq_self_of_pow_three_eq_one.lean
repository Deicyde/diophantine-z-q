/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_pow_three_eq_one (git blob ab6cd17c5b73635c1bc30d365bc61bcf0e6f94af, sha256 d344bee6ff1e962c92aefea236732541d5eff4621d20532ce4ec8b21a00070b3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_pow_three_eq_one

theorem solution
    {R : Type*} [CommRing R] (u : Rˣ) (hu : (u : R) ^ 3 = 1) (B : R) :
    (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve R) =
      ⟨0, 0, 0, 0, B⟩ := by
  have h1 : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h3 : ((u⁻¹ : Rˣ) : R) ^ 3 = 1 := by
    calc ((u⁻¹ : Rˣ) : R) ^ 3 = ((u⁻¹ : Rˣ) : R) ^ 3 * (u : R) ^ 3 := by rw [hu, mul_one]
      _ = (((u⁻¹ : Rˣ) : R) * (u : R)) ^ 3 := by ring
      _ = 1 := by rw [h1, one_pow]
  have h6 : ((u⁻¹ : Rˣ) : R) ^ 6 = 1 := by
    calc ((u⁻¹ : Rˣ) : R) ^ 6 = (((u⁻¹ : Rˣ) : R) ^ 3) ^ 2 := by ring
      _ = 1 := by rw [h3, one_pow]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
  · ring
  · ring
  · ring
  · ring
  · linear_combination B * h6
