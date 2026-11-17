/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_sq_eq_neg_one (git blob a7795dc83e843c0d4928f458614c9bb8432644cd, sha256 bbd02a745745b4543d10f15eb55725e520cbe7c47e24167916b09eaf758cc09b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_sq_eq_neg_one

theorem solution
    {R : Type*} [CommRing R] (u : Rˣ) (hu : (u : R) ^ 2 = -1) (A : R) :
    (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve R) =
      ⟨0, 0, 0, A, 0⟩ := by
  have h1 : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hu4 : (u : R) ^ 4 = 1 := by
    calc (u : R) ^ 4 = ((u : R) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hu]; ring
  have h4 : ((u⁻¹ : Rˣ) : R) ^ 4 = 1 := by
    calc ((u⁻¹ : Rˣ) : R) ^ 4 = ((u⁻¹ : Rˣ) : R) ^ 4 * (u : R) ^ 4 := by rw [hu4, mul_one]
      _ = (((u⁻¹ : Rˣ) : R) * (u : R)) ^ 4 := by ring
      _ = 1 := by rw [h1, one_pow]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
  · ring
  · ring
  · ring
  · linear_combination A * h4
  · ring
