/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_WeierstrassCurve_velu2_tangent_addX_cleared_identity
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_Velu
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_WeierstrassCurve_velu2_tangent_addX_cleared_identity

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

private theorem velu2TangentAddX_assemble {R : Type*} [CommRing R] {A M C D t u : R}
    (h1 : A * u = t ^ 2) (h2 : C = D ^ 2) (h3 : M = t ^ 2 * u + 2 * D ^ 2) :
    A * M * u * C = (t * D) ^ 2 * (t ^ 2 * u + 2 * C) := by
  linear_combination (M * C) * h1 + (t ^ 4 * u) * h2 + (t ^ 2 * C) * h3

theorem solution
    {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    (W.a₁ ^ 2 * (x - x₀)
            + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀))
          * (((x - x₀) ^ 2 - W.veluGx x₀ y₀)
                * (6 * x ^ 2 + (4 * W.a₂ + W.a₁ ^ 2) * x + 2 * W.a₄ + W.a₁ * W.a₃)
              + W.veluGx x₀ y₀
                * (W.a₁ ^ 2 * (x - x₀)
                    + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀)))
          * (x - x₀)
          * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
              + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃)
              - (W.a₂ + 2 * x + x₀) * (2 * y + W.a₁ * x + W.a₃) ^ 2)
      = ((2 * y + W.a₁ * x + W.a₃) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀)) ^ 2
        * ((2 * y + W.a₁ * x + W.a₃) ^ 2 * (x - x₀)
            + 2
              * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
                  + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
                    * (2 * y + W.a₁ * x + W.a₃)
                  - (W.a₂ + 2 * x + x₀) * (2 * y + W.a₁ * x + W.a₃) ^ 2)) := by
  rw [Affine.equation_iff] at hP hQ
  refine velu2TangentAddX_assemble ?_ ?_ ?_
  ·
    linear_combination (-4) * hP + 4 * hQ
      + (-2 * W.a₁ * x + W.a₁ * x₀ - W.a₃ - 2 * y₀) * hord
  ·
    simp only [veluGx]
    linear_combination (-W.a₁ ^ 2 - 4 * W.a₂ - 8 * x - 4 * x₀) * hP
      + (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x + 4 * x₀) * hQ
      + (-W.a₁ ^ 2 * y₀ + W.a₁ * W.a₂ * x₀ + W.a₁ * W.a₄ - W.a₁ * x ^ 2 + W.a₁ * x₀ ^ 2
          - W.a₂ * W.a₃ - 2 * W.a₂ * y₀ - 2 * W.a₃ * x - W.a₃ * x₀ - 4 * x * y₀
          - 2 * x₀ * y₀) * hord
  ·
    simp only [veluGx]
    linear_combination (-4 * x + 4 * x₀) * hP + (4 * x - 4 * x₀) * hQ
      + (W.a₁ ^ 2 * y₀ - 2 * W.a₁ * W.a₂ * x₀ - W.a₁ * W.a₄ - W.a₁ * x ^ 2 + W.a₁ * x * x₀
          - 3 * W.a₁ * x₀ ^ 2 - W.a₃ * x + W.a₃ * x₀ - 2 * x * y₀ + 2 * x₀ * y₀) * hord
