/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model (git blob dc204bda427d8a7165755a72eb4457ed9950b58f, sha256 815eb0bffd1c392cb40ea496ec7581d1f60623f2ff930b79acb96633b1cc364a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

set_option autoImplicit false

theorem ws13_some_congr' {k : Type*} [Field k] {V : Affine k} {x₁ x₂ y₁ y₂ : k}
    {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : V.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

theorem solution
    {k : Type*} [Field k] [DecidableEq k] (B : k) (h2 : (2 : k) ≠ 0) {y : k} (hy0 : y ≠ 0)
    (h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular 0 y) :
    (WeierstrassCurve.Affine.Point.some 0 y h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Point)
      + WeierstrassCurve.Affine.Point.some 0 y h
      = -(WeierstrassCurve.Affine.Point.some 0 y h) := by
  have hyne : y ≠ Affine.negY (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k) 0 y := by
    simp only [Affine.negY]
    intro heq
    have : (2 : k) * y = 0 := by linear_combination heq
    rcases mul_eq_zero.mp this with h' | h'
    · exact h2 h'
    · exact hy0 h'
  rw [Point.add_of_Y_ne hyne, Point.neg_some]
  refine ws13_some_congr' ?_ ?_
  · rw [slope_of_Y_ne rfl hyne]
    simp only [Affine.addX, Affine.negY]
    ring
  · rw [slope_of_Y_ne rfl hyne]
    simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX]
    ring
