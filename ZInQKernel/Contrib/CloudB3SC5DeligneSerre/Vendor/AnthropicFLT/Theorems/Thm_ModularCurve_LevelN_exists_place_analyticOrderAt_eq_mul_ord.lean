/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_LevelN_exists_place_analyticOrderAt_eq_mul_ord (git blob 8225574fd87f27445f1b9aa99a78aaba161e9284, sha256 4dda5101486ea0defc60c61c826a0e6c15b4272787b6dc30eb58341d457a093a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LevelNFunctionField
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_LevelN_exists_place_analyticOrderAt_eq_mul_ord

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.LevelN.exists_place_analyticOrderAt_eq_mul_ord (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] (τ₀ : UpperHalfPlane) :
    ∃ (W : AlgebraicCurve.Place ℂ K) (e : ℕ), 0 < e ∧
      ∀ (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N), F ≠ 0 →
        analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (τ₀ : ℂ) ≠ ⊤ ∧
        ((analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (τ₀ : ℂ)).toNat : ℤ) =
          e * W.ord (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) := by
  revert N K τ₀
  exact @_root_.P2MW.S_ModularCurve_LevelN_exists_place_analyticOrderAt_eq_mul_ord.solution
