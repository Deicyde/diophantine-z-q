/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_LevelN_isZeroAtImInfty_slash_of_mem_regularDifferentials (git blob 20cdd25ca1a35dd7b1bc2d2366d3b4a4aaa3ec17, sha256 46720a3705d886579a681b4e54dfe4213429a334277a6929436da5f1f8f7591b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LevelNFunctionField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_LevelN_isZeroAtImInfty_slash_of_mem_regularDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.LevelN.isZeroAtImInfty_slash_of_mem_regularDifferentials (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K]
    (ω : KaehlerDifferential ℂ K) (hω : ω ∈ AlgebraicCurve.regularDifferentials ℂ K)
    (F : UpperHalfPlane → ℂ)
    (hF : ∀ (a b c e : UpperHalfPlane → ℂ) (ha : a ∈ ModularCurve.LevelN.ring N)
      (hb : b ∈ ModularCurve.LevelN.ring N) (hc : c ∈ ModularCurve.LevelN.ring N)
      (he : e ∈ ModularCurve.LevelN.ring N), b ≠ 0 → e ≠ 0 →
      ω = (algebraMap (ModularCurve.LevelN.ring N) K ⟨a, ha⟩ /
            algebraMap (ModularCurve.LevelN.ring N) K ⟨b, hb⟩) •
          KaehlerDifferential.D ℂ K (algebraMap (ModularCurve.LevelN.ring N) K ⟨c, hc⟩ /
            algebraMap (ModularCurve.LevelN.ring N) K ⟨e, he⟩) →
      ∀ τ : UpperHalfPlane, F τ * b τ * e τ ^ 2 =
        a τ * (e τ * deriv (c ∘ UpperHalfPlane.ofComplex) τ -
          c τ * deriv (e ∘ UpperHalfPlane.ofComplex) τ))
    (δ : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty (F ∣[(2 : ℤ)] δ) := by
  revert N K ω hω F hF δ
  exact @_root_.P2MW.S_ModularCurve_LevelN_isZeroAtImInfty_slash_of_mem_regularDifferentials.solution
