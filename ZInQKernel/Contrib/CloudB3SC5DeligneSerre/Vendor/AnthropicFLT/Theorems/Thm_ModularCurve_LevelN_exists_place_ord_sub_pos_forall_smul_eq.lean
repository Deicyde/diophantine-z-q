/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_LevelN_exists_place_ord_sub_pos_forall_smul_eq (git blob f883494d35109a718593df9e0292de2851b2c01a, sha256 ceee49233280a7bc2c9a9582479e644cdb6fbe0b0637865e3aa8ee5a72efe9da).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LevelNFunctionField
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_BaseChangeGalois
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_LevelN_exists_place_ord_sub_pos_forall_smul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.LevelN.exists_place_ord_sub_pos_forall_smul_eq (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] (τ₀ : UpperHalfPlane) :
    ∃ W : AlgebraicCurve.Place ℂ K,
      0 < W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N) -
          algebraMap ℂ K (ModularCurve.LevelN.jAnalytic τ₀)) ∧
      ∀ (γ : SL(2, ℤ)) (_ : γ • τ₀ = τ₀)
        (hst : ∀ F ∈ ModularCurve.LevelN.ring N,
          (fun τ : UpperHalfPlane => F (γ⁻¹ • τ)) ∈ ModularCurve.LevelN.ring N)
        (φ : K ≃ₐ[ℂ] K),
        (∀ (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N),
            φ (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) =
              algebraMap (ModularCurve.LevelN.ring N) K
                ⟨fun τ : UpperHalfPlane => F (γ⁻¹ • τ), hst F hF⟩) →
        AlgebraicCurve.SemilinearAut.ofAlgAut φ • W = W := by
  revert N K τ₀
  exact @_root_.P2MW.S_ModularCurve_LevelN_exists_place_ord_sub_pos_forall_smul_eq.solution
