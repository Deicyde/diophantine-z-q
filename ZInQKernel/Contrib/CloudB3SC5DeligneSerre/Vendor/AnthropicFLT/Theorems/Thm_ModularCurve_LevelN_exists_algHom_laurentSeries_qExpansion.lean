/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion (git blob 08723f4bcd6ae75f5ce515d252d11e1496d35350, sha256 5a60625c96738055eb4fec35c5a64251dde2210269fe0636aac42d676c874885).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LevelNFunctionField
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.LevelN.exists_algHom_laurentSeries_qExpansion (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] :
    ∃ E : K →ₐ[ℂ] LaurentSeries ℂ,
      E (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) =
          ModularCurve.qExpand ℂ N (ModularCurve.jqModC ℂ) ∧
      ∀ (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N) (m : ℕ),
        UpperHalfPlane.IsBoundedAtImInfty (F * ModularForm.discriminant ^ m) →
        E (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) *
            HahnSeries.ofPowerSeries ℤ ℂ
              (UpperHalfPlane.qExpansion N (ModularForm.discriminant : UpperHalfPlane → ℂ)) ^ m =
          HahnSeries.ofPowerSeries ℤ ℂ
            (UpperHalfPlane.qExpansion N (F * ModularForm.discriminant ^ m)) := by
  revert N K
  exact @_root_.P2MW.S_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion.solution
