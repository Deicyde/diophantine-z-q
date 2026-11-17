/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_LevelN_exists_place_ord_neg_forall_smul_eq (git blob d143d981134390420640f34c8872c0b1fb66f788, sha256 13301c7ccaa070327ec2956719b70f72f245c6825019591be4a9133c1b5f5fd7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LevelNFunctionField
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_BaseChangeGalois
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_LevelN_exists_place_ord_neg_forall_smul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.LevelN.exists_place_ord_neg_forall_smul_eq (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K]
    (hst : ∀ F ∈ ModularCurve.LevelN.ring N,
      (fun τ : UpperHalfPlane => F (ModularGroup.T⁻¹ • τ)) ∈ ModularCurve.LevelN.ring N) :
    ∃ W : AlgebraicCurve.Place ℂ K,
      W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) < 0 ∧
      ∀ φ : K ≃ₐ[ℂ] K,
        (∀ (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N),
            φ (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) =
              algebraMap (ModularCurve.LevelN.ring N) K
                ⟨fun τ : UpperHalfPlane => F (ModularGroup.T⁻¹ • τ), hst F hF⟩) →
        AlgebraicCurve.SemilinearAut.ofAlgAut φ • W = W := by
  revert N K hst
  exact @_root_.P2MW.S_ModularCurve_LevelN_exists_place_ord_neg_forall_smul_eq.solution
