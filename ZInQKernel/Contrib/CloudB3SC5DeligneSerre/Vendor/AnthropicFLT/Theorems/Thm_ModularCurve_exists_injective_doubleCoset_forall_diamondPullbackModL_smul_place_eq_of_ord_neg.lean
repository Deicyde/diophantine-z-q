/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg (git blob d995342d84c7f31cbebc8490e0f5a1c76478eff7, sha256 05d05663951832e08197f0839e643ee12ddd0f50a106fe1b86ecfecbffac051e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0ModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHDiamondModL
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped MatrixGroups

theorem ModularCurve.exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (ρ : CongruenceSubgroup.Gamma0 M →*
      (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)))
    (hρ : ModularCurve.IsDiamondPullbackModL K M H ρ)
    (hle : ModularCurve.modularFunctionFieldFullC K M ≤
      ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hfix : ∀ (γ : CongruenceSubgroup.Gamma0 M)
      (x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
      (x : LaurentSeries K) ∈ ModularCurve.modularFunctionFieldFullC K M → ρ γ x = x) :
    ∃ ι : {P : AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldFullC K M) //
              P.ord (⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem_full K M⟩ :
                ModularCurve.modularFunctionFieldFullC K M) < 0} →
            DoubleCoset.Quotient
              (CongruenceSubgroup.Gamma0 M : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
              ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) :
                  Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
                Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
        Function.Injective ι ∧
        ∀ P (g : Matrix.SpecialLinearGroup (Fin 2) ℤ),
          ι P = DoubleCoset.mk (CongruenceSubgroup.Gamma0 M)
            (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1)) g →
          ∀ γ : CongruenceSubgroup.Gamma0 M,
            g⁻¹ * (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * g ∈
              Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) →
            ∀ Q : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
              Q.toValuationSubring.comap (IntermediateField.inclusion hle).toRingHom =
                P.1.toValuationSubring →
              ρ γ • Q = Q := by
  revert M H ℓ hℓM K ρ hρ hle hfix
  exact @_root_.P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg.solution
