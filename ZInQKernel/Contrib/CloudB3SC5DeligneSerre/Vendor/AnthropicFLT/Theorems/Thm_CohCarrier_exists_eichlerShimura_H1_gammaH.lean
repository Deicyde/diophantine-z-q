/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CohCarrier_exists_eichlerShimura_H1_gammaH (git blob ab1cd6f844ace26d3cbb9476c4dc6b7ddc6a3a6c, sha256 83efc2e19eb9a1e370a5e8efe831d5bc4642ff50f34ddbcfb5cb80ee8ae513c4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodHomPair
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CohCarrier_exists_eichlerShimura_H1_gammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.exists_eichlerShimura_H1_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ (J : ↥(CohCarrier.GammaH M H) →* ↥(CohCarrier.GammaH M H))
      (ES : (CuspForm (CohCarrier.GammaH M H) 2 × CuspForm (CohCarrier.GammaH M H) 2)
        →ₗ[ℂ] CohCarrier.H1 M H ℂ),
      (∀ γ : ↥(CohCarrier.GammaH M H), ((J γ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) =
        ModularCurve.Period.jConjSL (γ : SL(2, ℤ))) ∧
      (∀ (f g : CuspForm (CohCarrier.GammaH M H) 2) (γ : ↥(CohCarrier.GammaH M H)),
        ES (f, g) (Additive.ofMul γ) =
          ModularCurve.periodMapOf (CohCarrier.GammaH M H) f (Additive.ofMul γ) +
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) f (Additive.ofMul (J γ)) +
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) g (Additive.ofMul γ) -
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) g (Additive.ofMul (J γ))) ∧
      Function.Injective ES ∧
      LinearMap.range ES = ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ES (CuspForm.heckeTLinH 2 hℓ hℓM f, CuspForm.heckeTLinH 2 hℓ hℓM g) =
          CohCarrier.heckeT M H ℓ ℂ (ES (f, g))) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        haveI : NeZero q := ⟨hq.ne_zero⟩
        ES (CuspForm.heckeULinH 2 q f, CuspForm.heckeULinH 2 q g) =
          CohCarrier.heckeT M H q ℂ (ES (f, g))) ∧
      (∀ (d : (ZMod M)ˣ) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        ES (CuspForm.diamondLinH 2 d f, CuspForm.diamondLinH 2 d g) =
          CohCarrier.diamondL M H ℂ d (ES (f, g))) := by
  revert M H
  exact @_root_.P2MW.S_CohCarrier_exists_eichlerShimura_H1_gammaH.solution
