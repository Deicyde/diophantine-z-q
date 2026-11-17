/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod (git blob 6bc759bab8461304b6142c19f51b79de8b110c36, sha256 6778e86d6d2df3ae1a0336e7881ccc758203dccc41c3e15a9e2a057051702a9f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0ModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod
    (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ) [NeZero M] (hℓM : ¬ ℓ ∣ M) (H : Subgroup (ZMod M)ˣ) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →*
        (ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H) ≃ₐ[ZMod ℓ]
          ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H)),
      (∀ (γ : CongruenceSubgroup.Gamma0 M) (k : ℤ)
          (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) (p : PowerSeries ℤ),
          ModularCurve.IsIntegralQExp f p →
          ∃ (n : ℕ) (f₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) (p₁ : PowerSeries ℤ),
            (⇑f₁ : UpperHalfPlane → ℂ) = ((M : ℂ) ^ n) • ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) ∧
            ModularCurve.IsIntegralQExp f₁ p₁ ∧
            (ModularCurve.intSeriesC (ZMod ℓ) p₁ = 0 ↔ ModularCurve.intSeriesC (ZMod ℓ) p = 0)) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M) (k : ℤ)
          (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg pf₁ pg₁ : PowerSeries ℤ),
          ModularCurve.IsIntegralQExp f pf → ModularCurve.IsIntegralQExp g pg →
          ModularCurve.IsIntegralQExp f₁ pf₁ → ModularCurve.IsIntegralQExp g₁ pg₁ →
          (⇑f₁ : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) →
          (⇑g₁ : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) →
          ModularCurve.intSeriesC (ZMod ℓ) pg ≠ 0 →
          ∀ x : ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H),
            (x : LaurentSeries (ZMod ℓ)) =
                ModularCurve.intSeriesC (ZMod ℓ) pf₁ / ModularCurve.intSeriesC (ZMod ℓ) pg₁ →
            ((ρ γ x : ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H)) :
                LaurentSeries (ZMod ℓ)) =
              ModularCurve.intSeriesC (ZMod ℓ) pf / ModularCurve.intSeriesC (ZMod ℓ) pg) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 M,
          (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1)) → ρ γ = 1) ∧
      ModularCurve.modularFunctionFieldFullC (ZMod ℓ) M ≤
        ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M)
          (x : ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H)),
          (x : LaurentSeries (ZMod ℓ)) ∈ ModularCurve.modularFunctionFieldFullC (ZMod ℓ) M →
            ρ γ x = x) := by
  revert ℓ M hℓM H
  exact @_root_.P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod.solution
