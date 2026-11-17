/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularCurve_XHDiamondModL (git blob a98988f08ea1851094cf3cc4dfefe908fdcbbefe, sha256 e2326fae4908868188c391d5a2c4b526828950057c0cf507e4ba8c9506949e11).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ModularCurve

def IsDiamondPullbackModL (K : Type*) [Field K] (M : ℕ) (H : Subgroup (ZMod M)ˣ)
    (ρ : CongruenceSubgroup.Gamma0 M →*
      (qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        qExpFunctionFieldC K (CohCarrier.GammaH M H))) : Prop :=
  ∀ (γ : CongruenceSubgroup.Gamma0 M) (k : ℤ)
    (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg pf₁ pg₁ : PowerSeries ℤ),
    IsIntegralQExp f pf → IsIntegralQExp g pg →
    IsIntegralQExp f₁ pf₁ → IsIntegralQExp g₁ pg₁ →
    (⇑f₁ : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) →
    (⇑g₁ : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) →
    intSeriesC K pg ≠ 0 →
    ∀ x : qExpFunctionFieldC K (CohCarrier.GammaH M H),
      (x : LaurentSeries K) = intSeriesC K pf₁ / intSeriesC K pg₁ →
      ((ρ γ x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) =
        intSeriesC K pf / intSeriesC K pg

variable {K : Type*} [Field K] {M : ℕ} {H : Subgroup (ZMod M)ˣ}
  {ρ : CongruenceSubgroup.Gamma0 M →*
    (qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH M H))}

theorem IsDiamondPullbackModL.coe_apply_eq (hρ : IsDiamondPullbackModL K M H ρ)
    (γ : CongruenceSubgroup.Gamma0 M) {k : ℤ}
    {f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k}
    {pf pg pf₁ pg₁ : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hf₁ : IsIntegralQExp f₁ pf₁) (hg₁ : IsIntegralQExp g₁ pg₁)
    (hfs : (⇑f₁ : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))))
    (hgs : (⇑g₁ : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))))
    (hpg : intSeriesC K pg ≠ 0)
    {x : qExpFunctionFieldC K (CohCarrier.GammaH M H)}
    (hx : (x : LaurentSeries K) = intSeriesC K pf₁ / intSeriesC K pg₁) :
    ((ρ γ x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) =
      intSeriesC K pf / intSeriesC K pg :=
  hρ γ k f g f₁ g₁ pf pg pf₁ pg₁ hf hg hf₁ hg₁ hfs hgs hpg x hx

end ModularCurve

end
