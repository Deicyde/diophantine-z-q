import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_PeriodPair_discriminant_ne_zero
import ZInQKernel.Contrib.OneProof.CMBranch.Arith

/-! # cmheight62-p1, step 4 (second bullet): `Δ(ℤ + τℤ) = (2π)¹² η(τ)²⁴`

The discriminant of the Weierstrass curve `y² = 4x³ − g₂x − g₃` of the lattice `ℤτ + ℤ`, in the
normalization `PeriodPair.weierstrassCurve` (`a₄ = −g₂/4`, `a₆ = −g₃/4`, so `Δ = g₂³ − 27g₃²`), is
`discAn τ`. Inputs: the vendored `kw_discriminant_ofTau_eq`
(`g₂³ − 27g₃² = (64π¹²/27)(E₄³ − E₆²)`), Mathlib's `discriminant_eq_E₄_cube_sub_E₆_sq`
(`Δ = (E₄³ − E₆²)/1728`) and `ModularForm.discriminant z = η(z)²⁴`; `(64/27)·1728 = 4096 = 2¹²`. -/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62

open scoped UpperHalfPlane

/-- **Step 4, second bullet.** `Δ(ℤτ + ℤ) = discAn τ = (2π)¹² η(τ)²⁴`. -/
theorem weierstrassCurve_ofTau_Δ (τ : ℍ) :
    (PeriodPair.ofTau τ).weierstrassCurve.Δ = CMBranch.discAn (τ : ℂ) := by
  rw [PeriodPair.weierstrassCurve_Δ,
    P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair.kw_discriminant_ofTau_eq]
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  have h2 : ModularForm.discriminant τ = ModularForm.eta (τ : ℂ) ^ 24 := rfl
  unfold CMBranch.discAn
  rw [← h2, h]
  push_cast
  ring

end ZInQ.Contrib.CMHeight62
