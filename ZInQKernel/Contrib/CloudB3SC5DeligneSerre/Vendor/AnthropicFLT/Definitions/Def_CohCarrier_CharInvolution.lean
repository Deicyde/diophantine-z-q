/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_CohCarrier_CharInvolution (git blob f6c22aefd38d2d594fba3c6d584456d6cb50907a, sha256 0264f8623f76017e355ede227e62d232f0ece8dc7f2d4c8a98234ca5810cdd4c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodHomPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace CohCarrier

section Level

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem jConjSL_mem_GammaH {A : SL(2, ℤ)} (hA : A ∈ GammaH M H) :
    ModularCurve.Period.jConjSL A ∈ GammaH M H := by
  obtain ⟨hA0, hAH⟩ := mem_GammaH_iff.mp hA
  rw [mem_GammaH_iff]
  refine ⟨ModularCurve.Period.jConjSL_mem_Gamma0 hA0, ?_⟩
  exact hAH

def jConjGammaH : ↥(GammaH M H) →* ↥(GammaH M H) where
  toFun γ := ⟨ModularCurve.Period.jConjSL (γ : SL(2, ℤ)), jConjSL_mem_GammaH M H γ.2⟩
  map_one' := Subtype.ext (by
    show ModularCurve.Period.jConjSL ((1 : ↥(GammaH M H)) : SL(2, ℤ)) = 1
    rw [OneMemClass.coe_one, map_one])
  map_mul' γ δ := Subtype.ext (by
    show ModularCurve.Period.jConjSL ((γ * δ : ↥(GammaH M H)) : SL(2, ℤ)) =
      ModularCurve.Period.jConjSL (γ : SL(2, ℤ)) * ModularCurve.Period.jConjSL (δ : SL(2, ℤ))
    rw [Subgroup.coe_mul, map_mul])

@[simp] theorem coe_jConjGammaH (γ : ↥(GammaH M H)) :
    ((jConjGammaH M H γ : ↥(GammaH M H)) : SL(2, ℤ)) = ModularCurve.Period.jConjSL (γ : SL(2, ℤ)) :=
  rfl

@[simp] theorem jConjGammaH_jConjGammaH (γ : ↥(GammaH M H)) :
    jConjGammaH M H (jConjGammaH M H γ) = γ :=
  Subtype.ext (ModularCurve.Period.jConjSL_jConjSL _)

variable (A : Type*) [AddCommGroup A]

def charInvolution (R : Type*) [Semiring R] [Module R A] : H1 M H A →ₗ[R] H1 M H A where
  toFun φ := φ.comp (MonoidHom.toAdditive (jConjGammaH M H))
  map_add' := by intro φ ψ; ext; rfl
  map_smul' := by intro r φ; ext; rfl

@[simp] theorem charInvolution_apply (R : Type*) [Semiring R] [Module R A] (φ : H1 M H A)
    (γ : Additive ↥(GammaH M H)) :
    charInvolution M H A R φ γ = φ (Additive.ofMul (jConjGammaH M H (Additive.toMul γ))) := rfl

theorem charInvolution_charInvolution (R : Type*) [Semiring R] [Module R A] (φ : H1 M H A) :
    charInvolution M H A R (charInvolution M H A R φ) = φ := by
  ext γ
  show φ (Additive.ofMul (jConjGammaH M H (Additive.toMul
    (Additive.ofMul (jConjGammaH M H (Additive.toMul γ)))))) = φ γ
  rw [toMul_ofMul, jConjGammaH_jConjGammaH, ofMul_toMul]

theorem charInvolution_comp_charInvolution (R : Type*) [Semiring R] [Module R A] :
    charInvolution M H A R ∘ₗ charInvolution M H A R = LinearMap.id :=
  LinearMap.ext (charInvolution_charInvolution M H A R)

end Level

end CohCarrier
