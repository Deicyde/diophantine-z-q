/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_modularPolynomialFamily (git blob a93db85830601fe6b52b70a12be18024126cdd6e, sha256 bd71db2e461899ab5e3201cb04ab60ccd4f5a388cca7a656476a07819dc5d596).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_PhiGen_exists_phiGenDescends
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_PhiGen_PhiGenDescends_intCoeffs
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq
import Mathlib.NumberTheory.Cyclotomic.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_modularPolynomialFamily

noncomputable section

namespace ModularCurve
export _root_.ModularCurve (jq ModularPolynomialData EvalSymm ModularPolynomialFamily PhiGen.IntCoeffs PhiGen.exists_phiGenDescends PhiGen.mem_adjoin_jq_of_phiGenDescends PhiGen.exists_modularPolynomialData_coeff_eq PhiGen.evalSymm_of_coeff_evalAtJ_eq)
open _root_.ModularCurve

theorem exists_modularPolynomialData_evalSymm' (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ∃ data : ModularPolynomialData ℓ, EvalSymm data.Φ := by

  haveI : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  haveI hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  haveI : FiniteDimensional ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} ℚ (CyclotomicField ℓ ℚ)
  haveI : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]; exact hz
  have hζ1 : hzu.unit ^ ℓ = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]

  obtain ⟨c, hc⟩ := PhiGen.exists_phiGenDescends ℓ hzu.unit hζ

  have hint : ∀ k, PhiGen.IntCoeffs (c k) := fun k => hc.intCoeffs hζ1 k
  have hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq} :=
    fun k => PhiGen.mem_adjoin_jq_of_phiGenDescends ℓ hzu.unit hζ c hc k

  obtain ⟨data, hcoeff⟩ := PhiGen.exists_modularPolynomialData_coeff_eq hc hint hmem
  exact ⟨data, PhiGen.evalSymm_of_coeff_evalAtJ_eq hζ hc data hcoeff⟩

theorem modularPolynomialFamily' : ModularPolynomialFamily :=
  fun ℓ _ hℓ => by
    haveI : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
    exact exists_modularPolynomialData_evalSymm' ℓ

end ModularCurve

end

theorem solution : ModularCurve.ModularPolynomialFamily := ModularCurve.modularPolynomialFamily'

#print axioms solution
