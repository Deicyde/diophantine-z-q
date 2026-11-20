/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq (git blob 77a7ba254d553fb2904a5dc1e6acf11ea8e81de8, sha256 86842e80b28a5f65321ecba5e76cda4529149de9df91028c4897d2dd24d6e022).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_HeckeCharacter_FiniteOrder
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain

theorem HeckeCharacter.eq_of_forall_apply_localUnit_uniformizerUnit_eq
    (K : Type*) [Field K] [NumberField K]
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχ₁ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ₁)
    (hχ₂ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ₂)
    (hc₁ : Continuous χ₁)
    (hc₂ : Continuous χ₂)
    (𝔣₁ 𝔣₂ : Ideal (𝓞 K))
    (hmod₁ : HeckeCharacter.AdmitsModulus K χ₁ 𝔣₁)
    (hmod₂ : HeckeCharacter.AdmitsModulus K χ₂ 𝔣₂)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S,
      χ₁ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
          (NumberField.AdelicLevel.localUnit (𝓞 K) K v (NumberField.AdelicLevel.uniformizerUnit K v)))
        = χ₂ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
          (NumberField.AdelicLevel.localUnit (𝓞 K) K v (NumberField.AdelicLevel.uniformizerUnit K v)))) :
    χ₁ = χ₂ := by
  revert K χ₁ χ₂ hχ₁ hχ₂ hc₁ hc₂ 𝔣₁ 𝔣₂ hmod₁ hmod₂ S hS
  exact @_root_.P2MW.S_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq.solution
