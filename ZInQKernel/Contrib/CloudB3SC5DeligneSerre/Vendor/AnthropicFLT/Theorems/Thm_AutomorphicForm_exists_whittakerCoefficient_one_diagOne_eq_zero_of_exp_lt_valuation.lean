/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation (git blob a2134b4931c1b7302a4e72689364ffa58b2ca1eb, sha256 d8d0cbe647d1f123cc6e7197417b64cf9fa91bc2b44fadf14c59de8c8aba19b8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_M4aHerbrand_IdeleClassVocab
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm

theorem AutomorphicForm.exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g)
    (hsm : IsKfSmooth F φ) :
    ∃ c : HeightOneSpectrum (𝓞 F) → ℤ,
      (∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, c v = 0) ∧
      ∀ b : (AdeleRing (𝓞 F) F)ˣ,
        (∃ v : HeightOneSpectrum (𝓞 F),
          WithZero.exp (c v) < Valued.v (((b : AdeleRing (𝓞 F) F).2) v)) →
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 (diagOne b) = 0 := by
  revert F D U gen ψ hψ φ hleft hsm
  exact @_root_.P2MW.S_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation.solution
