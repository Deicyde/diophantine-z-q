/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct (git blob bcaad63f43ecbb23d8cbb095154827a7e2d64bd6, sha256 b3263b213369769940ffff02272983f9ff5ddd295fba2ce409297cdd001cc4cf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain

theorem NumberField.TateGlobal.exists_meromorphicOn_eq_partialEulerProduct (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχF : IsIdeleClassChar (𝓞 F) F χ) :
    ∃ L : ℂ → ℂ, MeromorphicOn L Set.univ ∧
      ∀ s : ℂ, 1 < s.re →
        L s = (∏' v : {v // v ∉ S},
          (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  revert F S ϖ hϖ χ hχc hχu hχF
  exact @_root_.P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.solution
