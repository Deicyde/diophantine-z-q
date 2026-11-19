/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_dirichletIdeleChar_mul_modulus_det_gen (git blob 39c2b771a3587e236f13dd49ae352c8527c32490, sha256 54a307c41e3d05a15594afd6d6e3184f0b0455df03e403abe7b8f6e286f9c793).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_DirichletCharacter_DirichletIdeleChar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_dirichletIdeleChar_mul_modulus_det_gen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField AutomorphicForm
open IsDedekindDomain

theorem LanglandsTunnell.dirichletIdeleChar_mul_modulus_det_gen
    {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℂ n)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ)
        = χ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹ := by
  revert n χ S hS
  exact @_root_.P2MW.S_LanglandsTunnell_dirichletIdeleChar_mul_modulus_det_gen.solution
