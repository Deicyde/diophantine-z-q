/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero (git blob e94604bc38db7fd8ae616075615b15091b11bc9f, sha256 d82ad663ea2d3512894389db9dfb07c0f7b58b41e1e41ce42321a04fc9fdf1ef).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open NumberField

theorem AutomorphicForm.exists_whittakerCoefficient_one_ne_zero
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hcusp : whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ 0 g₀
      = 0)
    (hcont : Continuous (fun x => φ (unipotentGL2 x * g₀)))
    (hsum : Summable (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ α g₀))
    (hg₀ : φ g₀ ≠ 0) :
    ∃ g : AdelicGL2 (𝓞 F) F,
      whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ 1 g ≠ 0 := by
  revert F D U gen ψ hψ φ hleft g₀ hcusp hcont hsum hg₀
  exact @_root_.P2MW.S_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero.solution
