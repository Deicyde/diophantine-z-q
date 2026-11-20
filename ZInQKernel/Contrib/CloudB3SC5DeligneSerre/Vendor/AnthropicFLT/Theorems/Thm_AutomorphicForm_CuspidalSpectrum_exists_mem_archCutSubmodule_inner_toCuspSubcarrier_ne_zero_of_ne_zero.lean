/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero (git blob e9cfa04344619b6d7e4d165175001e32032782b6, sha256 fa8676ed60803d478315d0cceb2ec454592373b8e47cb81f9dd608dfd62692b0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hv : v ≠ 0) :
    ∃ (tys : AutomorphicForm.ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F)),
      U ≤ finiteAdelicGL2Subgroup F ∧
      IsOpen ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) ∧
      IsCompact ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) ∧
      (AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) ⊆ (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) ∧
      ∃ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ cuspMemberSubmodule F Φ₀ ξ),
        ψ ∈ archCutSubmodule F tys ∧ (∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, ψ (g * u) = ψ g) ∧
        ⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩⟫_ℂ ≠ 0 := by
  revert F α β Φ₀ hΦ₀ σ ξ hσ v hv
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero.solution
