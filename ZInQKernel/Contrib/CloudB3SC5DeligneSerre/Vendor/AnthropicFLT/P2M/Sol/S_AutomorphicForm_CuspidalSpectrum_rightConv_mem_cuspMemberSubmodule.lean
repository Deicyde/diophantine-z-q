/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule (git blob be3524e09cfc61fbc2209ca3d4b3e7195f712fdb, sha256 8e6503100c1e484fd7025357b5d5898a219327a2e6ec7f9628bf5deb1c801617).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_isCuspidalFn_rightConv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_isKfSmooth_rightConv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ) :
    rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  obtain ⟨⟨⟨hmemb, hcusp⟩, hKf⟩, hcont⟩ := hφ
  obtain ⟨hLs, hL2⟩ := (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ φ).mp hmemb
  obtain ⟨hleft, hcentral⟩ := hLs
  obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  have hRC : ∀ g, rightConv F φ f g = ∫ x, φ (g * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := fun g => rfl

  have hcont' : Continuous (rightConv F φ f) :=
    AutomorphicForm.continuous_rightConv_of_continuous_of_hasCompactSupport F φ hcont f hfc hfcs

  have hLs' : IsLsXiFunction (𝓞 F) F ⊤ ξ (rightConv F φ f) := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · rw [hRC, hRC]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show φ (globalPoints (𝓞 F) F γ * g * x) * f x = φ (g * x) * f x
      rw [mul_assoc, hleft]
    · rw [hRC, hRC, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g * x) * f x = ((ξ z : ℂˣ) : ℂ) * (φ (g * x) * f x)
      rw [mul_assoc, hcentral, mul_assoc]

  have hL2' : MemLp (rightConv F φ f) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) := by
    by_cases h0 : φ = 0
    · subst h0
      have : rightConv F (0 : AdelicGL2 (𝓞 F) F → ℂ) f = 0 := by
        funext g
        rw [hRC]
        simp
      rw [this]
      exact MemLp.zero
    · obtain ⟨σ, hσ⟩ :=
        AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous F Φ₀ ξ φ hmemb hcont h0
      exact (AutomorphicForm.adjoint_rightConv_weightedPairing_of_isLsXiFunction F α β hΦ₀.pos Φ₀
        hΦ₀.subset hΦ₀.isFundamentalDomain ξ σ hσ φ φ ⟨hleft, hcentral⟩ ⟨hleft, hcentral⟩ hcont hcont hL2 hL2
        f hfc hfcs).1
  have hmemb' : IsAutomorphicFnAt F (fdPins F Φ₀) ξ (rightConv F φ f) :=
    (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ _).mpr ⟨hLs', hL2'⟩

  have hcusp' := AutomorphicForm.isCuspidalFn_rightConv F Φ₀ (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) φ hcont hcusp f hf
  have hKf' := AutomorphicForm.isKfSmooth_rightConv F φ f hf
  exact ⟨⟨⟨hmemb', hcusp'⟩, hKf'⟩, hcont'⟩
