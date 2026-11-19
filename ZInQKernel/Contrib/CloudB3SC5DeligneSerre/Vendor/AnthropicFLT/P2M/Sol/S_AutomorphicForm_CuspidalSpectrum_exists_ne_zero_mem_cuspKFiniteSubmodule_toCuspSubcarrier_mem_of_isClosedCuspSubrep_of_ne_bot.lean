/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_exists_ne_zero_mem_cuspKFiniteSubmodule_toCuspSubcarrier_mem_of_isClosedCuspSubrep_of_ne_bot (git blob c558a45b1bcf010ec0591b8df54096d76c4e6e03, sha256 7a98fd24faa963dc066aaa0efb08e384a8fe3fe6eca9e8c080bf5ad015dedef3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat_isCompactOperator_lift_rightConv_apply_ne_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_mem_cuspMemberSubmodule_toCuspSubcarrier_eq_rightConv_eq_smul
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule_of_isArchBiFinite
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ContinuousLinearMap_orthogonal_iSup_eigenspace_ne_zero_eq_ker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_ne_zero_mem_cuspKFiniteSubmodule_toCuspSubcarrier_mem_of_isClosedCuspSubrep_of_ne_bot

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace NonzeroKfin

theorem isCompactOperator_codRestrict {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    {f : E' →L[ℂ] E} (hf : IsCompactOperator f) (p : Submodule ℂ E) (hp : IsClosed (p : Set E)) (h : ∀ x, f x ∈ p) :
    IsCompactOperator (f.codRestrict p h) := by
  obtain ⟨K, hK, hKn⟩ := hf
  refine ⟨Subtype.val ⁻¹' K, hp.isClosedEmbedding_subtypeVal.isCompact_preimage hK, ?_⟩
  exact hKn

end NonzeroKfin

set_option synthInstance.maxHeartbeats 800000 in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M) (hM0 : M ≠ ⊥) :
    ∃ ψ : AdelicGL2 (𝓞 F) F → ℂ, ψ ≠ 0 ∧
      ψ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ∧
      ∃ h : ψ ∈ cuspMemberSubmodule F Φ₀ ξ, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, h⟩ ∈ M := by
  classical

  obtain ⟨v, hvM, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM0
  obtain ⟨tys, f, hf, hft, hflat, Tc, hcpt, hsymm, hlift, hTv⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isArchBiFinite_flat_isCompactOperator_lift_rightConv_apply_ne_zero
      F hΦ₀ σ ξ hσ v hv0
  have hstab : ∀ x ∈ M, Tc x ∈ M := fun x hx =>
    hM.map_le_of_rightConv f tys hf hft Tc hlift ⟨x, hx, rfl⟩

  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  letI iM1 : NormedAddCommGroup ↥M := Submodule.normedAddCommGroup M
  letI iM2 : InnerProductSpace ℂ ↥M := Submodule.innerProductSpace M
  haveI : CompleteSpace ↥M := hM.isClosed.completeSpace_coe
  obtain ⟨T', hT'def⟩ : ∃ T' : ↥M →L[ℂ] ↥M, T' = (Tc.comp M.subtypeL).codRestrict M (fun x => hstab _ x.2) := ⟨_, rfl⟩
  have hT'apply : ∀ x : ↥M, ((T' x : ↥M) : ↥(cuspSubcarrier F hΦ₀ σ ξ)) = Tc x := fun x => by rw [hT'def]; rfl
  have hT'cpt : IsCompactOperator T' := by
    rw [hT'def]
    exact NonzeroKfin.isCompactOperator_codRestrict (hcpt.comp_clm M.subtypeL) M hM.isClosed _
  have hT'symm : LinearMap.IsSymmetric (𝕜 := ℂ) (E := ↥M) (T' : ↥M →ₗ[ℂ] ↥M) := by
    intro x y
    show ⟪((T' x : ↥M) : ↥(cuspSubcarrier F hΦ₀ σ ξ)), (y : ↥(cuspSubcarrier F hΦ₀ σ ξ))⟫_ℂ =
      ⟪(x : ↥(cuspSubcarrier F hΦ₀ σ ξ)), ((T' y : ↥M) : ↥(cuspSubcarrier F hΦ₀ σ ξ))⟫_ℂ
    rw [hT'apply, hT'apply]
    exact hsymm _ _
  have hker := ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker hT'cpt hT'symm

  have hvker : (⟨v, hvM⟩ : ↥M) ∉ LinearMap.ker (T' : ↥M →ₗ[ℂ] ↥M) := by
    intro hmem
    rw [LinearMap.mem_ker] at hmem
    apply hTv
    have := congrArg (fun z : ↥M => (z : ↥(cuspSubcarrier F hΦ₀ σ ξ))) hmem
    simp only [ContinuousLinearMap.coe_coe, hT'apply] at this
    exact this

  have hex : ∃ μ : ℂ, μ ≠ 0 ∧ Module.End.eigenspace (T' : Module.End ℂ ↥M) μ ≠ ⊥ := by
    by_contra hall
    push Not at hall
    have hbot : (⨆ (μ : ℂ) (_ : μ ≠ 0), Module.End.eigenspace (T' : Module.End ℂ ↥M) μ) = ⊥ := by
      refine iSup_eq_bot.mpr fun μ => iSup_eq_bot.mpr fun hμ => hall μ hμ
    rw [hbot, Submodule.bot_orthogonal_eq_top] at hker
    exact hvker (hker ▸ Submodule.mem_top)
  obtain ⟨μ, hμ, hEμ⟩ := hex
  obtain ⟨w', hw'E, hw'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hEμ
  have hw'eig : T' w' = μ • w' := Module.End.mem_eigenspace_iff.mp hw'E
  set w : ↥(cuspSubcarrier F hΦ₀ σ ξ) := (w' : ↥(cuspSubcarrier F hΦ₀ σ ξ)) with hwdef
  have hwM : w ∈ M := w'.2
  have hw0 : w ≠ 0 := fun h => hw'0 (Subtype.ext h)
  have hweig : Tc w = μ • w := by
    have := congrArg (fun z : ↥M => (z : ↥(cuspSubcarrier F hΦ₀ σ ξ))) hw'eig
    simpa only [hT'apply, Submodule.coe_smul] using this

  obtain ⟨ψ, hψ, hψw, hψeig⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_mem_cuspMemberSubmodule_toCuspSubcarrier_eq_rightConv_eq_smul
      F hΦ₀ σ ξ hσ f hf Tc hlift μ hμ w hweig
  have hconv := AutomorphicForm.CuspidalSpectrum.rightConv_mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule_of_isArchBiFinite
      F c u d₁ d₂ T hc hd₁ ξ hΦ₀ tys f hf hft ψ hψ
  have hψkf : ψ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := by
    have hψeq : ψ = μ⁻¹ • rightConv F ψ f := by
      rw [hψeig, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    rw [hψeq]
    exact Submodule.smul_mem _ _ hconv
  have hψ0 : ψ ≠ 0 := by
    intro h0
    apply hw0
    rw [← hψw]
    have : (⟨ψ, hψ⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = 0 := Subtype.ext h0
    rw [this, map_zero]
  exact ⟨ψ, hψ0, hψkf, hψ, hψw ▸ hwM⟩
