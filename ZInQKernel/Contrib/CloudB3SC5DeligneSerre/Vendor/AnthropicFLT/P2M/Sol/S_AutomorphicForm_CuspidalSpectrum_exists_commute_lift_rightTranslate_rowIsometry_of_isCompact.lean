/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_rightTranslate_rowIsometry_of_isCompact (git blob 980f274a83c69ebedb1af479b57abad9d295b35d, sha256 60a74330095f9fbcd1639da08f6f6dc1b1a7d1a3965b5b9e0ce48bcec4dc3f10).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchSpherical
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_rightTranslate_rightConv_of_isLevelSphericalOfType
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_isCuspidalFn_rightConv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_isKfSmooth_rightConv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_rightTranslate_rowIsometry_of_isCompact

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (F : Type) [Field F] [NumberField F]
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F tys U f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    ∃ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ), S.comp Tc = Tc.comp S ∧
      ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ), ∃ h : rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ cuspMemberSubmodule F Φ₀ ξ,
        S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F (rowIsometryInclAt₀ F w k) φ, h⟩ := by
  classical
  obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf

  obtain ⟨Tk, -, hTk, -, -, -⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isLift_rightTranslate F α β Φ₀ hΦ₀ σ ξ hσ (rowIsometryInclAt₀ F w k)
  obtain ⟨Tf, -, hTf, -, -⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isLift_rightConv F α β Φ₀ hΦ₀ σ ξ hσ f hfc hfcs

  have memk : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
      rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ cuspMemberSubmodule F Φ₀ ξ := fun φ =>
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ (rowIsometryInclAt₀ F w k) φ φ.2
  have memf : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ), rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ := by
    intro φ
    have hcont : (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨φ.2.1.1.1, φ.2.2⟩
    have hmaps := hTf.mapsTo φ hcont
    refine ⟨⟨⟨hmaps.1, ?_⟩, AutomorphicForm.isKfSmooth_rightConv F φ f hf⟩, hmaps.2⟩
    exact AutomorphicForm.isCuspidalFn_rightConv F Φ₀ (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) φ φ.2.2 φ.2.1.1.2 f hf

  have hM : ∀ x ∈ (Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) : Set (Carrier F Φ₀ σ)),
      Tk x ∈ (Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) : Set (Carrier F Φ₀ σ)) := by
    rintro _ ⟨ψ, hψ, rfl⟩
    refine ⟨⟨rightTranslate F (rowIsometryInclAt₀ F w k) ψ, (memk ⟨ψ, hψ⟩).1.1.1⟩, memk ⟨ψ, hψ⟩, ?_⟩
    exact (hTk.comm ψ ⟨ψ.2, hψ.2⟩).symm
  have hinv : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Tk (v : Carrier F Φ₀ σ) ∈ cuspSubcarrier F hΦ₀ σ ξ := by
    intro v
    have hv : (v : Carrier F Φ₀ σ) ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) : Set (Carrier F Φ₀ σ))) := by
      rw [← Submodule.topologicalClosure_coe]
      exact v.2
    have h1 := image_closure_subset_closure_image Tk.continuous ⟨(v : Carrier F Φ₀ σ), hv, rfl⟩
    have h2 := closure_mono (by rintro _ ⟨x, hx, rfl⟩; exact hM x hx) h1
    rw [← Submodule.topologicalClosure_coe] at h2
    exact h2
  let S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    (Tk.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL).codRestrict (cuspSubcarrier F hΦ₀ σ ξ) fun v => hinv v
  have S_apply : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), (S v : Carrier F Φ₀ σ) = Tk v := fun v => rfl

  have S_lift : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
      S (toCuspSubcarrier F hΦ₀ σ ξ φ) =
        toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F (rowIsometryInclAt₀ F w k) φ, memk φ⟩ := by
    intro φ
    apply Subtype.ext
    rw [S_apply, toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
    exact hTk.comm φ ⟨φ.2.1.1.1, φ.2.2⟩

  have key : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
      (S.comp Tc) (toCuspSubcarrier F hΦ₀ σ ξ φ) = (Tc.comp S) (toCuspSubcarrier F hΦ₀ σ ξ φ) := by
    intro φ
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hcomm φ (memf φ), S_lift, S_lift,
      hcomm ⟨rightTranslate F (rowIsometryInclAt₀ F w k) φ, memk φ⟩
        (memf ⟨rightTranslate F (rowIsometryInclAt₀ F w k) φ, memk φ⟩)]
    congr 1
    apply Subtype.ext
    exact AutomorphicForm.rightTranslate_rightConv_of_isLevelSphericalOfType F tys _ f hsph w k φ

  have hdense : Dense (Set.range (toCuspSubcarrier F hΦ₀ σ ξ)) := by
    rw [Subtype.dense_iff]
    intro v hv
    have hv' : v ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) :
          Set (Carrier F Φ₀ σ))) := by
      rw [← Submodule.topologicalClosure_coe]
      exact hv
    refine closure_mono ?_ hv'
    rintro _ ⟨ψ, hψ, rfl⟩
    exact ⟨toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩, ⟨_, rfl⟩, rfl⟩
  refine ⟨S, ?_, fun φ => ⟨memk φ, S_lift φ⟩⟩
  exact ContinuousLinearMap.ext_on (hdense.mono Submodule.subset_span) (by rintro _ ⟨φ, rfl⟩; exact key φ)
