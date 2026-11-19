/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact (git blob 63421d8d6f5bd6a8127d69dab661dde22ea3d9fb, sha256 8f09e797b7af7001299b760168e27721e0a39dd485619e77fb9cd3adb7b7f8ab).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchSpherical
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_apply_mem_cuspSubcarrier_of_isLift_rightConv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_isCuspidalFn_rightConv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_isKfSmooth_rightConv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact

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
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) U f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (h : AdelicGL2 (𝓞 F) F → ℂ) (hh : IsFactorizableTestFn F h) (hbh : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h)
    (hhU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u' ∈ U, h (u' * x) = h x ∧ h (x * u') = h x) :
    ∃ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ), S.comp Tc = Tc.comp S ∧
      ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ), ∃ h' : rightConv F φ h ∈ cuspMemberSubmodule F Φ₀ ξ,
        S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ h, h'⟩ := by
  classical

  obtain ⟨hhc, hhcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F h hh
  obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf

  obtain ⟨Th, -, hTh, -, -⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isLift_rightConv F α β Φ₀ hΦ₀ σ ξ hσ h hhc hhcs
  obtain ⟨Tf, -, hTf, -, -⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isLift_rightConv F α β Φ₀ hΦ₀ σ ξ hσ f hfc hfcs

  have convMem : ∀ (g : AdelicGL2 (𝓞 F) F → ℂ), IsFactorizableTestFn F g →
      ∀ (Tg : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ), IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ g) Tg →
      ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, φ ∈ cuspMemberSubmodule F Φ₀ ξ →
        rightConv F φ g ∈ cuspMemberSubmodule F Φ₀ ξ := by
    intro g hg Tg hTg φ hφ
    have hcont : φ ∈ contMemberSubmodule F Φ₀ ξ := ⟨hφ.1.1.1, hφ.2⟩
    have hmaps := hTg.mapsTo φ hcont
    refine ⟨⟨⟨hmaps.1, ?_⟩, AutomorphicForm.isKfSmooth_rightConv F φ g hg⟩, hmaps.2⟩
    exact AutomorphicForm.isCuspidalFn_rightConv F Φ₀ (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) φ hφ.2 hφ.1.1.2 g hg
  have memh : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ), rightConv F φ h ∈ cuspMemberSubmodule F Φ₀ ξ :=
    fun φ => convMem h hh Th hTh φ φ.2
  have memf : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ), rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ :=
    fun φ => convMem f hf Tf hTf φ φ.2

  have hinv : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Th (v : Carrier F Φ₀ σ) ∈ cuspSubcarrier F hΦ₀ σ ξ := fun v =>
    AutomorphicForm.CuspidalSpectrum.apply_mem_cuspSubcarrier_of_isLift_rightConv F hΦ₀ σ ξ hσ h hh Th hTh v v.2
  let S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    (Th.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL).codRestrict (cuspSubcarrier F hΦ₀ σ ξ) fun v => hinv v
  have S_apply : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), (S v : Carrier F Φ₀ σ) = Th v := fun v => rfl

  have S_lift : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
      S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ h, memh φ⟩ := by
    intro φ
    apply Subtype.ext
    rw [S_apply, toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
    exact hTh.comm φ ⟨φ.2.1.1.1, φ.2.2⟩

  have key : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
      (S.comp Tc) (toCuspSubcarrier F hΦ₀ σ ξ φ) = (Tc.comp S) (toCuspSubcarrier F hΦ₀ σ ξ φ) := by
    intro φ
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hcomm φ (memf φ), S_lift, S_lift,
      hcomm ⟨rightConv F φ h, memh φ⟩ (memf ⟨rightConv F φ h, memh φ⟩)]
    congr 1
    apply Subtype.ext
    exact AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact F
      U hU O hO hUO τ hirr f hsph h hh hbh hhU φ φ.2.2

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
  refine ⟨S, ?_, fun φ => ⟨memh φ, S_lift φ⟩⟩
  exact ContinuousLinearMap.ext_on (hdense.mono Submodule.subset_span) (by rintro _ ⟨φ, rfl⟩; exact key φ)
