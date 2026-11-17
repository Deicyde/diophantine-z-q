/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_orthogonal (git blob de324a449f20da25efcbd3369d6006bb77242e99, sha256 80be4fa52ce0c8fb0a698d4e9cb10b687280b1d652769e40368de419a266160b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_apply_mem_cuspSubcarrier_of_isLift_rightConv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isFactorizableTestFn_flat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_orthogonal

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped ComplexConjugate

noncomputable section

namespace Ws48Perp

section generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem map_orthogonal_le_orthogonal (M : Submodule ℂ E) (S S' : E →L[ℂ] E) (c : ℂ)
    (h : ∀ u v, ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ)
    (hM : M.map (S' : E →ₗ[ℂ] E) ≤ M) :
    Mᗮ.map (S : E →ₗ[ℂ] E) ≤ Mᗮ := by
  intro w hw
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hw
  have hx' : x ∈ Mᗮ := hx
  rw [Submodule.mem_orthogonal] at hx'
  show S x ∈ Mᗮ
  rw [Submodule.mem_orthogonal]
  intro m hm

  have h1 : ⟪S' m, x⟫_ℂ = 0 := hx' (S' m) (hM ⟨m, hm, rfl⟩)
  have h2 : ⟪S x, m⟫_ℂ = 0 := by
    rw [h, ← inner_conj_symm, h1, map_zero, mul_zero]
  rw [← inner_conj_symm, h2, map_zero]

theorem inner_apply_eq_of_dense (D : Set E) (hD : Dense D) (S S' : E →L[ℂ] E) (c : ℂ)
    (h : ∀ u ∈ D, ∀ v ∈ D, ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ) :
    ∀ u v, ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ := by

  have step1 : ∀ v ∈ D, ∀ u, ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ := by
    intro v hv u
    have hc : IsClosed {u : E | ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ} :=
      isClosed_eq (Continuous.inner S.continuous continuous_const)
        (continuous_const.mul (Continuous.inner continuous_id continuous_const))
    have hsub : D ⊆ {u : E | ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ} := fun u hu => h u hu v hv
    have : u ∈ closure D := by rw [hD.closure_eq]; trivial
    exact hc.closure_subset_iff.2 hsub this
  intro u v
  have hc : IsClosed {v : E | ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ} :=
    isClosed_eq (Continuous.inner continuous_const continuous_id)
      (continuous_const.mul (Continuous.inner continuous_const S'.continuous))
  have hsub : D ⊆ {v : E | ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ} := fun v hv => step1 v hv u
  have : v ∈ closure D := by rw [hD.closure_eq]; trivial
  exact hc.closure_subset_iff.2 hsub this

end generic

variable {F : Type} [Field F] [NumberField F]
variable {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}

theorem dense_range_toCuspSubcarrier (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    Dense (Set.range (toCuspSubcarrier F hΦ₀ σ ξ) : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
  set N : Submodule ℂ (Carrier F Φ₀ σ) :=
    Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) with hN
  have hcl : cuspSubcarrier F hΦ₀ σ ξ = N.topologicalClosure := rfl
  have himg : Subtype.val '' Set.range (toCuspSubcarrier F hΦ₀ σ ξ) = (N : Set (Carrier F Φ₀ σ)) := by
    ext w
    constructor
    · rintro ⟨_, ⟨φ, rfl⟩, rfl⟩
      exact ⟨⟨(φ : AdelicGL2 (𝓞 F) F → ℂ), φ.2.1.1.1⟩, φ.2, rfl⟩
    · rintro ⟨ψ, hψ, rfl⟩
      have hψ' : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := hψ
      refine ⟨toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ'⟩, ⟨_, rfl⟩, ?_⟩
      rw [toCuspSubcarrier_apply_coe]
  rw [dense_iff_closure_eq, Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, himg,
    ← Submodule.topologicalClosure_coe, ← hcl, Set.eq_univ_iff_forall]
  exact fun v => v.2

def compress (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ)
    (hT : ∀ v ∈ cuspSubcarrier F hΦ₀ σ ξ, T v ∈ cuspSubcarrier F hΦ₀ σ ξ) :
    ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
  (T.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL).codRestrict (cuspSubcarrier F hΦ₀ σ ξ) fun v => hT v v.2

@[scoped simp] theorem compress_apply_coe (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ)
    (hT : ∀ v ∈ cuspSubcarrier F hΦ₀ σ ξ, T v ∈ cuspSubcarrier F hΦ₀ σ ξ) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) :
    (compress hΦ₀ σ ξ T hT v : Carrier F Φ₀ σ) = T v := rfl

theorem contMember_of_cuspMember {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : φ ∈ cuspMemberSubmodule F Φ₀ ξ) : φ ∈ contMemberSubmodule F Φ₀ ξ :=
  ⟨h.1.1.1, h.2⟩

theorem apply_mem_cuspSubcarrier_of_isLift (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (hop : ∀ φ ∈ cuspMemberSubmodule F Φ₀ ξ, op φ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ) (hT : IsLift F hΦ₀ σ ξ op T) :
    ∀ v ∈ cuspSubcarrier F hΦ₀ σ ξ, T v ∈ cuspSubcarrier F hΦ₀ σ ξ := by
  intro v hv
  set N : Submodule ℂ (Carrier F Φ₀ σ) :=
    Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) with hN
  have hcl : cuspSubcarrier F hΦ₀ σ ξ = N.topologicalClosure := rfl

  have hmaps : Set.MapsTo T (N : Set (Carrier F Φ₀ σ)) (N : Set (Carrier F Φ₀ σ)) := by
    rintro w ⟨ψ, hψ, rfl⟩
    have hψ' : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := hψ
    have hcont : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨ψ.2, hψ'.2⟩
    have hcomm := hT.comm (ψ : AdelicGL2 (𝓞 F) F → ℂ) hcont
    have hcusp : op (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := hop _ hψ'
    have heta : (⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), hcont.1⟩ : ↥(memberSubmodule F Φ₀ ξ)) = ψ := Subtype.coe_eta ψ hcont.1
    rw [heta] at hcomm
    refine ⟨⟨op (ψ : AdelicGL2 (𝓞 F) F → ℂ), hcusp.1.1.1⟩, hcusp, ?_⟩
    exact hcomm.symm
  have hv' : v ∈ closure (N : Set (Carrier F Φ₀ σ)) := by
    rw [← Submodule.topologicalClosure_coe, ← hcl]; exact hv
  have := map_mem_closure T.continuous hv' hmaps
  rw [← Submodule.topologicalClosure_coe, ← hcl] at this
  exact this

theorem isCuspLift_compress (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ) (hT : IsLift F hΦ₀ σ ξ op T)
    (hT' : ∀ v ∈ cuspSubcarrier F hΦ₀ σ ξ, T v ∈ cuspSubcarrier F hΦ₀ σ ξ) :
    IsCuspLift F hΦ₀ σ ξ op (compress hΦ₀ σ ξ T hT') := by
  intro φ h
  apply Subtype.ext
  rw [compress_apply_coe, toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
  exact hT.comm (φ : AdelicGL2 (𝓞 F) F → ℂ) (contMember_of_cuspMember φ.2)

theorem map_orthogonal_le_of_rightTranslate (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ) (y : AdelicGL2 (𝓞 F) F)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hM : ∀ S' : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F y⁻¹) S' →
        M.map (S' : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M)
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hS : IsCuspLift F hΦ₀ σ ξ (rightTranslate F y) S) :
    Mᗮ.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ Mᗮ := by
  obtain ⟨T, T', hT, hT', hadj, -⟩ := exists_isLift_rightTranslate F α β Φ₀ hΦ₀ σ ξ hσ y
  have hmem : ∀ z, ∀ φ ∈ cuspMemberSubmodule F Φ₀ ξ, rightTranslate F z φ ∈ cuspMemberSubmodule F Φ₀ ξ :=
    fun z φ hφ => rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ z φ hφ
  have hT'sub := apply_mem_cuspSubcarrier_of_isLift hΦ₀ σ ξ _ (hmem y⁻¹) T' hT'
  set S' := compress hΦ₀ σ ξ T' hT'sub with hS'def
  have hS'lift : IsCuspLift F hΦ₀ σ ξ (rightTranslate F y⁻¹) S' := isCuspLift_compress hΦ₀ σ ξ _ T' hT' hT'sub
  set c : ℂ := ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) with hc

  have hdense : ∀ u ∈ Set.range (toCuspSubcarrier F hΦ₀ σ ξ), ∀ v ∈ Set.range (toCuspSubcarrier F hΦ₀ σ ξ),
      ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ := by
    rintro _ ⟨φ, rfl⟩ _ ⟨ψ, rfl⟩
    have e1 : (toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F y φ, hmem y φ φ.2⟩ : Carrier F Φ₀ σ)
        = T (toCuspSubcarrier F hΦ₀ σ ξ φ : Carrier F Φ₀ σ) := by
      rw [toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
      exact (hT.comm (φ : AdelicGL2 (𝓞 F) F → ℂ) (contMember_of_cuspMember φ.2)).symm
    have e2 : (S' (toCuspSubcarrier F hΦ₀ σ ξ ψ) : Carrier F Φ₀ σ)
        = T' (toCuspSubcarrier F hΦ₀ σ ξ ψ : Carrier F Φ₀ σ) := rfl
    rw [hS φ (hmem y φ φ.2), Submodule.coe_inner, Submodule.coe_inner, e1, e2,
      ← ContinuousLinearMap.adjoint_inner_right, hadj, ContinuousLinearMap.smul_apply, inner_smul_right]
  have hall := inner_apply_eq_of_dense _ (dense_range_toCuspSubcarrier hΦ₀ σ ξ) S S' c hdense
  exact map_orthogonal_le_orthogonal M S S' c hall (hM S' hS'lift)

theorem map_orthogonal_le_of_rightConv (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F) (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M)
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hS : IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) S) :
    Mᗮ.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ Mᗮ := by
  obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  obtain ⟨T, T', hT, hT', hadj⟩ := exists_isLift_rightConv F α β Φ₀ hΦ₀ σ ξ hσ f hfc hfcs
  have hflat : IsFactorizableTestFn F (flat F σ f) := isFactorizableTestFn_flat F σ f hf
  obtain ⟨tys', hft'⟩ := exists_isArchBiFinite_flat F σ tys f hf hft
  have hT'sub : ∀ v ∈ cuspSubcarrier F hΦ₀ σ ξ, T' v ∈ cuspSubcarrier F hΦ₀ σ ξ :=
    fun v hv => apply_mem_cuspSubcarrier_of_isLift_rightConv F hΦ₀ σ ξ hσ (flat F σ f) hflat T' hT' v hv
  set S' := compress hΦ₀ σ ξ T' hT'sub with hS'def
  have hS'lift : IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ (flat F σ f)) S' :=
    isCuspLift_compress hΦ₀ σ ξ _ T' hT' hT'sub
  have hdense : ∀ u ∈ Set.range (toCuspSubcarrier F hΦ₀ σ ξ), ∀ v ∈ Set.range (toCuspSubcarrier F hΦ₀ σ ξ),
      ⟪S u, v⟫_ℂ = (1 : ℂ) * ⟪u, S' v⟫_ℂ := by
    rintro _ ⟨φ, rfl⟩ _ ⟨ψ, rfl⟩
    have hm : rightConv F (φ : AdelicGL2 (𝓞 F) F → ℂ) f ∈ cuspMemberSubmodule F Φ₀ ξ :=
      rightConv_mem_cuspMemberSubmodule F hΦ₀ ξ f hf φ φ.2
    have e1 : (toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F (φ : AdelicGL2 (𝓞 F) F → ℂ) f, hm⟩ : Carrier F Φ₀ σ)
        = T (toCuspSubcarrier F hΦ₀ σ ξ φ : Carrier F Φ₀ σ) := by
      rw [toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
      exact (hT.comm (φ : AdelicGL2 (𝓞 F) F → ℂ) (contMember_of_cuspMember φ.2)).symm
    have e2 : (S' (toCuspSubcarrier F hΦ₀ σ ξ ψ) : Carrier F Φ₀ σ)
        = T' (toCuspSubcarrier F hΦ₀ σ ξ ψ : Carrier F Φ₀ σ) := rfl
    rw [hS φ hm, Submodule.coe_inner, Submodule.coe_inner, e1, e2,
      ← ContinuousLinearMap.adjoint_inner_right, hadj, one_mul]
  have hall := inner_apply_eq_of_dense _ (dense_range_toCuspSubcarrier hΦ₀ σ ξ) S S' 1 hdense
  exact map_orthogonal_le_orthogonal M S S' 1 hall (hM.map_le_of_rightConv (flat F σ f) tys' hflat hft' S' hS'lift)

end Ws48Perp
open scoped _root_.P2MW.S_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_orthogonal.Ws48Perp

end
open scoped _root_.P2MW.S_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_orthogonal.Ws48Perp

open Ws48Perp in
theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M) :
    IsClosedCuspSubrep F hΦ₀ σ ξ Mᗮ := by
  refine ⟨Submodule.isClosed_orthogonal M, fun g hg S hS => ?_, fun w k S hS => ?_, fun f tys hf hft S hS => ?_⟩
  · exact map_orthogonal_le_of_rightTranslate hΦ₀ σ ξ hσ g M
      (fun S' h' => hM.map_le_of_rightTranslate_fin g⁻¹ (inv_mem hg) S' h') S hS
  · refine map_orthogonal_le_of_rightTranslate hΦ₀ σ ξ hσ (rowIsometryInclAt₀ F w k) M (fun S' h' => ?_) S hS
    rw [← map_inv] at h'
    exact hM.map_le_of_rightTranslate_arch w k⁻¹ S' h'
  · exact map_orthogonal_le_of_rightConv hΦ₀ σ ξ hσ f tys hf hft M hM S hS
