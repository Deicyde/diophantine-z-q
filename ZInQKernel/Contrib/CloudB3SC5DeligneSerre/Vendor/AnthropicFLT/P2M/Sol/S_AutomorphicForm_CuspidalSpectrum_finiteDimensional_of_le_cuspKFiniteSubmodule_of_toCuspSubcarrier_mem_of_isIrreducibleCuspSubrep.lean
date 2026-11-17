/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep (git blob 353ec25095c9cf7f4b2f2dee1a63dae86721bf27, sha256 9520fd3bba8285a08bc15541fffae78df5d4135a500d5bf885075104b751c199).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchSpherical
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_rightConv_injOn_of_finiteDimensional_of_forall_apply_mul_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isCompactOperator_isSymmetric_lift_rightConv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ContinuousLinearMap_le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_cuspKFiniteSubmodule_le_cuspMemberSubmodule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isCuspSubrep_cuspKFiniteSubmodule_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace IrredAdmProof

variable {F : Type} [Field F] [NumberField F]

private theorem finiteDimensional_single {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (X : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hXc : X ≤ cuspMemberSubmodule F Φ₀ ξ)
    (hXM : ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ X), toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hXc hψ⟩ ∈ M)
    (hXU : ∀ ψ ∈ X, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, ψ (g * k) = ψ g)
    (hXt : X ≤ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F)) :
    FiniteDimensional ℂ ↥X := by
  classical
  by_cases hX0 : X = ⊥
  · rw [hX0]; infer_instance
  obtain ⟨x, hxX, hx0⟩ := (Submodule.ne_bot_iff X).mp hX0
  have hxc : x ∈ cuspMemberSubmodule F Φ₀ ξ := hXc hxX

  set L : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ {x} with hL
  haveI hLfd : FiniteDimensional ℂ ↥L := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton x)
  have hLc : ∀ y ∈ L, Continuous y := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact hxc.2.const_smul a
  have hLU : ∀ y ∈ L, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, y (g * k) = y g := by
    intro y hy g k hk
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [Pi.smul_apply, hXU x hxX g k hk]
  have hLt : L ≤ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (hXt hxX))
  obtain ⟨f, hf, hsph, hflat, hinj⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional_of_forall_apply_mul_eq
      F U hU O hO hUO (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) σ L hLfd hLc hLU hLt
  have hxf : rightConv F x f ≠ 0 := fun h => hx0 (hinj x (Submodule.subset_span rfl) h)
  have hxfm : rightConv F x f ∈ cuspMemberSubmodule F Φ₀ ξ :=
    AutomorphicForm.CuspidalSpectrum.rightConv_mem_cuspMemberSubmodule F hΦ₀ ξ f hf x hxc

  obtain ⟨Tc, hTc, hsymm, hcomm⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isCompactOperator_isSymmetric_lift_rightConv F hΦ₀ σ ξ hσ f hf hflat

  have hdich := AutomorphicForm.CuspidalSpectrum.map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep
    F hΦ₀ σ ξ hσ M hM U hU O hO hUO τ hirr f hf hsph hflat Tc hsymm hcomm X hXc hXM hXU hXt

  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    have hcl : IsClosed ((cuspSubcarrier F hΦ₀ σ ξ : Submodule ℂ (Carrier F Φ₀ σ)) : Set (Carrier F Φ₀ σ)) := by
      unfold cuspSubcarrier; exact Submodule.isClosed_topologicalClosure _
    exact hcl.completeSpace_coe
  set φ : ↥X →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) := (toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hXc) with hφ
  rcases ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal (𝕜 := ℂ) hTc hsymm
      (Submodule.map φ ⊤) hdich with hker | hfd
  ·
    exfalso
    have hxim : φ ⟨x, hxX⟩ ∈ Submodule.map φ ⊤ := Submodule.mem_map_of_mem trivial
    have h1 : Tc (φ ⟨x, hxX⟩) = 0 := LinearMap.mem_ker.mp (hker hxim)
    have h2 : φ ⟨x, hxX⟩ = toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hxc⟩ := rfl
    rw [h2, hcomm ⟨x, hxc⟩ hxfm] at h1
    have h3 : toCarrier F hΦ₀ σ ξ ⟨rightConv F x f, hxfm.1.1.1⟩ = 0 := by
      have := congrArg (fun v : ↥(cuspSubcarrier F hΦ₀ σ ξ) => (v : Carrier F Φ₀ σ)) h1
      simpa [toCuspSubcarrier_apply_coe] using this
    exact hxf (AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ (rightConv F x f)
      ⟨hxfm.1.1.1, hxfm.2⟩ h3)
  ·
    have hφinj : Function.Injective φ := by
      intro a b hab
      have h0 : φ (a - b) = 0 := by rw [map_sub, hab, sub_self]
      have hmem : ((a - b : ↥X) : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := hXc (a - b).2
      have h3 : toCarrier F hΦ₀ σ ξ ⟨((a - b : ↥X) : AdelicGL2 (𝓞 F) F → ℂ), hmem.1.1.1⟩ = 0 := by
        have := congrArg (fun v : ↥(cuspSubcarrier F hΦ₀ σ ξ) => (v : Carrier F Φ₀ σ)) h0
        simp [toCuspSubcarrier_apply_coe] at this
        exact this
      have := AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ _ ⟨hmem.1.1.1, hmem.2⟩ h3
      exact sub_eq_zero.mp (Subtype.ext this)
    haveI : FiniteDimensional ℂ ↥(LinearMap.range φ) := by rw [LinearMap.range_eq_map]; exact hfd
    exact Module.Finite.equiv (LinearEquiv.ofInjective φ hφinj).symm -- [port]

end IrredAdmProof

open IrredAdmProof in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : ArchTypeFamily F)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hYK : Y ≤ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ)
    (hYM : ∀ ψ ∈ Y, ∃ h : ψ ∈ cuspMemberSubmodule F Φ₀ ξ, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, h⟩ ∈ M)
    (hYU : ∀ ψ ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, ψ (g * k) = ψ g)
    (hYt : Y ≤ archCutSubmodule F tys) :
    FiniteDimensional ℂ ↥Y := by
  classical

  have hV := AutomorphicForm.CuspidalSpectrum.isCuspSubrep_cuspKFiniteSubmodule_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
    F c u d₁ d₂ T hc hd₁ hd hcov ξ σ hσ hΦ₀ M hM.1
  set VM : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
    cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ⊓
      Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) M) with hVM
  have hmem := AutomorphicForm.CuspidalSpectrum.cuspKFiniteSubmodule_le_cuspMemberSubmodule F c u d₁ d₂ T hc hd₁ hd hcov ξ hΦ₀

  obtain ⟨n, τs, hirr, hsplit⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep
      F c u d₁ d₂ T ξ U hU O hO hUO tys VM hV

  have hYle : Y ≤ VM ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓ archCutSubmodule F tys := by
    intro ψ hψ
    obtain ⟨h, hMψ⟩ := hYM ψ hψ
    refine ⟨⟨⟨hYK hψ, ⟨⟨ψ, h⟩, hMψ, rfl⟩⟩, ?_⟩, hYt hψ⟩
    refine (Representation.mem_invariants _ _).mpr fun k => ?_
    funext g
    exact hYU ψ hψ g k k.2

  have hfd : ∀ j : Fin n, FiniteDimensional ℂ ↥(VM ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓
      archCutSubmodule F (⟨fun _ => 1, fun w _ => τs j w⟩ : AutomorphicForm.ArchTypeFamily F)) := by
    intro j
    set X := VM ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓
      archCutSubmodule F (⟨fun _ => 1, fun w _ => τs j w⟩ : AutomorphicForm.ArchTypeFamily F) with hX
    have hXc : X ≤ cuspMemberSubmodule F Φ₀ ξ := fun ψ hψ => hmem hψ.1.1.1
    refine finiteDimensional_single hΦ₀ σ ξ hσ M hM U hU O hO hUO (τs j) (hirr j) X hXc ?_ ?_ inf_le_right
    · intro ψ hψ
      obtain ⟨φ, hφM, hφψ⟩ := hψ.1.1.2
      have : (⟨ψ, hXc hψ⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = φ := Subtype.ext hφψ.symm
      rw [this]; exact hφM
    · intro ψ hψ g k hk
      have h := (Representation.mem_invariants _ _).mp hψ.1.2 ⟨k, hk⟩
      exact congrFun h g
  haveI := hfd
  haveI : FiniteDimensional ℂ ↥(⨆ j : Fin n, VM ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓
      archCutSubmodule F (⟨fun _ => 1, fun w _ => τs j w⟩ : AutomorphicForm.ArchTypeFamily F)) :=
    Submodule.finiteDimensional_iSup _
  exact Submodule.finiteDimensional_of_le (hYle.trans hsplit)
