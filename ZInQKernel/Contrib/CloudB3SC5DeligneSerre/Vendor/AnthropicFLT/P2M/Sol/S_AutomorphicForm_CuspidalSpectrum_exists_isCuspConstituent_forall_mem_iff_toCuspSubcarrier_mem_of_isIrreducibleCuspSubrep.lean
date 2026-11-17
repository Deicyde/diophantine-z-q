/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_exists_isCuspConstituent_forall_mem_iff_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep (git blob 91e0f8fdd515bb8151419ccddfe6bb0353ace213, sha256 bfc905dbb9c32692c5d24f815f8705eb770954c5aa0adb7071b3da8f09d745a5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isCuspSubrep_cuspKFiniteSubmodule_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_ne_zero_mem_cuspKFiniteSubmodule_toCuspSubcarrier_mem_of_isClosedCuspSubrep_of_ne_bot
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_cuspKFiniteSubmodule_le_cuspMemberSubmodule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_idempotent_cutProjector_of_isCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_IsKfSmooth_exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isCuspConstituent_forall_mem_iff_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace BridgeReduce

variable (F : Type) [Field F] [NumberField F]

def concatFamily (t₁ t₂ : ArchTypeFamily F) : ArchTypeFamily F :=
  ⟨fun w => t₁.card w + t₂.card w, fun w => Fin.append (t₁.rep w) (t₂.rep w)⟩

theorem archCutSubmodule_le_concat_left (t₁ t₂ : ArchTypeFamily F) :
    archCutSubmodule F t₁ ≤ archCutSubmodule F (concatFamily F t₁ t₂) := by
  intro f hf
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  have hle : (⨆ i, archTypeSubmoduleAt F w (t₁.rep w i)) ≤
      ⨆ j, archTypeSubmoduleAt F w ((concatFamily F t₁ t₂).rep w j) := iSup_le fun i => by
    have : (concatFamily F t₁ t₂).rep w (Fin.castAdd (t₂.card w) i) = t₁.rep w i := by
      show Fin.append (t₁.rep w) (t₂.rep w) (Fin.castAdd (t₂.card w) i) = t₁.rep w i
      rw [Fin.append_left]
    rw [← this]
    exact le_iSup (fun j => archTypeSubmoduleAt F w ((concatFamily F t₁ t₂).rep w j)) (Fin.castAdd (t₂.card w) i)
  exact hle (hf w)

theorem archCutSubmodule_le_concat_right (t₁ t₂ : ArchTypeFamily F) :
    archCutSubmodule F t₂ ≤ archCutSubmodule F (concatFamily F t₁ t₂) := by
  intro f hf
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  have hle : (⨆ i, archTypeSubmoduleAt F w (t₂.rep w i)) ≤
      ⨆ j, archTypeSubmoduleAt F w ((concatFamily F t₁ t₂).rep w j) := iSup_le fun i => by
    have : (concatFamily F t₁ t₂).rep w (Fin.natAdd (t₁.card w) i) = t₂.rep w i := by
      show Fin.append (t₁.rep w) (t₂.rep w) (Fin.natAdd (t₁.card w) i) = t₂.rep w i
      rw [Fin.append_right]
    rw [← this]
    exact le_iSup (fun j => archTypeSubmoduleAt F w ((concatFamily F t₁ t₂).rep w j)) (Fin.natAdd (t₁.card w) i)
  exact hle (hf w)

theorem exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) :
    ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys := by
  refine Submodule.span_induction (p := fun φ _ => ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨-, -, tys, htys⟩
    exact ⟨tys, htys⟩
  · exact ⟨⟨fun _ => 0, fun w i => Fin.elim0 i⟩, Submodule.zero_mem _⟩
  · rintro a b - - ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
    exact ⟨concatFamily F t₁ t₂, Submodule.add_mem _ (archCutSubmodule_le_concat_left F t₁ t₂ h₁)
      (archCutSubmodule_le_concat_right F t₁ t₂ h₂)⟩
  · rintro c a - ⟨t, h⟩
    exact ⟨t, Submodule.smul_mem _ c h⟩

theorem cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_fdPins
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) :
    cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ≤ cuspKFiniteSubmodule F (fdPins F Φ₀) ξ := by
  refine Submodule.span_le.mpr ?_
  rintro φ ⟨hsat, hcont, tys, htys⟩
  refine Submodule.subset_span ⟨fun g => ?_, hcont, tys, htys⟩
  have h := hsat g
  exact ⟨⟨AutomorphicForm.isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre F c u d₁ d₂ T hd hcov
      α β hΦ₀.pos Φ₀ hΦ₀.subset hΦ₀.isFundamentalDomain ξ _ h.1.1, h.1.2⟩, h.2⟩

theorem exists_isCompact_isOpen_forall_apply_mul_eq_of_isKfSmooth
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) :
    ∃ (U : Subgroup (AdelicGL2 (𝓞 F) F)) (_ : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
      (O : Subgroup (AdelicGL2 (𝓞 F) F)) (_ : IsOpen (O : Set (AdelicGL2 (𝓞 F) F))),
      U = O ⊓ finiteAdelicGL2Subgroup F ∧ ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ (g * k) = φ g :=
  AutomorphicForm.IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq F φ hφ

end BridgeReduce

open BridgeReduce in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M) :
    ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V ∧
      ∀ ψ : AdelicGL2 (𝓞 F) F → ℂ, ψ ∈ V ↔
        ψ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ∧
          ∃ h : ψ ∈ cuspMemberSubmodule F Φ₀ ξ, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, h⟩ ∈ M := by
  classical
  set pins := (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) with hpins
  set K : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := cuspKFiniteSubmodule F pins ξ with hK
  set Mb : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := cuspMemberSubmodule F Φ₀ ξ with hMb
  set ι := toCuspSubcarrier F hΦ₀ σ ξ with hι
  set V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := K ⊓ Submodule.map Mb.subtype (Submodule.comap ι M) with hV
  have hKMb : K ≤ Mb := AutomorphicForm.CuspidalSpectrum.cuspKFiniteSubmodule_le_cuspMemberSubmodule F c u d₁ d₂ T hc hd₁ hd hcov ξ hΦ₀

  have hmem : ∀ ψ : AdelicGL2 (𝓞 F) F → ℂ, ψ ∈ V ↔ ψ ∈ K ∧ ∃ h : ψ ∈ Mb, ι ⟨ψ, h⟩ ∈ M := by
    intro ψ
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa using hy⟩
    · rintro ⟨h, hM'⟩
      exact ⟨⟨ψ, h⟩, hM', rfl⟩

  have hsub : IsCuspSubrep F pins ξ V :=
    AutomorphicForm.CuspidalSpectrum.isCuspSubrep_cuspKFiniteSubmodule_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
      F c u d₁ d₂ T hc hd₁ hd hcov ξ σ hσ hΦ₀ M hM.isClosedCuspSubrep

  have hne : V ≠ ⊥ := by
    obtain ⟨ψ, hψ0, hψK, h, hψM⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_ne_zero_mem_cuspKFiniteSubmodule_toCuspSubcarrier_mem_of_isClosedCuspSubrep_of_ne_bot
        F c u d₁ d₂ T hc hd₁ hd hcov ξ σ hσ hΦ₀ M hM.isClosedCuspSubrep hM.ne_bot
    intro hbot
    have : ψ ∈ V := (hmem ψ).mpr ⟨hψK, h, hψM⟩
    rw [hbot, Submodule.mem_bot] at this
    exact hψ0 this

  have hmin : ∀ W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), IsCuspSubrep F pins ξ W → W ≤ V → W = ⊥ ∨ W = V := by
    intro W hW hWV
    by_cases hW0 : W = ⊥
    · exact Or.inl hW0
    refine Or.inr (le_antisymm hWV ?_)

    have hWfd : IsCuspSubrep F (fdPins F Φ₀) ξ W :=
      ⟨hW.le.trans (cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_fdPins F c u d₁ d₂ T hd hcov ξ hΦ₀),
        hW.rightTranslate_fin_mem, hW.rightTranslate_arch_mem, hW.rightConv_mem⟩
    set N : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
      (Submodule.map ι (Submodule.comap Mb.subtype W)).topologicalClosure with hN
    have hNcl : IsClosedCuspSubrep F hΦ₀ σ ξ N :=
      AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep F hΦ₀ σ ξ W hWfd
    have hmapM : Submodule.map ι (Submodule.comap Mb.subtype W) ≤ M := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨-, h, hyM⟩ := (hmem (y : AdelicGL2 (𝓞 F) F → ℂ)).mp (hWV hy)
      exact hyM
    have hNM : N ≤ M := Submodule.topologicalClosure_minimal _ hmapM hM.isClosedCuspSubrep.isClosed
    have hN0 : N ≠ ⊥ := by
      obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hW0
      have hwMb : w ∈ Mb := hKMb (hsub.le (hWV hwW))
      intro hNbot
      have hwN : ι ⟨w, hwMb⟩ ∈ N := Submodule.le_topologicalClosure _ ⟨⟨w, hwMb⟩, hwW, rfl⟩
      rw [hNbot, Submodule.mem_bot] at hwN
      have h0 : toCarrier F hΦ₀ σ ξ ⟨w, hwMb.1.1.1⟩ = 0 := congrArg Subtype.val hwN
      exact hw0 (AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ w ⟨hwMb.1.1.1, hwMb.2⟩ h0)
    have hNeq : N = M := (hM.2.2 N hNcl hNM).resolve_left hN0

    intro ψ hψV
    have hψK : ψ ∈ K := hψV.1
    have hψMb : ψ ∈ Mb := hKMb hψK
    obtain ⟨U, hU, O, hO, hUO, hψU⟩ := exists_isCompact_isOpen_forall_apply_mul_eq_of_isKfSmooth F hψMb.1.2
    obtain ⟨tys, hψt⟩ := exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule F pins ξ hψK

    obtain ⟨P, -, -, hP2, hP3, -⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_idempotent_cutProjector_of_isCompact F hΦ₀ σ ξ hσ U hU O hO hUO tys
    have hfix : P (ι ⟨ψ, hψMb⟩) = ι ⟨ψ, hψMb⟩ := hP2 ψ hψMb hψU hψt
    have hψN : ι ⟨ψ, hψMb⟩ ∈ N := by
      rw [hNeq]; exact ((hmem ψ).mp hψV).2.2

    set Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
      W ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓ archCutSubmodule F tys with hY
    have hYU : ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, y (g * k) = y g := by
      rintro y ⟨⟨-, hy⟩, -⟩ g k hk
      have := (Representation.mem_invariants _ _).mp hy ⟨k, hk⟩
      exact congrFun this g
    have hPimg : ∀ v ∈ Submodule.map ι (Submodule.comap Mb.subtype W), P v ∈ Submodule.map ι (Submodule.comap Mb.subtype Y) := by
      rintro _ ⟨y, hyW, rfl⟩
      have hyK : (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ K := hsub.le (hWV hyW)
      obtain ⟨φ', hφ', hφ'U, hφ't, hφ'stab, hPy⟩ :=
        hP3 y y.2 (exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule F pins ξ hyK)
      have hφ'W : φ' ∈ W := hφ'stab W hW.rightTranslate_fin_mem hW.rightTranslate_arch_mem hyW
      refine ⟨⟨φ', hφ'⟩, ⟨⟨hφ'W, ?_⟩, hφ't⟩, ?_⟩
      · show φ' ∈ Representation.invariants ((rightRegular F).comp U.subtype)
        rw [Representation.mem_invariants]
        rintro ⟨k, hk⟩
        funext g
        exact hφ'U g k hk
      · rw [hPy]

    haveI hYfd : FiniteDimensional ℂ ↥Y :=
      AutomorphicForm.CuspidalSpectrum.finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep
        F c u d₁ d₂ T hc hd₁ hd hcov ξ σ hσ hΦ₀ M hM U hU O hO hUO tys Y
        (fun y hy => hsub.le (hWV hy.1.1))
        (fun y hy => ((hmem y).mp (hWV hy.1.1)).2) hYU (fun y hy => hy.2)
    haveI hYfd' : FiniteDimensional ℂ ↥(Submodule.comap Mb.subtype Y) := by
      refine FiniteDimensional.of_injective
        (((Mb.subtype.domRestrict (Submodule.comap Mb.subtype Y)).codRestrict Y fun y => y.2)) ?_
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥Y => (z : AdelicGL2 (𝓞 F) F → ℂ)) hab
    haveI hYfd'' : FiniteDimensional ℂ ↥(Submodule.map ι (Submodule.comap Mb.subtype Y)) :=
      Module.Finite.map _ _
    have hYcl : IsClosed ((Submodule.map ι (Submodule.comap Mb.subtype Y) : Submodule ℂ _) : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) :=
      Submodule.closed_of_finiteDimensional _

    have hψimg : ι ⟨ψ, hψMb⟩ ∈ closure ((Submodule.map ι (Submodule.comap Mb.subtype Y)) : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
      rw [← hfix]
      have hNcoe : (N : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) =
          closure ((Submodule.map ι (Submodule.comap Mb.subtype W)) : Set _) := Submodule.topologicalClosure_coe _
      have hψN' : ι ⟨ψ, hψMb⟩ ∈ closure ((Submodule.map ι (Submodule.comap Mb.subtype W)) : Set _) := by
        rw [← hNcoe]; exact hψN
      have h1 : P (ι ⟨ψ, hψMb⟩) ∈ P '' closure ((Submodule.map ι (Submodule.comap Mb.subtype W)) : Set _) :=
        ⟨_, hψN', rfl⟩
      refine closure_mono ?_ (image_closure_subset_closure_image P.continuous h1)
      rintro _ ⟨v, hv, rfl⟩
      exact hPimg v hv
    rw [hYcl.closure_eq] at hψimg
    obtain ⟨y, hyY, hyeq⟩ := hψimg

    have hdiff0 : toCarrier F hΦ₀ σ ξ ⟨ψ - (y : AdelicGL2 (𝓞 F) F → ℂ), (Mb.sub_mem hψMb y.2).1.1.1⟩ = 0 := by
      have : ι (⟨ψ, hψMb⟩ - y) = 0 := by rw [map_sub, sub_eq_zero]; exact hyeq.symm
      exact congrArg Subtype.val this
    have hψy : ψ - (y : AdelicGL2 (𝓞 F) F → ℂ) = 0 :=
      AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ _
        ⟨(Mb.sub_mem hψMb y.2).1.1.1, (Mb.sub_mem hψMb y.2).2⟩ hdiff0
    rw [sub_eq_zero] at hψy
    rw [hψy]
    exact hyY.1.1
  exact ⟨V, ⟨hsub, hne, hmin⟩, hmem⟩

end
