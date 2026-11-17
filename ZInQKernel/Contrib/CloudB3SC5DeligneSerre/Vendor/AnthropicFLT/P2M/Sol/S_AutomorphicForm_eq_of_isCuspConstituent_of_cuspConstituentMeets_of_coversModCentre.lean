/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre (git blob 3f01eb313b7fa5ee7d3cf47c0d4f73dc89f02006, sha256 a884106f50e7e5418f5cc6db0313ddff7c4ae3903bd4bf29a6574e0aa1eba357).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_IsIsotypicCuspFormAt_exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_mem_of_isCuspConstituent_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_eq_of_isCuspConstituent_of_exists_mem_ne_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_coversModCentre_of_le_of_lt_of_coversModCentre
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_coversModCentre_centreCutSiegelSetAmple
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule
import Batteries.Tactic.Alias

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicVolume
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm
alias ArchTypeFamily := _root_.AutomorphicForm.ArchTypeFamily -- [port]
export _root_.AutomorphicForm (CuspidalConstituent.rightTranslate CuspidalConstituent.rightTranslate_apply CuspidalConstituent.cuspKFiniteSubmodule CuspidalConstituent.IsCuspConstituent CuspidalConstituent.CuspConstituentMeets IsIsotypicCuspFormAt archTypeSubmoduleAt archCutSubmodule mem_archCutSubmodule_iff CarrierPins productionPinsOf AdelicGL2 finiteAdelicGL2Subgroup IsSmoothCuspAutomorphicFnAt lsXiMemberAt_iff SmoothCuspRealizationAt HeckeEigensystem IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot CuspidalConstituent.mem_of_isCuspConstituent_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre coversModCentre_of_le_of_lt_of_coversModCentre exists_coversModCentre_centreCutSiegelSetAmple CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule CuspidalConstituent.le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule)
open _root_.AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

noncomputable abbrev stdPins (D : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
    (adelicBox F)

section Nesting

theorem isSmoothCuspAutomorphicFnAt_of_subset {D D' : Set (AdelicGL2 (𝓞 F) F)} (hDD' : D' ⊆ D)
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D U gen B) ξ φ) :
    IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D' U gen B) ξ φ := by
  obtain ⟨⟨hA, hC⟩, hK⟩ := h
  refine ⟨⟨?_, hC⟩, hK⟩
  have hA' := (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ D φ).mp hA
  exact (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ D' φ).mpr
    ⟨hA'.1, hA'.2.mono_measure (Measure.restrict_mono_set _ hDD')⟩

theorem cuspKFiniteSubmodule_le_of_subset {D D' : Set (AdelicGL2 (𝓞 F) F)} (hDD' : D' ⊆ D)
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ) :
    CuspidalConstituent.cuspKFiniteSubmodule F (productionPinsOf F D U gen B) ξ ≤
      CuspidalConstituent.cuspKFiniteSubmodule F (productionPinsOf F D' U gen B) ξ := by
  refine Submodule.span_mono ?_
  rintro φ ⟨hsat, hc, htys⟩
  exact ⟨fun g => isSmoothCuspAutomorphicFnAt_of_subset F hDD' U gen B ξ (hsat g), hc, htys⟩

theorem isCuspConstituent_of_le {D : Set (AdelicGL2 (𝓞 F) F)} (D' : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ) {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hV : CuspidalConstituent.IsCuspConstituent F (productionPinsOf F D U gen B) ξ V)
    (hle : V ≤ CuspidalConstituent.cuspKFiniteSubmodule F (productionPinsOf F D' U gen B) ξ) :
    CuspidalConstituent.IsCuspConstituent F (productionPinsOf F D' U gen B) ξ V := by
  obtain ⟨hsub, hne, hmin⟩ := hV
  refine ⟨⟨hle, hsub.rightTranslate_fin_mem, hsub.rightTranslate_arch_mem, hsub.rightConv_mem⟩, hne, ?_⟩
  intro W hW hWV
  exact hmin W ⟨hWV.trans hsub.le, hW.rightTranslate_fin_mem, hW.rightTranslate_arch_mem, hW.rightConv_mem⟩ hWV

theorem isIsotypicCuspFormAt_of_isSmoothCuspAutomorphicFnAt {D : Set (AdelicGL2 (𝓞 F) F)} (D' : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ) {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {Ψ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsIsotypicCuspFormAt F (productionPinsOf F D U gen B) ξ N S Ψ φ)
    (hs : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D' U gen B) ξ φ) :
    IsIsotypicCuspFormAt F (productionPinsOf F D' U gen B) ξ N S Ψ φ :=
  ⟨hs, h.continuous, h.level_invariant, h.hecke_eigen, h.central_eigen⟩

namespace SmoothCuspRealizationAt export _root_.AutomorphicForm.SmoothCuspRealizationAt (exists_ne_zero central_eigen smoothCusp exceptionalSet level_invariant centralChar hecke_eigen toFun) end SmoothCuspRealizationAt
open scoped _root_.AutomorphicForm.SmoothCuspRealizationAt in

noncomputable def SmoothCuspRealizationAt.rehome {D : Set (AdelicGL2 (𝓞 F) F)} (D' : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) {Φ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F (productionPinsOf F D U gen B) Φ)
    (hs : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D' U gen B) R.centralChar R.toFun) :
    SmoothCuspRealizationAt F (productionPinsOf F D' U gen B) Φ where
  toFun := R.toFun
  exists_ne_zero := R.exists_ne_zero
  centralChar := R.centralChar
  smoothCusp := hs
  level_invariant := R.level_invariant
  exceptionalSet := R.exceptionalSet
  hecke_eigen := R.hecke_eigen
  central_eigen := R.central_eigen

theorem iUnion_image_mul_mono {S S' : Set (AdelicGL2 (𝓞 F) F)} (h : S ⊆ S') (T : Finset (AdelicGL2 (𝓞 F) F)) :
    (⋃ x ∈ T, (· * x) '' S) ⊆ ⋃ x ∈ T, (· * x) '' S' :=
  Set.iUnion₂_mono fun _ _ => Set.image_mono h

theorem centreCutSiegelSet_subset_of_le (c u : ℝ) {d₁ d₁' : ℝ} (d₂ : ℝ) (h : d₁ ≤ d₁') :
    centreCutSiegelSet F c u d₁' d₂ ⊆ centreCutSiegelSet F c u d₁ d₂ :=
  fun _ hg => ⟨hg.1, hg.2.1, hg.2.2.1, fun w => ⟨h.trans (hg.2.2.2 w).1, (hg.2.2.2 w).2⟩⟩

theorem pos_of_coversModCentre {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)}
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) : 0 < d₂ := by
  obtain ⟨γ, z, hγ⟩ := hcov 1
  simp only [Set.mem_iUnion, Set.mem_image] at hγ
  obtain ⟨x, -, g, hg, -⟩ := hγ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact (archDetNorm_pos w g).trans_le (hg.2.2.2 w).2

end Nesting

section TypeFamilyAppend

namespace ArchTypeFamily export _root_.AutomorphicForm.ArchTypeFamily (card rep) end ArchTypeFamily
namespace ArchTypeFamily
open scoped _root_.AutomorphicForm.ArchTypeFamily in

private noncomputable def _root_.AutomorphicForm.ArchTypeFamily.append (t₁ t₂ : ArchTypeFamily F) : ArchTypeFamily F where
  card w := (AutomorphicForm.ArchTypeFamily.card t₁) w + (AutomorphicForm.ArchTypeFamily.card t₂) w
  rep w := Fin.append ((AutomorphicForm.ArchTypeFamily.rep t₁) w) ((AutomorphicForm.ArchTypeFamily.rep t₂) w)

end ArchTypeFamily
alias ArchTypeFamily.append := _root_.AutomorphicForm.ArchTypeFamily.append -- [port]
theorem archCutSubmodule_le_append_left (t₁ t₂ : ArchTypeFamily F) :
    archCutSubmodule F t₁ ≤ archCutSubmodule F (ArchTypeFamily.append F t₁ t₂) := by
  intro f hf
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  have hle : (⨆ i, archTypeSubmoduleAt F w ((AutomorphicForm.ArchTypeFamily.rep t₁) w i))
      ≤ ⨆ j, archTypeSubmoduleAt F w ((AutomorphicForm.ArchTypeFamily.rep (ArchTypeFamily.append F t₁ t₂)) w j) :=
    iSup_le fun i => le_iSup_of_le (Fin.castAdd ((AutomorphicForm.ArchTypeFamily.card t₂) w) i) (le_of_eq (by
      show archTypeSubmoduleAt F w ((AutomorphicForm.ArchTypeFamily.rep t₁) w i)
          = archTypeSubmoduleAt F w (Fin.append ((AutomorphicForm.ArchTypeFamily.rep t₁) w) ((AutomorphicForm.ArchTypeFamily.rep t₂) w) (Fin.castAdd ((AutomorphicForm.ArchTypeFamily.card t₂) w) i))
      rw [Fin.append_left]))
  exact hle (hf w)

theorem archCutSubmodule_le_append_right (t₁ t₂ : ArchTypeFamily F) :
    archCutSubmodule F t₂ ≤ archCutSubmodule F (ArchTypeFamily.append F t₁ t₂) := by
  intro f hf
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  have hle : (⨆ i, archTypeSubmoduleAt F w ((AutomorphicForm.ArchTypeFamily.rep t₂) w i))
      ≤ ⨆ j, archTypeSubmoduleAt F w ((AutomorphicForm.ArchTypeFamily.rep (ArchTypeFamily.append F t₁ t₂)) w j) :=
    iSup_le fun i => le_iSup_of_le (Fin.natAdd ((AutomorphicForm.ArchTypeFamily.card t₁) w) i) (le_of_eq (by
      show archTypeSubmoduleAt F w ((AutomorphicForm.ArchTypeFamily.rep t₂) w i)
          = archTypeSubmoduleAt F w (Fin.append ((AutomorphicForm.ArchTypeFamily.rep t₁) w) ((AutomorphicForm.ArchTypeFamily.rep t₂) w) (Fin.natAdd ((AutomorphicForm.ArchTypeFamily.card t₁) w) i))
      rw [Fin.append_right]))
  exact hle (hf w)

namespace CuspidalConstituent export _root_.AutomorphicForm.CuspidalConstituent (rightTranslate rightTranslate_apply cuspKFiniteSubmodule IsCuspSubrep IsCuspConstituent CuspConstituentMeets mem_of_isCuspConstituent_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt eq_of_isCuspConstituent_of_exists_mem_ne_zero continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule) end CuspidalConstituent
open scoped _root_.AutomorphicForm.CuspidalConstituent in

theorem CuspidalConstituent.exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule
    (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ CuspidalConstituent.cuspKFiniteSubmodule F pins ξ) :
    ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys := by
  refine Submodule.span_induction (p := fun φ _ => ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys)
    ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨-, -, tys, htys⟩
    exact ⟨tys, htys⟩
  · exact ⟨⟨fun _ => 0, fun _ i => i.elim0⟩, Submodule.zero_mem _⟩
  · rintro f g - - ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
    exact ⟨ArchTypeFamily.append F t₁ t₂, Submodule.add_mem _
      (archCutSubmodule_le_append_left F t₁ t₂ h₁) (archCutSubmodule_le_append_right F t₁ t₂ h₂)⟩
  · rintro a f - ⟨t, h⟩
    exact ⟨t, Submodule.smul_mem _ a h⟩

end TypeFamilyAppend

section Matched

theorem eq_of_isCuspConstituent_of_isIsotypicCuspFormAt_of_coversModCentre_ample
    (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hκ : 1 ≤ κ) (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcovA : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ))
    (ξ : (stdPins F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (h₁ : CuspidalConstituent.IsCuspConstituent F (stdPins F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) ξ V₁)
    (h₂ : CuspidalConstituent.IsCuspConstituent F (stdPins F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) ξ V₂)
    (φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (hφ₁V : φ₁ ∈ V₁) (hφ₁0 : φ₁ ≠ 0)
    (hφ₁ : IsIsotypicCuspFormAt F (stdPins F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) ξ N S Ψ φ₁)
    (hφ₂V : φ₂ ∈ V₂) (hφ₂0 : φ₂ ≠ 0)
    (hφ₂ : IsIsotypicCuspFormAt F (stdPins F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) ξ N S Ψ φ₂) :
    V₁ = V₂ := by
  have hsub : (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ)
      ⊆ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ :=
    iUnion_image_mul_mono F (centreCutSiegelSetAmple_subset c u d₁ d₂ κ) T

  obtain ⟨Ψ₁, R₁, -, ha₁, hb₁, hf₁, hξ₁, -⟩ :=
    IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot F _ ξ N hN S Ψ φ₁ hφ₁ hφ₁0
  obtain ⟨Ψ₂, R₂, -, ha₂, hb₂, hf₂, hξ₂, -⟩ :=
    IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot F _ ξ N hN S Ψ φ₂ hφ₂ hφ₂0
  subst hf₁
  subst hf₂

  have hs₁ : IsSmoothCuspAutomorphicFnAt F (stdPins F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ)) ξ R₁.toFun :=
    isSmoothCuspAutomorphicFnAt_of_subset F hsub _ _ _ ξ hφ₁.smoothCusp
  have hs₂ : IsSmoothCuspAutomorphicFnAt F (stdPins F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ)) ξ R₂.toFun :=
    isSmoothCuspAutomorphicFnAt_of_subset F hsub _ _ _ ξ hφ₂.smoothCusp

  let R₁a := SmoothCuspRealizationAt.rehome F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ) _ _ _ R₁ (by rw [hξ₁]; exact hs₁)
  let R₂a := SmoothCuspRealizationAt.rehome F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ) _ _ _ R₂ (by rw [hξ₂]; exact hs₂)
  have hagree : Ψ₁.AgreesAwayFromFinite Ψ₂ :=
    ⟨∅, fun v _ => ⟨(ha₁ v).trans (ha₂ v).symm, (hb₁ v).trans (hb₂ v).symm⟩⟩
  have happrox :=
    exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample
      F c u d₁ d₂ κ T hd hκ hc hd₁ hcovA Ψ₁ Ψ₂ hagree R₁a hφ₁.continuous R₂a hφ₂.continuous

  obtain ⟨tys, htys⟩ :=
    CuspidalConstituent.exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule F _ ξ (h₂.1.le hφ₂V)

  have hmem : R₂.toFun ∈ V₁ :=
    CuspidalConstituent.mem_of_isCuspConstituent_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt
      F c u d₁ d₂ κ T hd hκ hc hd₁ hcovA ξ N hN tys V₁ h₁ R₁.toFun hφ₁V R₂.toFun hs₂ hφ₂.continuous
      (fun g u hu => hφ₂.level_invariant g u hu) htys happrox

  exact CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero F _ ξ V₁ V₂ h₁ h₂
    ⟨R₂.toFun, ⟨hmem, hφ₂V⟩, hφ₂0⟩

end Matched

section Positive

theorem eq_of_isCuspConstituent_of_isIsotypicCuspFormAt_of_pos
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (stdPins F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (h₁ : CuspidalConstituent.IsCuspConstituent F (stdPins F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) ξ V₁)
    (h₂ : CuspidalConstituent.IsCuspConstituent F (stdPins F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) ξ V₂)
    (φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (hφ₁V : φ₁ ∈ V₁) (hφ₁0 : φ₁ ≠ 0)
    (hφ₁ : IsIsotypicCuspFormAt F (stdPins F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) ξ N S Ψ φ₁)
    (hφ₂V : φ₂ ∈ V₂) (hφ₂0 : φ₂ ≠ 0)
    (hφ₂ : IsIsotypicCuspFormAt F (stdPins F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) ξ N S Ψ φ₂) :
    V₁ = V₂ := by
  obtain ⟨κ, R, hκ, -, hamp⟩ := exists_coversModCentre_centreCutSiegelSetAmple F
  have hcovA := hamp c u d₁ d₂ T hcov

  have hle₁ := CuspidalConstituent.le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule
    F c u d₁ d₂ T hc hd₁ hd hcov ξ V₁ h₁ N hN ⟨φ₁, hφ₁V, hφ₁0, fun g u hu => hφ₁.level_invariant g u hu⟩
    c (max u R) d₁ d₂ T hc hd₁
  have hle₂ := CuspidalConstituent.le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule
    F c u d₁ d₂ T hc hd₁ hd hcov ξ V₂ h₂ N hN ⟨φ₂, hφ₂V, hφ₂0, fun g u hu => hφ₂.level_invariant g u hu⟩
    c (max u R) d₁ d₂ T hc hd₁
  have h₁' := isCuspConstituent_of_le F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c (max u R) d₁ d₂) _ _ _ ξ h₁ hle₁
  have h₂' := isCuspConstituent_of_le F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c (max u R) d₁ d₂) _ _ _ ξ h₂ hle₂

  have hs₁ := (CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
    F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c (max u R) d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) ξ φ₁ (hle₁ hφ₁V)).2 1
  have hs₂ := (CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
    F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c (max u R) d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) ξ φ₂ (hle₂ hφ₂V)).2 1
  have hrt : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, CuspidalConstituent.rightTranslate F 1 φ = φ := fun φ => by
    funext x; rw [CuspidalConstituent.rightTranslate_apply, mul_one]
  rw [hrt] at hs₁ hs₂
  exact eq_of_isCuspConstituent_of_isIsotypicCuspFormAt_of_coversModCentre_ample F c (max u R) d₁ d₂ κ T hd hκ hc hd₁
    hcovA ξ N hN S Ψ V₁ V₂ h₁' h₂' φ₁ φ₂ hφ₁V hφ₁0
    (isIsotypicCuspFormAt_of_isSmoothCuspAutomorphicFnAt F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c (max u R) d₁ d₂) _ _ _ ξ hφ₁ hs₁) hφ₂V hφ₂0
    (isIsotypicCuspFormAt_of_isSmoothCuspAutomorphicFnAt F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c (max u R) d₁ d₂) _ _ _ ξ hφ₂ hs₂)

end Positive

end AutomorphicForm

open _root_.AutomorphicForm
namespace AutomorphicForm
end AutomorphicForm
open _root_.P2MW.S_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre.AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (h₁ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ V₁)
    (h₂ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ V₂)
    (m₁ : AutomorphicForm.CuspidalConstituent.CuspConstituentMeets F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ N S Ψ V₁)
    (m₂ : AutomorphicForm.CuspidalConstituent.CuspConstituentMeets F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ N S Ψ V₂) :
    V₁ = V₂ := by
  obtain ⟨φ₁, hφ₁V, hφ₁0, hφ₁⟩ := m₁
  obtain ⟨φ₂, hφ₂V, hφ₂0, hφ₂⟩ := m₂

  rcases le_or_gt c 0 with hc | hc
  · exact absurd (AutomorphicForm.eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre
      F c u d₁ d₂ T hc hd hcov ξ φ₁ hφ₁.smoothCusp.1.1 hφ₁.continuous) hφ₁0

  by_cases hN : N = ⊥
  · exfalso
    subst hN
    have hb := AutomorphicForm.isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf F
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (adelicBox F) ξ S Ψ
    have hmem := hφ₁.mem_isotypicCuspSubmodule
    rw [hb, Submodule.mem_bot] at hmem
    exact hφ₁0 hmem

  have hd₂ : 0 < d₂ := pos_of_coversModCentre F hcov
  have hle : d₁ ≤ max d₁ (d₂ / 2) := le_max_left _ _
  have hd₁' : 0 < max d₁ (d₂ / 2) := lt_max_of_lt_right (half_pos hd₂)
  have hlt : max d₁ (d₂ / 2) < d₂ := max_lt hd (half_lt_self hd₂)
  have hcov' := AutomorphicForm.coversModCentre_of_le_of_lt_of_coversModCentre F c u d₁ d₂ (max d₁ (d₂ / 2)) T hle hlt hcov
  have hsub : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u (max d₁ (d₂ / 2)) d₂)
      ⊆ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ :=
    iUnion_image_mul_mono F (centreCutSiegelSet_subset_of_le F c u d₂ hle) T
  have hK := cuspKFiniteSubmodule_le_of_subset F hsub
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F) ξ

  exact eq_of_isCuspConstituent_of_isIsotypicCuspFormAt_of_pos F c u (max d₁ (d₂ / 2)) d₂ T hlt hc hd₁' hcov' ξ N hN S Ψ
    V₁ V₂ (isCuspConstituent_of_le F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u (max d₁ (d₂ / 2)) d₂) _ _ _ ξ h₁ (h₁.1.le.trans hK))
    (isCuspConstituent_of_le F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u (max d₁ (d₂ / 2)) d₂) _ _ _ ξ h₂ (h₂.1.le.trans hK)) φ₁ φ₂ hφ₁V hφ₁0
    (isIsotypicCuspFormAt_of_isSmoothCuspAutomorphicFnAt F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u (max d₁ (d₂ / 2)) d₂) _ _ _ ξ hφ₁
      (isSmoothCuspAutomorphicFnAt_of_subset F hsub _ _ _ ξ hφ₁.smoothCusp))
    hφ₂V hφ₂0
    (isIsotypicCuspFormAt_of_isSmoothCuspAutomorphicFnAt F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u (max d₁ (d₂ / 2)) d₂) _ _ _ ξ hφ₂
      (isSmoothCuspAutomorphicFnAt_of_subset F hsub _ _ _ ξ hφ₂.smoothCusp))
