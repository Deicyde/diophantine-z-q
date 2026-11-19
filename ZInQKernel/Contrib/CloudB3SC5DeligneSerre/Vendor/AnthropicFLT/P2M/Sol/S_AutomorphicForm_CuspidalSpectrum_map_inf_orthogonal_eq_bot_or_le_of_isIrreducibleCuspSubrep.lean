/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep (git blob 6068ae5c06382866c93b18e1b92e895e747f3b38, sha256 18f7b5890375046afb7047b001f9bdb932b292274d9777f39d7ba2bb95a414eb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchSpherical
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_rightTranslate_rowIsometry_of_isCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) U f)
    (hflat : flat F σ f = f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hsymm : (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)).IsSymmetric)
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hYc : Y ≤ cuspMemberSubmodule F Φ₀ ξ)
    (hYM : ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ Y), toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hYc hψ⟩ ∈ M)
    (hYU : ∀ ψ ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, ψ (g * k) = ψ g)
    (hYt : Y ≤ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F))
    (r : ℝ) (hr : 0 < r) :
    Submodule.map ((toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc)) ⊤ ⊓
        (⨆ (μ : ℂ) (_ : r ≤ ‖μ‖), Module.End.eigenspace (Tc : Module.End ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) μ)ᗮ = ⊥ ∨
      Submodule.map ((toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc)) ⊤ ≤
        (⨆ (μ : ℂ) (_ : r ≤ ‖μ‖), Module.End.eigenspace (Tc : Module.End ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) μ)ᗮ  := by
  classical
  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    unfold cuspSubcarrier; exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set low : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    (⨆ (μ : ℂ) (_ : r ≤ ‖μ‖), Module.End.eigenspace (Tc : Module.End ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) μ)ᗮ with hlow
  have hlowc : IsClosed (low : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
    rw [hlow]; exact Submodule.isClosed_orthogonal _
  have memL : ∀ {φ : AdelicGL2 (𝓞 F) F → ℂ}, φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) low) ↔
      ∃ hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ, toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ ∈ low := by
    intro φ
    constructor
    · rintro ⟨ψ, hψ, rfl⟩; exact ⟨ψ.2, by simpa using hψ⟩
    · rintro ⟨hφ, hl⟩; exact ⟨⟨φ, hφ⟩, hl, rfl⟩

  have lowStable : ∀ (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      S.comp Tc = Tc.comp S → ∀ v ∈ low, S v ∈ low := by
    intro S hS v hv
    rw [hlow] at hv ⊢
    exact ContinuousLinearMap.map_highPart_orthogonal_le_of_commute hsymm hS r ⟨v, hv, rfl⟩

  have hLk : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) low), rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) low) := by
    intro w k φ hφ
    obtain ⟨hφc, hl⟩ := memL.mp hφ
    obtain ⟨S, hS, hSφ⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_commute_lift_rightTranslate_rowIsometry_of_isCompact
        F hΦ₀ σ ξ hσ U hU O hO hUO (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) f hf hsph Tc hcomm w k
    obtain ⟨h', e⟩ := hSφ ⟨φ, hφc⟩
    refine memL.mpr ⟨h', ?_⟩
    rw [← e]; exact lowStable S hS _ hl
  have hLhecke : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u') →
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u) →
      (∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j) →
      ∀ φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) low) ⊓ Representation.invariants ((rightRegular F).comp U.subtype),
        (fun x => ∑ i, φ (x * reps i)) ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) low) := by
    intro g hg n reps h1 h2 h3 φ hφ
    obtain ⟨hφc, hl⟩ := memL.mp hφ.1
    obtain ⟨S, hS, hSφ⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact
        F hΦ₀ σ ξ hσ U hU O hO hUO (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) f hf hsph Tc hcomm g hg n reps h1 h2 h3
    obtain ⟨h', e⟩ := hSφ ⟨φ, hφc⟩ hφ.2
    refine memL.mpr ⟨h', ?_⟩
    rw [← e]; exact lowStable S hS _ hl
  have hLconv : ∀ h : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F h → IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h →
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u' ∈ U, h (u' * x) = h x ∧ h (x * u') = h x) →
      ∀ φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) low), rightConv F φ h ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) low) := by
    intro h hh hbh hhU φ hφ
    obtain ⟨hφc, hl⟩ := memL.mp hφ
    obtain ⟨S, hS, hSφ⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact
        F hΦ₀ σ ξ hσ U hU O hO hUO τ hirr f hf hsph Tc hcomm h hh hbh hhU
    obtain ⟨h', e⟩ := hSφ ⟨φ, hφc⟩
    refine memL.mpr ⟨h', ?_⟩
    rw [← e]; exact lowStable S hS _ hl

  exact AutomorphicForm.CuspidalSpectrum.map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed
    F hΦ₀ σ ξ hσ M hM U hU O hO hUO (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) Y hYc hYM hYU hYt low hlowc hLk hLhecke hLconv
