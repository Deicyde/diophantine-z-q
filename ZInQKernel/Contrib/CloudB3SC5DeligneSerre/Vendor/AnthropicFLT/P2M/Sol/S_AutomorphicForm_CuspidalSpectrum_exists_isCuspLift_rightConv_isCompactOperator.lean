/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightConv_isCompactOperator (git blob 052db509edf94eb34d86bdc604cd9997b091be6b, sha256 91429b44b3462aab6f90b2290a0d4cc05b150302943fa9876c39fbc568a73d7d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_apply_mem_cuspSubcarrier_of_isLift_rightConv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isCompactOperator_lift_rightConv_comp_cuspSubcarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightConv_isCompactOperator

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    ∃ Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) Tc ∧ IsCompactOperator Tc := by
  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    unfold cuspSubcarrier; exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  obtain ⟨hgc, hgs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  obtain ⟨T, T', hT, -, -⟩ := AutomorphicForm.CuspidalSpectrum.exists_isLift_rightConv F α β Φ₀ hΦ₀ σ ξ hσ f hgc hgs
  have hmem : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), (T.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL) v ∈ cuspSubcarrier F hΦ₀ σ ξ := fun v =>
    AutomorphicForm.CuspidalSpectrum.apply_mem_cuspSubcarrier_of_isLift_rightConv F hΦ₀ σ ξ hσ f hf T hT v v.2
  have hclosed : IsClosed ((cuspSubcarrier F hΦ₀ σ ξ : Submodule ℂ (Carrier F Φ₀ σ)) : Set (Carrier F Φ₀ σ)) := by
    unfold cuspSubcarrier; exact Submodule.isClosed_topologicalClosure _
  refine ⟨(T.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL).codRestrict (cuspSubcarrier F hΦ₀ σ ξ) hmem, ?_, ?_⟩
  · intro φ h
    apply Subtype.ext
    show T (toCuspSubcarrier F hΦ₀ σ ξ φ : Carrier F Φ₀ σ) = (toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, h⟩ : Carrier F Φ₀ σ)
    rw [toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
    exact hT.comm φ ⟨φ.2.1.1.1, φ.2.2⟩
  · exact (AutomorphicForm.CuspidalSpectrum.isCompactOperator_lift_rightConv_comp_cuspSubcarrier F α β Φ₀ hΦ₀ σ ξ hσ f hf T hT).codRestrict
      hmem hclosed
