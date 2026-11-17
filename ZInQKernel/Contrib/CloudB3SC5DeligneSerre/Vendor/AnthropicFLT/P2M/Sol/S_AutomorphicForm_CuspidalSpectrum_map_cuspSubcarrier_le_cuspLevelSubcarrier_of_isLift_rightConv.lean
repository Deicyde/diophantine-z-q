/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv (git blob 06fcf984b1885794686272e48eab6d0ed8acdec7, sha256 7d53492be409ea759bebaf6b2d398463b32d9c1a061c84434e179ee16aa40844).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_isCuspidalFn_rightConv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_isKfSmooth_rightConv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (N : Ideal (𝓞 F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hfU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (fdPins F Φ₀).U N, f (u * x) = f x)
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ) (hT : IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) T) :
    Submodule.map (T : Carrier F Φ₀ σ →ₗ[ℂ] Carrier F Φ₀ σ) (cuspSubcarrier F hΦ₀ σ ξ) ≤
      cuspLevelSubcarrier F hΦ₀ σ ξ N := by
  set M : Submodule ℂ (Carrier F Φ₀ σ) :=
    Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) with hM
  set MN : Submodule ℂ (Carrier F Φ₀ σ) :=
    Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype
        (cuspMemberSubmodule F Φ₀ ξ ⊓ CuspidalConstituent.levelInvariantSubmodule F (fdPins F Φ₀) N)) with hMN
  have hcl : cuspSubcarrier F hΦ₀ σ ξ = M.topologicalClosure := rfl
  have hclN : cuspLevelSubcarrier F hΦ₀ σ ξ N = MN.topologicalClosure := rfl

  have hmaps : Set.MapsTo T (M : Set (Carrier F Φ₀ σ)) (MN : Set (Carrier F Φ₀ σ)) := by
    rintro w ⟨ψ, hψ, rfl⟩
    have hψ' : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := hψ
    have hcont : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨ψ.2, hψ'.2⟩
    have hcomm := hT.comm (ψ : AdelicGL2 (𝓞 F) F → ℂ) hcont
    have hmt := hT.mapsTo (ψ : AdelicGL2 (𝓞 F) F → ℂ) hcont
    have hcusp : rightConv F (ψ : AdelicGL2 (𝓞 F) F → ℂ) f ∈ cuspMemberSubmodule F Φ₀ ξ := by
      refine ⟨⟨⟨hmt.1, ?_⟩, AutomorphicForm.isKfSmooth_rightConv F _ f hf⟩, hmt.2⟩
      exact AutomorphicForm.isCuspidalFn_rightConv F Φ₀ (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (ψ : AdelicGL2 (𝓞 F) F → ℂ) hψ'.2 hψ'.1.1.2 f hf
    have hlev : rightConv F (ψ : AdelicGL2 (𝓞 F) F → ℂ) f ∈
        CuspidalConstituent.levelInvariantSubmodule F (fdPins F Φ₀) N := by
      intro g u hu
      rw [AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
      have hfu : (fun y => f (u⁻¹ * y)) = f := funext fun y => hfU y u⁻¹ (Subgroup.inv_mem _ hu)
      rw [hfu]
    have heta : (⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), hcont.1⟩ : ↥(memberSubmodule F Φ₀ ξ)) = ψ := Subtype.coe_eta ψ hcont.1
    rw [heta] at hcomm
    refine ⟨⟨rightConv F (ψ : AdelicGL2 (𝓞 F) F → ℂ) f, hmt.1⟩, ⟨hcusp, hlev⟩, ?_⟩
    exact hcomm.symm

  intro w hw
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
  have hv' : v ∈ closure (M : Set (Carrier F Φ₀ σ)) := by
    rw [← Submodule.topologicalClosure_coe, ← hcl]; exact hv
  have := map_mem_closure T.continuous hv' hmaps
  rw [← Submodule.topologicalClosure_coe, ← hclN] at this
  exact this
