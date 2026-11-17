/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH (git blob 08947faa40b3bd773246a7942f47ae132d65e0e7, sha256 12f5de055dda8e2daa172dec6e16291438ddc21919df126b8f3b92f68d918182).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_meromorphic_smul_eq_mul_of_slashInvariant_residue
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_cuspForm_mul_exp_periodOf_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

namespace ModularCurve
export _root_.ModularCurve (ComplexPlaceDictionaryOf ComplexPlaceDictionary Gamma1_le_GammaH xHFunctionField periodAlongOf periodOf periodLatticeOf period exists_hasEquivariantPrimitiveOf periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf ComplexPlaceDictionaryOf.exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH exists_meromorphic_smul_eq_mul_of_slashInvariant_residue ComplexPlaceDictionaryOf.exists_cuspForm_mul_exp_periodOf_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH)
namespace AbelSufficiencyAssemblyH
open _root_.ModularCurve

open Filter Complex

theorem analyticAt_exp_comp {Φ : ℍ → ℂ} {f : ℍ → ℂ}
    (hΦ : ∀ τ : ℍ, HasDerivAt (Φ ∘ ofComplex) (f τ) (τ : ℂ)) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => Complex.exp (Φ (ofComplex z))) (τ : ℂ) := by
  have hd : DifferentiableOn ℂ (Φ ∘ ofComplex) {z : ℂ | 0 < z.im} := by
    intro z hz
    have h := hΦ ⟨z, hz⟩
    exact h.differentiableAt.differentiableWithinAt
  have ha : AnalyticAt ℂ (Φ ∘ ofComplex) (τ : ℂ) :=
    hd.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  exact ha.cexp

theorem meromorphicOrderAt_exp_comp {Φ : ℍ → ℂ} {f : ℍ → ℂ}
    (hΦ : ∀ τ : ℍ, HasDerivAt (Φ ∘ ofComplex) (f τ) (τ : ℂ)) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => Complex.exp (Φ (ofComplex z))) (τ : ℂ) = 0 := by
  have ha := analyticAt_exp_comp hΦ τ
  rw [ha.meromorphicOrderAt_eq]
  have h0 : analyticOrderAt (fun z : ℂ => Complex.exp (Φ (ofComplex z))) (τ : ℂ) = 0 := by
    rw [ha.analyticOrderAt_eq_zero]
    exact Complex.exp_ne_zero _
  simp [h0]

end ModularCurve.AbelSufficiencyAssemblyH

open ModularCurve.AbelSufficiencyAssemblyH in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0)
    (hΛ : (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
      ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
    ∃ F : UpperHalfPlane → ℂ,
      (∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ)) ∧
      (∀ γ ∈ CohCarrier.GammaH M H, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) ∧
      (∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto (fun τ : UpperHalfPlane => F (σ • τ)) UpperHalfPlane.atImInfty (𝓝 L)) ∧
      ∀ τ : UpperHalfPlane, meromorphicOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ) =
        (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : WithTop ℤ) := by
  classical
  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

  obtain ⟨ω, hωΓ, hωcusp, hωres⟩ :=
    ModularCurve.ComplexPlaceDictionaryOf.exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH
      M H D c hdeg

  obtain ⟨F₁, χ, hmer, hχ, hcusp₁, hord⟩ :=
    ModularCurve.exists_meromorphic_smul_eq_mul_of_slashInvariant_residue
      (CohCarrier.GammaH M H)
      (fun τ => (D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ)) ω hωΓ hωcusp hωres

  obtain ⟨f, hf⟩ :=
    ModularCurve.ComplexPlaceDictionaryOf.exists_cuspForm_mul_exp_periodOf_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH
      M H D c hdeg hΛ F₁ χ hmer hχ hcusp₁ hord

  obtain ⟨Φ, hΦ⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf (CohCarrier.GammaH M H) f
  have hperiod : ∀ γ : CohCarrier.GammaH M H, ∀ τ : ℍ,
      Φ ((γ : SL(2, ℤ)) • τ) = Φ τ + ModularCurve.periodOf (CohCarrier.GammaH M H) γ f := by
    intro γ τ
    have h1 := hΦ.2.2.1.sub_eq_period γ τ
    have h2 := ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf (CohCarrier.GammaH M H) f hΦ γ
    have h3 : hΦ.2.2.1.period γ = Φ ((γ : SL(2, ℤ)) • UpperHalfPlane.I) - Φ UpperHalfPlane.I :=
      rfl
    rw [h2, ← h3, ← h1]; ring

  refine ⟨fun τ => F₁ τ * Complex.exp (Φ τ), ?_, ?_, ?_, ?_⟩
  · intro τ
    exact (hmer τ).mul (analyticAt_exp_comp hΦ.1 τ).meromorphicAt
  · intro γ hγ τ
    have hχ' := hχ ⟨γ, hγ⟩ τ
    have hp := hperiod ⟨γ, hγ⟩ τ
    have hf' := hf ⟨γ, hγ⟩
    show F₁ (γ • τ) * Complex.exp (Φ (γ • τ)) = F₁ τ * Complex.exp (Φ τ)
    rw [hχ', hp, Complex.exp_add]
    calc χ ⟨γ, hγ⟩ * F₁ τ *
          (Complex.exp (Φ τ) * Complex.exp (ModularCurve.periodOf (CohCarrier.GammaH M H) ⟨γ, hγ⟩ f))
        = (χ ⟨γ, hγ⟩ * Complex.exp (ModularCurve.periodOf (CohCarrier.GammaH M H) ⟨γ, hγ⟩ f)) *
            (F₁ τ * Complex.exp (Φ τ)) := by ring
      _ = F₁ τ * Complex.exp (Φ τ) := by rw [hf', one_mul]
  · intro σ
    obtain ⟨L₁, hL₁, hT₁⟩ := hcusp₁ σ
    obtain ⟨L₂, hT₂⟩ := hΦ.2.2.2 σ
    refine ⟨L₁ * Complex.exp L₂, mul_ne_zero hL₁ (Complex.exp_ne_zero _), ?_⟩
    exact hT₁.mul ((Complex.continuous_exp.tendsto L₂).comp hT₂)
  · intro τ
    have h := fun_meromorphicOrderAt_mul (hmer τ) (analyticAt_exp_comp hΦ.1 τ).meromorphicAt
    rw [h, hord τ, meromorphicOrderAt_exp_comp hΦ.1 τ, add_zero]
