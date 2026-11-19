/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_sum_residue_eq_zero_of_slashInvariant_gammaH (git blob cb98e6556c6c9417b0d4d528bffd353cf6e896a1, sha256 9b5765ff0da38f71733ea45e7062312202327e2307fbd167d73e17e2254e046b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer_gammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_UpperHalfPlane_sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve.ComplexPlaceDictionaryOf
end ModularCurve.ComplexPlaceDictionaryOf
namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_sum_residue_eq_zero_of_slashInvariant_gammaH

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

namespace ModularCurve
export _root_.ModularCurve (ComplexPlaceDictionaryOf laurentBaseChange Gamma1_le_GammaH xHFunctionField ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer_gammaH)
namespace ComplexPlaceDictionaryOf
export _root_.ModularCurve.ComplexPlaceDictionaryOf (pt_smul_of_mem ramification ramification_pos pt pt_eq_pt_iff_gammaH two_mul_ramification_eq_card_stabilizer_gammaH)
namespace SumResH
open _root_.ModularCurve.ComplexPlaceDictionaryOf
open _root_.ModularCurve

theorem mem_sup_zpowers_neg_one_iff (Γ : Subgroup SL(2, ℤ)) (γ : SL(2, ℤ)) :
    γ ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ γ ∈ Γ ∨ -γ ∈ Γ := by
  haveI : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hc : g * (-1 : SL(2, ℤ)) ^ k * g⁻¹ = (-1) ^ k := by
      rw [((Commute.neg_one_right g).zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hc]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  have hz : ∀ a : SL(2, ℤ), a ∈ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ a = 1 ∨ a = -1 := by
    intro a
    constructor
    · intro ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rcases Int.even_or_odd k with hk | hk
      · left; rw [hk.neg_one_zpow]
      · right; rw [hk.neg_one_zpow]
    · rintro (rfl | rfl)
      · exact one_mem _
      · exact Subgroup.mem_zpowers _
  constructor
  · intro h
    have h' : γ ∈ ((Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)) := h
    rw [Subgroup.mul_normal] at h'
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp h'
    rcases (hz b).mp hb with rfl | rfl
    · left; simpa using ha
    · right; simpa using ha
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have : γ = -γ * (-1) := by simp
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left h) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem slash_two_neg (ω : ℍ → ℂ) (γ : SL(2, ℤ)) : ω ∣[(2 : ℤ)] (-γ) = ω ∣[(2 : ℤ)] γ := by
  funext τ
  rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul]
  congr 1
  have hden : denom ((-γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = -denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ := by
    rw [ModularGroup.denom_apply, ModularGroup.denom_apply]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
    push_cast
    ring
  rw [hden, Even.neg_zpow (by decide : Even (-2 : ℤ))]

end ModularCurve.ComplexPlaceDictionaryOf.SumResH

open ModularCurve.ComplexPlaceDictionaryOf.SumResH in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (ω : ℍ → ℂ) (r : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) →₀ ℂ)
    (hΓ : ∀ γ ∈ CohCarrier.GammaH M H, ω ∣[(2 : ℤ)] γ = ω)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
        (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im))
    (hsupp : ∀ P ∈ r.support, ∃ τ : ℍ, D.pt τ = P)
    (hloc : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) =
          (D.ramification τ : ℂ) * r (D.pt τ) / (z - τ) + g z) :
    r.sum (fun _ a => a) = 0 := by
  classical
  set Γ : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) with hΓdef
  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    (CongruenceSubgroup.isCongruenceSubgroup_trans _ _ (ModularCurve.Gamma1_le_GammaH M H)
      (CongruenceSubgroup.Gamma1_is_congruence M)).finiteIndex
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le (K := Γ) (H := CohCarrier.GammaH M H) le_sup_left

  have hΓ' : ∀ γ ∈ Γ, ω ∣[(2 : ℤ)] γ = ω := by
    intro γ hγ
    rcases (mem_sup_zpowers_neg_one_iff _ γ).mp hγ with h | h
    · exact hΓ γ h
    · rw [← neg_neg γ, slash_two_neg]
      exact hΓ (-γ) h
  have hpt : ∀ γ ∈ Γ, ∀ τ : ℍ, D.pt (γ • τ) = D.pt τ := by
    intro γ hγ τ
    rcases (mem_sup_zpowers_neg_one_iff _ γ).mp hγ with h | h
    · exact D.pt_smul_of_mem h τ
    · have hγ' : γ = (-1 : SL(2, ℤ)) * (-γ) := by simp
      rw [hγ', mul_smul, ModularGroup.SL_neg_smul, one_smul]
      exact D.pt_smul_of_mem h τ

  choose! lift hlift using hsupp
  set c : ℍ → ℂ := fun τ => (D.ramification τ : ℂ) * r (D.pt τ) with hc
  set S : Finset ℍ := r.support.image lift with hS_def
  have hloc' : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = c τ / (z - τ) + g z := by
    intro τ
    obtain ⟨g, hg, hω⟩ := hloc τ
    exact ⟨g, hg, hω⟩
  have hS : ∀ τ : ℍ, c τ ≠ 0 → ∃ σ ∈ S, ∃ γ ∈ Γ, γ • σ = τ := by
    intro τ hτ
    have hr : r (D.pt τ) ≠ 0 := by
      intro h
      exact hτ (by simp [hc, h])
    have hmem : D.pt τ ∈ r.support := Finsupp.mem_support_iff.2 hr
    refine ⟨lift (D.pt τ), Finset.mem_image_of_mem _ hmem, ?_⟩
    have hptl : D.pt (lift (D.pt τ)) = D.pt τ := hlift _ hmem
    obtain ⟨γ, hγ, hγe⟩ :=
      (ModularCurve.ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH M H D (lift (D.pt τ)) τ).1 hptl
    exact ⟨γ, Subgroup.mem_sup_left hγ, hγe⟩
  have hinj : ∀ σ ∈ S, ∀ σ' ∈ S, ∀ γ ∈ Γ, γ • σ = σ' → σ = σ' := by
    intro σ hσ σ' hσ' γ hγ hγσ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hσ
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hσ'
    have h1 : D.pt (γ • lift P) = D.pt (lift P) := hpt γ hγ (lift P)
    rw [hγσ, hlift P' hP', hlift P hP] at h1
    rw [h1]
  have key := UpperHalfPlane.sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant
    Γ ω c S hΓ' hcusp hloc' hS hinj
  have hlift_inj : Set.InjOn lift (r.support : Set _) := by
    intro P hP P' hP' h
    have := congrArg D.pt h
    rwa [hlift P hP, hlift P' hP'] at this
  rw [hS_def, Finset.sum_image hlift_inj] at key
  have hterm : ∀ P ∈ r.support,
      c (lift P) / (Nat.card (MulAction.stabilizer Γ (lift P)) : ℂ) = r P / 2 := by
    intro P hP
    have hcard := ModularCurve.ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer_gammaH
      M H D (lift P)
    have he : (D.ramification (lift P) : ℂ) ≠ 0 := by
      exact_mod_cast (D.ramification_pos (lift P)).ne'
    rw [hΓdef, ← hcard, hc]
    simp only [hlift P hP]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div] at key
  have hsum : ∑ P ∈ r.support, r P = 0 := by
    rcases div_eq_zero_iff.1 key with h | h
    · exact h
    · norm_num at h
  simpa [Finsupp.sum] using hsum
