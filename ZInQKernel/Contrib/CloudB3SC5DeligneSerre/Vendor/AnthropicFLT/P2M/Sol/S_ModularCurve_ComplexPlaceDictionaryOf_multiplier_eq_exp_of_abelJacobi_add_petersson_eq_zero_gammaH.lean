/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_multiplier_eq_exp_of_abelJacobi_add_petersson_eq_zero_gammaH (git blob 7780543d04c9a48c94e07bdc5aebc3466e504374, sha256 ab4a915c46f78d34ec577a51175bd4eef533150f6aaf9bf87f963ecacda50891).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer_gammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_multiplier_eq_exp_of_periodAlongOf_add_petersson_mem_periodLatticeOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve.ComplexPlaceDictionaryOf
end ModularCurve.ComplexPlaceDictionaryOf
namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_multiplier_eq_exp_of_abelJacobi_add_petersson_eq_zero_gammaH

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

namespace ModularCurve
export _root_.ModularCurve (ComplexPlaceDictionaryOf Gamma1_le_GammaH xHFunctionField periodAlongOf periodOf periodLatticeOf period ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer_gammaH exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf multiplier_eq_exp_of_periodAlongOf_add_petersson_mem_periodLatticeOf)
namespace ComplexPlaceDictionaryOf
export _root_.ModularCurve.ComplexPlaceDictionaryOf (ramification pt pt_eq_pt_iff_gammaH two_mul_ramification_eq_card_stabilizer_gammaH)
namespace MultExpH
open _root_.ModularCurve.ComplexPlaceDictionaryOf
open _root_.ModularCurve

abbrev Gpm (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup SL(2, ℤ) :=
  CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))

open Classical in

def D97 : Prop :=
  ∀ (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (_hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (_hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) (c : UpperHalfPlane →₀ ℤ)
    (F : ℍ → ℂ) (χ : Γ → ℂ) (f : CuspForm Γ 2)
    (_hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (_hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (_hunit : ∀ γ : Γ, ‖χ γ‖ = 1)
    (_hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (_hord : ∀ τ : ℍ, ∃ n : ℤ,
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) ∧
        2 * n = (Nat.card (MulAction.stabilizer Γ τ) : ℤ) *
          c.sum (fun τ' m => if ∃ γ : Γ, (γ : SL(2, ℤ)) • τ' = τ then m else 0))
    (_hf : ∃ Λ ∈ ModularCurve.periodLatticeOf Γ, ∀ g : CuspForm Γ 2,
      (c.sum fun τ n => n • ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ) g +
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
          UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = Λ g),
    ∀ γ : Γ, χ γ = Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ f).re : ℂ))

theorem mapDomain_apply_eq_sum {α β M : Type*} [AddCommMonoid M] [DecidableEq β]
    (p : α → β) (c : α →₀ M) (b : β) :
    Finsupp.mapDomain p c b = c.sum (fun a m => if p a = b then m else 0) := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finsupp.sum_congr ?_
  intro a _
  rw [Finsupp.single_apply]

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

theorem main (hD97 : D97) (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (F : ℍ → ℂ) (χ : CohCarrier.GammaH M H → ℂ)
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CohCarrier.GammaH M H) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hunit : ∀ γ : CohCarrier.GammaH M H, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : WithTop ℤ))
    (hf : ∀ g : CuspForm (CohCarrier.GammaH M H) 2,
      (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) g +
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))), UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = 0) :
    ∀ γ : CohCarrier.GammaH M H,
      χ γ = Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf (CohCarrier.GammaH M H) γ f).re : ℂ)) := by
  classical

  haveI hfi : (CohCarrier.GammaH M H).FiniteIndex :=
    (CongruenceSubgroup.isCongruenceSubgroup_trans _ _ (ModularCurve.Gamma1_le_GammaH M H)
      (CongruenceSubgroup.Gamma1_is_congruence M)).finiteIndex
  haveI : (Gpm M H).FiniteIndex := Subgroup.finiteIndex_of_le (K := (Gpm M H)) (H := (CohCarrier.GammaH M H)) le_sup_left
  have hneg : (-1 : SL(2, ℤ)) ∈ (Gpm M H) := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hcong : CongruenceSubgroup.IsCongruenceSubgroup (Gpm M H) :=
    CongruenceSubgroup.isCongruenceSubgroup_trans _ _
      ((ModularCurve.Gamma1_le_GammaH M H).trans le_sup_left) (CongruenceSubgroup.Gamma1_is_congruence M)

  obtain ⟨e, he₁, he₂, he₃, he₄, he₅, he₆⟩ :=
    ModularCurve.exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf (CohCarrier.GammaH M H)

  have hmem : ∀ γ : (Gpm M H), ((γ : SL(2, ℤ)) ∈ (CohCarrier.GammaH M H)) ∨ (-(γ : SL(2, ℤ)) ∈ (CohCarrier.GammaH M H)) := fun γ =>
    (mem_sup_zpowers_neg_one_iff (CohCarrier.GammaH M H) γ).mp γ.2
  let χ' : (Gpm M H) → ℂ := fun γ =>
    if h : (γ : SL(2, ℤ)) ∈ (CohCarrier.GammaH M H) then χ ⟨γ, h⟩ else χ ⟨-(γ : SL(2, ℤ)), (hmem γ).resolve_left h⟩
  have hχ' : ∀ (γ : (Gpm M H)) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ' γ * F τ := by
    intro γ τ
    by_cases h : (γ : SL(2, ℤ)) ∈ (CohCarrier.GammaH M H)
    · simp only [χ', dif_pos h]
      exact hχ ⟨γ, h⟩ τ
    · simp only [χ', dif_neg h]
      have h2 : (γ : SL(2, ℤ)) • τ = (-(γ : SL(2, ℤ))) • τ := by
        rw [ModularGroup.SL_neg_smul]
      rw [h2]
      exact hχ ⟨-(γ : SL(2, ℤ)), (hmem γ).resolve_left h⟩ τ
  have hunit' : ∀ γ : (Gpm M H), ‖χ' γ‖ = 1 := by
    intro γ
    by_cases h : (γ : SL(2, ℤ)) ∈ (CohCarrier.GammaH M H)
    · simp only [χ', dif_pos h]; exact hunit _
    · simp only [χ', dif_neg h]; exact hunit _

  set f' : CuspForm (Gpm M H) 2 := e.symm f with hf'
  have hcoe : (⇑f' : ℍ → ℂ) = ⇑f := funext fun τ => he₂ f τ

  have horb : ∀ τ' τ : ℍ, (∃ γ ∈ (CohCarrier.GammaH M H), γ • τ' = τ) ↔ ∃ γ : (Gpm M H), (γ : SL(2, ℤ)) • τ' = τ := by
    intro τ' τ
    constructor
    · rintro ⟨γ, hγ, h⟩
      exact ⟨⟨γ, Subgroup.mem_sup_left hγ⟩, h⟩
    · rintro ⟨γ, h⟩
      rcases hmem γ with h1 | h1
      · exact ⟨γ, h1, h⟩
      · refine ⟨-(γ : SL(2, ℤ)), h1, ?_⟩
        rw [ModularGroup.SL_neg_smul]; exact h

  have hord' : ∀ τ : ℍ, ∃ n : ℤ,
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) ∧
        2 * n = (Nat.card (MulAction.stabilizer (Gpm M H) τ) : ℤ) *
          c.sum (fun τ' m => if ∃ γ : (Gpm M H), (γ : SL(2, ℤ)) • τ' = τ then m else 0) := by
    intro τ
    refine ⟨(D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ), hord τ, ?_⟩
    have hram : (2 : ℤ) * (D.ramification τ : ℤ) = (Nat.card (MulAction.stabilizer (Gpm M H) τ) : ℤ) := by
      exact_mod_cast ModularCurve.ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer_gammaH M H D τ
    have hfib : Finsupp.mapDomain D.pt c (D.pt τ) =
        c.sum (fun τ' m => if ∃ γ : (Gpm M H), (γ : SL(2, ℤ)) • τ' = τ then m else 0) := by
      rw [mapDomain_apply_eq_sum]
      refine Finsupp.sum_congr ?_
      intro τ' _
      have hiff : D.pt τ' = D.pt τ ↔ ∃ γ : (Gpm M H), (γ : SL(2, ℤ)) • τ' = τ :=
        (ModularCurve.ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH M H D τ' τ).trans (horb τ' τ)
      by_cases h : ∃ γ : (Gpm M H), (γ : SL(2, ℤ)) • τ' = τ
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
    rw [hfib, ← mul_assoc, hram]

  have hf'' : ∃ Λ ∈ ModularCurve.periodLatticeOf (Gpm M H), ∀ g : CuspForm (Gpm M H) 2,
      (c.sum fun τ n => n • ModularCurve.periodAlongOf (Gpm M H) UpperHalfPlane.I τ) g +
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet (Gpm M H),
          UpperHalfPlane.petersson 2 ⇑f' ⇑g τ) = Λ g := by
    refine ⟨0, Submodule.zero_mem _, fun g => ?_⟩
    have h1 : (c.sum fun τ n => n • ModularCurve.periodAlongOf (Gpm M H) UpperHalfPlane.I τ) g =
        (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) (e g) := by
      simp only [Finsupp.sum, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← he₃ UpperHalfPlane.I τ, LinearMap.dualMap_apply]
      rfl
    have h2 : (fun τ => UpperHalfPlane.petersson 2 ⇑f' ⇑g τ) =
        fun τ => UpperHalfPlane.petersson 2 ⇑f ⇑(e g) τ := by
      funext τ
      rw [hcoe]
      have : (⇑(e g) : ℍ → ℂ) = ⇑g := funext fun τ => he₁ g τ
      rw [this]
    rw [h1, show (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet (Gpm M H), UpperHalfPlane.petersson 2 ⇑f' ⇑g τ)
        = ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet (Gpm M H), UpperHalfPlane.petersson 2 ⇑f ⇑(e g) τ from by
          rw [h2], hf (e g), LinearMap.zero_apply]

  have key := hD97 (Gpm M H) hneg hcong c F χ' f' hF hχ' hunit' hcusp hord' hf''
  intro γ
  have hγ' : ((γ : SL(2, ℤ))) ∈ (Gpm M H) := Subgroup.mem_sup_left γ.2
  have h := key ⟨γ, hγ'⟩
  have hχγ : χ' ⟨γ, hγ'⟩ = χ γ := by
    simp only [χ', dif_pos (show ((⟨(γ : SL(2, ℤ)), hγ'⟩ : (Gpm M H)) : SL(2, ℤ)) ∈ (CohCarrier.GammaH M H) from γ.2)]
  have hper : ModularCurve.periodOf (Gpm M H) ⟨γ, hγ'⟩ f' = ModularCurve.periodOf (CohCarrier.GammaH M H) γ f := by
    rw [← he₄ γ, LinearMap.dualMap_apply, hf']
    show ModularCurve.periodOf (CohCarrier.GammaH M H) γ (e (e.symm f)) = _
    rw [LinearEquiv.apply_symm_apply]
  rw [hχγ, hper] at h
  exact h

end ModularCurve.ComplexPlaceDictionaryOf.MultExpH

open ModularCurve.ComplexPlaceDictionaryOf.MultExpH in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0)
    (F : ℍ → ℂ) (χ : CohCarrier.GammaH M H → ℂ)
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CohCarrier.GammaH M H) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hunit : ∀ γ : CohCarrier.GammaH M H, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : WithTop ℤ))
    (hf : ∀ g : CuspForm (CohCarrier.GammaH M H) 2,
      (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) g +
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))), UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = 0) :
    ∀ γ : CohCarrier.GammaH M H,
      χ γ = Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf (CohCarrier.GammaH M H) γ f).re : ℂ)) :=
  main ModularCurve.multiplier_eq_exp_of_periodAlongOf_add_petersson_mem_periodLatticeOf
    M H D c F χ f hF hχ hunit hcusp hord hf
