/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH (git blob 6476d85c654c4ca56d5bf1b51d131477694495d7, sha256 20f2413da73e2d752cbd8071fa88e098c6279a166d732bf909c4426e82e37b3f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH.ModularCurve
end P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH.ModularCurve
namespace P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH.ModularCurve.PetLatTransport
end P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH.ModularCurve.PetLatTransport

namespace P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

namespace ModularCurve
export _root_.ModularCurve (Gamma1_le_GammaH periodOf periodLatticeOf petersson_mem_periodLatticeOf_iff_re_periodOf_int exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf)
namespace PetLatTransport
open _root_.ModularCurve

theorem neg_one_zpow_eq_or (k : ℤ) : (-1 : SL(2, ℤ)) ^ k = 1 ∨ (-1 : SL(2, ℤ)) ^ k = -1 := by
  rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    rw [← two_mul, zpow_mul, zpow_ofNat, neg_one_sq, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_ofNat, neg_one_sq, one_zpow, one_mul, zpow_one]

scoped instance zpowers_neg_one_normal : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  rcases neg_one_zpow_eq_or k with h | h
  · rw [h, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · rw [h, mul_neg_one, neg_mul, mul_inv_cancel]
    exact Subgroup.mem_zpowers _

theorem mem_or_neg_mem_of_mem_sup {Γ : Subgroup SL(2, ℤ)} {x : SL(2, ℤ)}
    (hx : x ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) : x ∈ Γ ∨ -x ∈ Γ := by
  rw [Subgroup.mem_sup_of_normal_right] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rcases neg_one_zpow_eq_or k with h | h
  · exact Or.inl (by rw [h, mul_one]; exact hy)
  · exact Or.inr (by rw [h, mul_neg_one, neg_neg]; exact hy)

theorem transport (Γ Γ' : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hΓ' : Γ' = Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)))
    (hcong : CongruenceSubgroup.IsCongruenceSubgroup Γ')
    (f : CuspForm Γ 2) :
    (∃ Λ ∈ ModularCurve.periodLatticeOf Γ, ∀ g : CuspForm Γ 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ',
          UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = Λ g) ↔
      ∀ γ : Γ, ∃ m : ℤ, (ModularCurve.periodOf Γ γ f).re = m := by
  classical
  subst hΓ'
  haveI : ((Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))).FiniteIndex :=
    Subgroup.finiteIndex_of_le (le_sup_left : Γ ≤ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)))
  have hneg : (-1 : SL(2, ℤ)) ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨e, he, hesymm, -, heper, hnegper, hlat⟩ :=
    ModularCurve.exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf Γ
  have key := ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int
    (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) hcong hneg (e.symm f)
  have hcoe_f : (⇑(e.symm f) : ℍ → ℂ) = ⇑f := funext (hesymm f)
  have hper : ∀ γ : Γ, ModularCurve.periodOf Γ γ f =
      ModularCurve.periodOf (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) ⟨γ, Subgroup.mem_sup_left γ.2⟩ (e.symm f) := by
    intro γ
    have h := congrArg (fun φ => φ (e.symm f)) (heper γ)
    simpa [LinearMap.dualMap_apply] using h
  constructor
  · rintro ⟨Λ, hΛ, hval⟩
    have hL := key.mp ⟨e.toLinearMap.dualMap Λ, (hlat Λ).mp hΛ, fun g' => by
      rw [LinearMap.dualMap_apply, LinearEquiv.coe_coe, ← hval (e g'), hcoe_f,
        show (⇑(e g') : ℍ → ℂ) = ⇑g' from funext (he g')]⟩
    intro γ
    obtain ⟨m, hm⟩ := hL ⟨γ, Subgroup.mem_sup_left γ.2⟩
    exact ⟨m, by rw [hper]; exact hm⟩
  · intro hint
    have hint' : ∀ γ' : ↥(Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))), ∃ m : ℤ,
        (ModularCurve.periodOf (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) γ' (e.symm f)).re = m := by
      intro γ'
      rcases mem_or_neg_mem_of_mem_sup γ'.2 with h | h
      · obtain ⟨m, hm⟩ := hint ⟨γ', h⟩
        refine ⟨m, ?_⟩
        rw [hper] at hm
        convert hm using 3
      · obtain ⟨m, hm⟩ := hint ⟨-(γ' : SL(2, ℤ)), h⟩
        refine ⟨m, ?_⟩
        rw [hper] at hm
        have h2 := hnegper (γ' : SL(2, ℤ)) γ'.2 (Subgroup.mem_sup_left h)
        have h2' := congrArg (fun φ => (φ (e.symm f)).re) h2
        simp only [Subtype.coe_eta] at h2'
        rw [← h2']
        convert hm using 3
    obtain ⟨Λ', hΛ', hval'⟩ := key.mpr hint'
    refine ⟨e.symm.toLinearMap.dualMap Λ', ?_, fun g => ?_⟩
    · rw [hlat]
      convert hΛ' using 1
      ext g'
      simp [LinearMap.dualMap_apply]
    · rw [LinearMap.dualMap_apply, LinearEquiv.coe_coe, ← hval' (e.symm g), hcoe_f,
        show (⇑(e.symm g) : ℍ → ℂ) = ⇑g from funext (hesymm g)]

end ModularCurve.PetLatTransport
open scoped _root_.P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH.ModularCurve _root_.P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH.ModularCurve.PetLatTransport
open scoped _root_.P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH.ModularCurve

open ModularCurve.PetLatTransport in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) 2) :
    (∃ Λ ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H), ∀ g : CuspForm (CohCarrier.GammaH M H) 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))), UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = Λ g) ↔
      ∀ γ : CohCarrier.GammaH M H, ∃ m : ℤ, (ModularCurve.periodOf (CohCarrier.GammaH M H) γ f).re = m := by
  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  exact transport (CohCarrier.GammaH M H) _ rfl
    (CongruenceSubgroup.isCongruenceSubgroup_trans _ _ le_sup_left
      (CongruenceSubgroup.isCongruenceSubgroup_trans _ _ (ModularCurve.Gamma1_le_GammaH M H)
        (CongruenceSubgroup.Gamma1_is_congruence M))) f
