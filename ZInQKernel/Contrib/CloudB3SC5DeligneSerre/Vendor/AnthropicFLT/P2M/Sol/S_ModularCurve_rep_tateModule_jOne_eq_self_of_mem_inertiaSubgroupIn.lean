/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn (git blob e3c49fbcca8719368bfa5d667d9807e5004836f7, sha256 cc06ac705842fe11eeab5a164a7159a9e0ef9003258d27cdd16d83c487173e20).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_TateModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpReductionModL
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn.ModularCurve
end P2MW.S_ModularCurve_rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn.ModularCurve
namespace CongruenceSubgroup
end CongruenceSubgroup

namespace P2MW.S_ModularCurve_rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn

set_option autoImplicit false

namespace ModularCurve
export _root_.ModularCurve (qExpFunctionFieldC JOne laurentBaseChange GammaH_bot ReductionInputsQExpModL reductionQExpModL exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero)
namespace JOneGoodReduction
open _root_.ModularCurve

open _root_.ModularCurve
open _root_.P2MW.S_ModularCurve_rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn.ModularCurve
open _root_.CongruenceSubgroup

set_option synthInstance.maxHeartbeats 1600000 in

theorem reductionInputsQExpModL_of_eq (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ : CohCarrier.GammaH M H = Γ)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    ReductionInputsQExpModL A Γ := by
  subst hΓ
  exact (exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd M H hℓM A hA).2

set_option synthInstance.maxHeartbeats 1600000 in

theorem reductionQExpModL_smul_eq_of_eq (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ : CohCarrier.GammaH M H = Γ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (h : ReductionInputsQExpModL A Γ)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    (z : AlgebraicCurve.Pic0 (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) :
    reductionQExpModL A Γ (τ • z) = reductionQExpModL A Γ z := by
  subst hΓ
  exact reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn M H A h τ hτ z

set_option synthInstance.maxHeartbeats 1600000 in

theorem eq_zero_of_reductionQExpModL_eq_zero_of_eq (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ : CohCarrier.GammaH M H = Γ)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (h : ReductionInputsQExpModL A Γ)
    (m : ℕ) (hm : ¬ ℓ ∣ m)
    (z : AlgebraicCurve.Pic0 (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))
    (hmz : m • z = 0) (hz : reductionQExpModL A Γ z = 0) :
    z = 0 := by
  subst hΓ
  exact eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero M H hℓM A hA h m hm z hmz hz

set_option synthInstance.maxHeartbeats 1600000 in

theorem smul_eq_self_of_nsmul_eq_zero_of_eq (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ : CohCarrier.GammaH M H = Γ)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (m : ℕ) (hm : ¬ ℓ ∣ m)
    (z : AlgebraicCurve.Pic0 (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))
    (hmz : m • z = 0) :
    σ • z = z := by

  have hred : ReductionInputsQExpModL A Γ := reductionInputsQExpModL_of_eq M H Γ hΓ hℓM A hA

  rw [← sub_eq_zero]
  refine eq_zero_of_reductionQExpModL_eq_zero_of_eq M H Γ hΓ hℓM A hA hred m hm (σ • z - z) ?_ ?_
  · rw [nsmul_sub, smul_comm, hmz, sub_zero]
    exact smul_zero (A := AlgebraicCurve.Pic0 (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) σ
  · rw [map_sub, reductionQExpModL_smul_eq_of_eq M H Γ hΓ A hred σ hσ z, sub_self]

end ModularCurve.JOneGoodReduction

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn.ModularCurve CongruenceSubgroup in

theorem solution (M p : ℕ) [NeZero M]
    [Fact p.Prime]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓMp : ¬ ℓ ∣ M * p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : TateModule p (ModularCurve.JOne M)) :
    TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x = x := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓM : ¬ ℓ ∣ M := fun h => hℓMp (dvd_mul_of_dvd_left h p)
  have hℓp : ¬ ℓ ∣ p := fun h => hℓMp (dvd_mul_of_dvd_right h M)

  refine Subtype.ext (funext fun n => ?_)
  rw [TateModule.rep_apply]
  set z : JOne M := (x : ℕ → JOne M) n with hz_def
  have hz : (p ^ n : ℕ) • z = 0 := by
    rw [← natCast_zsmul]
    exact TateModule.torsion x n
  have hℓpn : ¬ ℓ ∣ p ^ n := fun h => hℓp (hℓ.dvd_of_dvd_pow h)
  exact ModularCurve.JOneGoodReduction.smul_eq_self_of_nsmul_eq_zero_of_eq M ⊥ (Gamma1 M)
    (GammaH_bot M) hℓM A hA σ hσ (p ^ n) hℓpn z hz
