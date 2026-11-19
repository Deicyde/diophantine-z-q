/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_frobeniusQuadratic_tateModule_jOne (git blob 94d60855be6e84a60c0f8439258fbc644d2ce018, sha256 a48cea4ae930798fd06afce5d41277c2baf3ee79bff4c3ea68b4d48f969a2b5d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_TateModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpReductionModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpFrobeniusModL
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_ReductionMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ValuationSubring_ReduceAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_heckeDiamondInputsAll
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_frobeniusQuadratic_tateModule_jOne.ModularCurve
end P2MW.S_ModularCurve_frobeniusQuadratic_tateModule_jOne.ModularCurve
namespace AlgebraicCurve
end AlgebraicCurve
namespace IntermediateField
end IntermediateField

namespace P2MW.S_ModularCurve_frobeniusQuadratic_tateModule_jOne

set_option autoImplicit false

noncomputable section

namespace ModularCurve
export _root_.ModularCurve (HeckeAlgOne heckeGenOne diamondGen heckeOperatorOneBar HeckeDiamondCommuteBar HeckeDiamondInputsAll heckeModuleOneBar heckeModuleOneBar_heckeGenOne_smul heckeModuleOneBar_diamondGen_smul qExpFunctionFieldC JOne JOneC arithmeticRingAut coe_arithmeticRingAut_apply arithmeticRingAut_algebraMap arithmeticGalois galois_smul_pic0_def coeffMap_coeffMap coeffMap_id coeffMap_congr coeffEmb coeffMap_coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange IsBaseChangeAutOf baseChangeAut isBaseChangeAutOf_baseChangeAut baseChangeAut_of_not diamondAutBar diamondOneBar diamondOneBar_apply ReductionInputsQExpModL reductionQExpModL qExpFrobeniusPushforwardModL qExpFrobeniusPullbackModL GammaH_bot xHFunctionFieldC JH exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd reductionQExpModL_gammaH_smul_of_isFrobeniusAt reductionQExpModL_gamma1_heckeOperatorOneBar heckeDiamondInputsAll eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental)
namespace A2JOneFrobQuad
open _root_.ModularCurve

open _root_.ModularCurve
open _root_.P2MW.S_ModularCurve_frobeniusQuadratic_tateModule_jOne.ModularCurve
open _root_.AlgebraicCurve
open _root_.IntermediateField

section Commute

variable {L : Type*} [Field L] [Algebra ℚ L] {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

def conjAlgHom (σ : L ≃ₐ[ℚ] L) (τ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀) :
    laurentBaseChange L F₀ →ₐ[L] laurentBaseChange L F₀ :=
  { (((arithmeticRingAut F₀ σ.symm).trans (τ : laurentBaseChange L F₀ ≃+* laurentBaseChange L F₀)).trans
      (arithmeticRingAut F₀ σ)).toRingHom with
    commutes' := fun c => by
      show arithmeticRingAut F₀ σ (τ (arithmeticRingAut F₀ σ.symm (algebraMap L _ c))) = algebraMap L _ c
      rw [arithmeticRingAut_algebraMap, AlgEquiv.commutes, arithmeticRingAut_algebraMap,
        AlgEquiv.apply_symm_apply] }

theorem conjAlgHom_apply (σ : L ≃ₐ[ℚ] L) (τ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀)
    (x : laurentBaseChange L F₀) :
    conjAlgHom σ τ x = arithmeticRingAut F₀ σ (τ (arithmeticRingAut F₀ σ.symm x)) :=
  rfl

theorem arithmeticRingAut_comm_of_isBaseChangeAutOf {σ₀ : F₀ ≃ₐ[ℚ] F₀}
    {τ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀} (hτ : IsBaseChangeAutOf L σ₀ τ)
    (σ : L ≃ₐ[ℚ] L) (x : laurentBaseChange L F₀) :
    arithmeticRingAut F₀ σ (τ x) = τ (arithmeticRingAut F₀ σ x) := by

  have key : conjAlgHom σ τ = τ.toAlgHom := by
    refine IntermediateField.adjoin_algHom_ext L fun y hy => ?_
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    show arithmeticRingAut F₀ σ (τ (arithmeticRingAut F₀ σ.symm ⟨coeffEmb L y₀, _⟩)) = τ ⟨coeffEmb L y₀, _⟩

    have h1 : arithmeticRingAut F₀ σ.symm ⟨coeffEmb L y₀, coeffEmb_mem_laurentBaseChange L hy₀⟩ =
        ⟨coeffEmb L y₀, coeffEmb_mem_laurentBaseChange L hy₀⟩ :=
      Subtype.ext (coeffMap_coeffEmb σ.symm y₀)
    rw [h1]

    have h2 := hτ ⟨y₀, hy₀⟩
    refine Subtype.ext ?_
    rw [coe_arithmeticRingAut_apply, h2, coeffMap_coeffEmb]
  have h := congrArg (fun φ : laurentBaseChange L F₀ →ₐ[L] laurentBaseChange L F₀ =>
    φ (arithmeticRingAut F₀ σ x)) key
  simp only [conjAlgHom_apply, AlgEquiv.toAlgHom_apply] at h
  rw [← h]
  congr 2
  exact Subtype.ext (by
    rw [coe_arithmeticRingAut_apply, coe_arithmeticRingAut_apply, coeffMap_coeffMap,
      coeffMap_congr (g := RingHom.id L) (RingHom.ext fun a => σ.symm_apply_apply a), coeffMap_id])

theorem arithmeticGalois_mul_ofAlgAut_baseChangeAut (σ₀ : F₀ ≃ₐ[ℚ] F₀) (σ : L ≃ₐ[ℚ] L) :
    arithmeticGalois F₀ σ * SemilinearAut.ofAlgAut (baseChangeAut L σ₀) =
      SemilinearAut.ofAlgAut (baseChangeAut L σ₀) * arithmeticGalois F₀ σ := by
  rcases Classical.em
      (∃ τ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀, IsBaseChangeAutOf L σ₀ τ) with h | h
  · have hτ := isBaseChangeAutOf_baseChangeAut h
    refine Subtype.ext (Prod.ext (RingEquiv.ext fun x => ?_) ?_)
    · exact arithmeticRingAut_comm_of_isBaseChangeAutOf hτ σ x
    · show σ.toRingEquiv * 1 = 1 * σ.toRingEquiv
      rw [mul_one, one_mul]
  · rw [baseChangeAut_of_not h, show (AlgEquiv.refl : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀)
      = 1 from rfl, map_one, mul_one, one_mul]

end Commute

theorem smul_diamondOneBar (M d : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (z : JOne M) :
    σ • diamondOneBar M d z = diamondOneBar M d (σ • z) := by
  rw [diamondOneBar_apply, diamondOneBar_apply, galois_smul_pic0_def, galois_smul_pic0_def,
    ← mul_smul, ← mul_smul, diamondAutBar, arithmeticGalois_mul_ofAlgAut_baseChangeAut]

section Transport

variable (M : ℕ) [NeZero M] {ℓ : ℕ} [Fact ℓ.Prime]
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hℓM : ¬ ℓ ∣ M) (hA : A.LiesOverPrime ℓ)

include hℓM hA

set_option synthInstance.maxHeartbeats 1600000 in

theorem D1_gamma1 :
    (∃ x : qExpFunctionFieldC (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma1 M),
        Transcendental (IsLocalRing.ResidueField A) x ∧
          FiniteDimensional
            (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              ({x} : Set (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma1 M))))
            (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma1 M))) ∧
      ReductionInputsQExpModL A (CongruenceSubgroup.Gamma1 M) := by
  have h := exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd M ⊥ hℓM A hA
  rw [xHFunctionFieldC, GammaH_bot] at h
  exact h

set_option synthInstance.maxHeartbeats 1600000 in

theorem D2_gamma1 [CharP (IsLocalRing.ResidueField A) ℓ]
    (h : ReductionInputsQExpModL A (CongruenceSubgroup.Gamma1 M))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) (z : JOne M) :
    reductionQExpModL A (CongruenceSubgroup.Gamma1 M) (σ • z) =
      qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma1 M) ℓ
        (reductionQExpModL A (CongruenceSubgroup.Gamma1 M) z) := by
  have key : ∀ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ), Γ = CohCarrier.GammaH M ⊥ →
      ∀ (hΓ : ReductionInputsQExpModL A Γ)
        (w : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))),
        reductionQExpModL A Γ (σ • w) =
          qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A) Γ ℓ (reductionQExpModL A Γ w) := by
    rintro Γ rfl hΓ w
    exact reductionQExpModL_gammaH_smul_of_isFrobeniusAt M ⊥ hℓM A hA hΓ σ hσ w
  exact key (CongruenceSubgroup.Gamma1 M) (GammaH_bot M).symm h z

set_option synthInstance.maxHeartbeats 1600000 in

theorem D4_gamma1 (h : ReductionInputsQExpModL A (CongruenceSubgroup.Gamma1 M))
    (m : ℕ) (hm : ¬ ℓ ∣ m) (z : JOne M) (hmz : m • z = 0)
    (hz : reductionQExpModL A (CongruenceSubgroup.Gamma1 M) z = 0) : z = 0 := by
  have key : ∀ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ), Γ = CohCarrier.GammaH M ⊥ →
      ∀ (hΓ : ReductionInputsQExpModL A Γ)
        (w : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))),
        m • w = 0 → reductionQExpModL A Γ w = 0 → w = 0 := by
    rintro Γ rfl hΓ w hmw hw
    exact eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero M ⊥ hℓM A hA hΓ m hm w hmw hw
  exact key (CongruenceSubgroup.Gamma1 M) (GammaH_bot M).symm h z hmz hz

end Transport

theorem map_quadratic_eq_zero {J Jb : Type*} [AddCommGroup J] [AddCommGroup Jb]
    (red : J →+ Jb) (s T Dm : J → J) (Fr V : Jb → Jb) (ℓ : ℕ)
    (hcomm : ∀ w, s (Dm w) = Dm (s w))
    (hs : ∀ w, red (s w) = Fr (red w))
    (hT : ∀ w, red (T w) = Fr (red (Dm w)) + V (red w))
    (hE : ∀ y, V (Fr y) = ℓ • y) (z : J) :
    red (Dm (s (s z)) - T (s z) + ℓ • z) = 0 := by
  rw [map_add, map_sub, map_nsmul, ← hcomm, hs, hT, hs, hE]
  abel

set_option synthInstance.maxHeartbeats 1600000 in

theorem torsion_key (M : ℕ) [NeZero M] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) (hℓM : ¬ ℓ ∣ M)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ)
    (z : JOne M) (m : ℕ) (hm : ¬ ℓ ∣ m) (hz : m • z = 0) :
    diamondOneBar M ℓ (σ • σ • z) - heckeOperatorOneBar M ⟨ℓ, hℓ⟩ (σ • z) + ℓ • z = 0 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP (IsLocalRing.ResidueField A) ℓ := A.charP_residueField_of_liesOverPrime_def hℓ hA

  obtain ⟨hcurve, hred⟩ := D1_gamma1 M A hℓM hA

  refine D4_gamma1 M A hℓM hA hred m hm _ ?_ ?_
  ·
    have h0 : σ • (0 : JOne M) = 0 := smul_zero (A := JOne M) σ
    have h1 : m • diamondOneBar M ℓ (σ • σ • z) = 0 := by
      rw [← map_nsmul, smul_comm, smul_comm m σ z, hz, h0, h0, map_zero]
    have h2 : m • heckeOperatorOneBar M ⟨ℓ, hℓ⟩ (σ • z) = 0 := by
      rw [← map_nsmul, smul_comm, hz, h0, map_zero]
    have h3 : m • (ℓ • z) = 0 := by
      rw [smul_comm, hz, smul_zero]
    rw [nsmul_add, nsmul_sub, h1, h2, h3, sub_zero, add_zero]
  ·
    exact map_quadratic_eq_zero (reductionQExpModL A (CongruenceSubgroup.Gamma1 M)) (σ • ·)
      (heckeOperatorOneBar M ⟨ℓ, hℓ⟩) (diamondOneBar M ℓ)
      (qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma1 M) ℓ)
      (qExpFrobeniusPullbackModL (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma1 M) ℓ) ℓ
      (fun w => smul_diamondOneBar M ℓ σ w)
      (fun w => D2_gamma1 M A hℓM hA hred σ hσ w)
      (fun w => reductionQExpModL_gamma1_heckeOperatorOneBar M hℓM A hA (heckeDiamondInputsAll M) hred w)
      (fun y => qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental
        (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma1 M) hcurve y) z

end ModularCurve.A2JOneFrobQuad

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_frobeniusQuadratic_tateModule_jOne.ModularCurve in
theorem solution (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓMp : ¬ ℓ ∣ M * p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ)
    (x : TateModule p (ModularCurve.JOne M)) :
    letI := ModularCurve.heckeModuleOneBar M
    TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne (ModularCurve.diamondGen ℓ)
        (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
          (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x))
      - TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne
          (ModularCurve.heckeGenOne ⟨ℓ, hℓ⟩)
          (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
      + ℓ • x = 0 := by
  letI := ModularCurve.heckeModuleOneBar M
  have hℓM : ¬ ℓ ∣ M := fun h => hℓMp (dvd_mul_of_dvd_left h p)
  have hℓp : ¬ ℓ ∣ p := fun h => hℓMp (dvd_mul_of_dvd_right h M)

  refine Subtype.ext (funext fun n => ?_)
  change (diamondGen ℓ : HeckeAlgOne) • (σ • σ • (x : ℕ → JOne M) n)
      - (heckeGenOne ⟨ℓ, hℓ⟩ : HeckeAlgOne) • (σ • (x : ℕ → JOne M) n) + ℓ • (x : ℕ → JOne M) n = 0

  rw [heckeModuleOneBar_heckeGenOne_smul hcomm, heckeModuleOneBar_diamondGen_smul hcomm]

  have hz : (p ^ n : ℕ) • (x : ℕ → JOne M) n = 0 := by
    rw [← natCast_zsmul]
    exact TateModule.torsion x n
  have hℓpn : ¬ ℓ ∣ p ^ n := fun h => hℓp (hℓ.dvd_of_dvd_pow h)
  exact A2JOneFrobQuad.torsion_key M hℓ A hA hℓM σ hσ _ (p ^ n) hℓpn hz
