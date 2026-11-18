import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.Multiplier
import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.Translation
import ZInQKernel.Contrib.OneProof.RC.AppE.Galois

/-!
# Twisting from the theta multiplier compatibility (tex 8101–8103)

The translation sum is a half-integral weight cusp form at level `N³` if the
theta multiplier is compatible with the translation conjugates. The matrix
calculation, choice of level, and reindexing proof are provenance (c).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.HalfIntegral

open AppE PrintsAnalytic UpperHalfPlane Filter Function CongruenceSubgroup
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology

/-- The identity of theta multipliers needed by Appendix E. The divisibility
condition on the bottom-left entry is the one used in the twist. -/
def ThetaTranslationCompatibility : Prop :=
  ∀ (m : ℕ) [NeZero m] (u v : ZMod m) (γ δ : SL(2, ℤ)),
    (4 * (m : ℤ) ^ 2 : ℤ) ∣ γ 1 0 →
    translateMatrix (ratShift u) * γ.map (Int.castRingHom ℚ) =
      δ.map (Int.castRingHom ℚ) * translateMatrix (ratShift v) →
    ∀ z : ℍ, thetaMultiplier δ (residueShift v +ᵥ z) = thetaMultiplier γ z

theorem halfIntegralTwist_of_thetaTranslationCompatibility (hθ : ThetaTranslationCompatibility) :
    HalfIntegralTwist := by
  intro N hN h4 ψ ν f hf
  let _ : NeZero N := ⟨hN.ne'⟩
  have hNM : N ∣ N ^ 3 := dvd_pow_self N (by decide)
  have h4M : 4 * N ^ 2 ∣ N ^ 3 := by
    obtain ⟨k, hk⟩ := h4
    refine ⟨k, ?_⟩
    calc N ^ 3 = N * N ^ 2 := by ring
         _ = 4 * N ^ 2 * k := by rw [hk]; ring
  have hform : IsHalfIntegralWeightCuspForm 3 (N ^ 3) ((ψ * ν ^ 2).changeLevel hNM)
      (translationSum ν f) := by
    refine ⟨?_, ?_, fun α ↦ ?_⟩
    · exact DifferentiableOn.fun_sum (fun u _ ↦
        (translate_differentiableOn hf.1 (residueShift u)).const_mul (translationWeights ν u))
    · intro γ hγ z
      let d : ZMod N := ((γ 1 1 : ℤ) : ZMod N)
      have hu : IsUnit d :=
        (ZMod.coe_int_isUnit_iff_isCoprime _ _).mpr
          (isCoprime_d_of_mem_Gamma0 (Gamma0_mono hNM hγ)).symm
      let D := hu.unit
      have hD : (D : ZMod N) = d := hu.unit_spec
      have hc : (4 * (N : ℤ) ^ 2 : ℤ) ∣ γ 1 0 := by
        exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
          (Gamma0_mem.mp (Gamma0_mono h4M hγ))
      rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ (isCoprime_d_of_mem_Gamma0 hγ)]
      change (∑ u : ZMod N, translationWeights ν u * f (residueShift u +ᵥ (γ • z))) =
        (ψ * ν ^ 2) d * thetaMultiplier γ z ^ 3 *
          ∑ u : ZMod N, translationWeights ν u * f (residueShift u +ᵥ z)
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (D ^ 2).mulLeft _ _ fun u ↦ ?_
      obtain ⟨δ, hδ, hδd, heq⟩ := exists_translation_conjugate γ hγ u
      let v := d ^ 2 * u
      have hvu : ((D ^ 2).mulLeft u : ZMod N) = v := by simp [v, hD]
      have hw : translationWeights ν u = ν d ^ 2 * translationWeights ν v := by
        have e := translationWeights_unit ν D v
        have he : ((↑(D⁻¹ ^ 2) : ZMod N) * v) = u := by
          have hProd : D⁻¹ ^ 2 * D ^ 2 = 1 := by
            rw [← (Commute.all D⁻¹ D).mul_pow, inv_mul_cancel, one_pow]
          have hVal := congrArg Units.val hProd
          change ((↑D⁻¹ : ZMod N) ^ 2 * (↑D : ZMod N) ^ 2) = 1 at hVal
          dsimp [v]
          rw [← hD, ← mul_assoc, hVal, one_mul]
        simpa only [he, hD] using e
      have ha := congrArg (fun g : SL(2, ℚ) ↦ g • z) heq
      simp only [mul_smul, translateMatrix_smul, ratShift_cast, coe_rat_map_smul] at ha
      rw [ha, hf.2.1 δ hδ, hδd, hθ N u v γ δ hc heq z, hvu, hw]
      rw [MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero d]
      ring
    · exact translationSum_cuspidal ν hf.2.2 α
  refine ⟨N ^ 3, hNM, pow_pos hN _, fun p hp h ↦ hp.dvd_of_dvd_pow h,
    translationSum ν f, hform, ?_⟩
  intro n
  exact qExpansion_translationSum ν
    (hasSum_qExpansion one_pos (hiwForm_periodic_comp hf) (hiwForm_mdiff hf)
      (hiwForm_isZeroAtImInfty hf).boundedAtFilter)
    (hiwForm_analyticAt hform) n

/-- The Poisson comparison gives compatibility for the tree's theta multiplier. -/
theorem thetaTranslationCompatibility : ThetaTranslationCompatibility := by
  intro m _ u v γ δ hc he z
  exact theta_ratio_translate u v γ δ hc he z

/-- The Appendix E weight-`3/2` twisting statement (tex 8099–8103). -/
theorem halfIntegralTwist : HalfIntegralTwist :=
  halfIntegralTwist_of_thetaTranslationCompatibility thetaTranslationCompatibility

#print axioms halfIntegralTwist_of_thetaTranslationCompatibility
#print axioms thetaTranslationCompatibility
#print axioms halfIntegralTwist

end ZInQ.Manuscript.RC.HalfIntegral
