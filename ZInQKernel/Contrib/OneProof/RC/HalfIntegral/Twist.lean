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
open scoped MatrixGroups Topology ZMod

/-- The identity of theta multipliers needed by Appendix E. The divisibility
condition on the bottom-left entry is the one used in the twist. -/
def ThetaTranslationCompatibility : Prop :=
  ∀ (m : ℕ) [NeZero m] (u v : ZMod m) (γ δ : SL(2, ℤ)),
    (4 * (m : ℤ) ^ 2 : ℤ) ∣ γ 1 0 →
    translateMatrix (ratShift u) * γ.map (Int.castRingHom ℚ) =
      δ.map (Int.castRingHom ℚ) * translateMatrix (ratShift v) →
    ∀ z : ℍ, thetaMultiplier δ (residueShift v +ᵥ z) = thetaMultiplier γ z

/-- A periodic coefficient multiplier defines a cusp form at level `N³`
if its Fourier weights have the covariance of a character squared. -/
theorem translationSum_isHalfIntegralWeightCuspForm {N : ℕ} [NeZero N]
    (hθ : ThetaTranslationCompatibility) (h4 : 4 ∣ N)
    {ψ ν : DirichletCharacter ℂ N} {f : ℍ → ℂ}
    (hf : IsHalfIntegralWeightCuspForm 3 N ψ f) (w : ZMod N → ℂ)
    (hwgt : ∀ (d : (ZMod N)ˣ) (u : ZMod N),
      translationWeights w ((↑(d⁻¹ ^ 2) : ZMod N) * u) =
        ν d ^ 2 * translationWeights w u) :
    IsHalfIntegralWeightCuspForm 3 (N ^ 3) ((ψ * ν ^ 2).changeLevel (dvd_pow_self N (by decide)))
      (translationSum w f) := by
  have hNM : N ∣ N ^ 3 := dvd_pow_self N (by decide)
  have h4M : 4 * N ^ 2 ∣ N ^ 3 := by
    obtain ⟨k, hk⟩ := h4
    refine ⟨k, ?_⟩
    calc N ^ 3 = N * N ^ 2 := by ring
         _ = 4 * N ^ 2 * k := by rw [hk]; ring
  refine ⟨?_, ?_, fun α ↦ ?_⟩
  · exact DifferentiableOn.fun_sum (fun u _ ↦
      (translate_differentiableOn hf.1 (residueShift u)).const_mul (translationWeights w u))
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
    change (∑ u : ZMod N, translationWeights w u * f (residueShift u +ᵥ (γ • z))) =
      (ψ * ν ^ 2) d * thetaMultiplier γ z ^ 3 *
        ∑ u : ZMod N, translationWeights w u * f (residueShift u +ᵥ z)
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (D ^ 2).mulLeft _ _ fun u ↦ ?_
    obtain ⟨δ, hδ, hδd, heq⟩ := exists_translation_conjugate γ hγ u
    let v := d ^ 2 * u
    have hvu : ((D ^ 2).mulLeft u : ZMod N) = v := by simp [v, hD]
    have hw : translationWeights w u = ν d ^ 2 * translationWeights w v := by
      have e := hwgt D v
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
  · exact translationSum_cuspidal w hf.2.2 α

theorem halfIntegralTwist_of_thetaTranslationCompatibility (hθ : ThetaTranslationCompatibility) :
    HalfIntegralTwist := by
  intro N hN h4 ψ ν f hf
  let _ : NeZero N := ⟨hN.ne'⟩
  have hNM : N ∣ N ^ 3 := dvd_pow_self N (by decide)
  have hform := translationSum_isHalfIntegralWeightCuspForm hθ h4 hf ν
    (translationWeights_unit ν)
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

/-- At a conductor dividing `N`, the primitive Gauss sum gives the twist
before deletion at the additional primes of `N`. -/
theorem primitive_twist {N r : ℕ} [NeZero N] [NeZero r]
    (hrN : r ∣ N) (h4 : 4 ∣ N) {ψ : DirichletCharacter ℂ N} {f : ℍ → ℂ}
    (hf : IsHalfIntegralWeightCuspForm 3 N ψ f)
    (ν : DirichletCharacter ℂ r) (hν : ν.IsPrimitive) :
    let g (z : ℍ) := (gaussSum ν⁻¹ ZMod.stdAddChar)⁻¹ *
      ∑ u : ZMod r, ν⁻¹ u * f (residueShift u +ᵥ z)
    IsHalfIntegralWeightCuspForm 3 (N ^ 3)
      ((ψ * (ν.changeLevel hrN) ^ 2).changeLevel (dvd_pow_self N (by decide))) g ∧
      ∀ n : ℕ, hiwCoeff g n = ν n * hiwCoeff f n := by
  let χ := ν.changeLevel hrN
  -- Use a periodic coefficient function, keeping the primitive values even on
  -- those nonunits at level N which are still units at level r.
  let w (x : ZMod N) := ν (ZMod.castHom hrN (ZMod r) x)
  have hwgt (d : (ZMod N)ˣ) (u : ZMod N) :
      translationWeights w ((↑(d⁻¹ ^ 2) : ZMod N) * u) =
        χ d ^ 2 * translationWeights w u := by
    have h := ZMod.dft_comp_unitMul w (d ^ 2) u
    have hh : (fun j : ZMod N ↦ w ((↑(d ^ 2) : ZMod N) * j)) = χ d ^ 2 • w := by
      funext j
      simp only [w, χ, Units.val_pow_eq_pow_val, map_mul, map_pow, Pi.smul_apply, smul_eq_mul,
        DirichletCharacter.changeLevel_eq_cast_of_dvd]
      rfl
    rw [hh, ZMod.dft_const_smul] at h
    simpa only [translationWeights, inv_pow, Pi.smul_apply, smul_eq_mul,
      mul_left_comm (χ d ^ 2)] using congrArg ((N : ℂ)⁻¹ * ·) h.symm
  have hg := translationSum_isHalfIntegralWeightCuspForm thetaTranslationCompatibility
    h4 hf w hwgt
  have hs := hasSum_qExpansion one_pos (hiwForm_periodic_comp hf) (hiwForm_mdiff hf)
    (hiwForm_isZeroAtImInfty hf).boundedAtFilter
  have hw (n : ℕ) : w n = ν n := by simp only [w, map_natCast]
  have he : translationSum ν f = translationSum w f := by
    funext z
    exact (hasSum_translationSum ν hs z).unique
      (by simpa only [hw] using hasSum_translationSum w hs z)
  have hG : (fun z : ℍ ↦ (gaussSum ν⁻¹ ZMod.stdAddChar)⁻¹ *
      ∑ u : ZMod r, ν⁻¹ u * f (residueShift u +ᵥ z)) = translationSum ν f := by
    funext z
    simp_rw [translationSum, translationWeights_primitive ν hν, mul_assoc, Finset.mul_sum]
  dsimp only
  rw [hG, he]
  exact ⟨hg, fun n ↦ by
    simpa only [hiwCoeff, hw] using qExpansion_translationSum w hs (hiwForm_analyticAt hg) n⟩

#print axioms translationSum_isHalfIntegralWeightCuspForm
#print axioms halfIntegralTwist_of_thetaTranslationCompatibility
#print axioms thetaTranslationCompatibility
#print axioms halfIntegralTwist
#print axioms primitive_twist

end ZInQ.Manuscript.RC.HalfIntegral
