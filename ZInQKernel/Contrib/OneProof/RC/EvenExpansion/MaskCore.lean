import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Projector
import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.Twist

/-! The finite character projector on an actual weight (3/2) cusp form. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenExpansion

open AppE HalfIntegral PrintsAnalytic UpperHalfPlane
open scoped BigOperators Classical

private def squareTwist {M : ℕ} {Q : Type} [CommGroup Q]
    (label : (ZMod M)ˣ →* Q) (χ : Q →* ℂˣ) : DirichletCharacter ℂ M :=
  MulChar.ofUnitHom (χ.comp label)

private theorem squareTwist_sq {M : ℕ} {Q : Type} [CommGroup Q]
    (hQ : ∀ q : Q, q ^ 2 = 1) (label : (ZMod M)ˣ →* Q) (χ : Q →* ℂˣ) :
    squareTwist label χ ^ 2 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply' _ two_ne_zero, MulChar.one_apply_coe, squareTwist, MulChar.ofUnitHom_coe]
  change ((χ (label u) : ℂˣ) : ℂ) ^ 2 = 1
  rw [← Units.val_pow_eq_pow_val, ← map_pow, hQ, map_one, Units.val_one]

/-- Twist at one level by every character of an elementary two-group
quotient of the units. The normalized average is cuspidal of the original
character at the cubed level, and retains exactly the specified unit label. -/
theorem quadraticProjection {N M : ℕ} [NeZero M] {ψ : DirichletCharacter ℂ N} {g : ℍ → ℂ}
    (hg : IsHalfIntegralWeightCuspForm 3 N ψ g) (hNM : N ∣ M) (hfour : 4 ∣ M)
    {Q : Type} [CommGroup Q] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    (label : (ZMod M)ˣ →* Q) (target : Q) (normalization : ℂ) :
    ∃ G, IsHalfIntegralWeightCuspForm 3 (M ^ 3)
        (ψ.changeLevel (hNM.trans (dvd_pow_self M (by decide)))) G ∧
      ∀ n : ℕ, hiwCoeff G n =
        if hu : IsUnit (n : ZMod M) then
          if label hu.unit = target then normalization * hiwCoeff g n else 0
        else 0 := by
  letI := dualFintype Q
  have hg' := hiwForm_changeLevel hg hNM
  let f (χ : Q →* ℂˣ) := translationSum (squareTwist label χ) g
  have hf (χ : Q →* ℂˣ) :
      IsHalfIntegralWeightCuspForm 3 (M ^ 3)
        (ψ.changeLevel (hNM.trans (dvd_pow_self M (by decide)))) (f χ) := by
    have h := translationSum_isHalfIntegralWeightCuspForm thetaTranslationCompatibility
      hfour hg' (squareTwist label χ) (translationWeights_unit (squareTwist label χ))
    simpa only [squareTwist_sq hQ, mul_one, ← DirichletCharacter.changeLevel_trans] using h
  have hq (χ : Q →* ℂˣ) (n : ℕ) :
      hiwCoeff (f χ) n = squareTwist label χ n * hiwCoeff g n :=
    qExpansion_translationSum (squareTwist label χ)
      (hasSum_qExpansion one_pos (hiwForm_periodic_comp hg') (hiwForm_mdiff hg')
        (hiwForm_isZeroAtImInfty hg').boundedAtFilter) (hiwForm_analyticAt (hf χ)) n
  let c (χ : Q →* ℂˣ) : ℂ := (χ target : ℂ)⁻¹
  let s : ℂ := (Fintype.card (Q →* ℂˣ) : ℂ)⁻¹
  have hform := hiwForm_sum Finset.univ c f (fun χ _ => hf χ)
  refine ⟨(normalization * s) • (∑ χ, c χ • f χ),
    hiwForm_smul _ hform, fun n => ?_⟩
  rw [hiwCoeff_smul hform, hiwCoeff_sum Finset.univ c f (fun χ _ => hf χ)]
  simp_rw [hq, ← mul_assoc]
  rw [← Finset.sum_mul, mul_assoc, ← mul_assoc s]
  by_cases hu : IsUnit (n : ZMod M)
  · rw [dite_eq_left hu]
    have he (χ : Q →* ℂˣ) : squareTwist label χ n = (χ (label hu.unit) : ℂ) := by
      calc
        _ = squareTwist label χ (hu.unit : ZMod M) := congrArg (squareTwist label χ) hu.unit_spec.symm
        _ = _ := by rw [squareTwist, MulChar.ofUnitHom_coe, MonoidHom.comp_apply]
    simp_rw [he]
    rw [show s * (∑ χ : Q →* ℂˣ, c χ * (χ (label hu.unit) : ℂ)) =
      if label hu.unit = target then 1 else 0 from dual_orthogonality _ _]
    split_ifs <;> simp
  · rw [dite_eq_right hu]
    simp [MulChar.map_nonunit _ hu]


end ZInQ.Manuscript.RC.EvenExpansion
