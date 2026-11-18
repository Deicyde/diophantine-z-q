import DirectHeckeCharacterV001
import DirectLevelOneArithmeticV004
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFiveRationalGenerators

/-!
# An actual rational cusp form need not be a character eigenform

At level five, a nonzero real-coefficient cusp form of weight thirteen
cannot lie in any single nebentypus space. The actual discriminant times
the normalized constant-one torsion generator supplies a rational example.
This obstructs a componentwise rationality shortcut; it is not a
counterexample to Hecke rationality, and no integrality claim is made for
the constructed example.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace DirectCharacterObstruction

open ZInQ.Contrib.HeckePrimeRationality

/-- The actual residue-two unit squares to minus one at level five. -/
theorem unit_two_square :
    (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 5)) ^ 2 = (-1 : (ZMod 5)ˣ) := by
  apply Units.ext
  decide +kernel

/-- A real nonzero actual cusp form in this odd weight is not in any single character space. -/
theorem real_weight_thirteen_not_character
    (g : CuspForm ((Gamma1 5).map (mapGL ℝ)) 13) (hg0 : g ≠ 0)
    (hg : HasRealQExpansion g) (χ : (ZMod 5)ˣ →* ℂˣ) :
    g ∉ cuspFormCharSpace 13 χ := by
  intro hχ
  let u : (ZMod 5)ˣ := ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 5)
  have hs := DirectHeckeCharacter.character_value_sign_of_real χ g hχ hg0 hg u
  have hneg := diamondOpCusp_apply_of_mem_cuspFormCharSpace 13 χ (-1) hχ
  rw [TauCeti.diamondOpCusp_neg_one] at hneg
  norm_num at hneg
  have hc : (χ (-1) : ℂ) = -1 := by
    apply smul_left_injective ℂ hg0
    simpa only [neg_one_smul] using hneg.symm
  have hsq : (χ u : ℂ) ^ 2 = -1 := by
    calc
      (χ u : ℂ) ^ 2 = (χ (u ^ 2) : ℂ) := by simp only [map_pow, Units.val_pow_eq_pow_val]
      _ = (χ (-1) : ℂ) := by rw [show u ^ 2 = -1 from unit_two_square]
      _ = -1 := hc
  rcases hs with hs | hs <;> norm_num [hs] at hsq

/-- The actual level-five discriminant cusp form, obtained by genuine restriction. -/
def deltaFive : CuspForm ((Gamma1 5).map (mapGL ℝ)) 12 :=
  CuspForm.restrict (Subgroup.map_le_range _ _) CuspForm.discriminant

/-- The concrete actual rational cusp form used in the obstruction. -/
def mixedCusp : CuspForm ((Gamma1 5).map (mapGL ℝ)) 13 :=
  CuspForm.mcast (by norm_num) (deltaFive.mulModularForm NormalizedFive.B)

/-- All invariance, holomorphy, and cusp fields are those of the actual factors. -/
theorem mixedCusp_coe : ⇑mixedCusp = ⇑deltaFive * ⇑NormalizedFive.B := by
  funext τ
  rfl

/-- Its exact actual width-one expansion is the product of the factor expansions. -/
theorem mixedCusp_qExpansion :
    qExpansion 1 mixedCusp = qExpansion 1 deltaFive * qExpansion 1 NormalizedFive.B := by
  rw [mixedCusp_coe]
  exact ModularForm.qExpansion_mul_coe one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map 5)
    deltaFive NormalizedFive.B

/-- The leading coefficient is exactly one, so this is not a formal or zero example. -/
theorem mixedCusp_coeff_one : (qExpansion 1 mixedCusp).coeff 1 = 1 := by
  rw [mixedCusp_qExpansion, PowerSeries.coeff_one_mul]
  have hd0 : (qExpansion 1 deltaFive).coeff 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero deltaFive one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map 5)
  have hd1 : (qExpansion 1 deltaFive).coeff 1 = 1 := ModularForm.discriminant_qExpansion_coeff_one
  have hb0 : (qExpansion 1 NormalizedFive.B).coeff 0 = 1 := NormalizedFive.B_coeff_zero
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [hd0, hd1, hb0]
  ring

/-- Every coefficient of this actual cusp form is rational. -/
theorem mixedCusp_rational : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 mixedCusp).coeff n = (q : ℂ) := by
  obtain ⟨a, ha⟩ := DirectLevelOneArithmetic.series_lift DirectLevelOneArithmetic.discriminant_rational
  obtain ⟨b, hb⟩ := DirectLevelOneArithmetic.series_lift NormalizedFive.B_rational
  intro n
  refine ⟨(a * b).coeff n, ?_⟩
  rw [mixedCusp_qExpansion]
  change (qExpansion 1 (CuspForm.discriminant : ModularForm 𝒮ℒ 12) *
    qExpansion 1 NormalizedFive.B).coeff n = _
  rw [← ha, ← hb, ← map_mul, PowerSeries.coeff_map]
  rfl

/-- The actual rational cusp example lies in no single character space. -/
theorem mixedCusp_not_character (χ : (ZMod 5)ˣ →* ℂˣ) : mixedCusp ∉ cuspFormCharSpace 13 χ := by
  have h0 : mixedCusp ≠ 0 := by
    intro hz
    have h := mixedCusp_coeff_one
    simp only [hz, FunLike.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero] at h
    exact zero_ne_one h
  have hr : HasRealQExpansion mixedCusp := by
    intro n
    obtain ⟨q, hq⟩ := mixedCusp_rational n
    exact ⟨(q : ℝ), by simpa using hq⟩
  exact real_weight_thirteen_not_character mixedCusp h0 hr χ

end DirectCharacterObstruction
