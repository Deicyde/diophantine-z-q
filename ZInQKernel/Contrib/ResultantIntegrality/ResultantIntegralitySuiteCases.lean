/-
Resultant integrality tests and exact contract/body checks.
AI-assisted development; no change to the mathematical declarations.
Checking-add resource limits are not trust levels; closure walks are not library replay.
-/

import ZInQKernel.Contrib.ResultantIntegrality.Basic
import ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralityPositiveCases
import ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralityAdverseCases
import ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralityContractCounterexamples
import ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralityReductionBranches
set_option autoImplicit false
open Polynomial
namespace ResultantIntegralitySuiteCases
theorem genuineIntegerInputs :
    ∀ F R : ℤ[X], ∃ z : ℤ,
      (F.map (Int.castRingHom ℚ)).resultant
        (R.map (Int.castRingHom ℚ)) = (z : ℚ) := by
  intro F R
  exact ResultantIntegralityCases.allIntegerResultants_of_intLift F R
theorem positiveOne :
    (1 : ℚ[X]).natDegree = 0 ∧
      ∃ F : ℤ[X], F.Monic ∧ F.map (Int.castRingHom ℚ) = (1 : ℚ[X]) := by
  exact ⟨ResultantIntegralityCases.chiOneQ_natDegree,
    PrivateResultantIntegrality.integerPolynomial_of_integral_resultants
      (1 : ℚ[X]) ResultantIntegralityCases.chiOneQ_monic
      ResultantIntegralityCases.chiOne_integerResultantInput⟩
theorem positiveX :
    (X : ℚ[X]).natDegree = 1 ∧
      ∃ F : ℤ[X], F.Monic ∧ F.map (Int.castRingHom ℚ) = (X : ℚ[X]) := by
  exact ⟨ResultantIntegralityCases.chiXQ_natDegree,
    PrivateResultantIntegrality.integerPolynomial_of_integral_resultants
      (X : ℚ[X]) ResultantIntegralityCases.chiXQ_monic
      ResultantIntegralityCases.chiX_integerResultantInput⟩
theorem positiveQuadratic :
    (X ^ 2 - 2 : ℚ[X]).natDegree = 2 ∧
      ∃ F : ℤ[X], F.Monic ∧ F.map (Int.castRingHom ℚ) = (X ^ 2 - 2 : ℚ[X]) := by
  exact ⟨ResultantIntegralityCases.chiQuadQ_natDegree,
    PrivateResultantIntegrality.integerPolynomial_of_integral_resultants
      (X ^ 2 - 2 : ℚ[X]) ResultantIntegralityCases.chiQuadQ_monic
      ResultantIntegralityCases.chiQuad_integerResultantInput⟩
theorem positiveRepeated :
    (X ^ 2 : ℚ[X]).natDegree = 2 ∧
      ∃ F : ℤ[X], F.Monic ∧ F.map (Int.castRingHom ℚ) = (X ^ 2 : ℚ[X]) := by
  exact ⟨ResultantIntegralityCases.chiSquareQ_natDegree,
    PrivateResultantIntegrality.integerPolynomial_of_integral_resultants
      (X ^ 2 : ℚ[X]) ResultantIntegralityCases.chiSquareQ_monic
      ResultantIntegralityCases.chiSquare_integerResultantInput⟩
theorem adverseLinear :
    (X - C (1 / 2 : ℚ)).Monic ∧
      (X : ℤ[X]).natDegree ≤ (X - C (1 / 2 : ℚ)).natDegree ∧
      (X - C (1 / 2 : ℚ)).resultant
        ((X : ℤ[X]).map (Int.castRingHom ℚ)) = (1 / 2 : ℚ) ∧
      (¬ ∃ z : ℤ, (X - C (1 / 2 : ℚ)).resultant
        ((X : ℤ[X]).map (Int.castRingHom ℚ)) = (z : ℚ)) ∧
      ¬ (∀ R : ℤ[X], R.natDegree ≤ (X - C (1 / 2 : ℚ)).natDegree →
        ∃ z : ℤ, (X - C (1 / 2 : ℚ)).resultant
          (R.map (Int.castRingHom ℚ)) = (z : ℚ)) := by
  refine ⟨ResultantIntegralityCases.badHalfLinear_monic,
    ResultantIntegralityCases.badHalfLinear_natDegree_le,
    ResultantIntegralityCases.badHalfLinear_resultant,
    ResultantIntegralityCases.badHalfLinear_not_intCast, ?_⟩
  intro h
  exact ResultantIntegralityCases.badHalfLinear_not_intCast
    (h (X : ℤ[X]) ResultantIntegralityCases.badHalfLinear_natDegree_le)
theorem adverseQuadratic :
    (X ^ 2 + C (1 / 2 : ℚ) * X).Monic ∧
      (X + 1 : ℤ[X]).natDegree ≤ (X ^ 2 + C (1 / 2 : ℚ) * X).natDegree ∧
      (X ^ 2 + C (1 / 2 : ℚ) * X).resultant
        ((X + 1 : ℤ[X]).map (Int.castRingHom ℚ)) = (1 / 2 : ℚ) ∧
      (¬ ∃ z : ℤ, (X ^ 2 + C (1 / 2 : ℚ) * X).resultant
        ((X + 1 : ℤ[X]).map (Int.castRingHom ℚ)) = (z : ℚ)) ∧
      ¬ (∀ R : ℤ[X], R.natDegree ≤ (X ^ 2 + C (1 / 2 : ℚ) * X).natDegree →
        ∃ z : ℤ, (X ^ 2 + C (1 / 2 : ℚ) * X).resultant
          (R.map (Int.castRingHom ℚ)) = (z : ℚ)) := by
  refine ⟨ResultantIntegralityCases.badHalfQuadratic_monic,
    ResultantIntegralityCases.badHalfQuadratic_natDegree_le,
    ResultantIntegralityCases.badHalfQuadratic_resultant,
    ResultantIntegralityCases.badHalfQuadratic_not_intCast, ?_⟩
  intro h
  exact ResultantIntegralityCases.badHalfQuadratic_not_intCast
    (h (X + 1 : ℤ[X]) ResultantIntegralityCases.badHalfQuadratic_natDegree_le)
theorem adverseCubic :
    (X ^ 3 + C (1 / 3 : ℚ)).Monic ∧
      (X : ℤ[X]).natDegree ≤ (X ^ 3 + C (1 / 3 : ℚ)).natDegree ∧
      (X ^ 3 + C (1 / 3 : ℚ)).resultant
        ((X : ℤ[X]).map (Int.castRingHom ℚ)) = -(1 / 3 : ℚ) ∧
      (¬ ∃ z : ℤ, (X ^ 3 + C (1 / 3 : ℚ)).resultant
        ((X : ℤ[X]).map (Int.castRingHom ℚ)) = (z : ℚ)) ∧
      ¬ (∀ R : ℤ[X], R.natDegree ≤ (X ^ 3 + C (1 / 3 : ℚ)).natDegree →
        ∃ z : ℤ, (X ^ 3 + C (1 / 3 : ℚ)).resultant
          (R.map (Int.castRingHom ℚ)) = (z : ℚ)) := by
  refine ⟨ResultantIntegralityCases.badThirdCubic_monic,
    ResultantIntegralityCases.badThirdCubic_natDegree_le,
    ResultantIntegralityCases.badThirdCubic_resultant,
    ResultantIntegralityCases.badThirdCubic_not_intCast, ?_⟩
  intro h
  exact ResultantIntegralityCases.badThirdCubic_not_intCast
    (h (X : ℤ[X]) ResultantIntegralityCases.badThirdCubic_natDegree_le)
theorem strictBoundCounterexample :
    (X - C (1 / 2 : ℚ)).natDegree = 1 ∧
      (X - C (1 / 2 : ℚ)).Monic ∧
      (∀ R : ℤ[X], R.natDegree < (X - C (1 / 2 : ℚ)).natDegree →
        ∃ z : ℤ, (X - C (1 / 2 : ℚ)).resultant
          (R.map (Int.castRingHom ℚ)) = (z : ℚ)) ∧
      ¬ ∃ F : ℤ[X], F.map (Int.castRingHom ℚ) = (X - C (1 / 2 : ℚ)) := by
  exact ⟨ResultantIntegralityContractCases.monicLinearChi_natDegree,
    ResultantIntegralityContractCases.monicLinearChi_monic,
    ResultantIntegralityContractCases.monicLinearChi_integer_resultants_lt,
    ResultantIntegralityContractCases.monicLinearChi_no_integer_lift⟩
theorem noMonicityCounterexample :
    (C (1 / 2 : ℚ)).natDegree = 0 ∧
      (¬ (C (1 / 2 : ℚ)).Monic) ∧
      (∀ R : ℤ[X], R.natDegree ≤ (C (1 / 2 : ℚ)).natDegree →
        ∃ z : ℤ, (C (1 / 2 : ℚ)).resultant
          (R.map (Int.castRingHom ℚ)) = (z : ℚ)) ∧
      ¬ ∃ F : ℤ[X], F.map (Int.castRingHom ℚ) = C (1 / 2 : ℚ) := by
  exact ⟨ResultantIntegralityContractCases.nonmonicConstantChi_natDegree,
    ResultantIntegralityContractCases.nonmonicConstantChi_not_monic,
    ResultantIntegralityContractCases.nonmonicConstantChi_integer_resultants_le,
    ResultantIntegralityContractCases.nonmonicConstantChi_no_integer_lift⟩
theorem positiveReductionDegree :
    (2 * X ^ 2 + X : ℤ[X]).map (Int.castRingHom ℚ) =
        C (2 : ℚ) * (X ^ 2 + C (1 / 2 : ℚ) * X) ∧
      (2 * X ^ 2 + X : ℤ[X]).map (Int.castRingHom (ZMod 2)) = (X : (ZMod 2)[X]) ∧
      ((2 * X ^ 2 + X : ℤ[X]).map (Int.castRingHom (ZMod 2))).natDegree = 1 ∧
      0 < ((2 * X ^ 2 + X : ℤ[X]).map (Int.castRingHom (ZMod 2))).natDegree ∧
      ((2 * X ^ 2 + X : ℤ[X]).map (Int.castRingHom (ZMod 2))).natDegree <
        (X ^ 2 + C (1 / 2 : ℚ) * X).natDegree := by
  exact ⟨ResultantIntegralityReductionCases.F2_map_rat,
    ResultantIntegralityReductionCases.F2_map_zmod2,
    ResultantIntegralityReductionCases.F2_mod2_natDegree,
    ResultantIntegralityReductionCases.F2_reduction_branch.1,
    ResultantIntegralityReductionCases.F2_reduction_branch.2⟩
theorem constantReductionDegree :
    (3 * X ^ 3 + 1 : ℤ[X]).map (Int.castRingHom ℚ) =
        C (3 : ℚ) * (X ^ 3 + C (1 / 3 : ℚ)) ∧
      (3 * X ^ 3 + 1 : ℤ[X]).map (Int.castRingHom (ZMod 3)) = (1 : (ZMod 3)[X]) ∧
      ((3 * X ^ 3 + 1 : ℤ[X]).map (Int.castRingHom (ZMod 3))).natDegree = 0 ∧
      ((3 * X ^ 3 + 1 : ℤ[X]).map (Int.castRingHom (ZMod 3))).natDegree <
        (X ^ 3 + C (1 / 3 : ℚ)).natDegree := by
  exact ⟨ResultantIntegralityReductionCases.F3_map_rat,
    ResultantIntegralityReductionCases.F3_map_zmod3,
    ResultantIntegralityReductionCases.F3_mod3_natDegree,
    ResultantIntegralityReductionCases.F3_reduction_branch.2⟩
end ResultantIntegralitySuiteCases
