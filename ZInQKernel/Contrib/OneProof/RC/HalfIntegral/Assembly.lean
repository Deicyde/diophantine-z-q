import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.Twist
import ZInQKernel.Contrib.OneProof.RC.AppE.Assembly

/-! Appendix E's twisting step and its application to `EvenPhaseData`. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HalfIntegral

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 AppE PrintsAnalytic

/-- Appendix E phase data for `E_ℓ` with the twisting hypothesis discharged. -/
theorem evenPhaseData_Ecurve (hWN : WaldspurgerNonvanishingTwoPower) (hW : WaldspurgerCor2)
    (hR : RamseyAlgebraicModel) (hM : ModularNewform)
    (hH : HasseConvergence) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (L : ZInQ.Manuscript.RC.Even.CentralNormalization (Ecurve ℓ)) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    {N₀ : ℕ} {w₀ : ℤ} (h₀ : RootNumberAt (Ecurve ℓ) N₀ w₀)
    {D₀ : ℕ} (hD₀ : 0 < D₀) (hsq₀ : Squarefree D₀)
    (hD₀S : ∀ p ∈ (2 * N₀).primeFactors, ¬ p ∣ D₀)
    (hL₀ : L.Lstar (σ * D₀) ≠ 0) :
    ∃ P : ZInQ.Manuscript.RC.Even.EvenPhaseData (Ecurve ℓ) L σ D₀,
      P.retained = {D | S0Filter (2 * N₀).primeFactors D₀ D} ∧ P.z = phase P.N P.η D₀ :=
  AppE.evenPhaseData_Ecurve hWN hW hR halfIntegralTwist hM hH hℓ L hσ h₀ hD₀ hsq₀ hD₀S hL₀

#print axioms evenPhaseData_Ecurve

end ZInQ.Manuscript.RC.HalfIntegral
