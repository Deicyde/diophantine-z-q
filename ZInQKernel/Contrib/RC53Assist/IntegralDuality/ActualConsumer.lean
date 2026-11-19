import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralLevelOne
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TruncIsotropyGenuine

/-!
# Actual consumer types for the integral central pairing

These declarations specialize the generic non-discrete pairing interface to
the actual central Tate module and its compact Kummer local conditions. Local
truncated isotropy remains a separate input; it is not proved or assumed to
follow merely from coefficient perfectness. No trace or derived duality
conclusion is asserted.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.SwitchInputs

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The exact remaining local isotropy input for the actual central integral pairing. -/
abbrev CentralIntegralTruncIsotropy (D : GenuineKummerData K E₀ hZ) :=
  TruncIsotropyData ℤ_[2] (GKS K D.S) (fun v : Places K D.S => Gloc K v.1)
    (fun v => locMap K D.S v.1) (centralIntegralBeta D)
    integralBeta_galois integralBeta_continuous
    (tateKummerLocalConditions D.S (centralCurve D) (centralFullTorsion D))
    (tateKummerLocalConditions D.S (centralCurve D) (centralFullTorsion D))

/-- The generic continuous-cochain interface consumes the proved actual pairing
hypotheses and a separately supplied local isotropy witness. -/
def centralIntegralPairDataTrunc (D : GenuineKummerData K E₀ hZ)
    (I : CentralIntegralTruncIsotropy D) :
    SelPairDataTrunc (compactCentralSelData D) (compactCentralSelData D) :=
  genuinePairDataTrunc ℤ_[2] (GKS K D.S) (fun v : Places K D.S => Gloc K v.1)
    (fun v => locMap K D.S v.1) (centralIntegralBeta D)
    integralBeta_galois integralBeta_continuous
    (tateKummerLocalConditions D.S (centralCurve D) (centralFullTorsion D))
    (tateKummerLocalConditions D.S (centralCurve D) (centralFullTorsion D)) I

/-- The global target is literally continuous cochains with values in the integral
cyclotomic line. -/
theorem centralIntegralPairDataTrunc_target (D : GenuineKummerData K E₀ hZ)
    (I : CentralIntegralTruncIsotropy D) :
    (centralIntegralPairDataTrunc D I).E = globalCx ℤ_[2] (GKS K D.S) (IntegralTate1 K D.S) := rfl

end ZInQ.Contrib.RC53Assist.IntegralDuality
