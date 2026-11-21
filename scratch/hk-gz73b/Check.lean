import ZInQKernel.Contrib.OneProof.HKGZ73.Reduction
import ZInQKernel.Contrib.OneProof.HKRefereed.HKRefereedSubstitute
import ZInQKernel.Contrib.CloudB3RC53.Prints

open ZInQ.Manuscript ZInQ.Manuscript.HKGZ73
open ZInQ.Contrib.RC53Assist.BCDTPrint
open ZInQ.Contrib.RC53Assist.NewformGlueG0
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent
open ZInQ.Contrib.CloudB3RC53 (IsLContinuation KolyvaginThm1Printed analyticRank_one_iff)
open RC.PrintsAnalytic (IsNewformOf eq_L_of_isLContinuation)
open HeckeRing.GL2 (Newform)

#print axioms GZ73Print
#print axioms level_eq_newformLevel_of_isNewformOf
#print axioms analyticRankOne_iff_exists_value_deriv
#print axioms analyticRankOne_iff_value_deriv
#print axioms hkConsumed_of_gz73

-- The curve continuation in the leaf is the matching newform's arithmetic L-function.
example {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N] {f : Newform N 2}
    {F : ℂ → ℂ} (hf : IsNewformOf E f) (hF : IsLContinuation E F) :
    F = ModularForm.L (by decide : 0 < (2 : ℤ)) f.toCuspForm :=
  eq_L_of_isLContinuation hf hF

-- The actual pole-completeness assembly accepts the replacement.
example (hRC : SelmerTwoPower.RestrictedConverseGenuine) (hCT : PoleS12.CasselsTatePairingCurves)
    (hB : BCDTThmAPrinted) (hGZ : GZ73Print)
    (hS : Shimura1973ConjugateEigenforms) (hL : Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986RationalNewformEulerFactors) (hF : Faltings1983EulerFactorRigidityQ) :
    ZInQ.PoleCompleteness :=
  HKRefereed.poleCompleteness_of_hkConsumed hRC hCT (bcdtThmA_of_printed hB)
    (hkConsumed_of_gz73 hGZ hB hS hL hC hF)

-- The current Theorem 5.3 forward input also implies the original pole hypothesis.
example (h : KolyvaginThm1Printed) : PoleS12.KolyvaginThm1 := by
  intro E hE hM hA
  simpa using h E hE hM 1 le_rfl ((analyticRank_one_iff E).mpr hA)
