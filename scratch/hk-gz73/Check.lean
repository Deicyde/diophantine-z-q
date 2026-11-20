import ZInQKernel.Contrib.OneProof.HKGZ73.Reduction
import ZInQKernel.Contrib.OneProof.HKRefereed.HKRefereedSubstitute
import ZInQKernel.Contrib.CloudB3RC53.Prints

open ZInQ.Manuscript ZInQ.Manuscript.HKGZ73
open ZInQ.Contrib.RC53Assist.BCDTPrint
open ZInQ.Contrib.RC53Assist.NewformGlueG0
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent
open ZInQ.Contrib.CloudB3RC53 (KolyvaginThm1Printed analyticRank_one_iff)

#print axioms level_eq_newformLevel_of_isNewformOf
#print axioms analyticRankOne_iff_exists_value_deriv
#print axioms analyticRankOne_iff_value_deriv
#print axioms hkConsumed_of_gz73

-- Dry run of the replacement with the actual pole-completeness assembly.
example (hRC : SelmerTwoPower.RestrictedConverseGenuine) (hCT : PoleS12.CasselsTatePairingCurves)
    (hB : BCDTThmAPrinted) (hGZ : GZ73Print)
    (hS : Shimura1973ConjugateEigenforms) (hL : Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986RationalNewformEulerFactors) (hF : Faltings1983EulerFactorRigidityQ)
    (hCond : PoleNewformLevelIsConductor) : ZInQ.PoleCompleteness :=
  HKRefereed.poleCompleteness_of_hkConsumed hRC hCT (bcdtThmA_of_printed hB)
    (hkConsumed_of_gz73 hGZ hB hS hL hC hF hCond)

-- Counting check: the existing Theorem 5.3 bundle's forward input already implies hK.
example (h : KolyvaginThm1Printed) : PoleS12.KolyvaginThm1 := by
  intro E hE hM hA
  simpa using h E hE hM 1 le_rfl ((analyticRank_one_iff E).mpr hA)
