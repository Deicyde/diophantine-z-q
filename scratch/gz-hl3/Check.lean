import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.Cd

open ZInQ.GZHL3 in
#check @grossZagierHeegner_of_leaves
#print axioms ZInQ.GZHL3.grossZagierHeegner_of_leaves
#print axioms ZInQ.GZHL3.heegner_at
#print axioms ZInQ.GZHL3.heegnerRepsExist
#print axioms ZInQ.GZHL3.eichlerShimuraParamAt_of_leaves
#print axioms ZInQ.GZHL3.weierPt_some
#print axioms ZInQ.GZHL3.grossZagierHeegnerCd_of_leaves
#print axioms ZInQ.GZHL3.shimuraCMParamCd_of_leaves
#print axioms ZInQ.GZHL3.heegnerPointRationalCd_of
#print axioms ZInQ.GZHL3.grossZagierFormulaCd_of
#print axioms ZInQ.GZHL3.grossConjugationCd_of
-- the statement is unchanged: the theorem's type is the kernel constant itself
example : (ZInQ.GZHL3.WeierstrassUniformization → ZInQ.GZHL3.StrongWeilCurve →
    ZInQ.GZHL3.IsogenyLattice → ZInQ.GZHL3.HeegnerPointRational →
    ZInQ.GZHL3.GrossZagierFormula → ZInQ.GZHL3.GrossConjugation →
    ZInQ.GZDecomp.GrossZagierHeegner) := ZInQ.GZHL3.grossZagierHeegner_of_leaves
