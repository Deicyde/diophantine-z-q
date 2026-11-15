import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.FHNonvanishing
import ZInQKernel.Contrib.OneProof.FHNonvanishing.FE
import ZInQKernel.Contrib.GZStatements.Weak

#discharges

/-! The proposed Main.lean edit, checked without editing Main: `frozenTarget` with `hL2` replaced by
the single printed leaf `FriedbergHoffsteinB_FE`. -/
theorem gzfh_frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves20) (t : HDec.HSyn.OpenTextbookLeaves11)
    (l : HDec.HSyn.OpenAddedLeaves16) (g : HDec.HSyn.OpenGlue7)
    (h11 : ZInQ.Contrib.TYZDecomp.TYZThm11Integral) (h29 : ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE)
    (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l g h11 h29 hCM hX h33
    (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH) hL3

/-- The restricted form `FHNonvanishingCd` (wip/gz-statements) follows from the same leaf. -/
theorem gzfh_fhNonvanishingCd (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) :
    ZInQ.GZStatements.FHNonvanishingCd :=
  ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing
    (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH)

#print axioms gzfh_frozenTarget
#print axioms gzfh_fhNonvanishingCd
#print axioms ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE
#print axioms ZInQ.GZFH.twistFunctionalEquation
#print axioms ZInQ.GZFH.fhNonvanishing_of_printed
#print axioms ZInQ.GZFH.fhNonvanishing_of_printed_fe
#print axioms ZInQ.GZFH.twistFunctionalEquation_of_twistNewformRootNumber
#print axioms ZInQ.GZFH.friedbergHoffsteinB_of_fe
