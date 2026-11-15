import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.SGA7CP
import ZInQKernel.Contrib.OneProof.SGA7CPFold

/-! sga7-cp checks: the switched `frozenTarget'` compiles with the standard axioms; its type is `frozenTarget`'s with
`OpenResearchLeaves21` replaced by `OpenResearchLeaves22`; `#discharges` on the two new modules. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- `ZInQ.OneProof.frozenTarget` (Main.lean) with the research bundle switched to `OpenResearchLeaves22` and the top
theorem to `sixContactMin_of_open29` (sga7-cp): the integrator's two-token edit of Main.lean. -/
theorem _root_.SGA7CPCheck.frozenTarget'
    (r : HDec.HSyn.OpenResearchLeaves22) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open29 r t l g)
    (tyzThm35ReadingA_of_leaves h11 h29 (_root_.T5Glue.shimuraReciprocityModFn_of_printed hCM hX) (ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33 h33))
    ZInQ.GZTheta.Frontier.heckeThetaNewform hL2 hL3

end ZInQ.Contrib.TYZChain

#print axioms SGA7CPCheck.frozenTarget'
#print axioms HDec.HSyn.sixContactMin_of_open29
#print axioms SGA7CP.raynaudCriterionNF_of_cpLeaves
#print axioms SGA7CP.ss1_ss3_of_cpLeaves
#print axioms SGA7CP.forwardGeomCP_of_forward

/-- The old top theorem follows from the new one (the new hypotheses are implied by the old). -/
example : type_of% @ZInQ.OneProof.frozenTarget := fun r t l g h11 h29 hCM hX h33 hL2 hL3 =>
  SGA7CPCheck.frozenTarget' (HDec.HSyn.openResearchLeaves22_of_OpenResearchLeaves21 r) t l g h11 h29 hCM hX h33 hL2 hL3

#check @ZInQ.OneProof.frozenTarget
#check @SGA7CPCheck.frozenTarget'

#discharges
