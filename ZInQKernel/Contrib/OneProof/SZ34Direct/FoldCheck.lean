import ZInQKernel.OneProof.H.TailZ107
import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal
import ZInQKernel.Contrib.OneProof.CasselsTatePairing
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent
import ZInQKernel.Contrib.OneProof.SilvermanRankOne
import ZInQKernel.Contrib.OneProof.SZ34Direct.Glue

/-! # Headline check for SZ34Direct

* `OpenResearchLeaves79SZ`: the research bundle `HDec.HSyn.OpenResearchLeaves79` (`TailZ107`, live)
  with the field `silverbergZarhinThm34` replaced by `silverbergZarhinThm34Given`
  (`SZ34Direct.SilverbergZarhinThm34Given`). Same number of fields.
* `openResearchLeaves79_of_SZ`: the live bundle from the new one, field by field, with
  `silverbergZarhinThm34` from `SZ34Direct.silverbergZarhinThm34_of_given`.
* `frozenTarget_sz34Given`: `ZInQ.OneProof.frozenTarget`'s body (`OneProof/Main.lean`) verbatim,
  over `OpenResearchLeaves79SZ`.
-/

namespace SZ34Direct

/-- `HDec.HSyn.OpenResearchLeaves79` with `silverbergZarhinThm34` replaced by the row with the
Néron model given. The other fields are copied with their types. -/
structure OpenResearchLeaves79SZ : Prop where
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  afCharpolyDS965 : _root_.AfTateLam.AfCharpolyDS965
  modularHTCoeff : _root_.HTNewAssembly.ModularHTCoeff
  deligneCanonicalModelY3EveryPrint : _root_.Y3Hodge.DeligneCanonicalModelY3EveryPrint
  gaudronRemondSec9LowerAnSS : _root_.ZInQ.BostGR9.GaudronRemondSec9LowerAnSS
  javanpeykarThm111An : _root_.JavanpeykarAnRetype.JavanpeykarThm111An
  y3FullThreeRepZ30 : _root_.Y3RouteA.Y3FullThreeRepZ30
  carayolThmAFrob : _root_.CarayolRefold.CarayolThmAFrob
  cmHeight62 : _root_.HDec.CMBranch.CMHeight62
  fowlerProp27PrintCanonical : _root_.HDec.CMBranch.FowlerBridges.FowlerProp27PrintCanonical
  cmjDegreePrint : _root_.HDec.CMBranch.CMjBridges.CMjDegreePrint
  /-- Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), Theorem 3.4, pp. 405–406, with the Néron
  model given (`SZ34Direct.SilverbergZarhinThm34Given`). -/
  silverbergZarhinThm34Given : SilverbergZarhinThm34Given
  bergerSurveyF : _root_.HDec.PkgI4.PanDict.BergerSurveyF
  panThm104F : _root_.HDec.PkgI4.PanBergerRefereed.PanThm104F
  gaudronRemondThm14Printed : _root_.ZInQ.GR14Printed.GaudronRemondThm14Printed

/-- The live bundle from the new one: `silverbergZarhinThm34` from the row with the Néron model
given and the proved Néron-model existence. -/
theorem openResearchLeaves79_of_SZ (n : OpenResearchLeaves79SZ) :
    HDec.HSyn.OpenResearchLeaves79 where
  pazukiCor13Upper := n.pazukiCor13Upper
  dsThm966Printed := n.dsThm966Printed
  afCharpolyDS965 := n.afCharpolyDS965
  modularHTCoeff := n.modularHTCoeff
  deligneCanonicalModelY3EveryPrint := n.deligneCanonicalModelY3EveryPrint
  gaudronRemondSec9LowerAnSS := n.gaudronRemondSec9LowerAnSS
  javanpeykarThm111An := n.javanpeykarThm111An
  y3FullThreeRepZ30 := n.y3FullThreeRepZ30
  carayolThmAFrob := n.carayolThmAFrob
  cmHeight62 := n.cmHeight62
  fowlerProp27PrintCanonical := n.fowlerProp27PrintCanonical
  cmjDegreePrint := n.cmjDegreePrint
  silverbergZarhinThm34 := silverbergZarhinThm34_of_given n.silverbergZarhinThm34Given
  bergerSurveyF := n.bergerSurveyF
  panThm104F := n.panThm104F
  gaudronRemondThm14Printed := n.gaudronRemondThm14Printed

/-- The new bundle from the live one (the converse direction of the glue). -/
theorem openResearchLeaves79SZ_of_live (r : HDec.HSyn.OpenResearchLeaves79) :
    OpenResearchLeaves79SZ where
  pazukiCor13Upper := r.pazukiCor13Upper
  dsThm966Printed := r.dsThm966Printed
  afCharpolyDS965 := r.afCharpolyDS965
  modularHTCoeff := r.modularHTCoeff
  deligneCanonicalModelY3EveryPrint := r.deligneCanonicalModelY3EveryPrint
  gaudronRemondSec9LowerAnSS := r.gaudronRemondSec9LowerAnSS
  javanpeykarThm111An := r.javanpeykarThm111An
  y3FullThreeRepZ30 := r.y3FullThreeRepZ30
  carayolThmAFrob := r.carayolThmAFrob
  cmHeight62 := r.cmHeight62
  fowlerProp27PrintCanonical := r.fowlerProp27PrintCanonical
  cmjDegreePrint := r.cmjDegreePrint
  silverbergZarhinThm34Given := given_of_silverbergZarhinThm34 r.silverbergZarhinThm34
  bergerSurveyF := r.bergerSurveyF
  panThm104F := r.panThm104F
  gaudronRemondThm14Printed := r.gaudronRemondThm14Printed

/-- **Theorem 1.1 with the row with the Néron model given**: `frozenTarget` over
`OpenResearchLeaves79SZ` (the live research bundle with `silverbergZarhinThm34` replaced by
`silverbergZarhinThm34Given`), same textbook and added bundles and the same three hypotheses. -/
theorem frozenTarget_sz34Given
    (r : OpenResearchLeaves79SZ) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves30)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves)
    (hRank : ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne) :
    _root_.ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open100 (openResearchLeaves79_of_SZ r) t l)
    (ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne hRC hCT
      (ZInQ.Manuscript.PoleS12.SilvermanRank.rankOne_of_aec hRank))

end SZ34Direct

#print axioms SZ34Direct.frozenTarget_sz34Given
#print axioms SZ34Direct.openResearchLeaves79_of_SZ
#print axioms SZ34Direct.openResearchLeaves79SZ_of_live
#print axioms SZ34Direct.silverbergZarhinThm34_of_given
#print axioms SZ34Direct.given_of_silverbergZarhinThm34
#print axioms SZ34Direct.silverbergZarhinThm34Given_iff
#print axioms SZ34Direct.neronSchemeModelExistsDVR_proof
#print axioms SZ34Direct.exists_neron_groupModelO
