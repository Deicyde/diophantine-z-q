import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilLattice

/-! The `Main.lean` edit for gz-weil, checked out of tree: `frozenTarget` with `hL3` replaced by the
restricted (`C_d`) Gross–Zagier chain (gz-statements' `GrossZagierHeegnerCd`), whose parametrization
leaf is Jacobi's derivative formula `JacobiLambdaDeriv` (`frozenTarget_gzweil`; with x0-32's
eta-quotient identity `X0.EtaModelDifferential` in its place: `frozenTarget_gzweil'`) instead of
gz-hl3's `StrongWeilCurve` and `IsogenyLattice`. -/

namespace ZInQ.Contrib.TYZChain
open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_gzweil'
    (r : HDec.HSyn.OpenResearchLeaves20) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves16)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing)
    (hU : ZInQ.GZHL3.WeierstrassUniformization) (hD : ZInQ.Contrib.TYZGenus.X0.EtaModelDifferential)
    (hHP : ZInQ.GZHL3.HeegnerPointRationalCd) (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd)
    (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open27 r t l g)
    (tyzThm35ReadingA_of_leaves h11 h29 (_root_.T5Glue.shimuraReciprocityModFn_of_printed hCM hX)
      (ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33 h33))
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing hL2)
    (ZInQ.GZWeil.grossZagierHeegnerCd_of_weil hU hD hHP hGZ hGC)


theorem frozenTarget_gzweil
    (r : HDec.HSyn.OpenResearchLeaves20) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves16)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing)
    (hU : ZInQ.GZHL3.WeierstrassUniformization) (hJ : ZInQ.GZWeil.JacobiLambdaDeriv)
    (hHP : ZInQ.GZHL3.HeegnerPointRationalCd) (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd)
    (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.FrozenTarget :=
  frozenTarget_gzweil' r t l g h11 h29 hCM hX h33 hL2 hU
    (ZInQ.GZWeil.etaModelDifferential_of_jacobiLambdaDeriv hJ) hHP hGZ hGC

/-- **The final form**: `hL3` replaced by four leaves (uniformization and gz-hl3's three
Heegner-point leaves for `C_d`); the parametrization of `C_d` is proved (`WeilJacobi.lean`). -/
theorem frozenTarget_gzweil_final
    (r : HDec.HSyn.OpenResearchLeaves20) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves16)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing)
    (hU : ZInQ.GZHL3.WeierstrassUniformization)
    (hHP : ZInQ.GZHL3.HeegnerPointRationalCd) (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd)
    (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.FrozenTarget :=
  frozenTarget_gzweil r t l g h11 h29 hCM hX h33 hL2 hU ZInQ.GZWeil.jacobiLambdaDeriv hHP hGZ hGC

/-- **The final form**: `hL3` replaced by gz-hl3's three Heegner-point leaves for `C_d`; the
parametrization (`WeilJacobi.lean`) and the period lattice (`WeilLattice.lean`) are proved. -/
theorem frozenTarget_gzweil_three
    (r : HDec.HSyn.OpenResearchLeaves20) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves16)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing)
    (hHP : ZInQ.GZHL3.HeegnerPointRationalCd) (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd)
    (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open27 r t l g)
    (tyzThm35ReadingA_of_leaves h11 h29 (_root_.T5Glue.shimuraReciprocityModFn_of_printed hCM hX)
      (ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33 h33))
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing hL2)
    (ZInQ.GZWeil.grossZagierHeegnerCd_of_threeLeaves hHP hGZ hGC)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_gzweil_three
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_gzweil_final
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_gzweil'
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_gzweil
