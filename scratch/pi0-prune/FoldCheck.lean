import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.Pi0Prune
/-! pi0-prune: the generation-style fold, compiled. A new chain module after `Pi0Prune` would hold the bundle
`OpenAddedLeaves18` (`OpenAddedLeaves17`, TailZ34 L117-152, without its two fields) and `sixContactMin_of_open30`;
`Main.frozenTarget` then takes `l : OpenAddedLeaves18` and calls `sixContactMin_of_open30`. -/

set_option linter.all false

namespace HDec.HSyn

/-- **The added leaves still open** (pi0-prune): `OpenAddedLeaves17` without `deligneComponentsX6PrintedAb` and
`geomConnOfAlgClosure`, which the single proof no longer uses. 12 fields. -/
structure OpenAddedLeaves18 : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  shimuraTaniyamaQbar : G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  /-- shimura-glue, printed form, on abelian schemes (route-a-fold): Deligne's theorem on the connected
  components of a Shimura variety for `G = B^×` at level `K₃` on one fine witness `Y₃` (Deligne, Sém. Bourbaki
  389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.1.3, 2.6.3; locators UNVERIFIED). -/
  deligneComponentsY3PrintedAb : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb
  /-- t09-pic, L1, printed form: the relative Picard fppf sheaf of an abelian variety over a field is representable
  (Murre 1964, Oort 1962; FGA Exp. 232 Thm 3.1; Kleiman, *The Picard scheme*, Thm 9.4.8 with 9.2.5; locators
  UNVERIFIED). With the next three replaces `t09SymmIsogenyExists`. -/
  picRepresentableAbVar : _root_.T09Pic.PicRepresentableAbVar
  /-- t09-pic, L2, printed form: for every representation of `Pic_{A/K}`, its identity component with the induced
  group law is an abelian variety (`IsPicZero`; Mumford §13, Kleiman 9.5.1 and 9.5.3, SGA 3 VI_A 2.4; locators
  UNVERIFIED). -/
  picZeroAbVar : _root_.T09Pic.PicZeroAbVar
  /-- t09-pic, L3, printed form: for ample `L`, the lift `λ_L : A → Pic⁰` of `φ_L` is an isogeny (Mumford §6
  Application 1 and §8 Thm 1; locators UNVERIFIED). -/
  phiAmpleIsogeny : _root_.T09Pic.PhiAmpleIsogeny
  /-- t09-pic, L4, printed form (single leaf): there is a pairing `A[n] × Pic⁰[n] → μ_n`, `n` invertible in `K`, with
  the values of Mumford's `ē_n` (`weilScalar`), perfect, Galois-equivariant, compatible in `n`, adjoint for the
  genuine dual `f^∨`, and trivial on `(x, λ_L x)` for ample `L` (Mumford §20 and §23; Milne 1986 §16; locators
  UNVERIFIED). -/
  weilPairingMumford : _root_.T09Pic.WeilPairingMumford
  /-- Representability over Z_(p), p > 324, of the moduli problem of QM abelian surfaces (disc 6) with full level 3, by a proper smooth curve (printed form on QMAbScheme): Kottwitz, J. AMS 5 (1992) 5; Buzzard, Duke 87 (1997) 1-4; Morita, Hokkaido 10 (1981); locators UNVERIFIED -/
  shimuraIntegralModelRep : _root_.SGRSplit.ShimuraIntegralModelRep

theorem openAddedLeaves17P_of_OpenAddedLeaves18 (n : OpenAddedLeaves18) : OpenAddedLeaves17P where
  thetaRatiosAlgebraic := n.thetaRatiosAlgebraic
  tateTwistInvariants := n.tateTwistInvariants
  axSenTate := n.axSenTate
  milneIsogenyQuasiInverse := n.milneIsogenyQuasiInverse
  shimuraTaniyamaQbar := n.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := n.egaIV_8_10_5_xii
  deligneComponentsY3PrintedAb := n.deligneComponentsY3PrintedAb
  picRepresentableAbVar := n.picRepresentableAbVar
  picZeroAbVar := n.picZeroAbVar
  phiAmpleIsogeny := n.phiAmpleIsogeny
  weilPairingMumford := n.weilPairingMumford
  shimuraIntegralModelRep := n.shimuraIntegralModelRep

/-- **G0 with only the open leaves and the open glue** (pi0-prune). -/
theorem sixContactMin_of_open30 (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves18)
    (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open29P r t (openAddedLeaves17P_of_OpenAddedLeaves18 l) g

end HDec.HSyn

namespace ZInQ.Contrib.TYZChain.Pi0PruneCheck
open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- `frozenTarget` from the bundles minus the two fields (`OpenAddedLeaves17P`). -/
theorem frozenTarget_open30
    (r : HDec.HSyn.OpenResearchLeaves22) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves18)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open30 r t l g)
    (tyzThm35ReadingA_of_leaves h11 h29 (_root_.T5Glue.shimuraReciprocityModFn_of_printed hCM hX) (ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33 h33))
    ZInQ.GZTheta.Frontier.heckeThetaNewform (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH) hL3

end ZInQ.Contrib.TYZChain.Pi0PruneCheck

#print axioms HDec.HSyn.sixContactMin_of_open30
#print axioms ZInQ.Contrib.TYZChain.Pi0PruneCheck.frozenTarget_open30
