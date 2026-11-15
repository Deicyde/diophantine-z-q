import ZInQKernel.OneProof.H.TailZ34
import ZInQKernel.Contrib.OneProof.ShimuraIntegralModelUsed
import ZInQKernel.OneProof.Main

/-! # sir-printed: dry run of the bypass fold (`sixContactMin_of_open29`)

Field removed: `shimuraIntegralModelRep` (OpenAddedLeaves17). Leaf added: `shimuraIntegralModelUsed`, weaker than the
field, so the new generation maps to `OpenAddedLeaves16` directly (autofold.py maps generation k+1 to k only, which
would need `ShimuraIntegralModelRep` from the weaker leaf). -/

namespace HDec

namespace HSyn

/-- `OpenAddedLeaves17` without `shimuraIntegralModelRep`, with the weaker leaf `shimuraIntegralModelUsed` (sir-printed;
bypass fold: the map goes to `OpenAddedLeaves16`, the generation whose field `shimuraGoodReductionNoGuard` consumes it). -/
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
  /-- x6-glue (shimura-glue), printed form (on abelian schemes): Deligne's theorem on the connected components of a
  Shimura variety (Sém. Bourbaki 389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.6.3; locators UNVERIFIED) for
  `G = B^×` at level `𝒪̂^×` on one canonical coarse witness `X₆` (the double coset is computed in Lean). -/
  deligneComponentsX6PrintedAb : _root_.ShimuraGlue.DeligneComponentsX6PrintedAb
  /-- x6-glue (shimura-split), textbook, weakened: for a proper `X → Spec k`, `char k = 0`, connectedness of
  `X ×_k k̄` gives geometric connectedness (EGA IV 4.5; Stacks 0389; locators UNVERIFIED). -/
  geomConnOfAlgClosure : QMSplit.Moduli.GeomConnOfAlgClosure
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
  /-- sir-printed: the integral model of the level-3 Shimura curve of discriminant 6 over Z_(p), p > 324, at the bases
  its consumer uses (Spec Qbar points and the Hecke relabelings of the universal object over the model); a consequence of
  Lan 2013 Thm 1.4.1.11 with Thm 5.3.3.1 (PEL form; Kottwitz, J. AMS 5 (1992) section 5 via Lan 1.4.3) and Lemma P over
  Qbar; locators UNVERIFIED. Replaces `shimuraIntegralModelRep`. -/
  shimuraIntegralModelUsed : _root_.SIRPrinted.ShimuraIntegralModelUsed

/-- `OpenAddedLeaves16` from `OpenAddedLeaves18` (bypassing `OpenAddedLeaves17`): `shimuraGoodReductionNoGuard` from the
weaker leaf. -/
theorem openAddedLeaves16_of_OpenAddedLeaves18 (n : OpenAddedLeaves18) : OpenAddedLeaves16 where
  thetaRatiosAlgebraic := n.thetaRatiosAlgebraic
  tateTwistInvariants := n.tateTwistInvariants
  axSenTate := n.axSenTate
  milneIsogenyQuasiInverse := n.milneIsogenyQuasiInverse
  shimuraTaniyamaQbar := n.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := n.egaIV_8_10_5_xii
  shimuraGoodReductionNoGuard := _root_.SIRPrinted.shimuraGoodReductionNoGuard_of_used n.shimuraIntegralModelUsed
  deligneComponentsY3PrintedAb := n.deligneComponentsY3PrintedAb
  deligneComponentsX6PrintedAb := n.deligneComponentsX6PrintedAb
  geomConnOfAlgClosure := n.geomConnOfAlgClosure
  picRepresentableAbVar := n.picRepresentableAbVar
  picZeroAbVar := n.picZeroAbVar
  phiAmpleIsogeny := n.phiAmpleIsogeny
  weilPairingMumford := n.weilPairingMumford

/-- **G0 with only the open leaves and the open glue** (sir-printed bypass fold). -/
theorem sixContactMin_of_open29 (r : OpenResearchLeaves21) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves18) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open27 (openResearchLeaves20_of_OpenResearchLeaves21 r t) t (openAddedLeaves16_of_OpenAddedLeaves18 l) g

end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open29

/-! Main.lean after the bypass fold: `l : OpenAddedLeaves18` and `sixContactMin_of_open29` (two edits). -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1, from every statement still open.** -/
theorem _root_.SIRPrinted.frozenTargetBypass
    (r : HDec.HSyn.OpenResearchLeaves21) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves18)
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

#print axioms SIRPrinted.frozenTargetBypass
