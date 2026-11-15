import ZInQKernel.OneProof.H.TailZ34
import ZInQKernel.Contrib.OneProof.LinYangPrinted

/-! # OneProof H, theta-fold: `sixContactMin_of_open29`

The consumer of the added-leaf field `thetaRatiosAlgebraic` (TailK's `gluePieces_of_open4`) now takes theta-split's
use form `ThetaRatiosAtQM` as a function of `QMHauptmodul` (`hθ`, threaded through `sixContactMin_of_open4` …
`_open28`). Here it is supplied from two printed leaves by igusa-alg's and linyang-printed's proof
(`ZInQKernel/Contrib/OneProof/LinYang*.lean`, `IgusaAlgFinal.thetaRatiosAtQM_of_printedAll`).

Fields added (new leaves): `igusaThetaExpressions`, `linYangEx29All`. The field `thetaRatiosAlgebraic` has no consumer
left and is pruned from every generation (docs/research/theta-fold.md). -/

namespace HDec

namespace HSyn

/-- `OpenAddedLeaves17` (after the prune, without `thetaRatiosAlgebraic`) with the leaves `igusaThetaExpressions`,
`linYangEx29All` (theta-fold). -/
structure OpenAddedLeaves18 : Prop where
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
  /-- Representability over Z_(p), p > 324, of the moduli problem of QM abelian surfaces (disc 6) with full level 3, by a proper smooth curve (printed form on QMAbScheme): Kottwitz, J. AMS 5 (1992) 5; Buzzard, Duke 87 (1997) 1-4; Morita, Hokkaido 10 (1981); locators UNVERIFIED -/
  shimuraIntegralModelRep : _root_.SGRSplit.ShimuraIntegralModelRep
  /-- theta-fold (linyang-printed), printed form: **Igusa's theta expressions of the generators.** On `𝔥₂` the genuine
  Siegel Eisenstein series `ψ₄`, `ψ₆` (sums over `Γ_∞\Sp₄(ℤ)`) and Igusa's cusp forms `χ₁₀`, `χ₁₂` (his 1962
  combinations of Eisenstein series) equal theta-glue's theta expressions (Igusa, Amer. J. Math. 86 (1964) and 89
  (1967) p. 848; locators UNVERIFIED; 76 Fourier coefficients checked exactly by linyang-printed). With
  `linYangEx29All` replaces the universal field `thetaRatiosAlgebraic` (pruned). -/
  igusaThetaExpressions : G0Split.ThetaPt.LinYangPrinted.IgusaThetaExpressions
  /-- theta-fold (linyang-printed), printed form: **Lin–Yang 2020, Example 29, the relations only.** For every
  normalized Hauptmodul `j₆` of `Γ*\ℍ` (values `0, ∞, −16/27` at the CM points of discriminants `−4, −3, −24`),
  wherever `j₆(τ) = z ≠ ∞`: `s₃² = z s₂³`, `s₅ = s₂s₃`, `s₆ = (z+1)s₂³` along `Ω(τ)` (Lin–Yang, Math. Z. 295 (2020);
  arXiv:1807.00466v1 Ex. 29; the display UNVERIFIED). No existence claim: the Hauptmodul comes from the chain's
  `QMHauptmodul`. -/
  linYangEx29All : G0Split.ThetaPt.LinYangPrinted.LinYangEx29All

/-- `OpenAddedLeaves17` from `OpenAddedLeaves18` (theta-fold). -/
theorem openAddedLeaves17_of_OpenAddedLeaves18 (n : OpenAddedLeaves18) : OpenAddedLeaves17 where
  tateTwistInvariants := n.tateTwistInvariants
  axSenTate := n.axSenTate
  milneIsogenyQuasiInverse := n.milneIsogenyQuasiInverse
  shimuraTaniyamaQbar := n.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := n.egaIV_8_10_5_xii
  deligneComponentsY3PrintedAb := n.deligneComponentsY3PrintedAb
  deligneComponentsX6PrintedAb := n.deligneComponentsX6PrintedAb
  geomConnOfAlgClosure := n.geomConnOfAlgClosure
  picRepresentableAbVar := n.picRepresentableAbVar
  picZeroAbVar := n.picZeroAbVar
  phiAmpleIsogeny := n.phiAmpleIsogeny
  weilPairingMumford := n.weilPairingMumford
  shimuraIntegralModelRep := n.shimuraIntegralModelRep

/-- **G0 with only the open leaves and the open glue** (theta-fold): the use form of the theta algebraicity from
Igusa's theta expressions and Lin–Yang's Example 29 (with the chain's `QMHauptmodul`). -/
theorem sixContactMin_of_open29 (r : OpenResearchLeaves21) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves18) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open28 r t (openAddedLeaves17_of_OpenAddedLeaves18 l) g
    (G0Split.ThetaPt.IgusaAlgFinal.thetaRatiosAtQM_of_printedAll l.igusaThetaExpressions l.linYangEx29All)

end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open29
