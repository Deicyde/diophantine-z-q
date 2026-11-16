import ZInQKernel.Contrib.OneProof.Pi0Prune.Upper

/-!
# pi0-prune: `ZInQ.SixContactMin` without `deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure`

The single proof used the two fields of `HDec.HSyn.OpenAddedLeaves17`

* `deligneComponentsX6PrintedAb : ShimuraGlue.DeligneComponentsX6PrintedAb` (Deligne's `π₀` of `X₆`) and
* `geomConnOfAlgClosure : QMSplit.Moduli.GeomConnOfAlgClosure` (EGA IV 4.5 / Stacks 0389, weakened)

only to produce the last conjunct `R1pi0Props X` (`X₆` geometrically connected) of the row
`HDec.LeafAdopt.R1R2fpRep`, and no proof reads that conjunct (triage2's probe `scratch/triage2/Pi0Use.lean`; every
destructurer drops it). This contribution reroutes the row through its weak form:

* `Pi0Prune/Base.lean`: `LeafAdopt.R1R2fpRepW` (`R1R2fpRep` without `R1pi0Props`), `R1R2fpRepW_of_rep`, the
  destructurers (`R1R2fp_of_repW`, `r1rec_of_repW`, `r5fp_of_repW`, `pairsLift_of_repW`, …, same proofs), and the
  producer `QMSplit.Moduli.r1r2_of_publishedW` (the chain's `r1r2_of_published` without `hD`, `hE`: the base witness
  of the moduli clause lists comes from González–Rotger's leaf `GonzalezRotgerX6`, already an input);
* `Pi0Prune/Old.lean`: the six old bundle generations carrying the row (`ResearchLeaves3`, `OpenResearchLeaves2`,
  `5`, `7`, `8`, `9`) and every declaration of the single proof that mentions them, copied with the weak row
  (suffix `W`);
* `Pi0Prune/Upper.lean`: the stack `sixContactMin_of_open17` … `_open29` copied with the weak row, over the
  added-leaf bundles `OpenAddedLeaves12` … `17` without the two fields (suffix `P`).

The main theorems below prove `ZInQ.SixContactMin` from the current bundles `OpenResearchLeaves22`,
`OpenTextbookLeaves11`, `OpenGlue7` and `OpenAddedLeaves17` minus the two fields (`OpenAddedLeaves17P`), and from the
current `OpenAddedLeaves17` without reading the two fields (`sixContactMin_of_open29_pruned`, the form for the fold).

No `sorry`; standard axioms only.
-/

set_option linter.all false
set_option autoImplicit false

namespace HDec.HSyn

/-- **`OpenAddedLeaves17` minus the two fields** (`OpenAddedLeaves17P`, `Pi0Prune/Upper.lean`) from the current
bundle: every field except `deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure` is copied. -/
theorem openAddedLeaves17P_of (l : OpenAddedLeaves17) : OpenAddedLeaves17P where
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  shimuraTaniyamaQbar := l.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  deligneComponentsY3PrintedAb := l.deligneComponentsY3PrintedAb
  picRepresentableAbVar := l.picRepresentableAbVar
  picZeroAbVar := l.picZeroAbVar
  phiAmpleIsogeny := l.phiAmpleIsogeny
  weilPairingMumford := l.weilPairingMumford
  shimuraIntegralModelRep := l.shimuraIntegralModelRep

/-- **G0 from the current bundles minus `deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure`** (pi0-prune).
`ZInQ.SixContactMin` from `OpenResearchLeaves22`, `OpenTextbookLeaves11`, `OpenAddedLeaves17P` (`OpenAddedLeaves17`
without the two fields) and `OpenGlue7`. -/
theorem sixContactMin_of_open29P (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17P)
    (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open29W r t l g

/-- **The same over the current bundle `OpenAddedLeaves17`**, which reads neither `deligneComponentsX6PrintedAb` nor
`geomConnOfAlgClosure` (same type as `sixContactMin_of_open29`; the term for the fold). -/
theorem sixContactMin_of_open29_pruned (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11)
    (l : OpenAddedLeaves17) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open29P r t (openAddedLeaves17P_of l) g

end HDec.HSyn

#print axioms HDec.QMSplit.Moduli.r1r2_of_publishedW
#print axioms HDec.HSyn.sixContactMin_of_open29P
#print axioms HDec.HSyn.sixContactMin_of_open29_pruned
