import ZInQKernel.OneProof.H.TailZ12

/-! # OneProof H, leaf-fold10: the bundle `OpenAddedLeaves9` and `sixContactMin_of_open11`

The field `y3Connected` (`TSHecke.Y3Connected`, a composite: Deligne's `π₀` with an orbit computation) is replaced
by shimura-glue's printed form of Deligne's theorem on `Y₃` (`ShimuraGlue.DeligneComponentsY3Printed`, `TailZ12`).
The proof is shimura-glue's `deligneComponentsY3_of_printed` (the idele computation
`ℚ^×_{>0}\𝔸_f^×/nrd(K₃) ≅ (ℤ/3)^×` and the cyclotomic character) followed by shimura-split's orbit computation
`y3Connected_of_deligne`. docs/research/leaf-fold10.md lists every field. -/

namespace HDec

namespace HSyn

/-! ## The bundle -/

/-- **The added leaves still open** (leaf-fold10): leaf-fold8's `OpenAddedLeaves8` with `y3Connected` replaced by
shimura-glue's `DeligneComponentsY3Printed`. 14 fields. dcy3-fold: that field is pruned (13 fields); `y3Connected`
is an argument of `addedLeaves8_of_open9`. -/
structure OpenAddedLeaves9 : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  x6ConicModel : X6Kummer.X6ConicModel
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop. 2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
  /-- qm-split, H-87/H-88: `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` (Shimura 1971 Prop. 9.2;
  Shimizu 1965). -/
  shimizuCovolumeO1 : LeafQCheck.HM.QMSplit.ShimizuCovolumeO1
  /-- qm-glue, H-88: Lin–Yang's Igusa vector at the Baba–Granath CM value `j = −16/27` (discriminant `−24`). -/
  igusaCMValue24 : LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24

/-! ## From the new bundle to leaf-fold8's -/

/-- leaf-fold8's added-leaf bundle from leaf-fold10's. dcy3-fold: `y3Connected` is the argument `hY3`, supplied in
`sixContactMin_of_open28` (TailZ34) by dcy3-used's `DCY3Used.y3Connected_of_leaves` from the research fields
`mumfordGroupLaw` and `shimuraMainThmIDeligneY3AbU`; Deligne's printed leaf is no longer read. -/
theorem addedLeaves8_of_open9 (l : OpenAddedLeaves9) (hY3 : TSHecke.Y3Connected) : OpenAddedLeaves8 where
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := hY3
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  valenceFormulaCocompactEq := l.valenceFormulaCocompactEq
  shimizuCovolumeO1 := l.shimizuCovolumeO1
  igusaCMValue24 := l.igusaCMValue24

/-- **G0 with only the open leaves and the open glue** (leaf-fold10; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from leaf-fold9's `OpenResearchLeaves9` (30), `OpenTextbookLeaves10` (17),
`OpenAddedLeaves9` (14) and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every field is
`docs/research/leaf-fold10.md` §2. -/
theorem sixContactMin_of_open11 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves9)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected) : ZInQ.SixContactMin :=
  sixContactMin_of_open10 r t (addedLeaves8_of_open9 l hY3) g hF5 hYu

end HSyn

end HDec
