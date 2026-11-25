import ZInQKernel.OneProof.H.TailZ102
import ZInQKernel.Contrib.OneProof.C8TwistFinite.Adapter

/-! # The live route without `conradAppB` (generated)

Generated from `C8Chain.lean`, `TailZ87`, `Y3Copy5`, `NOSNarrowChain.lean` and the generations
`TailZ91`–`TailZ102`: every declaration reachable from `sixContactMin_of_open95` that carries
`conradAppB` (through `OpenAddedLeaves28`, the C8 inputs `C8Inputs`, the added-leaves bundles with
a field `c8`, or `GaloisPiecesC8`) is copied with the suffix `C8TF` (structures) / `_c8tf`
(theorems). In the copies, the field `conradAppB` of `OpenAddedLeaves28` and every field or
argument `c8` are deleted, and the only reader of `c8`, `C8Conrad.g12DetPZ_of_inputs r.r14 r.r13
m.c8 h9 r.r10` in `g8_g12_of_leaves3_hf_pz_eb_u_c8_y3c_nos`, is replaced by
`ZInQ.Contrib.C8TwistFinite.g12DetPZ_proof r.r14 r.r13 h9 r.r10` (step C8 from R13 and R14,
`C8TwistFinite/Adapter.lean`). `set_option maxHeartbeats` lines are dropped and long lines are
wrapped; nothing else changes. The originals are unchanged.
-/

set_option linter.style.haveILetI false

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:19 (there: copied from
-- ZInQKernel/OneProof/H/TailA.lean:2530 (GaloisPieces))
namespace HDec
namespace G0Galois
open _root_.PkgI4 (GaloisRep GaloisChar) -- op-dedupe
noncomputable section
/-- The pieces of the range G8-G12 that are not in the leaf bundles: Burnside (a textbook leaf;
`G8Matrix` is proved from it, `g8Matrix_of_burnside`), R14's determinant clause (a leaf, R14 as
published), and the named glue `G9Glue`, `G10Glue`, `G12Weight`, `DetTate`, `ResQFiniteIndex`
(`G12Det` is proved from the last two, R14Det and T18, `g12Det_of`). -/
structure GaloisPiecesC8C8TF : Prop where
  burnside : BurnsideAbsIrred
  r14det : R14Det
  deRham : G9Glue
  odd : G10Glue
  weight : G12Weight
  finIndex : ResQFiniteIndex
end
end G0Galois
end HDec

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:251 (there: copied from
-- ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean:513 (OpenAddedLeaves12PZ))
namespace HDec
namespace HSyn
/-- **The added leaves still open** (x6-fold): leaf-fold12's `OpenAddedLeaves11` without
`x6ConicModel` (proved by
x6-glue's `x6ConicModel_of_published`), with two of its leaves added. 14 fields. -/
structure OpenAddedLeaves12PZC8C8TF : Prop where
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop.
  2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
  /-- qm-split, H-87/H-88: `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` (Shimura 1971 Prop.
  9.2;
  Shimizu 1965). -/
  shimizuCovolumeO1 : LeafQCheck.HM.QMSplit.ShimizuCovolumeO1
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:275 (there: copied from
-- ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean:538 (OpenAddedLeaves13PZ))
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj
namespace HDec
namespace HSyn
/-- **The added leaves still open** (leaf-fold14, t09-pic fold): x6-fold's
`OpenAddedLeaves12PZC8C8TF` without
`t09SymmIsogenyExists` (t09-pic's `T09Pic.t09SymmIsogenyExists_of_four`), with its four printed
leaves added.
17 fields. -/
structure OpenAddedLeaves13PZC8C8TF : Prop where
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop.
  2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
  /-- qm-split, H-87/H-88: `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` (Shimura 1971 Prop.
  9.2;
  Shimizu 1965). -/
  shimizuCovolumeO1 : LeafQCheck.HM.QMSplit.ShimizuCovolumeO1
end HSyn
end HDec
end

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:304 (there: copied from
-- ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean:577 (addedLeaves12_of_open13_pz))
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj
namespace HDec
namespace HSyn
/-- x6-fold's added-leaf bundle from leaf-fold14's: `t09SymmIsogenyExists` from t09-pic's four
printed leaves. -/
theorem addedLeaves12_of_open13_pz_c8_c8tf (l : OpenAddedLeaves13PZC8C8TF) :
    OpenAddedLeaves12PZC8C8TF where
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  valenceFormulaCocompactEq := l.valenceFormulaCocompactEq
  shimizuCovolumeO1 := l.shimizuCovolumeO1
end HSyn
end HDec
end

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:324 (there: copied from
-- ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean:595 (OpenAddedLeaves14PZ))
namespace HDec
namespace HSyn
/-- `OpenAddedLeaves13PZC8C8TF` without `shimizuCovolumeO1` (leaf-fold16). -/
structure OpenAddedLeaves14PZC8C8TF : Prop where
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop.
  2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:344 (there: copied from
-- ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean:627 (openAddedLeaves13_of_OpenAddedLeaves14_pz))
namespace HDec
namespace HSyn
/-- `OpenAddedLeaves13PZC8C8TF` from `OpenAddedLeaves14PZC8C8TF`: `shimizuCovolumeO1` by the
contributions. -/
theorem openAddedLeaves13_of_OpenAddedLeaves14_pz_c8_c8tf (n : OpenAddedLeaves14PZC8C8TF) :
    OpenAddedLeaves13PZC8C8TF where
  qmCentralizerCMC := n.qmCentralizerCMC
  tateTwistInvariants := n.tateTwistInvariants
  axSenTate := n.axSenTate
  milneIsogenyQuasiInverse := n.milneIsogenyQuasiInverse
  egaIV_8_10_5_xii := n.egaIV_8_10_5_xii
  valenceFormulaCocompactEq := n.valenceFormulaCocompactEq
  shimizuCovolumeO1 := _root_.HDec.GammaStarArea.shimizuCovolumeO1_proof
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:360 (there: copied from
-- ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean:646 (OpenAddedLeaves15PZ))
namespace HDec
namespace HSyn
/-- `OpenAddedLeaves14PZC8C8TF` without `qmCentralizerCMC` (leaf-fold18). -/
structure OpenAddedLeaves15PZC8C8TF : Prop where
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop.
  2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:379 (there: copied from
-- ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean:677 (OpenAddedLeaves16PZ))
namespace HDec
namespace HSyn
/-- `OpenAddedLeaves15PZC8C8TF` without `valenceFormulaCocompactEq` (leaf-fold18). -/
structure OpenAddedLeaves16PZC8C8TF : Prop where
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:395 (there: copied from
-- ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean:705 (openAddedLeaves15_of_OpenAddedLeaves16_pz))
namespace HDec
namespace HSyn
/-- `OpenAddedLeaves15PZC8C8TF` from `OpenAddedLeaves16PZC8C8TF`: `valenceFormulaCocompactEq` by the
contributions. -/
theorem openAddedLeaves15_of_OpenAddedLeaves16_pz_c8_c8tf (n : OpenAddedLeaves16PZC8C8TF) :
    OpenAddedLeaves15PZC8C8TF where
  tateTwistInvariants := n.tateTwistInvariants
  axSenTate := n.axSenTate
  milneIsogenyQuasiInverse := n.milneIsogenyQuasiInverse
  egaIV_8_10_5_xii := n.egaIV_8_10_5_xii
  valenceFormulaCocompactEq := _root_.ValenceCocompact.valenceFormulaCocompactEq_proof
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:409 (there: copied from
-- ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean:722 (OpenAddedLeaves17PZ))
namespace HDec
namespace HSyn
/-- `OpenAddedLeaves16PZC8C8TF` without `shimuraGoodReductionNoGuard`, with the leaves
`shimuraIntegralModelRep` (leaf-fold22). -/
structure OpenAddedLeaves17PZC8C8TF : Prop where
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:425 (there: copied from
-- ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean:750 (openAddedLeaves16_of_OpenAddedLeaves17_pz))
namespace HDec
namespace HSyn
/-- `OpenAddedLeaves16PZC8C8TF` from `OpenAddedLeaves17PZC8C8TF`: `shimuraGoodReductionNoGuard` by
the contributions. -/
theorem openAddedLeaves16_of_OpenAddedLeaves17_pz_c8_c8tf (n : OpenAddedLeaves17PZC8C8TF) :
    OpenAddedLeaves16PZC8C8TF where
  tateTwistInvariants := n.tateTwistInvariants
  axSenTate := n.axSenTate
  milneIsogenyQuasiInverse := n.milneIsogenyQuasiInverse
  egaIV_8_10_5_xii := n.egaIV_8_10_5_xii
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:438 (there: copied from
-- ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean:766 (OpenAddedLeaves18PZ))
namespace HDec
namespace HSyn
/-- `OpenAddedLeaves17PZC8C8TF` without `axSenTate`, `tateTwistInvariants`,
`milneIsogenyQuasiInverse` (leaf-fold32). -/
structure OpenAddedLeaves18PZC8C8TF : Prop where
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:451 (there: copied from
-- ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean:791 (openAddedLeaves17_of_OpenAddedLeaves18_pz))
namespace HDec
namespace HSyn
/-- `OpenAddedLeaves17PZC8C8TF` from `OpenAddedLeaves18PZC8C8TF`: `axSenTate`,
`tateTwistInvariants`, `milneIsogenyQuasiInverse` by the contributions. -/
theorem openAddedLeaves17_of_OpenAddedLeaves18_pz_c8_c8tf (n : OpenAddedLeaves18PZC8C8TF) :
    OpenAddedLeaves17PZC8C8TF where
  tateTwistInvariants := _root_.ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
  axSenTate := _root_.ZInQ.Contrib.CloudB3W11.axSenTate_proof
  milneIsogenyQuasiInverse := _root_.ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof
  egaIV_8_10_5_xii := n.egaIV_8_10_5_xii
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:529 (there: copied from
-- ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean:1786
-- (openAddedLeaves14_of_OpenAddedLeaves15_hf_pz))
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
namespace HDec
namespace HSyn
/-- `OpenAddedLeaves14PZC8C8TF` from `OpenAddedLeaves15PZC8C8TF`: `qmCentralizerCMC` by the
contributions. -/
theorem openAddedLeaves14_of_OpenAddedLeaves15_hf_pz_c8_c8tf (n : OpenAddedLeaves15PZC8C8TF) (t :
    OpenTextbookLeaves10HF) : OpenAddedLeaves14PZC8C8TF where
  qmCentralizerCMC := _root_.HDec.QMLattice.qmCentralizerCMC_of t.uniformizationLeafAll
      t.gagaMorphism t.mumfordTorsionAlgClosed
  tateTwistInvariants := n.tateTwistInvariants
  axSenTate := n.axSenTate
  milneIsogenyQuasiInverse := n.milneIsogenyQuasiInverse
  egaIV_8_10_5_xii := n.egaIV_8_10_5_xii
  valenceFormulaCocompactEq := n.valenceFormulaCocompactEq
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:1391 (there: edited copy of
-- ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean:2193 (openAddedLeaves18_of_OpenAddedLeaves22_pz))
set_option linter.style.longLine false
set_option linter.unusedVariables false
namespace HDec
namespace HSyn
/-- Copy of the generated `openAddedLeaves18_of_OpenAddedLeaves22_pz_c8` without its unread
arguments `t`, `n`
(`n : OpenAddedLeaves22PZ` carries the Picard rows). -/
theorem openAddedLeaves18_hm_c8tf : OpenAddedLeaves18PZC8C8TF where
  egaIV_8_10_5_xii := _root_.ZInQ.Contrib.EGAProperLimit.egaIV_8_10_5_xii_proof
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ87.lean:68
namespace HDec
namespace HSyn
/-- `OpenAddedLeaves27` without the Picard rows, with the leaves of the joint C8 fold (all GLUE
until reviewed). -/
structure OpenAddedLeaves28C8TF : Prop where
  /-- Scholze, p-adic Hodge theory for rigid-analytic varieties, Forum Math. Pi 1 (2013), Cor. 1.8
  with Thms 9.1, 9.3 (diophantine_zq.tex lem:de-rham-descent L10954-10965, step C3) with the Hodge
  numbers of `H¹_dR(A/F)` (L10996): `H¹_et(A_F̄, ℚ_p)` of an abelian variety of dimension g over a
  finite `F/ℚ_p` is de Rham with Hodge jumps in [0, 1] and `dim Fil¹ D_dR = [F:ℚ_p] g`, over
  Mathlib's pro-étale `Scheme.EllAdicCohomology`. General g is a generalization (the manuscript's
  lemma is g = 2, `ScholzeH1AbSurf`, implied). -/
  scholzeH1AbVar : _root_.DeRhamScholze.HTMerge.ScholzeH1AbVar
  /-- `H¹(A_K̄, ℤ_ℓ) = Hom(T_ℓ A, ℤ_ℓ)`, Galois-equivariantly, over Mathlib's pro-étale
  `EllAdicCohomology`: a consequence of Milne, Abelian Varieties v2.0 (March 16, 2008), Part I,
  Thm 12.1(a), p. 55, with Rem. 12.5, p. 56 (Galois compatibility), as the manuscript cites it
  (lem:de-rham-descent L10966-10970). The 1986 Cornell-Silverman chapter (Thm 15.1(a)) was not
  read. -/
  t10TateDuality : _root_.T10Etale.T10_TateDuality
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/Y3Copy5.lean:845 (there: copied from
-- ZInQKernel.OneProof.H.C8Chain 52-89 (HDec.HSyn.OpenAddedLeaves4PZC8, value))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry G0Split
/-- **The added leaves still open** (leaf-fold4): `OpenAddedLeaves3` with
* `qmDenZeroCM3` (LEAF?) replaced by period-glue's leaf candidates `GammaStarGen` and
  `ValenceBoundGammaStar` (with R4, `qmDenZeroCM3_of_leaves4`);
* `properSmoothGenConnected` (LEAF?) replaced by Zariski's connectedness theorem in its published
form
  (zariski-conn);
* `divisiblePoints` dropped (G12's `DetTate` now uses T5, `detTate_of_leaves4_pz`);
* new: period-map's leaf candidate `CMDescends` (for `PeriodMapGlue`) and spread-out's three EGA IV
  leaves (for `AbVarSpreadsOut`). -/
structure _root_.HDec.HSyn.OpenAddedLeaves4PZC8_y3cC8TF : Prop where
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  qmHauptmodul : PkgI1.QMHauptmodul
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  senTwist : G0Galois.SenTwist
  finiteImageHT : G0Galois.FiniteImageHT
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  x6ConicModel : _root_.HDec.X6Kummer.X6ConicModel_y3c
  y3Connected : TSHecke.Y3Connected
  qmAutCard : HeckeRest.QMAutCard
  serreRigidity3 : HeckeRest.SerreRigidity3
  alFixedPoints : HeckeRest.ALFixedPoints
  /-- zariski-conn, LEAF: Zariski's connectedness theorem (EGA III₁ 4.3.1 with 4.3.4). -/
  zariskiConnectedness : _root_.ZariskiConn.ZariskiConnectedness.{0}
  /-- period-map, LEAF?: a QM pair over `ℂ` with CM descends (Shimura; for `PeriodMapGlue`). -/
  cmDescends : G0Split.FibreQM.PeriodMapH.CMDescends
  /-- period-glue, LEAF?: `Γ*` is generated by `ι(1+i+j)`, `ι((j−3)/2)` and `ℚ^×`. -/
  gammaStarGen : G0Split.FibreQM.PeriodGlue.GammaStarGen
  /-- period-map, LEAF?: the valence bound for weight-8 forms on `Γ*`. -/
  valenceBoundGammaStar : G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar
  /-- spread-out, LEAF: EGA IV₃ 8.8.2 (ii) (descent of finitely presented schemes to a stage of a
  limit). -/
  egaIV_8_8_2_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii
  /-- spread-out, LEAF: EGA IV₃ 8.10.5 (xii) (properness descends). -/
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  /-- spread-out, LEAF: EGA IV₄ 17.7.8 (ii) (smoothness descends). -/
  egaIV_17_7_8_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii
end HDec.HSyn
end

-- copied from ZInQKernel/OneProof/H/Y3Copy5.lean:894 (there: copied from
-- ZInQKernel.OneProof.H.C8Chain 100-131 (HDec.HSyn.OpenAddedLeaves6PZC8, value))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- **The added leaves still open** (leaf-fold6): leaf-fold5's `OpenAddedLeaves5` with leafq-check's
reductions:
`gammaStarGen` dropped (proved), `valenceBoundGammaStar` → `valenceFormulaGammaStar`, `cmDescends` →
`stQM`,
`qmHauptmodul` → `qmHauptmodulBase3`. 20 fields. -/
structure _root_.HDec.HSyn.OpenAddedLeaves6PZC8_y3cC8TF : Prop where
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  /-- leafq-check, LEAF?: the Hauptmodul property of the theta quotient on `Γ*` and its value
  `−16/27` at the
  order-2 point (the clauses at the discriminants `−4`, `−3` are proved). -/
  qmHauptmodulBase3 : LeafQCheck.HM.QMHauptmodulBase3
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  senTwist : G0Galois.SenTwist
  finiteImageHT : G0Galois.FiniteImageHT
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  x6ConicModel : _root_.HDec.X6Kummer.X6ConicModel_y3c
  y3Connected : TSHecke.Y3Connected
  qmAutCard : HeckeRest.QMAutCard
  alFixedPoints : HeckeRest.ALFixedPoints
  zariskiConnectedness : _root_.ZariskiConn.ZariskiConnectedness.{0}
  /-- leafq-check, LEAF: Shimura–Taniyama for QM surfaces with CM (`A ≅ A₀ ×_{ℚ̄} ℂ`). -/
  stQM : G0Split.FibreQM.PeriodMapH.LeafQCheck.STQM
  /-- leafq-check, LEAF: the valence formula on `Γ*` (signature `(0;2,4,6)`) on finite sets of
  inequivalent
  points. -/
  valenceFormulaGammaStar : LeafQCheck.VB.ValenceFormulaGammaStar
  egaIV_8_8_2_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  egaIV_17_7_8_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii
  /-- model-glue, LEAF?: a morphism of proper smooth curves over `ℚ` bijective on `ℚ̄`-points is an
  isomorphism (Hartshorne II.6.7-6.9, III.10.7; EGA III 4.4.2). -/
  curveBijIso : ModelGlue.CurveBijIso
end HDec.HSyn
end

-- copied from ZInQKernel/OneProof/H/Y3Copy5.lean:937 (there: copied from
-- ZInQKernel.OneProof.H.C8Chain 140-166 (HDec.HSyn.OpenAddedLeaves7PZC8, value))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- **The added leaves still open** (leaf-fold7): leaf-fold6's
`_root_.HDec.HSyn.OpenAddedLeaves6PZC8_y3cC8TF` without `qmClassNumberOne` and
`curveBijIso` (proved), with the three QM computations replaced by `QMCentralizerCMC`, `stQM` by
`ShimuraTaniyamaQbar`, `isogenyQuasiInverse` by `MilneIsogenyQuasiInverse`, `senTwist`,
`finiteImageHT` by
Tate's two theorems, and `shimuraGoodReduction` by its guard-free form. 16 fields. -/
structure _root_.HDec.HSyn.OpenAddedLeaves7PZC8_y3cC8TF : Prop where
  qmHauptmodulBase3 : LeafQCheck.HM.QMHauptmodulBase3
  /-- qm-split, H-42/H-61/H-63: `End_𝒪(A)` of a QM surface over `ℂ` is `ℤ` or an optimally embedded
  order of an
  imaginary quadratic field (replaces `cmOptimalEmbedding`, `qmAutCard`, `alFixedPoints`). -/
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  /-- hodge-split, H-51/H-52/H-8: Tate 1967 §3.3 Thm 2, `ℂ_p(i)^{G_K} = 0` for `i ≠ 0` (with
  `axSenTate`, replaces
  `senTwist` and `finiteImageHT`). -/
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  /-- hodge-split: Ax–Sen–Tate, `ℂ_p^{G_K} = K` (Tate 1967 §3.3 Thm 1; Sen 1969; Ax 1970). -/
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  /-- av-split, H-54: Milne's quasi-inverse of an isogeny, as morphisms (replaces
  `isogenyQuasiInverse`). -/
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  x6ConicModel : _root_.HDec.X6Kummer.X6ConicModel_y3c
  y3Connected : TSHecke.Y3Connected
  zariskiConnectedness : _root_.ZariskiConn.ZariskiConnectedness.{0}
  valenceFormulaGammaStar : LeafQCheck.VB.ValenceFormulaGammaStar
  egaIV_8_8_2_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  egaIV_17_7_8_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii
end HDec.HSyn
end

-- copied from ZInQKernel/OneProof/H/Y3Copy5.lean:976 (there: copied from
-- ZInQKernel.OneProof.H.C8Chain 175-198 (HDec.HSyn.OpenAddedLeaves8PZC8, value))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- **The added leaves still open** (leaf-fold8): leaf-fold7's
`_root_.HDec.HSyn.OpenAddedLeaves7PZC8_y3cC8TF` without `zariskiConnectedness`,
`egaIV_8_8_2_ii`, `egaIV_17_7_8_ii` (proved by cloud workers W02, W01), and with
`valenceFormulaGammaStar`,
`qmHauptmodulBase3` replaced by the valence formula, Shimizu's covolume and the CM value at `−24`
(qm-glue). 14
fields. -/
structure _root_.HDec.HSyn.OpenAddedLeaves8PZC8_y3cC8TF : Prop where
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  x6ConicModel : _root_.HDec.X6Kummer.X6ConicModel_y3c
  y3Connected : TSHecke.Y3Connected
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop.
  2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
  /-- qm-split, H-87/H-88: `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` (Shimura 1971 Prop.
  9.2;
  Shimizu 1965). -/
  shimizuCovolumeO1 : LeafQCheck.HM.QMSplit.ShimizuCovolumeO1
  /-- qm-glue, H-88: Lin–Yang's Igusa vector at the Baba–Granath CM value `j = −16/27` (discriminant
  `−24`). -/
  igusaCMValue24 : LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24
end HDec.HSyn
end

-- copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1012 (there: copied from
-- ZInQKernel.OneProof.H.C8Chain 205-226 (HDec.HSyn.OpenAddedLeaves9PZC8, value))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
/-- **The added leaves still open** (leaf-fold10): leaf-fold8's
`_root_.HDec.HSyn.OpenAddedLeaves8PZC8_y3cC8TF` with `y3Connected` replaced by
shimura-glue's `DeligneComponentsY3Printed`. 14 fields. dcy3-fold: that field is pruned (13 fields);
`y3Connected`
is an argument of `_root_.HDec.HSyn.addedLeaves8_of_open9_pz_c8_y3c_c8tf`. -/
structure _root_.HDec.HSyn.OpenAddedLeaves9PZC8_y3cC8TF : Prop where
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  x6ConicModel : _root_.HDec.X6Kummer.X6ConicModel_y3c
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop.
  2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
  /-- qm-split, H-87/H-88: `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` (Shimura 1971 Prop.
  9.2;
  Shimizu 1965). -/
  shimizuCovolumeO1 : LeafQCheck.HM.QMSplit.ShimizuCovolumeO1
  /-- qm-glue, H-88: Lin–Yang's Igusa vector at the Baba–Granath CM value `j = −16/27` (discriminant
  `−24`). -/
  igusaCMValue24 : LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24
end HDec.HSyn
end

-- copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1044 (there: copied from
-- ZInQKernel.OneProof.H.C8Chain 233-247 (HDec.HSyn.addedLeaves8_of_open9_pz_c8, TYPE))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
/-- leaf-fold8's added-leaf bundle from leaf-fold10's. dcy3-fold: `y3Connected` is the argument
`hY3`, supplied in
`sixContactMin_of_open28` (TailZ34) by dcy3-used's `DCY3Used.y3Connected_of_leaves` from the
research fields
`mumfordGroupLaw` and `shimuraMainThmIDeligneY3AbU`; Deligne's printed leaf is no longer read. -/
theorem _root_.HDec.HSyn.addedLeaves8_of_open9_pz_c8_y3c_c8tf (l :
    _root_.HDec.HSyn.OpenAddedLeaves9PZC8_y3cC8TF) (hY3 : TSHecke.Y3Connected) :
    _root_.HDec.HSyn.OpenAddedLeaves8PZC8_y3cC8TF where
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := hY3
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  valenceFormulaCocompactEq := l.valenceFormulaCocompactEq
  shimizuCovolumeO1 := l.shimizuCovolumeO1
  igusaCMValue24 := l.igusaCMValue24
end HDec.HSyn
end

-- copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1069 (there: copied from
-- ZInQKernel.OneProof.H.C8Chain 468-484 (HDec.HSyn.textbookLeaves4_of_open6_hf_pz_c8, TYPE))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- leaf-fold4's textbook bundle from leaf-fold6's (as leaf-fold5's `textbookLeaves4_of_open5`, with
`t8 := t8_ofK6 t.t8`). -/
theorem _root_.HDec.HSyn.textbookLeaves4_of_open6_hf_pz_c8_y3c_c8tf (t : OpenTextbookLeaves6HF) (l
    : _root_.HDec.HSyn.OpenAddedLeaves6PZC8_y3cC8TF) : OpenTextbookLeaves4HFPZ where
  t3 := t3_of_surj5 t.t3Surj
  t4 := reductionTorsionBijective_ofK5 t.t4
  t5 := torsionStructure_ofK5 t.t5
  t6 := t.homFreeFiniteAlgClosed
  t7 := t7_of_algClosed5 t.charPolyIndepOfEllAlgClosed
  t8 := t8_ofK6 t.t8
  homLatticeCorr := homLatticeCorr_ofK5 t.homLatticeCorr
  t11b := t11b_of_exists5 t.t11bExists
  t24 := eigenformTwist_ofK5 t.t24
  t33 := jacobianExists_ofK5 t.t33
  t35 := uniformizationExists_ofK5 t.t35
  t38 := t38_of_split5 t.normalModelOfFunctionFieldQ t.normalCurveSmoothQ
      t.geomConnectedOfConstantFieldQ
  x0Transitive := t.x0Transitive
  t41 := t41_of_extension5 t.neronSchemeExtensionExists
end HDec.HSyn
end

-- copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1097 (there: copied from
-- ZInQKernel.OneProof.H.C8Chain 493-513 (HDec.HSyn.textbookLeaves6_of_open7_hf_pz_c8, TYPE))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- leaf-fold6's textbook bundle from leaf-fold7's. -/
theorem _root_.HDec.HSyn.textbookLeaves6_of_open7_hf_pz_c8_y3c_c8tf (t : OpenTextbookLeaves7HF) (l
    : _root_.HDec.HSyn.OpenAddedLeaves7PZC8_y3cC8TF) : OpenTextbookLeaves6HF where
  t3Surj := t.t3Surj
  t4 := _root_.AvSplit.Final.h24 t.mulEtaleAbelianScheme
  t5 := _root_.AvSplit.Final.h25 t.mumfordTorsionAlgClosed
  homFreeFiniteAlgClosed := t.homFreeFiniteAlgClosed
  charPolyIndepOfEllAlgClosed := t.charPolyIndepOfEllAlgClosed
  t8 := _root_.AVGlue.poincareReducibility_of_published' t.cartierSmooth t.poincareComplement
    (isogenyQuasiInverseAG_lf7 l.milneIsogenyQuasiInverse) t.geomConnOfRationalPoint
        t.groupSchemeEquidim
  homLatticeCorr := _root_.AvSplit.Final.h69 t.uniformizationLeafAll t.gagaMorphism
  t11bExists := t.t11bExists
  t24 := t.t24
  t33 := t.t33
  dimJacobianEqGenus := t.dimJacobianEqGenus
  t35 := _root_.AvSplit.Final.h38 t.uniformizationLeafAll t.mumfordTorsionAlgClosed
  normalModelOfFunctionFieldQ := t.normalModelOfFunctionFieldQ
  normalCurveSmoothQ := _root_.CurveSplit.normalCurveSmoothQ_of_regularSmooth t.regularSmoothPerfect
  geomConnectedOfConstantFieldQ :=
    _root_.CurveSplit.geomConnectedOfConstantFieldQ_of_zariski l.zariskiConnectedness
  x0Transitive := _root_.FltCqj2.x0Transitive_proof
  neronSchemeExtensionExists := t.neronSchemeExtensionExists
end HDec.HSyn
end

-- copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1130 (there: copied from
-- ZInQKernel.OneProof.H.C8Chain 522-525 (HDec.HSyn.qmRows_of7_hf_pz_c8, TYPE))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- The three QM rows from `QMCentralizerCMC` and T11(b) (qm-split's `rows_of_C`). -/
theorem _root_.HDec.HSyn.qmRows_of7_hf_pz_c8_y3c_c8tf (t : OpenTextbookLeaves7HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves7PZC8_y3cC8TF) :
    HeckeRest.QMAutCard ∧ HeckeRest.ALFixedPoints ∧ FS5NoCM.CMOptimalEmbedding :=
  QMSplit.Aut.rows_of_C l.qmCentralizerCMC (t11b_of_exists5 t.t11bExists)
end HDec.HSyn
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:2884 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1161 (_root_.HDec.HSyn.qmHauptmodul_of6_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- **`QMHauptmodul` from `QMHauptmodulBase3`** (leafq-check's `base2_of_base3` and
`qmHauptmodul_of_base2`:
R4, `GammaStarGen` (proved) and the valence bound (from the valence formula)). -/
theorem _root_.HDec.HSyn.qmHauptmodul_of6_pz_eb_u_c8_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOS) (l :
    _root_.HDec.HSyn.OpenAddedLeaves6PZC8_y3cC8TF) : PkgI1.QMHauptmodul :=
  LeafQCheck.HM.qmHauptmodul_of_base2
    (LeafQCheck.HM.base2_of_base3 r.r4 LeafQCheck.gammaStarGen_proof
      (LeafQCheck.VB.valenceBound_of_formula l.valenceFormulaGammaStar) l.qmHauptmodulBase3)
end HDec.HSyn
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:2906 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1183
-- (_root_.HDec.HSyn.researchLeaves5_of_open7_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- leaf-fold6's research bundle (`_root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOS`) from
leaf-fold7's. -/
theorem _root_.HDec.HSyn.researchLeaves5_of_open7_pz_eb_u_c8_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.OpenResearchLeaves7EBU_y3cNOS) (l :
    _root_.HDec.HSyn.OpenAddedLeaves7PZC8_y3cC8TF) : _root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOS
    where
  r1r2 := r.r1r2
  r1b := _root_.HDec.QMSplit.Moduli.r1b_of'_y3c r.shimuraFamily
  r1rec := r.r1rec
  r4 := QMSplit.Theta.thetaModularity_of r.igusaPsi4 r.igusaChi10
  r5 := r.r5
  r5count := r.r5count
  r6 := r.r6
  r9a := r.r9a
  r9b := r.r9b
  r10 := HodgeLF7.r10 (_root_.ZInQ.Contrib.HodgeSplit.deRhamComparisonHT_of_leavesT
      r.hodgeTateDecompAbVar
    l.tateTwistInvariants l.axSenTate r.deRhamH1AbVarT)
  r11r12 := r.r11r12
  r13 := HodgeLF7.eigenformHT (_root_.ZInQ.Contrib.HodgeSplit.eigenformHT_of_kato_ds
      r.eigenformHTNew
    HodgeLF7.newformOfEigenformG9 r.dsThm965 r.dsThm966)
  r14 := HodgeLF7.r14Det (_root_.ZInQ.Contrib.HodgeSplit.r14Det_of_printed r.dsThm965 r.dsThm966)
  r15 := r.r15
  r16 := r.r16
  r17 := r.r17
  r18 := r.r18
  r19 := r.r19
  r21 := r.r21
  r22 := r.r22
  h5fin := r.h5fin
end HDec.HSyn
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:2948 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1225
-- (_root_.HDec.G0Galois.g8_g12_of_leaves3_hf_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.G0Galois
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
open _root_.PkgI4 (GaloisRep GaloisChar) -- op-dedupe
theorem _root_.HDec.G0Galois.g8_g12_of_leaves3_hf_pz_eb_u_c8_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.ResearchLeaves3EBU_y3cNOS) (t : HSyn.TextbookLeavesHFPZ) (m :
    GaloisPiecesC8C8TF)
    (h9 : G9GlueNoT23)
    {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (T : Finset ℕ)
    (h2 : G2Out K T) (h6 : G6Out A) (h3 : G3Out A 5 T)
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a β : PkgI4.GQ → PadicAlgCl 5)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl 5) (Vb A 5))
    (h7 : G7Out A 5 Tm c ε a β u) :
    ∃ r₅ : GaloisRep 5 2, G8Out A 5 (GlueDescent.rho Tm a β) r₅ ∧ G9Out r₅ ∧ G10Out r₅ ∧
      G11Out T r₅ ∧ G12Out r₅ :=
  g8_g12_hf_pz r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t11a t.t11b
    r.r11r12 r.r14 r.r13 r.r15 t.frobeniusDense HSyn.t19_proved (g8Matrix_of_burnside m.burnside)
        h9 m.odd m.weight
    (_root_.ZInQ.Contrib.C8TwistFinite.g12DetPZ_proof r.r14 r.r13 h9 r.r10)
    A T h2 h6 h3 Tm c ε a β u h7
end HDec.G0Galois
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:2979 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1256 (_root_.HDec.HSyn.cmDescends_of6_hf_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- **`CMDescends` from Shimura–Taniyama** (leafq-check's `cmDescends_of`, with leaf-fold5's T11(b)
and T5). -/
theorem _root_.HDec.HSyn.cmDescends_of6_hf_pz_eb_u_c8_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOS) (t : OpenTextbookLeaves6HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves6PZC8_y3cC8TF) :
    G0Split.FibreQM.PeriodMapH.CMDescends :=
  _root_.HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.cmDescends_ofW_y3c l.stQM (t11b_of_exists5
      t.t11bExists)
    (G0Split.FibreQM.PeriodMapH.LeafQCheck.torsionDescends_of_t5 (torsionStructure_ofK5 t.t5))
        r.r1r2
end HDec.HSyn
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3000 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1277
-- (_root_.HDec.HSyn.addedLeaves4_of_open6_hf_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- leaf-fold4's added-leaves bundle from leaf-fold6's. -/
theorem _root_.HDec.HSyn.addedLeaves4_of_open6_hf_pz_eb_u_c8_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOS) (t : OpenTextbookLeaves6HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves6PZC8_y3cC8TF) :
    _root_.HDec.HSyn.OpenAddedLeaves4PZC8_y3cC8TF where
  cmOptimalEmbedding := l.cmOptimalEmbedding
  qmHauptmodul := _root_.HDec.HSyn.qmHauptmodul_of6_pz_eb_u_c8_y3c_nos_c8tf r l
  qmClassNumberOne := l.qmClassNumberOne
  senTwist := l.senTwist
  finiteImageHT := l.finiteImageHT
  isogenyQuasiInverse := l.isogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  qmAutCard := l.qmAutCard
  serreRigidity3 := serreRigidity3_of_T35_5 (uniformizationExists_ofK5 t.t35) (homLatticeCorr_ofK5
      t.homLatticeCorr)
  alFixedPoints := l.alFixedPoints
  zariskiConnectedness := l.zariskiConnectedness
  cmDescends := _root_.HDec.HSyn.cmDescends_of6_hf_pz_eb_u_c8_y3c_nos_c8tf r t l
  gammaStarGen := LeafQCheck.gammaStarGen_proof
  valenceBoundGammaStar := LeafQCheck.VB.valenceBound_of_formula l.valenceFormulaGammaStar
  egaIV_8_8_2_ii := l.egaIV_8_8_2_ii
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := l.egaIV_17_7_8_ii
end HDec.HSyn
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3038 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1318 (_root_.HDec.HSyn.glue4_of_open6_hf_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- leaf-fold4's glue bundle from leaf-fold6's: `HeckeVertWitness` by sgr-direct's route NV
(`_root_.SGRDirect.heckeVertWitness_of_nvSqrtAny_y3c`) from `r1r2`, T5, `qmAutCard`, Serre's
rigidity (from T35),
`alFixedPoints`, `NVLocalInertia` and `HeckeSqrtBranchAny`, without the integral model of the
Shimura curve
(sgr-fold; leaf-fold5's `heckeVertWitness_of_leaves5` needed `shimuraGoodReduction` and
`ModelCoordinateResidue`). -/
theorem _root_.HDec.HSyn.glue4_of_open6_hf_pz_eb_u_c8_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOS) (t : OpenTextbookLeaves6HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves6PZC8_y3cC8TF)
    (g : OpenGlue6) : OpenGlue4 where
  heckeVertWitness := _root_.SGRDirect.heckeVertWitness_of_nvSqrtAny_y3c
      (_root_.HDec.LeafAdopt.R1R2fp_of_rep_y3c r.r1r2)
    (torsionStructure_ofK5 t.t5) l.qmAutCard
    (serreRigidity3_of_T35_5 (uniformizationExists_ofK5 t.t35) (homLatticeCorr_ofK5
        t.homLatticeCorr))
    l.alFixedPoints g.nvLocalInertia g.heckeSqrtBranchAny
end HDec.HSyn
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3064 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1342
-- (_root_.HDec.HSyn.addedLeaves6_of_open7_hf_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- leaf-fold6's added bundle from leaf-fold7's. -/
theorem _root_.HDec.HSyn.addedLeaves6_of_open7_hf_pz_eb_u_c8_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.OpenResearchLeaves7EBU_y3cNOS) (t : OpenTextbookLeaves7HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves7PZC8_y3cC8TF) :
    _root_.HDec.HSyn.OpenAddedLeaves6PZC8_y3cC8TF where
  cmOptimalEmbedding := (_root_.HDec.HSyn.qmRows_of7_hf_pz_c8_y3c_c8tf t l).2.2
  qmHauptmodulBase3 := l.qmHauptmodulBase3
  qmClassNumberOne := QMSplit.CNO.qmClassNumberOne_proof
  senTwist := HodgeLF7.senTwist (_root_.ZInQ.Contrib.HodgeSplit.senTwist_of_tate
      l.tateTwistInvariants l.axSenTate)
  finiteImageHT :=
    HodgeLF7.finiteImageHT (_root_.ZInQ.Contrib.HodgeSplit.finiteImageHT_of_tate
        l.tateTwistInvariants l.axSenTate)
  isogenyQuasiInverse := isogenyQuasiInverse_lf7 l.milneIsogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  qmAutCard := (_root_.HDec.HSyn.qmRows_of7_hf_pz_c8_y3c_c8tf t l).1
  alFixedPoints := (_root_.HDec.HSyn.qmRows_of7_hf_pz_c8_y3c_c8tf t l).2.1
  zariskiConnectedness := l.zariskiConnectedness
  stQM := _root_.GapST.stQM_ofW_y3c r.r1r2 l.y3Connected
      (_root_.HDec.HSyn.qmRows_of7_hf_pz_c8_y3c_c8tf t l).2.1
    (_root_.AvSplit.Final.h25 t.mumfordTorsionAlgClosed)
    (_root_.AvSplit.Final.h38 t.uniformizationLeafAll t.mumfordTorsionAlgClosed)
    (_root_.AvSplit.Final.h69 t.uniformizationLeafAll t.gagaMorphism)
  valenceFormulaGammaStar := l.valenceFormulaGammaStar
  egaIV_8_8_2_ii := l.egaIV_8_8_2_ii
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := l.egaIV_17_7_8_ii
  curveBijIso := curveBijIso_lf7
end HDec.HSyn
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3106 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1384
-- (_root_.HDec.HSyn.GR9.x6Rows_of_open14_hf_gm_pz_eb_sf_u_c8_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- **The two `X₆` rows from the new bundles** (the term of `x6Rows_of_open13`). pi0-fold: the weak
row
`_root_.HDec.LeafAdopt.R1R2fpRepW_y3c` from `_root_.HDec.QMSplit.Moduli.x6Rows_of_leavesW_y3c`,
whose base witness is González–Rotger's (`_root_.HDec.QMSplit.Moduli.GonzalezRotgerX6_y3c`); the
added leaves
`deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure` are no longer read. -/
theorem _root_.HDec.HSyn.GR9.x6Rows_of_open14_hf_gm_pz_eb_sf_u_c8_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves12PZC8C8TF) :
    _root_.HDec.LeafAdopt.R1R2fpRepW_y3c ∧ _root_.HDec.X6Kummer.X6ConicModel_y3c :=
  have hR := _root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw
  ⟨_root_.Y3X6.r1r2fpY3_of r.y3row ((_root_.LeafQM.AV.R1UnivRigid.rayClassCM_iff_ab_gl hR).mpr
      r.rayClassCMAb), trivial⟩
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3128 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1405
-- (_root_.HDec.HSyn.GR9.openGlue7_of_OpenGlue8_hf_gm_pz_eb_sf_u_c8_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `OpenGlue7` from `OpenGlue8`: `HeckeSqrtBranchAny` by the contribution (Elkies' printed model,
through
generation 22 of the research bundle). -/
theorem _root_.HDec.HSyn.GR9.openGlue7_of_OpenGlue8_hf_gm_pz_eb_sf_u_c8_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves17PZC8C8TF)
    (g : OpenGlue8) : OpenGlue7 where
  nvLocalInertia := g.nvLocalInertia
  heckeSqrtBranchAny := r.heckeSqrtY3
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3149 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1426
-- (_root_.HDec.HSyn.GR9.addedLeaves9_of_open14_hf_gm_pz_eb_sf_u_c8_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- leaf-fold10's added-leaf bundle from leaf-fold14's (the composite of `addedLeaves11_of_open12`,
`addedLeaves10_of_open11` and `addedLeaves9_of_open10`). -/
theorem _root_.HDec.HSyn.GR9.addedLeaves9_of_open14_hf_gm_pz_eb_sf_u_c8_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves12PZC8C8TF) :
    _root_.HDec.HSyn.OpenAddedLeaves9PZC8_y3cC8TF where
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := (_root_.HDec.HSyn.GR9.x6Rows_of_open14_hf_gm_pz_eb_sf_u_c8_y3c_nos_c8tf r t l).2
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  valenceFormulaCocompactEq := l.valenceFormulaCocompactEq
  shimizuCovolumeO1 := l.shimizuCovolumeO1
  igusaCMValue24 := _root_.CM24.igusaCMValue24_field
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3178 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1455
-- (_root_.HDec.HSyn.GR9.ss1_ss3_of14NF_hf_gm_pz_eb_sf_u_c8_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- **SS1 and SS3** (r6-nf; the reroute of `ss1_ss3_of14`, docs/research/neron-dvr.md §3.2):
neron-dvr's
`GapNeron.ss1_ss3_of_cpNF`, with the Néron field at number fields from N1. -/
theorem _root_.HDec.HSyn.GR9.ss1_ss3_of14NF_hf_gm_pz_eb_sf_u_c8_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves12PZC8C8TF) :
    _root_.ZInQ.SSFaltings.SemistableReductionThmIF :=
  _root_.ZInQ.SSFaltings.semistableReductionThmIF_of_raynaud
      (_root_.HDec.HSyn.GR9.raynaudSemistable_of14_hf_gm_eb_sf_u_y3c_nos r t)
    t.mumfordTorsionAlgClosed t.mulEtaleAbelianScheme
    (_root_.GapNeron.neronSchemeModelExistsNF t.neronSchemeExtensionExists)
    (_root_.ReductGlue.semistableLocalGlobal_leaf (_root_.CToPrinted.neronLocalizesDVR_of_printed
        r.blr_1_2_4))
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3201 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1481
-- (_root_.HDec.HSyn.GR9.researchLeaves9_of_open14_hf_gm_pz_eb_sf_u_c8_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- leaf-fold9's research bundle from leaf-fold14's (the composite of `researchLeaves12_of_open13`,
`researchLeaves11_of_open12`, `researchLeaves10_of_open11` and `researchLeaves9_of_open10`, with the
three reduct
fields replaced by reduct-b's theorems). r6-nf: r6 (at number fields) and SS1, SS3 are arguments,
supplied in
`sixContactMin_of_open20_hf_gm_pz_eb_sf_u_c8` (TailZ26) by
`_root_.HDec.HSyn.GR9.raynaudCriterionNF_of14_hf_gm_eb_sf_u_y3c_nos` and
`_root_.HDec.HSyn.GR9.ss1_ss3_of14NF_hf_gm_pz_eb_sf_u_c8_y3c_nos_c8tf` from neron-dvr's
number-field Néron theorem (N1 alone), which replaced BLR 1.4/3 over every DVR. -/
theorem _root_.HDec.HSyn.GR9.researchLeaves9_of_open14_hf_gm_pz_eb_sf_u_c8_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves12PZC8C8TF)
    (h6 : _root_.HDec.D2A6.R6U)
    (hSS : _root_.ZInQ.SSFaltings.SemistableReductionThmIF) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOS where
  r1r2 := (_root_.HDec.HSyn.GR9.x6Rows_of_open14_hf_gm_pz_eb_sf_u_c8_y3c_nos_c8tf r t l).1
  shimuraFamily := (_root_.LeafQM.AV.R1UnivRigid.shimuraFamily_iff_ab_gl
      (_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw)).mpr
    r.shimuraFamilyAb
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
  r6 := h6
  r9a := r.r9a
  r9b := r.r9b
  hodgeTateDecompAbVar := r.hodgeTateDecompAbVar
  deRhamH1AbVarT := r.deRhamH1AbVarT
  r11r12 := r.r11r12
  eigenformHTNew := r.eigenformHTNew
  dsThm965 := r.dsThm965
  dsThm966 := r.dsThm966
  r16 := r.r16
  r17 := r.r17
  semistableReductionThmIF := hSS
  faltingsSemistableHeightBC := r.faltingsSemistableHeightBC
  bostLowerBound := r.bostLowerBound
  javanpeykarBound := r.javanpeykarBound
  pazukiCor13Upper := r.pazukiCor13Upper
  gaudronRemondThm14 := r.gaudronRemondThm14
  gonzalezRotgerCountX6 := r.gonzalezRotgerCountX6Ab
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3249 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1528
-- (_root_.HDec.HSyn.GR9.addedLeaves7_of_open8_pz_eb_sf_u_c8_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- leaf-fold7's added bundle from leaf-fold8's. -/
theorem _root_.HDec.HSyn.GR9.addedLeaves7_of_open8_pz_eb_sf_u_c8_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOS) (l :
    _root_.HDec.HSyn.OpenAddedLeaves8PZC8_y3cC8TF) : _root_.HDec.HSyn.OpenAddedLeaves7PZC8_y3cC8TF
    where
  qmHauptmodulBase3 := LeafQCheck.HM.QMSplit.qmHauptmodulBase3_of_leaves
    (QMSplit.Theta.thetaModularity_of r.igusaPsi4 r.igusaChi10) l.valenceFormulaCocompactEq
        l.shimizuCovolumeO1
    l.igusaCMValue24
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  zariskiConnectedness := _root_.ZariskiConn.ZariskiConnectedness_proof.{0}
  valenceFormulaGammaStar :=
    LeafQCheck.HM.QMSplit.valenceFormulaGammaStar_of_leaves l.valenceFormulaCocompactEq
        l.shimizuCovolumeO1
  egaIV_8_8_2_ii := _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii_proof
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii_proof
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3284 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1556
-- (_root_.HDec.HSyn.G0AssembleMod.afterG7NC_of3_hf_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.HSyn.G0AssembleMod
open CategoryTheory AlgebraicGeometry
open G0ModField
/-- cm-branch's `_root_.HDec.HSyn.G0AssembleMod.afterG7NC_of3_hf_pz_eb_y3c` on
`_root_.HDec.HSyn.ResearchLeaves3EBU_y3cNOS` and `GaloisPiecesC8C8TF` (fold-c8's
`afterG7_of3_hf_pz_eb_u_c8`, localized). -/
theorem _root_.HDec.HSyn.G0AssembleMod.afterG7NC_of3_hf_pz_eb_u_c8_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.ResearchLeaves3EBU_y3cNOS) (t : TextbookLeavesHFPZ)
    (m : G0Galois.GaloisPiecesC8C8TF)
    (h9 : G0Galois.G9GlueNoT23)
    (hDF : G0ModNewform.DirichletOfFinite) (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hG36 : ModelG3G6NC) (hLink : LinkedTateDataNC) : AfterG7NC := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨h6, h3₅, h3₃⟩ := hG36 Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  obtain ⟨Tm₅, c₅, ε₅, a₅, β₅, u₅, Tm₃, c₃, ε₃, a₃, β₃, u₃, h7₅, h7₃, hlink⟩ :=
    hLink Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  have h2 : G0Galois.G2Out L' (T u) :=
    galoisG2Out_of_g7Data resQRange u P L A ε N χ β L' hLL' hdata
  obtain ⟨r₅, h8₅, -, -, h11₅, h12⟩ :=
    _root_.HDec.G0Galois.g8_g12_of_leaves3_hf_pz_eb_u_c8_y3c_nos_c8tf r t m h9 _ (T u) h2 h6 h3₅
        Tm₅ c₅ ε₅ a₅ β₅ u₅ h7₅
  obtain ⟨r₃, h8₃, -, -, h11₃⟩ :=
    G0Galois.g8_g11_hf r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t11a
      t.t11b (G0Galois.g8Matrix_of_burnside m.burnside) h9 m.odd _ (T u) h2 h6 3 h3₃
      Tm₃ c₃ ε₃ a₃ β₃ u₃ h7₃
  obtain ⟨i, ιC, ι5, hspec⟩ := G0ModNewform.g12Spec_of_galois hDF _ _ _ r₅ r₃ h8₅ h8₃ h12
  obtain ⟨ι3, h14, h15⟩ := hlink r₅ r₃ h8₅ h8₃ i ιC ι5
  obtain ⟨M, J, hM, hJ, hMle, hCC⟩ :=
    G0ModNewform.modularConstituent_tail_G
        (_root_.HDec.HSyn.G0AssembleMod.newformLeaves_of3_hf_pz_eb_u_y3c_nos r t hCar) t.t33
        t.x1ModelExists
      hSw hL8 hAd _ u ⟨_, hspec ι3, h14, g15RamG_of_wild _ u h15 h11₅ h11₃⟩
  exact ⟨M, J, hM, hJ, hMle, (commonConstituent_copy' _ _).1 hCC⟩
end HDec.HSyn.G0AssembleMod
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3378 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1650 (_root_.HDec.HSyn.sixContactMin_of_open4_cm_u_c8_y3c))
noncomputable section
namespace HDec.HSyn
open CategoryTheory AlgebraicGeometry G0Split
/-- cm-branch's `_root_.HDec.HSyn.sixContactMin_of_open4_cm_y3c` on the live chain's bundles at this
generation (`_root_.HDec.HSyn.OpenResearchLeaves2EBU_y3cNOS`:
R6 = `D2A6.R6U`; `_root_.HDec.HSyn.OpenAddedLeaves4PZC8_y3cC8TF`: `c8` for the Weil-pairing fields):
the manuscript's CM branch (L581-631)
in place of FS5 (NoCM) in fold-c8's `sixContactMin_of_open4_hf_pz_eb_u_c8`. -/
theorem _root_.HDec.HSyn.sixContactMin_of_open4_cm_u_c8_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.OpenResearchLeaves2EBU_y3cNOS) (t : OpenTextbookLeaves4HFPZ)
    (l : _root_.HDec.HSyn.OpenAddedLeaves4PZC8_y3cC8TF) (g : OpenGlue4) (h20 : G0Split.R20Lower)
        (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM)
    (hSplit : CMBranch.CMFibreSplit) (hF : CMBranch.FowlerProp27) (hJ : CMBranch.CMjDegree)
    (hPG : CMBranch.CMPotentialGood) (h62 : CMBranch.CMHeight62) (hRP : CMBranch.ReducedCMPeriod)
    (hAddU : CMBranch.HeightAdditivityUpper) : ZInQ.SixContactMin :=
  let t2 := textbookLeaves2_of_open3_hf_pz (textbookLeaves3_of_open4_hf_pz t)
  let r3 := _root_.HDec.HSyn.researchLeaves3_of_open2_eb_u_y3c_nos r
  let t3 := textbookLeaves_of_open2_hf_pz t2
  have hMob : LeafQM.AV.Pin.MobiusGlue := mobiusGlue_of_t5' t.t5
  have hFSNC : CMBranch.FibreSimpleNC :=
    CMBranch.fibreSimpleNC_of_pieces_hf hYu
      (G0FibreSimple.endDivisionDescent_of G0FibreSimple.baseChangeFaithful_proof
        (G0FibreSimple.isogenyDescends_of G0FibreSimple.finiteDescends_proof))
      (G0FibreSimple.endDivisionOfSchemeIso_of_rigidity G0FibreSimple.rigidityHom)
      (G0FibreSimple.end0Division_of_homFree_hf t3.t6 mulIsogeny_proved)
      (G0FibreSimple.centralizerOfMatrixEnd0_of_homFree_hf t3.t6)
  have hModNC : CMBranch.ModularConstituentNC :=
    HSyn.modularConstituentNC_of_field_hf_pz t3
      (G0ModField.fibreCoverExists_of_propTSAll' t.t5
        (_root_.HDec.HSyn.propTSAll_of_pieces3_y3c r.r1r2 t.t5 l.y3Connected l.qmAutCard
            l.serreRigidity3 l.alFixedPoints
          chartProper_proved4 chartQuasiFinite_proved4 g.heckeVertWitness)
              unramifiedConjugates_proved)
      (G0ModField.KernelField.kernelFieldExistsNC_of_split_hf_u_nos t.t6
          _root_.NOSNarrow.nosForward_proof r.r6 t.t5 hYu
        G0ModField.KernelField.oMaximal endTransport_proved conjIsogMaps_proved3)
      UnramTate.unramifiedSup_mf
      (_root_.HDec.HSyn.G0AssembleMod.afterG7NC_of3_hf_pz_eb_u_c8_y3c_nos_c8tf r3 t3
        ⟨burnsideAbsIrred_proved3, r.r14,
          g9Glue_of_deRhamComparisonHT r.r10,
          G0Galois.g10Glue_of_conjTwist
            (G0Galois.conjTwistNontrivial_of_leaves t.t5 (tateModuleFree_of_t5' t.t5) t.t35
              (HomUnify.homLinearLift_of_corr t.homLatticeCorr)),
          G0Galois.g12Weight_of_senTwist l.senTwist l.finiteImageHT,
          G0AssembleMod.resQFiniteIndex⟩
        (g9GlueNoT23_of_deRhamComparisonHT r.r10)
        (G0ModNewform.dirichletOfFinite_of_t17 t17_proved) r.r17
        Swan.swanIndependent_proved Swan.swanIntegral_proved
        Swan.adaptedExists_proved
        (HSyn.modelG3G6NC_of_leaves3U_nos hFSNC _root_.NOSNarrow.nosForward_proof r.r6 t.t5)
        (G0AssembleMod.linkedTateDataNC_of_local t.t7
          (HSyn.linkedTateLocalNC_of_leaves3_hf_u r.r6 t.t5 (tateModuleFree_of_t5' t.t5)
            (abVarSpreadsOut_of_ega4 l.egaIV_8_8_2_ii l.egaIV_8_10_5_xii l.egaIV_17_7_8_ii)
            (properSmoothGenConnected_of_zariski4 l.zariskiConnectedness)
            t.t4 t.t3 hFSNC t.t6 hYu)))
  have hDimF : DimFinite := G0Split.dimFinite
  have hDim : DimBaseChange := G0Split.dimBaseChange
  have hPMH : ZInQ.H5Neron.ProductModelHeight := ZInQ.ProductHeight.productModelHeight_of_splits
      productUnifSplits_proved
      (ZInQ.UnifDims.productMetrizationOfProductUnif_of_tangentDim t.t35 tangentDimAtOrigin_proved3)
  have hBC : StableHeightBaseChange := G0StableBC.stableHeightBaseChange_of_hodgeLine
      (ZInQ.HeightBC.g0_hodgeLine_iff.mpr (ZInQ.HeightBC.hodgeLineBaseChange_of_glue4
        hodgeBCInjective_proved3 cotangentSpanBC_proved omegaBaseChange_proved3
        uniformizationLiftAnalytic_proved))
  have hProdE : ProductExists := G0Product.productExists
  have hRev : ReverseIsogeny := _root_.HDec.HSyn.G0RevIsog.reverseIsogeny_of_leaves3_eb_u_y3c_nos
      r3 G0Split.dimFinite
  have hThetaPt : ThetaPointOfFibre := G0Split.ThetaPt.ThetaSplit.thetaPointOfFibre_of_qm_atQM
      (_root_.HDec.HSyn.G0Split.FibreQM.fibreQMPeriod_main_rep_y3c r.r1r2 hMob l.qmHauptmodul
        t.t35 t2.t11a l.qmClassNumberOne (r.r1b r.r1r2)
            (_root_.HDec.HSyn.periodMapGlue_of_leaves4_y3c r.r1r2 t.t5 t.homLatticeCorr
            l.cmDescends)
        hauptmodulUnique_proved4
        (qmDenZeroCM3_of_leaves4 r.r4 l.gammaStarGen l.valenceBoundGammaStar) cPtsTransport_proved3)
      (hθ l.qmHauptmodul)
  have hCopies : HeightCopiesAgree := G0HeightCopies.heightCopiesAgree
  CMBranch.sixContactMin_of_branches (_root_.LeafQM.AV.exists_fibre_object_y3c
      (_root_.HDec.LeafAdopt.R1R2fp_of_rep_y3c r3.r1r2))
    (_root_.HDec.CMBranch.nonCMBranch_of_u_y3c_nos r3 t3 hDimF hDim hPMH hBC hProdE hRev hThetaPt
        hCopies hFSNC hModNC h20)
    (CMBranch.cmBranchOut_of r3.h5.1 hDim (thetaPazuki (r22Concrete_of r3.r22 hCopies) hThetaPt)
      hSplit hF hJ hPG h62 hRP hAddU r3.r19 h20)
end HDec.HSyn
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3454 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1726
-- (_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.longLine false
/-- The base: CMBranchUC8's `_root_.HDec.HSyn.sixContactMin_of_open4_cm_u_c8_y3c_nos_c8tf` (the
manuscript's CM branch, L581-631, on the live
bundles) with `ReducedCMPeriod` and `HeightAdditivityUpper` proved from the textbook fields `t35`,
`homLatticeCorr`,
`t11b` (cm-branch2) and `CoxProperLattice` proved (cox-lattice). -/
theorem _root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.OpenResearchLeaves2EBU_y3cNOS) (t : OpenTextbookLeaves4HFPZ)
    (l : _root_.HDec.HSyn.OpenAddedLeaves4PZC8_y3cC8TF) (g : OpenGlue4) (h20 : G0Split.R20Lower)
        (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) :
    ZInQ.SixContactMin :=
  _root_.HDec.HSyn.sixContactMin_of_open4_cm_u_c8_y3c_nos_c8tf r t l g h20 hYu hθ c.cmFibreSplit
      c.fowlerProp27 c.cmjDegree
    c.cmPotentialGood c.cmHeight62
    (CMBranch.reducedCMPeriod_of_leaves t.t35 t.homLatticeCorr t.t11b
        CMBranch.coxProperLattice_proof)
    (CMBranch.heightAdditivityUpper_of_t35 t.t35)
end HDec.HSyn
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3473 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1753
-- (_root_.HDec.HSyn.sixContactMin_of_open6_hf_pz_eb_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- `sixContactMin_of_open6_hf_pz_eb_u_c8` with the base switched to the manuscript's CM branch
(`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.sixContactMin_of_open6_hf_pz_eb_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOS) (t : OpenTextbookLeaves6HF)
    (l : _root_.HDec.HSyn.OpenAddedLeaves6PZC8_y3cC8TF) (g : OpenGlue6) (h20 : G0Split.R20Lower)
        (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.researchLeaves2_of_open5_eb_u_y3c_nos r)
      (_root_.HDec.HSyn.textbookLeaves4_of_open6_hf_pz_c8_y3c_c8tf t l)
      (_root_.HDec.HSyn.addedLeaves4_of_open6_hf_pz_eb_u_c8_y3c_nos_c8tf r t l)
    (_root_.HDec.HSyn.glue4_of_open6_hf_pz_eb_u_c8_y3c_nos_c8tf r t l g) h20 hYu hθ
end HDec.HSyn
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3497 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1778
-- (_root_.HDec.HSyn.sixContactMin_of_open7_hf_pz_eb_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- `sixContactMin_of_open7_hf_pz_eb_u_c8` with the base switched to the manuscript's CM branch
(`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.sixContactMin_of_open7_hf_pz_eb_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.OpenResearchLeaves7EBU_y3cNOS) (t : OpenTextbookLeaves7HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves7PZC8_y3cC8TF)
    (g : OpenGlue7) (h20 : G0Split.R20Lower) (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.sixContactMin_of_open6_hf_pz_eb_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.researchLeaves5_of_open7_pz_eb_u_c8_y3c_nos_c8tf r l)
      (_root_.HDec.HSyn.textbookLeaves6_of_open7_hf_pz_c8_y3c_c8tf t l)
      (_root_.HDec.HSyn.addedLeaves6_of_open7_hf_pz_eb_u_c8_y3c_nos_c8tf r t l)
    (glue6_of_open7 g) h20 hYu hθ
end HDec.HSyn
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3522 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1803
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open8_hf_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- `sixContactMin_of_open8_hf_pz_eb_sf_u_c8` with the base switched to the manuscript's CM branch
(`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open8_hf_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOS) (t : OpenTextbookLeaves8HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves8PZC8_y3cC8TF)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.sixContactMin_of_open7_hf_pz_eb_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.researchLeaves7_of_open8_hf_eb_sf_u_y3c_nos r t)
      (textbookLeaves7_of_open8_hf t)
      (_root_.HDec.HSyn.GR9.addedLeaves7_of_open8_pz_eb_sf_u_c8_y3c_nos_c8tf r l) g
    (_root_.HDec.HSyn.GR9.r20Lower_of8_hf_eb_sf_u_y3c_nos r t hF5) hYu hθ
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3547 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1827
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open9_hf_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits
/-- `sixContactMin_of_open9_hf_pz_eb_sf_u_c8` with the base switched to the manuscript's CM branch
(`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open9_hf_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOS) (t : OpenTextbookLeaves9HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves8PZC8_y3cC8TF)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open8_hf_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.researchLeaves8_of_open9_hf_eb_sf_u_y3c_nos r t)
      (textbookLeaves8_of_open9_hf t) l g hF5 hYu hθ
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3570 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1849
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open10_hf_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open10_hf_pz_eb_sf_u_c8` with the base switched to the manuscript's CM branch
(`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open10_hf_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOS) (t : OpenTextbookLeaves10HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves8PZC8_y3cC8TF)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open9_hf_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c) r
      (textbookLeaves9_of_open10_hf t) l g hF5 hYu hθ
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3592 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1871
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open11_hf_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open11_hf_pz_eb_sf_u_c8` with the base switched to the manuscript's CM branch
(`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open11_hf_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOS) (t : OpenTextbookLeaves10HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves9PZC8_y3cC8TF)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open10_hf_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c) r t
      (_root_.HDec.HSyn.addedLeaves8_of_open9_pz_c8_y3c_c8tf l hY3) g hF5 hYu hθ
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3615 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1894
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open17_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open17_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open17_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves12PZC8C8TF)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) (h6 : _root_.HDec.D2A6.R6U)
    (hSS : _root_.ZInQ.SSFaltings.SemistableReductionThmIF)
    (hY3 : TSHecke.Y3Connected)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open11_hf_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.researchLeaves9_of_open14_hf_gm_pz_eb_sf_u_c8_y3c_nos_c8tf r t l h6
      hSS) t (_root_.HDec.HSyn.GR9.addedLeaves9_of_open14_hf_gm_pz_eb_sf_u_c8_y3c_nos_c8tf r t l) g
    (_root_.ReductSplit.faltingsLemma5BCLower_final _root_.GapHeight.faltingsLemma5Lower) hYu hY3 hθ
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3640 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1921
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open18_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj
/-- `sixContactMin_of_open18_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open18_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves13PZC8C8TF)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) (h6 : _root_.HDec.D2A6.R6U)
    (hSS : _root_.ZInQ.SSFaltings.SemistableReductionThmIF)
    (hY3 : TSHecke.Y3Connected)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open17_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c) r t
      (addedLeaves12_of_open13_pz_c8_c8tf l) g hYu h6 hSS hY3 hθ
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3666 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1945
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open19_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open19_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open19_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves13PZC8C8TF) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (h6 : _root_.HDec.D2A6.R6U)
    (hSS : _root_.ZInQ.SSFaltings.SemistableReductionThmIF)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open18_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves14_of_OpenResearchLeaves15_gm_eb_sf_u_y3c_nos r) t l
      g hYu h6 hSS hY3
    HDec.ThetaDirect.thetaRatiosAtQM_of_qmHauptmodul
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3690 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1969
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open20_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open20_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open20_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves14PZC8C8TF) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open19_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves15_of_OpenResearchLeaves16_gm_eb_sf_u_y3c_nos r) t
      (openAddedLeaves13_of_OpenAddedLeaves14_pz_c8_c8tf l) g hYu
    (_root_.HDec.HSyn.GR9.raynaudCriterionNF_of14_hf_gm_eb_sf_u_y3c_nos
      (_root_.HDec.HSyn.GR9.openResearchLeaves14_of_OpenResearchLeaves15_gm_eb_sf_u_y3c_nos
          (_root_.HDec.HSyn.GR9.openResearchLeaves15_of_OpenResearchLeaves16_gm_eb_sf_u_y3c_nos r))
          t)
    (_root_.HDec.HSyn.GR9.ss1_ss3_of14NF_hf_gm_pz_eb_sf_u_c8_y3c_nos_c8tf
        (_root_.HDec.HSyn.GR9.openResearchLeaves14_of_OpenResearchLeaves15_gm_eb_sf_u_y3c_nos
        (_root_.HDec.HSyn.GR9.openResearchLeaves15_of_OpenResearchLeaves16_gm_eb_sf_u_y3c_nos r)) t
      (addedLeaves12_of_open13_pz_c8_c8tf (openAddedLeaves13_of_OpenAddedLeaves14_pz_c8_c8tf l)))
          hY3
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3715 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:1994
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open21_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open21_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open21_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves14PZC8C8TF) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open20_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves16_of_OpenResearchLeaves17_gm_eb_sf_u_y3c_nos r) t l
      g hYu hY3
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3736 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:2015
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open22_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open22_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open22_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves14PZC8C8TF) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open21_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves17_of_OpenResearchLeaves18_gm_eb_sf_u_y3c_nos r) t l
      g hYu hY3
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3757 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:2036
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open23_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open23_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open23_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves14PZC8C8TF) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open22_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves18_of_OpenResearchLeaves19_gm_eb_sf_u_y3c_nos r) t l
      g hYu hY3
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3778 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:2057
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open24_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open24_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open24_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves15PZC8C8TF) (g : OpenGlue7)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open23_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c) r t
      (openAddedLeaves14_of_OpenAddedLeaves15_hf_pz_c8_c8tf l t) g
    (QMLattice.yuB6Alg_of' t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed) hY3
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3800 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:2079
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open25_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open25_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open25_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves16PZC8C8TF) (g : OpenGlue7)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open24_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c) r t
      (openAddedLeaves15_of_OpenAddedLeaves16_pz_c8_c8tf l) g hY3
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3821 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:2100
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open26_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open26_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open26_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves16PZC8C8TF) (g : OpenGlue7)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open25_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c) r
      (openTextbookLeaves10_of_OpenTextbookLeaves11_hf t) l g hY3
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3842 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:2121
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open27_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open27_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open27_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves16PZC8C8TF) (g : OpenGlue7)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open26_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves19_of_OpenResearchLeaves20_hf_gm_eb_sf_u_y3c_nos r t)
      t l g hY3
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3863 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:2142
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open28_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open28_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open28_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves17PZC8C8TF) (g : OpenGlue7) (c : _root_.HDec.CMBranch.CMInputs3) :
    ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open27_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves20_of_OpenResearchLeaves21_hf_gm_eb_sf_u_y3c_nos r t)
      t (openAddedLeaves16_of_OpenAddedLeaves17_pz_c8_c8tf l) g
    (_root_.DCY3Used.y3Connected_of_ab_gl (_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr
        r.mumfordGroupLaw)
      (_root_.DCY3Used.y3ConnectedAb_of_U r.shimuraMainThmIDeligneY3AbU))
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3885 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:2164
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open29_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open29_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open29_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves17PZC8C8TF) (g : OpenGlue7) (c : _root_.HDec.CMBranch.CMInputs3) :
    ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open28_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves21_of_OpenResearchLeaves22_hf_gm_eb_sf_u_y3c_nos r t)
      t l g
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3905 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:2184
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open30_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open30_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open30_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves17PZC8C8TF) (g : OpenGlue7) (c : _root_.HDec.CMBranch.CMInputs3) :
    ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open29_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves22_of_OpenResearchLeaves23_gm_eb_sf_u_y3c_nos r) t l g
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3925 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:2204
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open31_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open31_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open31_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3cNOS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves17PZC8C8TF) (g : OpenGlue7) (c : _root_.HDec.CMBranch.CMInputs3) :
    ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open30_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves23_of_OpenResearchLeaves24_hf_gm_eb_sf_u_y3c_nos r t)
      t l g
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3945 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:2224
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open32_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open32_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open32_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves17PZC8C8TF) (g : OpenGlue7) (c : _root_.HDec.CMBranch.CMInputs3) :
    ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open31_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves24_of_OpenResearchLeaves25_gm_eb_sf_u_y3c_nos r) t l g
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3965 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:2244
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open33_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open33_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open33_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves17PZC8C8TF)
    (g : OpenGlue8) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open32_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c) r t l
      (_root_.HDec.HSyn.GR9.openGlue7_of_OpenGlue8_hf_gm_pz_eb_sf_u_c8_y3c_nos_c8tf r t l g)
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:3986 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:2265
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open34_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open34_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open34_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves17PZC8C8TF) (g : OpenGlue8) (c : _root_.HDec.CMBranch.CMInputs3) :
    ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open33_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves25_of_OpenResearchLeaves26_hf_gm_eb_sf_u_y3c_nos r t)
      t l g
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:4006 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:2285
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open35_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open35_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open35_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOS) (t : OpenTextbookLeaves12HF) (l :
    OpenAddedLeaves17PZC8C8TF) (g : OpenGlue8) (c : _root_.HDec.CMBranch.CMInputs3) :
    ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open34_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c) r
      (openTextbookLeaves11_of_OpenTextbookLeaves12_hf t) l g
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:4026 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy5.lean:2305
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open36_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open36_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open36_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOS) (t : OpenTextbookLeaves12HF) (l :
    OpenAddedLeaves17PZC8C8TF) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open35_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c) r t l
      openGlue8_proof
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:4046 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy6.lean:28
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open37_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open37_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open37_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3cNOS) (t : OpenTextbookLeaves13HF) (l :
    OpenAddedLeaves18PZC8C8TF) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open36_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves26_of_OpenResearchLeaves27_gm_eb_sf_u_y3c_nos r)
      (openTextbookLeaves12_of_OpenTextbookLeaves13_hf t)
      (openAddedLeaves17_of_OpenAddedLeaves18_pz_c8_c8tf l)
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:4066 (there: copied from
-- ZInQKernel/OneProof/H/Y3Copy6.lean:50
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open45_pz_eb_sf_u_hm_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedVariables false
/-- `sixContactMin_of_open45_pz_eb_sf_u_hm` with the base switched to the manuscript's CM branch
(`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_c8tf`); generated by
`scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open45_pz_eb_sf_u_hm_cm_y3c_nos_c8tf (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOS) (t : OpenTextbookLeaves16)
    (hP : _root_.ZInQ.Contrib.AVB1.PoincareComplement) (c : _root_.HDec.CMBranch.CMInputs3) :
    ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open37_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_c8tf (c := c)
    (_root_.HDec.HSyn.GR9.openResearchLeaves27_of_OpenResearchLeaves28_gm_eb_sf_u_y3c_nos
      (_root_.HDec.HSyn.GR9.openResearchLeaves28_of_OpenResearchLeaves29_gm_eb_sf_u_y3c_nos
          (_root_.HDec.HSyn.GR9.openResearchLeaves29GM_of_OpenResearchLeaves31_eb_sf_u_y3c_nos r)))
    (openTextbookLeaves13HF_of_open16_P t r.neronSchemeExtensionDedekind hP)
    (openAddedLeaves18_hm_c8tf)
end HDec.HSyn.GR9
end

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:4677 (there: copied from
-- ZInQKernel/OneProof/H/TailZ89.lean:79 (openResearchLeaves60_y3x6_of_OpenResearchLeaves63))
namespace HDec
namespace HSyn
/-- `OpenResearchLeaves60_y3x6NOS` from the new generation (fold-c8's conversion without the
Gonzalez-Rotger field). -/
theorem openResearchLeaves60_y3x6_of_OpenResearchLeaves63_nos_c8tf (n : OpenResearchLeaves63NOS) (l
    : OpenAddedLeaves28C8TF) : OpenResearchLeaves60_y3x6NOS where
  r9a := n.r9a
  r9b := n.r9b
  pazukiCor13Upper := n.pazukiCor13Upper
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  panPrintedF := n.panPrintedF
  afCharpolyDS965 := n.afCharpolyDS965
  deRhamVpAbVarDirect := n.deRhamVpAbVarDirect
  hodgeTateDecompOr := _root_.DeRhamScholze.HTMerge.hodgeTateDecompOr_of_scholzeH1Milne
      l.scholzeH1AbVar l.t10TateDuality
  modularHTCoeff := n.modularHTCoeff
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  elliotWildInertiaTrivial := n.elliotWildInertiaTrivial
  bergerSurveyF := n.bergerSurveyF
  deligneCanonicalModelY3EveryPrint := n.deligneCanonicalModelY3EveryPrint
  gaudronRemondSec9LowerAnSS := n.gaudronRemondSec9LowerAnSS
  gaudronRemondThm14AnSS := n.gaudronRemondThm14AnSS
  javanpeykarThm111An := n.javanpeykarThm111An
  silverbergZarhinThm35 := n.silverbergZarhinThm35
  y3FullThreeRepZ30 := n.y3FullThreeRepZ30
  carayolThmAFrob := n.carayolThmAFrob
  bShStandardModel := n.bShStandardModel
  shimuraThm1Af := n.shimuraThm1Af
  y3ToP1j := n.y3ToP1j
  heckeSqrtBranchAny := n.heckeSqrtBranchAny
end HSyn
end HDec

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:4710 (there: copied from
-- ZInQKernel/OneProof/H/TailZ89.lean:110 (sixContactMin_of_open82))
namespace HDec
namespace HSyn
/-- **G0 with only the open leaves and the open glue** (fold-cm, the CM-branch package with y3-x6b):
the manuscript's CM
branch (L581-631) in place of NoCM and the moduli row over `Y₃` (L411-526) in place of `X₆`; no
González–Rotger
statement and no `X₆` clause is read. -/
theorem sixContactMin_of_open82_nos_c8tf (r : OpenResearchLeaves63NOS) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves28C8TF) : ZInQ.SixContactMin :=
  let t16 := openTextbookLeaves16_of_OpenTextbookLeaves17
      (openTextbookLeaves17_of_OpenTextbookLeaves18 t)
  _root_.HDec.HSyn.GR9.sixContactMin_of_open45_pz_eb_sf_u_hm_cm_y3c_nos_c8tf
    (c := ⟨r.cmFibreSplit, r.fowlerProp27, r.cmjDegree, r.cmPotentialGood, r.cmHeight62⟩)
    (_root_.HDec.HSyn.GR9.openResearchLeaves31_of_OpenResearchLeaves32_eb_cf_sf_u_y3c_nos
      (_root_.HDec.HSyn.GR9.openResearchLeaves32_of_OpenResearchLeaves33_eb_cf_sf_u_y3c_nos
        (_root_.HDec.HSyn.GR9.openResearchLeaves33_of_OpenResearchLeaves34_eb_cf_sf_u_y3c_nos
          (_root_.HDec.HSyn.GR9.openResearchLeaves34_y3c_of_35EBCFSFU_y3x6_nos
            (GR9.openResearchLeaves35EBCFSFU_y3x6_of_36_y3x6_nos
              (GR9.openResearchLeaves36EBCFSFU_y3x6_of_54SFU_y3x6_nos
                (openResearchLeaves54SFU_y3x6_of_59_y3x6_nos
                    (openResearchLeaves59_y3x6_of_60_y3x6_nos
                  (openResearchLeaves60_y3x6_of_OpenResearchLeaves63_nos_c8tf r l))) t)
              (_root_.DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1 l.scholzeH1AbVar
                  l.t10TateDuality)) t16) t16)))
    t16 _root_.ZInQ.Contrib.CloudR2Poincare.poincareComplement_proof
end HSyn
end HDec

-- copied from ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:4833 (there: copied from
-- ZInQKernel/OneProof/H/TailZ90.lean:106 (sixContactMin_of_open83))
namespace HDec
namespace HSyn
/-- **G0 with only the open leaves and the open glue** (hecke-sqrt; generated). -/
theorem sixContactMin_of_open83_nos_c8tf (r : OpenResearchLeaves64NOS) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves28C8TF) : ZInQ.SixContactMin :=
  sixContactMin_of_open82_nos_c8tf (openResearchLeaves63_of_OpenResearchLeaves64_nos r) t l
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ91.lean:104
namespace HDec
namespace HSyn
/-- The H chain with the NOS row removed. -/
theorem sixContactMin_of_open84_c8tf (r : OpenResearchLeaves65) (t : OpenTextbookLeaves18) (l :
    OpenAddedLeaves28C8TF) : ZInQ.SixContactMin :=
  sixContactMin_of_open83_nos_c8tf (openResearchLeaves64NOS_of_OpenResearchLeaves65 r) t l
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ92.lean:66
namespace HDec
namespace HSyn
/-- `OpenResearchLeaves65` from `OpenResearchLeaves66`: `deRhamVpAbVarDirect`, `cmFibreSplit` by the
contributions. -/
theorem openResearchLeaves65_of_OpenResearchLeaves66_c8tf (n : OpenResearchLeaves66) (l :
    OpenAddedLeaves28C8TF) : OpenResearchLeaves65 where
  r9a := n.r9a
  r9b := n.r9b
  pazukiCor13Upper := n.pazukiCor13Upper
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  panPrintedF := n.panPrintedF
  afCharpolyDS965 := n.afCharpolyDS965
  deRhamVpAbVarDirect := _root_.DeRhamScholze.HTMerge.deRhamVpAbVarDirect_of_scholzeH1Milne
      l.scholzeH1AbVar l.t10TateDuality
  modularHTCoeff := n.modularHTCoeff
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  elliotWildInertiaTrivial := n.elliotWildInertiaTrivial
  bergerSurveyF := n.bergerSurveyF
  deligneCanonicalModelY3EveryPrint := n.deligneCanonicalModelY3EveryPrint
  gaudronRemondSec9LowerAnSS := n.gaudronRemondSec9LowerAnSS
  gaudronRemondThm14AnSS := n.gaudronRemondThm14AnSS
  javanpeykarThm111An := n.javanpeykarThm111An
  silverbergZarhinThm35 := n.silverbergZarhinThm35
  y3FullThreeRepZ30 := n.y3FullThreeRepZ30
  carayolThmAFrob := n.carayolThmAFrob
  bShStandardModel := n.bShStandardModel
  shimuraThm1Af := n.shimuraThm1Af
  cmFibreSplit := _root_.HDec.CMBranch.FibreSplit.cmFibreSplit_of_liveInputs_nos
      n.neronSchemeExtensionDedekind n.silverbergZarhinThm35 n.elliotWildInertiaTrivial
      n.y3FullThreeRepZ30 n.deligneCanonicalModelY3EveryPrint n.y3ToP1j
  fowlerProp27 := n.fowlerProp27
  cmjDegree := n.cmjDegree
  cmPotentialGood := n.cmPotentialGood
  cmHeight62 := n.cmHeight62
  y3ToP1j := n.y3ToP1j
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ92.lean:97
namespace HDec
namespace HSyn
/-- **G0 with only the open leaves and the open glue** (pr106 + cm-port2; generated). -/
theorem sixContactMin_of_open85_c8tf (r : OpenResearchLeaves66) (t : OpenTextbookLeaves18) (l :
    OpenAddedLeaves28C8TF) : ZInQ.SixContactMin :=
  sixContactMin_of_open84_c8tf (openResearchLeaves65_of_OpenResearchLeaves66_c8tf r l) t l
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ93.lean:95
namespace HDec
namespace HSyn
/-- **G0 with only the open leaves and the open glue** (faltings-fold; generated). -/
theorem sixContactMin_of_open86_c8tf (r : OpenResearchLeaves67) (t : OpenTextbookLeaves18) (l :
    OpenAddedLeaves28C8TF) : ZInQ.SixContactMin :=
  sixContactMin_of_open85_c8tf (openResearchLeaves66_of_OpenResearchLeaves67 r) t l
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ94.lean:95
namespace HDec
namespace HSyn
/-- **G0 with only the open leaves and the open glue** (fowler-fold; generated). -/
theorem sixContactMin_of_open87_c8tf (r : OpenResearchLeaves68) (t : OpenTextbookLeaves18) (l :
    OpenAddedLeaves28C8TF) : ZInQ.SixContactMin :=
  sixContactMin_of_open86_c8tf (openResearchLeaves67_of_OpenResearchLeaves68 r) t l
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ95.lean:93
namespace HDec
namespace HSyn
/-- **G0 with only the open leaves and the open glue** (bsh-fold; generated). -/
theorem sixContactMin_of_open88_c8tf (r : OpenResearchLeaves69) (t : OpenTextbookLeaves18) (l :
    OpenAddedLeaves28C8TF) : ZInQ.SixContactMin :=
  sixContactMin_of_open87_c8tf (openResearchLeaves68_of_OpenResearchLeaves69 r) t l
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ96.lean:90
namespace HDec
namespace HSyn
/-- **G0 with only the open leaves and the open glue** (cm-serre-tate; generated). -/
theorem sixContactMin_of_open89_c8tf (r : OpenResearchLeaves70) (t : OpenTextbookLeaves18) (l :
    OpenAddedLeaves28C8TF) : ZInQ.SixContactMin :=
  sixContactMin_of_open88_c8tf (openResearchLeaves69_of_OpenResearchLeaves70 r) t l
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ97.lean:89
namespace HDec
namespace HSyn
/-- **G0 with only the open leaves and the open glue** (elliot-wild; generated). -/
theorem sixContactMin_of_open90_c8tf (r : OpenResearchLeaves71) (t : OpenTextbookLeaves18) (l :
    OpenAddedLeaves28C8TF) : ZInQ.SixContactMin :=
  sixContactMin_of_open89_c8tf (openResearchLeaves70_of_OpenResearchLeaves71 r) t l
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ98.lean:89
namespace HDec
namespace HSyn
/-- **G0 with only the open leaves and the open glue** (Fowler singular modulus degree (CM degree
row closed); generated). -/
theorem sixContactMin_of_open91_c8tf (r : OpenResearchLeaves72) (t : OpenTextbookLeaves18) (l :
    OpenAddedLeaves28C8TF) : ZInQ.SixContactMin :=
  sixContactMin_of_open90_c8tf (openResearchLeaves71_of_OpenResearchLeaves72 r) t l
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ99.lean:85
namespace HDec
namespace HSyn
/-- **G0 with only the open leaves and the open glue** (outside-fold-1120; generated). -/
theorem sixContactMin_of_open92_c8tf (r : OpenResearchLeaves73) (t : OpenTextbookLeaves18) (l :
    OpenAddedLeaves28C8TF) : ZInQ.SixContactMin :=
  sixContactMin_of_open91_c8tf (openResearchLeaves72_of_OpenResearchLeaves73 r) t l
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ100.lean:74
namespace HDec
namespace HSyn
/-- **G0 with only the open leaves and the open glue** (outside-fold-1121; generated). -/
theorem sixContactMin_of_open93_c8tf (r : OpenResearchLeaves74) (t : OpenTextbookLeaves18) (l :
    OpenAddedLeaves28C8TF) : ZInQ.SixContactMin :=
  sixContactMin_of_open92_c8tf (openResearchLeaves73_of_OpenResearchLeaves74 r) t l
end HSyn
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ101.lean:75
namespace HDec.HSyn
/-- The same height estimate from the updated research hypotheses. -/
theorem sixContactMin_of_open94_c8tf (r : OpenResearchLeaves75) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves28C8TF) : ZInQ.SixContactMin :=
  sixContactMin_of_open93_c8tf (openResearchLeaves74_of_OpenResearchLeaves75 r) t l
end HDec.HSyn

-- copied from ZInQKernel/OneProof/H/TailZ102.lean:88
namespace HDec
namespace HSyn
/-- **G0 with only the open leaves and the open glue** (sz35-swap-1121; generated). -/
theorem sixContactMin_of_open95_c8tf (r : OpenResearchLeaves76) (t : OpenTextbookLeaves18) (l :
    OpenAddedLeaves28C8TF) : ZInQ.SixContactMin :=
  sixContactMin_of_open94_c8tf (openResearchLeaves75_of_OpenResearchLeaves76 r) t l
end HSyn
end HDec
