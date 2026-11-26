import ZInQKernel.Contrib.OneProof.DS965Reroute.Chain1

/-! # The live chain without `dsThm965AtPrimes` (part 2 of 5; ds965-reroute, generated)

Generated from `NOSNarrowChain.lean` and the generations `TailZ91`–`TailZ103`: every declaration
that takes a bundle carrying a Diamond–Shurman 9.6.5 field, `R14Det` or `GaloisPiecesC8` is copied
with the suffix `DS` / `_ds`. Below the conversion that reads `modularHTCoeff`, the 9.6.5 field is
replaced by `repExists` (R14 without its determinant, from `modularHTCoeff` and
`dsThm966Printed`); above it, it is deleted. `r14` carries `EigenformRepExists` and
`GaloisPiecesC8DS` has no `r14det` (neither determinant is read on this route). The originals are
unchanged.
-/

set_option linter.style.haveILetI false

-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:1299
-- (_root_.HDec.HSyn.GR9.openResearchLeaves21_of_OpenResearchLeaves22_hf_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOSDS` from
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOSDS`: `r16` by the contributions. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves21_of_OpenResearchLeaves22_hf_gm_eb_sf_u_y3c_nos_ds
    (n : _root_.HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves11HF) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOSDS where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  repExists := n.repExists
  dsThm966 := n.dsThm966
  r16 := _root_.R16Split.r16_of_printed n.r16CoreY t.mumfordTorsionAlgClosed
      t.charPolyIndepOfEllAlgClosed
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := n.mumfordGroupLaw
  y3row := n.y3row
  raynaudSemistableSH := n.raynaudSemistableSH
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  heckeSqrtY3 := n.heckeSqrtY3
  r6u := n.r6u
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:1341
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOSDS` without `sga7_IX_3_3`, `r6u`, with
  the leaves `sga7_IX_3_3_SH`, `r6u` (leaf-fold20). -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOSDS : Prop where
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each
    connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune
  proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3
  -- VI_B 3.10)
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the
    canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class
  form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of
  conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I
    Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O`
  and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in
  `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically
  closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with
  `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models
    commute with strict henselization), for unramified strictly henselian extensions with
    separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces
    strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction
    semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a
    time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability
    read on the geometric special fibre; reading risk: if the print reads it over k(s), this form
    exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue
    fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward).
    Replaces r6u; StrictHenselizationInside and the K^s axis are proved. -/
  r6u : _root_.HDec.D2A6.R6U
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:1416
-- (_root_.HDec.HSyn.GR9.openResearchLeaves20_of_OpenResearchLeaves21_hf_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOSDS` from
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOSDS`: `rayClassCMAb`, `shimuraFamilyAb`
  by the contributions. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves20_of_OpenResearchLeaves21_hf_gm_eb_sf_u_y3c_nos_ds
    (n : _root_.HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves11HF) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOSDS where
  shimuraFamilyAb := _root_.RayClassCFT.shimuraFamilyAb_of_U n.shimuraMainThmIDeligneY3AbU
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  repExists := n.repExists
  dsThm966 := n.dsThm966
  r16 := n.r16
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := n.mumfordGroupLaw
  y3row := n.y3row
  rayClassCMAb := _root_.RayClassCFT.rayClassCMAb_of_leaves n.shimuraMainThmIDeligneY3AbU
      t.uniformizationLeafAll t.gagaMorphism
  raynaudSemistableSH := n.raynaudSemistableSH
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  heckeSqrtY3 := n.heckeSqrtY3
  r6u := n.r6u
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:1459
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOSDS` without `elkiesEquationsX6Ab`,
  with the leaves `elkiesX6StarPrinted` (leaf-fold18). -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOSDS : Prop where
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest
    reading). -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each
    connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune
  proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3
  -- VI_B 3.10)
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the
    canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class
  form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of
  conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I
    Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O`
  and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in
  `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically
  closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with
  `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models
    commute with strict henselization), for unramified strictly henselian extensions with
    separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces
    strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:1534
-- (_root_.HDec.HSyn.GR9.openResearchLeaves19_of_OpenResearchLeaves20_hf_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOSDS` from
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOSDS`: `sga7_IX_3_3`, `r6u` by the
  contributions. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves19_of_OpenResearchLeaves20_hf_gm_eb_sf_u_y3c_nos_ds
    (n : _root_.HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves11HF) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOSDS where
  shimuraFamilyAb := n.shimuraFamilyAb
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  repExists := n.repExists
  dsThm966 := n.dsThm966
  r16 := n.r16
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  r6u := n.r6u
  mumfordGroupLaw := n.mumfordGroupLaw
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  y3row := n.y3row
  rayClassCMAb := n.rayClassCMAb
  raynaudSemistableSH := n.raynaudSemistableSH
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  heckeSqrtY3 := n.heckeSqrtY3
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:1577
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOSDS` without `strictHenselizationPair`,
  with the leaves `neronBaseChangeStrictHenselization` (leaf-fold18). -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOSDS : Prop where
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest
    reading). -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each
    connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune
  proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3
  -- VI_B 3.10)
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the
    canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class
  form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of
  conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I
    Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O`
  and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in
  `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically
  closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with
  `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models
    commute with strict henselization), for unramified strictly henselian extensions with
    separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces
    strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:1652
-- (_root_.HDec.HSyn.GR9.openResearchLeaves18_of_OpenResearchLeaves19_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOSDS` from
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOSDS`: `elkiesEquationsX6Ab` by the
  contributions. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves18_of_OpenResearchLeaves19_gm_eb_sf_u_y3c_nos_ds (n
    : _root_.HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOSDS) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOSDS where
  shimuraFamilyAb := n.shimuraFamilyAb
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  repExists := n.repExists
  dsThm966 := n.dsThm966
  r16 := n.r16
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  r6u := n.r6u
  mumfordGroupLaw := n.mumfordGroupLaw
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  y3row := n.y3row
  heckeSqrtY3 := n.heckeSqrtY3
  rayClassCMAb := n.rayClassCMAb
  raynaudSemistableSH := n.raynaudSemistableSH
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:27
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOSDS` without `gonzalezRotgerCountX6Ab`,
  with the leaves `gonzalezRotgerProp56X6` (gt-grcount-fold). -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOSDS : Prop where
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest
    reading). -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each
    connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune
  proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3
  -- VI_B 3.10)
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the
    canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class
  form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of
  conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I
    Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O`
  and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in
  `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically
  closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with
  `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-glue, composite (GLUE): strict henselization along a finite extension of DVRs (EGA
    IV₄ 18.8.10 and
  18.6.8, Stacks 05WR) with Néron models commuting with it (BLR §1.2 Prop. 2); numbers UNVERIFIED.
  -/
  strictHenselizationPair : _root_.ReductGlue.StrictHenselizationPair
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:103
-- (_root_.HDec.HSyn.GR9.openResearchLeaves17_of_OpenResearchLeaves18_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOSDS` from
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOSDS`: `strictHenselizationPair` by the
  contributions. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves17_of_OpenResearchLeaves18_gm_eb_sf_u_y3c_nos_ds (n
    : _root_.HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOSDS) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOSDS where
  shimuraFamilyAb := n.shimuraFamilyAb
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  repExists := n.repExists
  dsThm966 := n.dsThm966
  r16 := n.r16
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  r6u := n.r6u
  mumfordGroupLaw := n.mumfordGroupLaw
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  y3row := n.y3row
  heckeSqrtY3 := n.heckeSqrtY3
  rayClassCMAb := n.rayClassCMAb
  raynaudSemistableSH := n.raynaudSemistableSH
  strictHenselizationPair := _root_.GapSHPair.strictHenselizationPair_of_neron
      n.neronBaseChangeStrictHenselization
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:146
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOSDS` without `blr_1_2_4`, `igusaPsi4`,
  `igusaChi10` (leaf-fold16). -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOSDS : Prop where
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest
    reading). -/
  r6u : _root_.HDec.D2A6.R6U
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerCountX6Ab : _root_.GR56.R5fpCountLe
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each
    connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune
  proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3
  -- VI_B 3.10)
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the
    canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class
  form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of
  conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I
    Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O`
  and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in
  `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically
  closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with
  `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-glue, composite (GLUE): strict henselization along a finite extension of DVRs (EGA
    IV₄ 18.8.10 and
  18.6.8, Stacks 05WR) with Néron models commuting with it (BLR §1.2 Prop. 2); numbers UNVERIFIED.
  -/
  strictHenselizationPair : _root_.ReductGlue.StrictHenselizationPair
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:222
-- (_root_.HDec.HSyn.GR9.openResearchLeaves16_of_OpenResearchLeaves17_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOSDS` from
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOSDS`: `gonzalezRotgerCountX6Ab` by the
  contributions. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves16_of_OpenResearchLeaves17_gm_eb_sf_u_y3c_nos_ds (n
    : _root_.HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOSDS) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOSDS where
  shimuraFamilyAb := n.shimuraFamilyAb
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  repExists := n.repExists
  dsThm966 := n.dsThm966
  r16 := n.r16
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  r6u := n.r6u
  gonzalezRotgerCountX6Ab := n.gonzalezRotgerProp56X6
  mumfordGroupLaw := n.mumfordGroupLaw
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  y3row := n.y3row
  heckeSqrtY3 := n.heckeSqrtY3
  rayClassCMAb := n.rayClassCMAb
  raynaudSemistableSH := n.raynaudSemistableSH
  strictHenselizationPair := n.strictHenselizationPair
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:265
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOSDS` without `egaIV_8_10_5_openImm`
  (gt-ega). -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOSDS : Prop where
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest
    reading). -/
  r6u : _root_.HDec.D2A6.R6U
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerCountX6Ab : _root_.GR56.R5fpCountLe
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each
    connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune
  proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  /-- c-to-printed, printed form: Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.2 Prop. 4 (over a
    Dedekind
  domain, a smooth separated model of finite type is a Néron model iff its localizations at the
  closed points are;
  locator UNVERIFIED). Replaces `neronLocalizesDVR`. -/
  blr_1_2_4 : _root_.CToPrinted.BLR_1_2_4
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3
  -- VI_B 3.10)
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the
    canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class
  form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of
  conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I
    Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O`
  and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in
  `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically
  closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with
  `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-glue, composite (GLUE): strict henselization along a finite extension of DVRs (EGA
    IV₄ 18.8.10 and
  18.6.8, Stacks 05WR) with Néron models commuting with it (BLR §1.2 Prop. 2); numbers UNVERIFIED.
  -/
  strictHenselizationPair : _root_.ReductGlue.StrictHenselizationPair
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:347
-- (_root_.HDec.HSyn.GR9.openResearchLeaves15_of_OpenResearchLeaves16_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOSDS` from
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOSDS`: `blr_1_2_4`, `igusaPsi4`,
  `igusaChi10` by the contributions. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves15_of_OpenResearchLeaves16_gm_eb_sf_u_y3c_nos_ds (n
    : _root_.HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOSDS) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOSDS where
  shimuraFamilyAb := n.shimuraFamilyAb
  igusaPsi4 := _root_.GapTheta.igusaPsi4_proof
  igusaChi10 := _root_.GapTheta.igusaChi10_proof
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  repExists := n.repExists
  dsThm966 := n.dsThm966
  r16 := n.r16
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  r6u := n.r6u
  gonzalezRotgerCountX6Ab := n.gonzalezRotgerCountX6Ab
  mumfordGroupLaw := n.mumfordGroupLaw
  blr_1_2_4 := _root_.GapBLR.blr_1_2_4
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  y3row := n.y3row
  heckeSqrtY3 := n.heckeSqrtY3
  rayClassCMAb := n.rayClassCMAb
  raynaudSemistableSH := n.raynaudSemistableSH
  strictHenselizationPair := n.strictHenselizationPair
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:395
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- **The research leaves still open** (leaf-fold14, reduct fold): x6-fold's
  `OpenResearchLeaves13` without
`semistableReductionDVR`, `raynaudSemistable` and `semistablePersistsDVR` (reduct-b), with
`raynaudSemistableSH`, `semistablePersistsSHcp` and `strictHenselizationPair` added. 35 fields. -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOSDS : Prop where
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest
    reading). -/
  r6u : _root_.HDec.D2A6.R6U
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerCountX6Ab : _root_.GR56.R5fpCountLe
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each
    connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune
  proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  /-- c-to-printed, printed form: Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.2 Prop. 4 (over a
    Dedekind
  domain, a smooth separated model of finite type is a Néron model iff its localizations at the
  closed points are;
  locator UNVERIFIED). Replaces `neronLocalizesDVR`. -/
  blr_1_2_4 : _root_.CToPrinted.BLR_1_2_4
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3
  -- VI_B 3.10)
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- c-to-printed, printed form: EGA IV 8.10.5, open immersions descend through limits (locator
    UNVERIFIED). -/
  egaIV_8_10_5_openImm : _root_.CToPrinted.EGAIV_8_10_5_openImm
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the
    canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class
  form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of
  conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I
    Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O`
  and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in
  `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically
  closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with
  `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-glue, composite (GLUE): strict henselization along a finite extension of DVRs (EGA
    IV₄ 18.8.10 and
  18.6.8, Stacks 05WR) with Néron models commuting with it (BLR §1.2 Prop. 2); numbers UNVERIFIED.
  -/
  strictHenselizationPair : _root_.ReductGlue.StrictHenselizationPair
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:479
-- (_root_.HDec.HSyn.GR9.openResearchLeaves14_of_OpenResearchLeaves15_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOSDS` from
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOSDS`: `egaIV_8_10_5_openImm` by the
  contributions. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves14_of_OpenResearchLeaves15_gm_eb_sf_u_y3c_nos_ds (n
    : _root_.HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOSDS) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOSDS where
  shimuraFamilyAb := n.shimuraFamilyAb
  igusaPsi4 := n.igusaPsi4
  igusaChi10 := n.igusaChi10
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  repExists := n.repExists
  dsThm966 := n.dsThm966
  r16 := n.r16
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  r6u := n.r6u
  gonzalezRotgerCountX6Ab := n.gonzalezRotgerCountX6Ab
  mumfordGroupLaw := n.mumfordGroupLaw
  blr_1_2_4 := n.blr_1_2_4
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  egaIV_8_10_5_openImm := _root_.ZInQ.Contrib.EGAOpenImm.egaIV_8_10_5_openImm_proof
  y3row := n.y3row
  heckeSqrtY3 := n.heckeSqrtY3
  rayClassCMAb := n.rayClassCMAb
  raynaudSemistableSH := n.raynaudSemistableSH
  strictHenselizationPair := n.strictHenselizationPair
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:550
-- (_root_.HDec.HSyn.GR9.raynaudSemistable_of14_hf_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- **SGA 7 IX 4.7 over a DVR** (the old field `raynaudSemistable`) from the strictly henselian
  printed leaf, the
pair and the textbook field `mulEtaleAbelianScheme` (reduct-b, Route B). -/
theorem _root_.HDec.HSyn.GR9.raynaudSemistable_of14_hf_gm_eb_sf_u_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) :
    _root_.ReductSplit.RaynaudSemistable :=
  _root_.ReductB.raynaudSemistable_of_SH_pair r.raynaudSemistableSH r.strictHenselizationPair
    t.mulEtaleAbelianScheme
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:573
-- (_root_.HDec.HSyn.GR9.raynaudCriterionNF_of14_hf_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- **r6 at number fields** (r6-nf) from leaf-fold14's bundles: neron-dvr's
  `GapNeron.raynaudCriterion_leavesNF`
with the Néron field at number fields proved from the textbook field N1
(`GapNeron.neronSchemeModelExistsNF`),
replacing `ReductGlue.raynaudCriterion_leaves … r.neronSchemeModelExistsDVR …` (BLR 1.4/3 over
every DVR). -/
theorem _root_.HDec.HSyn.GR9.raynaudCriterionNF_of14_hf_gm_eb_sf_u_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) :
    _root_.HDec.D2A6.R6U :=
  r.r6u
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:598
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open CategoryTheory AlgebraicGeometry Limits
/-- **The research leaves still open** (leaf-fold9): leaf-fold8's
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOSDS` without `r1rec`, `r5`
(proved from `r1r2`, `_root_.HDec.HSyn.r1rec_of_rep_y3c`, `r5fp_of_rep`) and `r15` (proved from
`dsThm966`, modular-split's
`deligneSerreConseq_of_ds`), and `r7b`, `r8` replaced by reduct-split's four published-form leaves
(`ReductSplit.serreTatePotentialGood_final`, `grothendieckMonodromy_final'`), and `r5count`
replaced by shimura-split's
`GonzalezRotgerCountX6` (`ShimuraSplit.r5fpCount_of_points`). 30 fields. -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOSDS : Prop where
  r1r2 : _root_.HDec.LeafAdopt.R1R2fpRepW_y3c
  shimuraFamily : QMSplit.Moduli.ShimuraFamily
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r6 : _root_.HDec.D2A6.R6U
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- ss-faltings: semistable reduction over every number field containing `K(A[15])`, from
    Raynaud's criterion (`ZInQ.SSFaltings.semistableReductionThmIF_of_raynaud`); replaces SS1 and
    SS3. -/
  semistableReductionThmIF : _root_.ZInQ.SSFaltings.SemistableReductionThmIF
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension; replaces SS2 (SGA 7 IX Cor. 3.3). -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerCountX6 : _root_.GR56.R5fpCountLe
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:652
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- **The research leaves still open** (leaf-fold8): leaf-fold7's
  `_root_.HDec.HSyn.OpenResearchLeaves7EBU_y3cNOSDS` with the six height rows
`r18`-`r22`, `h5fin` replaced by height-split's leaves over the published stable height. 31
fields. -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOSDS : Prop where
  r1r2 : _root_.HDec.LeafAdopt.R1R2fpRepW_y3c
  shimuraFamily : QMSplit.Moduli.ShimuraFamily
  r1rec : LeafQM.AV.R1rec
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r5 : True
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  r5count : _root_.GR56.R5fpCountLe
  r6 : _root_.HDec.D2A6.R6U
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r15 : DeligneSerreConseq
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- ss-faltings: semistable reduction over every number field containing `K(A[15])`, from
    Raynaud's criterion (`ZInQ.SSFaltings.semistableReductionThmIF_of_raynaud`); replaces SS1 and
    SS3. -/
  semistableReductionThmIF : _root_.ZInQ.SSFaltings.SemistableReductionThmIF
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension; replaces SS2 (SGA 7 IX Cor. 3.3). -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:707
-- (_root_.HDec.HSyn.GR9.researchLeaves8_of_open9_hf_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open CategoryTheory AlgebraicGeometry Limits
/-- leaf-fold8's research bundle from leaf-fold9's. -/
theorem _root_.HDec.HSyn.GR9.researchLeaves8_of_open9_hf_eb_sf_u_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOSDS) (t : OpenTextbookLeaves9HF) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOSDS where
  r1r2 := r.r1r2
  shimuraFamily := r.shimuraFamily
  r1rec := _root_.HDec.HSyn.r1rec_of_rep_y3c r.r1r2
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
  r5 := trivial
  r5count := r.gonzalezRotgerCountX6
  r6 := r.r6
  r9a := r.r9a
  r9b := r.r9b
  hodgeTateDecompAbVar := r.hodgeTateDecompAbVar
  deRhamH1AbVarT := r.deRhamH1AbVarT
  r11r12 := r.r11r12
  eigenformHTNew := r.eigenformHTNew
  repExists := r.repExists
  dsThm966 := r.dsThm966
  r15 := _root_.ModularSplit.deligneSerreConseq_of_ds r.dsThm966
  r16 := r.r16
  r17 := r.r17
  semistableReductionThmIF := r.semistableReductionThmIF
  faltingsSemistableHeightBC := r.faltingsSemistableHeightBC
  bostLowerBound := r.bostLowerBound
  javanpeykarBound := r.javanpeykarBound
  pazukiCor13Upper := r.pazukiCor13Upper
  gaudronRemondThm14 := r.gaudronRemondThm14
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:754
-- (_root_.HDec.HSyn.GR9.r20Lower_of8_hf_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- **The lower half of R20** (sem-prune) from the lower half of `faltingsLemma5BC` and the fields
`heightRows_of8` uses for R20 (N1 from `neronSchemeExtensionExists`, SS1, SS2, SS3). -/
theorem _root_.HDec.HSyn.GR9.r20Lower_of8_hf_eb_sf_u_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOSDS) (t : OpenTextbookLeaves8HF)
    (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) : G0Split.R20Lower :=
  _root_.ZInQ.SSFaltings.r20Lower_of_leavesF hF5
    (_root_.ZInQ.Contrib.NeronC.neronModelExists_of_extension t.neronSchemeExtensionExists)
    r.semistableReductionThmIF r.faltingsSemistableHeightBC
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:779
-- (_root_.HDec.HSyn.GR9.heightRowsNo20_of8_hf_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- **The five height rows other than R20** (sem-prune), from the fields `heightRows_of8` reads
  except
`faltingsLemma5BC`: the proofs of `ZInQ.HeightSplit.heightRows_of`'s other components. -/
theorem _root_.HDec.HSyn.GR9.heightRowsNo20_of8_hf_eb_sf_u_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOSDS) (t : OpenTextbookLeaves8HF) :
    _root_.ZInQ.LeafPush2.R18_Javanpeykar ∧ _root_.ZInQ.DefFaltings.R19_GaudronRemond ∧
      _root_.ZInQ.DefFaltings.R21_Bost ∧ _root_.ZInQ.LeafPush2.R22_Pazuki ∧
      _root_.ZInQ.DefFaltings.StableHeightFinite :=
  have hN1 := _root_.ZInQ.Contrib.NeronC.neronModelExists_of_extension t.neronSchemeExtensionExists
  have gl := _root_.ZInQ.HeightGlue.heightGlue_of_t35
    (_root_.AvSplit.Final.h38 t.uniformizationLeafAll t.mumfordTorsionAlgClosed)
  have hMet := _root_.ZInQ.HeightSplit.neronMetrizable_of gl.an3Exists gl.unifDim gl.metrize
  ⟨_root_.ZInQ.SSFaltings.r18_of_leavesF r.javanpeykarBound hN1
      (_root_.ZInQ.SSFaltings.semistableReductionThm_of_IF r.semistableReductionThmIF)
      r.faltingsSemistableHeightBC hMet,
    _root_.ZInQ.SSFaltings.r19_of_leavesF r.gaudronRemondThm14 hN1
        (_root_.ZInQ.SSFaltings.semistableReductionThm_of_IF r.semistableReductionThmIF)
      r.faltingsSemistableHeightBC,
    _root_.ZInQ.SSFaltings.r21_of_grBostF' r.bostLowerBound hN1
        (_root_.ZInQ.SSFaltings.semistableReductionThm_of_IF r.semistableReductionThmIF)
      r.faltingsSemistableHeightBC gl.an3Unique,
    _root_.ZInQ.SSFaltings.r22_of_upperF r.pazukiCor13Upper hN1
        (_root_.ZInQ.SSFaltings.semistableReductionThm_of_IF r.semistableReductionThmIF)
      r.faltingsSemistableHeightBC,
    _root_.ZInQ.SSFaltings.stableHeightFinite_ofF hN1
        (_root_.ZInQ.SSFaltings.semistableReductionThm_of_IF r.semistableReductionThmIF)
        r.faltingsSemistableHeightBC
      hMet gl.an3Unique⟩
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:816
-- (_root_.HDec.HSyn.GR9.researchLeaves7_of_open8_hf_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- leaf-fold7's research bundle from leaf-fold8's. -/
theorem _root_.HDec.HSyn.GR9.researchLeaves7_of_open8_hf_eb_sf_u_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOSDS) (t : OpenTextbookLeaves8HF) :
    _root_.HDec.HSyn.OpenResearchLeaves7EBU_y3cNOSDS where
  r1r2 := r.r1r2
  shimuraFamily := r.shimuraFamily
  r1rec := r.r1rec
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
  r5 := r.r5
  r5count := r.r5count
  r6 := r.r6
  r9a := r.r9a
  r9b := r.r9b
  hodgeTateDecompAbVar := r.hodgeTateDecompAbVar
  deRhamH1AbVarT := r.deRhamH1AbVarT
  r11r12 := r.r11r12
  eigenformHTNew := r.eigenformHTNew
  repExists := r.repExists
  dsThm966 := r.dsThm966
  r15 := r.r15
  r16 := r.r16
  r17 := r.r17
  r18 := r18_lf8 (_root_.HDec.HSyn.GR9.heightRowsNo20_of8_hf_eb_sf_u_y3c_nos_ds r t).1
  r19 := (_root_.HDec.HSyn.GR9.heightRowsNo20_of8_hf_eb_sf_u_y3c_nos_ds r t).2.1
  r21 := (_root_.HDec.HSyn.GR9.heightRowsNo20_of8_hf_eb_sf_u_y3c_nos_ds r t).2.2.1
  r22 := r22_lf8 (_root_.HDec.HSyn.GR9.heightRowsNo20_of8_hf_eb_sf_u_y3c_nos_ds r t).2.2.2.1
  h5fin := (_root_.HDec.HSyn.GR9.heightRowsNo20_of8_hf_eb_sf_u_y3c_nos_ds r t).2.2.2.2
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1161
-- (_root_.HDec.HSyn.qmHauptmodul_of6_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- **`QMHauptmodul` from `QMHauptmodulBase3`** (leafq-check's `base2_of_base3` and
  `qmHauptmodul_of_base2`:
R4, `GammaStarGen` (proved) and the valence bound (from the valence formula)). -/
theorem _root_.HDec.HSyn.qmHauptmodul_of6_pz_eb_u_c8_y3c_nos_ds (r :
    _root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOSDS) (l :
    _root_.HDec.HSyn.OpenAddedLeaves6PZC8_y3c) : PkgI1.QMHauptmodul :=
  LeafQCheck.HM.qmHauptmodul_of_base2
    (LeafQCheck.HM.base2_of_base3 r.r4 LeafQCheck.gammaStarGen_proof
      (LeafQCheck.VB.valenceBound_of_formula l.valenceFormulaGammaStar) l.qmHauptmodulBase3)
end HDec.HSyn
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1183
-- (_root_.HDec.HSyn.researchLeaves5_of_open7_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- leaf-fold6's research bundle (`_root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOSDS`) from
  leaf-fold7's. -/
theorem _root_.HDec.HSyn.researchLeaves5_of_open7_pz_eb_u_c8_y3c_nos_ds (r :
    _root_.HDec.HSyn.OpenResearchLeaves7EBU_y3cNOSDS) (l :
    _root_.HDec.HSyn.OpenAddedLeaves7PZC8_y3c) : _root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOSDS
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
  r13 := HodgeLF7.eigenformHT (_root_.ZInQ.Contrib.HodgeSplit.eigenformHT_of_kato r.eigenformHTNew
    HodgeLF7.newformOfEigenformG9 r.repExists)
  r14 := _root_.DS965Reroute.eigenformRepExists_hsyn_of_g9 r.repExists
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


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1225
-- (_root_.HDec.G0Galois.g8_g12_of_leaves3_hf_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.G0Galois
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
open _root_.PkgI4 (GaloisRep GaloisChar) -- op-dedupe
theorem _root_.HDec.G0Galois.g8_g12_of_leaves3_hf_pz_eb_u_c8_y3c_nos_ds (r :
    _root_.HDec.HSyn.ResearchLeaves3EBU_y3cNOS) (t : HSyn.TextbookLeavesHFPZ) (m : GaloisPiecesC8DS)
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
    (_root_.HDec.G0Galois.C8Conrad.g12DetPZ_of_inputs r.r14 r.r13 m.c8 h9 r.r10)
    A T h2 h6 h3 Tm c ε a β u h7
end HDec.G0Galois
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1256
-- (_root_.HDec.HSyn.cmDescends_of6_hf_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- **`CMDescends` from Shimura–Taniyama** (leafq-check's `cmDescends_of`, with leaf-fold5's
  T11(b) and T5). -/
theorem _root_.HDec.HSyn.cmDescends_of6_hf_pz_eb_u_c8_y3c_nos_ds (r :
    _root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOSDS) (t : OpenTextbookLeaves6HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves6PZC8_y3c) :
    G0Split.FibreQM.PeriodMapH.CMDescends :=
  _root_.HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.cmDescends_ofW_y3c l.stQM
      (t11b_of_exists5 t.t11bExists)
    (G0Split.FibreQM.PeriodMapH.LeafQCheck.torsionDescends_of_t5 (torsionStructure_ofK5 t.t5))
        r.r1r2
end HDec.HSyn
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1277
-- (_root_.HDec.HSyn.addedLeaves4_of_open6_hf_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- leaf-fold4's added-leaves bundle from leaf-fold6's. -/
theorem _root_.HDec.HSyn.addedLeaves4_of_open6_hf_pz_eb_u_c8_y3c_nos_ds (r :
    _root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOSDS) (t : OpenTextbookLeaves6HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves6PZC8_y3c) :
    _root_.HDec.HSyn.OpenAddedLeaves4PZC8_y3c where
  cmOptimalEmbedding := l.cmOptimalEmbedding
  qmHauptmodul := _root_.HDec.HSyn.qmHauptmodul_of6_pz_eb_u_c8_y3c_nos_ds r l
  qmClassNumberOne := l.qmClassNumberOne
  senTwist := l.senTwist
  finiteImageHT := l.finiteImageHT
  c8 := l.c8
  isogenyQuasiInverse := l.isogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  qmAutCard := l.qmAutCard
  serreRigidity3 := serreRigidity3_of_T35_5 (uniformizationExists_ofK5 t.t35) (homLatticeCorr_ofK5
      t.homLatticeCorr)
  alFixedPoints := l.alFixedPoints
  zariskiConnectedness := l.zariskiConnectedness
  cmDescends := _root_.HDec.HSyn.cmDescends_of6_hf_pz_eb_u_c8_y3c_nos_ds r t l
  gammaStarGen := LeafQCheck.gammaStarGen_proof
  valenceBoundGammaStar := LeafQCheck.VB.valenceBound_of_formula l.valenceFormulaGammaStar
  egaIV_8_8_2_ii := l.egaIV_8_8_2_ii
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := l.egaIV_17_7_8_ii
end HDec.HSyn
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1318
-- (_root_.HDec.HSyn.glue4_of_open6_hf_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- leaf-fold4's glue bundle from leaf-fold6's: `HeckeVertWitness` by sgr-direct's route NV
(`_root_.SGRDirect.heckeVertWitness_of_nvSqrtAny_y3c`) from `r1r2`, T5, `qmAutCard`, Serre's
rigidity (from T35),
`alFixedPoints`, `NVLocalInertia` and `HeckeSqrtBranchAny`, without the integral model of the
Shimura curve
(sgr-fold; leaf-fold5's `heckeVertWitness_of_leaves5` needed `shimuraGoodReduction` and
`ModelCoordinateResidue`). -/
theorem _root_.HDec.HSyn.glue4_of_open6_hf_pz_eb_u_c8_y3c_nos_ds (r :
    _root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOSDS) (t : OpenTextbookLeaves6HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves6PZC8_y3c)
    (g : OpenGlue6) : OpenGlue4 where
  heckeVertWitness := _root_.SGRDirect.heckeVertWitness_of_nvSqrtAny_y3c
      (_root_.HDec.LeafAdopt.R1R2fp_of_rep_y3c r.r1r2)
    (torsionStructure_ofK5 t.t5) l.qmAutCard
    (serreRigidity3_of_T35_5 (uniformizationExists_ofK5 t.t35) (homLatticeCorr_ofK5
        t.homLatticeCorr))
    l.alFixedPoints g.nvLocalInertia g.heckeSqrtBranchAny
end HDec.HSyn
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1342
-- (_root_.HDec.HSyn.addedLeaves6_of_open7_hf_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- leaf-fold6's added bundle from leaf-fold7's. -/
theorem _root_.HDec.HSyn.addedLeaves6_of_open7_hf_pz_eb_u_c8_y3c_nos_ds (r :
    _root_.HDec.HSyn.OpenResearchLeaves7EBU_y3cNOSDS) (t : OpenTextbookLeaves7HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves7PZC8_y3c) :
    _root_.HDec.HSyn.OpenAddedLeaves6PZC8_y3c where
  cmOptimalEmbedding := (_root_.HDec.HSyn.qmRows_of7_hf_pz_c8_y3c t l).2.2
  qmHauptmodulBase3 := l.qmHauptmodulBase3
  qmClassNumberOne := QMSplit.CNO.qmClassNumberOne_proof
  senTwist := HodgeLF7.senTwist (_root_.ZInQ.Contrib.HodgeSplit.senTwist_of_tate
      l.tateTwistInvariants l.axSenTate)
  finiteImageHT :=
    HodgeLF7.finiteImageHT (_root_.ZInQ.Contrib.HodgeSplit.finiteImageHT_of_tate
        l.tateTwistInvariants l.axSenTate)
  c8 := l.c8
  isogenyQuasiInverse := isogenyQuasiInverse_lf7 l.milneIsogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  qmAutCard := (_root_.HDec.HSyn.qmRows_of7_hf_pz_c8_y3c t l).1
  alFixedPoints := (_root_.HDec.HSyn.qmRows_of7_hf_pz_c8_y3c t l).2.1
  zariskiConnectedness := l.zariskiConnectedness
  stQM := _root_.GapST.stQM_ofW_y3c r.r1r2 l.y3Connected (_root_.HDec.HSyn.qmRows_of7_hf_pz_c8_y3c
      t l).2.1
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


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1384
-- (_root_.HDec.HSyn.GR9.x6Rows_of_open14_hf_gm_pz_eb_sf_u_c8_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- **The two `X₆` rows from the new bundles** (the term of `x6Rows_of_open13`). pi0-fold: the
  weak row
`_root_.HDec.LeafAdopt.R1R2fpRepW_y3c` from `_root_.HDec.QMSplit.Moduli.x6Rows_of_leavesW_y3c`,
whose base witness is González–Rotger's (`_root_.HDec.QMSplit.Moduli.GonzalezRotgerX6_y3c`); the
added leaves
`deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure` are no longer read. -/
theorem _root_.HDec.HSyn.GR9.x6Rows_of_open14_hf_gm_pz_eb_sf_u_c8_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves12PZC8) :
    _root_.HDec.LeafAdopt.R1R2fpRepW_y3c ∧ _root_.HDec.X6Kummer.X6ConicModel_y3c :=
  have hR := _root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw
  ⟨_root_.Y3X6.r1r2fpY3_of r.y3row ((_root_.LeafQM.AV.R1UnivRigid.rayClassCM_iff_ab_gl hR).mpr
      r.rayClassCMAb), trivial⟩
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1405
-- (_root_.HDec.HSyn.GR9.openGlue7_of_OpenGlue8_hf_gm_pz_eb_sf_u_c8_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `OpenGlue7` from `OpenGlue8`: `HeckeSqrtBranchAny` by the contribution (Elkies' printed model,
  through
generation 22 of the research bundle). -/
theorem _root_.HDec.HSyn.GR9.openGlue7_of_OpenGlue8_hf_gm_pz_eb_sf_u_c8_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves17PZC8)
    (g : OpenGlue8) : OpenGlue7 where
  nvLocalInertia := g.nvLocalInertia
  heckeSqrtBranchAny := r.heckeSqrtY3
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1426
-- (_root_.HDec.HSyn.GR9.addedLeaves9_of_open14_hf_gm_pz_eb_sf_u_c8_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- leaf-fold10's added-leaf bundle from leaf-fold14's (the composite of `addedLeaves11_of_open12`,
`addedLeaves10_of_open11` and `addedLeaves9_of_open10`). -/
theorem _root_.HDec.HSyn.GR9.addedLeaves9_of_open14_hf_gm_pz_eb_sf_u_c8_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves12PZC8) :
    _root_.HDec.HSyn.OpenAddedLeaves9PZC8_y3c where
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  c8 := l.c8
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := (_root_.HDec.HSyn.GR9.x6Rows_of_open14_hf_gm_pz_eb_sf_u_c8_y3c_nos_ds r t l).2
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  valenceFormulaCocompactEq := l.valenceFormulaCocompactEq
  shimizuCovolumeO1 := l.shimizuCovolumeO1
  igusaCMValue24 := _root_.CM24.igusaCMValue24_field
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1455
-- (_root_.HDec.HSyn.GR9.ss1_ss3_of14NF_hf_gm_pz_eb_sf_u_c8_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- **SS1 and SS3** (r6-nf; the reroute of `ss1_ss3_of14`, docs/research/neron-dvr.md §3.2):
  neron-dvr's
`GapNeron.ss1_ss3_of_cpNF`, with the Néron field at number fields from N1. -/
theorem _root_.HDec.HSyn.GR9.ss1_ss3_of14NF_hf_gm_pz_eb_sf_u_c8_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves12PZC8) :
    _root_.ZInQ.SSFaltings.SemistableReductionThmIF :=
  _root_.ZInQ.SSFaltings.semistableReductionThmIF_of_raynaud
      (_root_.HDec.HSyn.GR9.raynaudSemistable_of14_hf_gm_eb_sf_u_y3c_nos_ds r t)
    t.mumfordTorsionAlgClosed t.mulEtaleAbelianScheme
    (_root_.GapNeron.neronSchemeModelExistsNF t.neronSchemeExtensionExists)
    (_root_.ReductGlue.semistableLocalGlobal_leaf (_root_.CToPrinted.neronLocalizesDVR_of_printed
        r.blr_1_2_4))
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1481
-- (_root_.HDec.HSyn.GR9.researchLeaves9_of_open14_hf_gm_pz_eb_sf_u_c8_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- leaf-fold9's research bundle from leaf-fold14's (the composite of `researchLeaves12_of_open13`,
`researchLeaves11_of_open12`, `researchLeaves10_of_open11` and `researchLeaves9_of_open10`, with
the three reduct
fields replaced by reduct-b's theorems). r6-nf: r6 (at number fields) and SS1, SS3 are arguments,
supplied in
`sixContactMin_of_open20_hf_gm_pz_eb_sf_u_c8` (TailZ26) by
`_root_.HDec.HSyn.GR9.raynaudCriterionNF_of14_hf_gm_eb_sf_u_y3c_nos_ds` and
`_root_.HDec.HSyn.GR9.ss1_ss3_of14NF_hf_gm_pz_eb_sf_u_c8_y3c_nos_ds` from neron-dvr's
number-field Néron theorem (N1 alone), which replaced BLR 1.4/3 over every DVR. -/
theorem _root_.HDec.HSyn.GR9.researchLeaves9_of_open14_hf_gm_pz_eb_sf_u_c8_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves12PZC8)
    (h6 : _root_.HDec.D2A6.R6U)
    (hSS : _root_.ZInQ.SSFaltings.SemistableReductionThmIF) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOSDS where
  r1r2 := (_root_.HDec.HSyn.GR9.x6Rows_of_open14_hf_gm_pz_eb_sf_u_c8_y3c_nos_ds r t l).1
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
  repExists := r.repExists
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


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1528
-- (_root_.HDec.HSyn.GR9.addedLeaves7_of_open8_pz_eb_sf_u_c8_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- leaf-fold7's added bundle from leaf-fold8's. -/
theorem _root_.HDec.HSyn.GR9.addedLeaves7_of_open8_pz_eb_sf_u_c8_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOSDS) (l :
    _root_.HDec.HSyn.OpenAddedLeaves8PZC8_y3c) : _root_.HDec.HSyn.OpenAddedLeaves7PZC8_y3c where
  qmHauptmodulBase3 := LeafQCheck.HM.QMSplit.qmHauptmodulBase3_of_leaves
    (QMSplit.Theta.thetaModularity_of r.igusaPsi4 r.igusaChi10) l.valenceFormulaCocompactEq
        l.shimizuCovolumeO1
    l.igusaCMValue24
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  c8 := l.c8
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


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1556
-- (_root_.HDec.HSyn.G0AssembleMod.afterG7NC_of3_hf_pz_eb_u_c8_y3c))
noncomputable section
namespace HDec.HSyn.G0AssembleMod
open CategoryTheory AlgebraicGeometry
open G0ModField
/-- cm-branch's `_root_.HDec.HSyn.G0AssembleMod.afterG7NC_of3_hf_pz_eb_y3c` on
  `_root_.HDec.HSyn.ResearchLeaves3EBU_y3cNOS` and `GaloisPiecesC8DS` (fold-c8's
`afterG7_of3_hf_pz_eb_u_c8`, localized). -/
theorem _root_.HDec.HSyn.G0AssembleMod.afterG7NC_of3_hf_pz_eb_u_c8_y3c_nos_ds (r :
    _root_.HDec.HSyn.ResearchLeaves3EBU_y3cNOS) (t : TextbookLeavesHFPZ)
    (m : G0Galois.GaloisPiecesC8DS)
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
    _root_.HDec.G0Galois.g8_g12_of_leaves3_hf_pz_eb_u_c8_y3c_nos_ds r t m h9 _ (T u) h2 h6 h3₅ Tm₅
        c₅ ε₅ a₅ β₅ u₅ h7₅
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


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1650
-- (_root_.HDec.HSyn.sixContactMin_of_open4_cm_u_c8_y3c))
noncomputable section
namespace HDec.HSyn
open CategoryTheory AlgebraicGeometry G0Split
/-- cm-branch's `_root_.HDec.HSyn.sixContactMin_of_open4_cm_y3c` on the live chain's bundles at
  this generation (`_root_.HDec.HSyn.OpenResearchLeaves2EBU_y3cNOSDS`:
R6 = `D2A6.R6U`; `_root_.HDec.HSyn.OpenAddedLeaves4PZC8_y3c`: `c8` for the Weil-pairing fields):
the manuscript's CM branch (L581-631)
in place of FS5 (NoCM) in fold-c8's `sixContactMin_of_open4_hf_pz_eb_u_c8`. -/
theorem _root_.HDec.HSyn.sixContactMin_of_open4_cm_u_c8_y3c_nos_ds (r :
    _root_.HDec.HSyn.OpenResearchLeaves2EBU_y3cNOSDS) (t : OpenTextbookLeaves4HFPZ)
    (l : _root_.HDec.HSyn.OpenAddedLeaves4PZC8_y3c) (g : OpenGlue4) (h20 : G0Split.R20Lower) (hYu
        : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM)
    (hSplit : CMBranch.CMFibreSplit) (hF : CMBranch.FowlerProp27) (hJ : CMBranch.CMjDegree)
    (hPG : CMBranch.CMPotentialGood) (h62 : CMBranch.CMHeight62) (hRP : CMBranch.ReducedCMPeriod)
    (hAddU : CMBranch.HeightAdditivityUpper) : ZInQ.SixContactMin :=
  let t2 := textbookLeaves2_of_open3_hf_pz (textbookLeaves3_of_open4_hf_pz t)
  let r3 := _root_.HDec.HSyn.researchLeaves3_of_open2_eb_u_y3c_nos_ds r
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
      (_root_.HDec.HSyn.G0AssembleMod.afterG7NC_of3_hf_pz_eb_u_c8_y3c_nos_ds r3 t3
        ⟨burnsideAbsIrred_proved3,
          g9Glue_of_deRhamComparisonHT r.r10,
          G0Galois.g10Glue_of_conjTwist
            (G0Galois.conjTwistNontrivial_of_leaves t.t5 (tateModuleFree_of_t5' t.t5) t.t35
              (HomUnify.homLinearLift_of_corr t.homLatticeCorr)),
          G0Galois.g12Weight_of_senTwist l.senTwist l.finiteImageHT,
          l.c8,
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


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1726
-- (_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn
/-- The base: CMBranchUC8's `_root_.HDec.HSyn.sixContactMin_of_open4_cm_u_c8_y3c_nos_ds` (the
  manuscript's CM branch, L581-631, on the live
bundles) with `ReducedCMPeriod` and `HeightAdditivityUpper` proved from the textbook fields `t35`,
`homLatticeCorr`,
`t11b` (cm-branch2) and `CoxProperLattice` proved (cox-lattice). -/
theorem _root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.OpenResearchLeaves2EBU_y3cNOSDS) (t : OpenTextbookLeaves4HFPZ)
    (l : _root_.HDec.HSyn.OpenAddedLeaves4PZC8_y3c) (g : OpenGlue4) (h20 : G0Split.R20Lower) (hYu
        : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) :
    ZInQ.SixContactMin :=
  _root_.HDec.HSyn.sixContactMin_of_open4_cm_u_c8_y3c_nos_ds r t l g h20 hYu hθ c.cmFibreSplit
      c.fowlerProp27 c.cmjDegree
    c.cmPotentialGood c.cmHeight62
    (CMBranch.reducedCMPeriod_of_leaves t.t35 t.homLatticeCorr t.t11b
        CMBranch.coxProperLattice_proof)
    (CMBranch.heightAdditivityUpper_of_t35 t.t35)
end HDec.HSyn
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1753
-- (_root_.HDec.HSyn.sixContactMin_of_open6_hf_pz_eb_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- `sixContactMin_of_open6_hf_pz_eb_u_c8` with the base switched to the manuscript's CM branch
  (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.sixContactMin_of_open6_hf_pz_eb_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOSDS) (t : OpenTextbookLeaves6HF)
    (l : _root_.HDec.HSyn.OpenAddedLeaves6PZC8_y3c) (g : OpenGlue6) (h20 : G0Split.R20Lower) (hYu
        : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds (c := c)
      (_root_.HDec.HSyn.researchLeaves2_of_open5_eb_u_y3c_nos_ds r)
      (_root_.HDec.HSyn.textbookLeaves4_of_open6_hf_pz_c8_y3c t l)
      (_root_.HDec.HSyn.addedLeaves4_of_open6_hf_pz_eb_u_c8_y3c_nos_ds r t l)
    (_root_.HDec.HSyn.glue4_of_open6_hf_pz_eb_u_c8_y3c_nos_ds r t l g) h20 hYu hθ
end HDec.HSyn
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1778
-- (_root_.HDec.HSyn.sixContactMin_of_open7_hf_pz_eb_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- `sixContactMin_of_open7_hf_pz_eb_u_c8` with the base switched to the manuscript's CM branch
  (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.sixContactMin_of_open7_hf_pz_eb_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.OpenResearchLeaves7EBU_y3cNOSDS) (t : OpenTextbookLeaves7HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves7PZC8_y3c)
    (g : OpenGlue7) (h20 : G0Split.R20Lower) (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.sixContactMin_of_open6_hf_pz_eb_u_c8_cm_y3c_nos_ds (c := c)
      (_root_.HDec.HSyn.researchLeaves5_of_open7_pz_eb_u_c8_y3c_nos_ds r l)
      (_root_.HDec.HSyn.textbookLeaves6_of_open7_hf_pz_c8_y3c t l)
      (_root_.HDec.HSyn.addedLeaves6_of_open7_hf_pz_eb_u_c8_y3c_nos_ds r t l)
    (glue6_of_open7 g) h20 hYu hθ
end HDec.HSyn
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1803
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open8_hf_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- `sixContactMin_of_open8_hf_pz_eb_sf_u_c8` with the base switched to the manuscript's CM branch
  (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open8_hf_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOSDS) (t : OpenTextbookLeaves8HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves8PZC8_y3c)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.sixContactMin_of_open7_hf_pz_eb_u_c8_cm_y3c_nos_ds (c := c)
      (_root_.HDec.HSyn.GR9.researchLeaves7_of_open8_hf_eb_sf_u_y3c_nos_ds r t)
      (textbookLeaves7_of_open8_hf t)
      (_root_.HDec.HSyn.GR9.addedLeaves7_of_open8_pz_eb_sf_u_c8_y3c_nos_ds r l) g
    (_root_.HDec.HSyn.GR9.r20Lower_of8_hf_eb_sf_u_y3c_nos_ds r t hF5) hYu hθ
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1827
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open9_hf_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits
/-- `sixContactMin_of_open9_hf_pz_eb_sf_u_c8` with the base switched to the manuscript's CM branch
  (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open9_hf_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOSDS) (t : OpenTextbookLeaves9HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves8PZC8_y3c)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open8_hf_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c)
      (_root_.HDec.HSyn.GR9.researchLeaves8_of_open9_hf_eb_sf_u_y3c_nos_ds r t)
      (textbookLeaves8_of_open9_hf t) l g hF5 hYu hθ
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1849
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open10_hf_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `sixContactMin_of_open10_hf_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open10_hf_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves8PZC8_y3c)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open9_hf_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c) r
      (textbookLeaves9_of_open10_hf t) l g hF5 hYu hθ
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1871
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open11_hf_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `sixContactMin_of_open11_hf_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open11_hf_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) (l :
    _root_.HDec.HSyn.OpenAddedLeaves9PZC8_y3c)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open10_hf_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c) r t
      (_root_.HDec.HSyn.addedLeaves8_of_open9_pz_c8_y3c l hY3) g hF5 hYu hθ
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1894
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open17_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `sixContactMin_of_open17_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open17_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves12PZC8)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) (h6 : _root_.HDec.D2A6.R6U)
    (hSS : _root_.ZInQ.SSFaltings.SemistableReductionThmIF)
    (hY3 : TSHecke.Y3Connected)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open11_hf_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c)
      (_root_.HDec.HSyn.GR9.researchLeaves9_of_open14_hf_gm_pz_eb_sf_u_c8_y3c_nos_ds r t l h6 hSS)
      t (_root_.HDec.HSyn.GR9.addedLeaves9_of_open14_hf_gm_pz_eb_sf_u_c8_y3c_nos_ds r t l) g
    (_root_.ReductSplit.faltingsLemma5BCLower_final _root_.GapHeight.faltingsLemma5Lower) hYu hY3 hθ
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1921
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open18_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj
/-- `sixContactMin_of_open18_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open18_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves13PZC8)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) (h6 : _root_.HDec.D2A6.R6U)
    (hSS : _root_.ZInQ.SSFaltings.SemistableReductionThmIF)
    (hY3 : TSHecke.Y3Connected)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) (c :
        _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open17_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c) r t
      (addedLeaves12_of_open13_pz_c8 l) g hYu h6 hSS hY3 hθ
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1945
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open19_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `sixContactMin_of_open19_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open19_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves13PZC8) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (h6 : _root_.HDec.D2A6.R6U)
    (hSS : _root_.ZInQ.SSFaltings.SemistableReductionThmIF)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open18_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves14_of_OpenResearchLeaves15_gm_eb_sf_u_y3c_nos_ds r)
      t l g hYu h6 hSS hY3
    HDec.ThetaDirect.thetaRatiosAtQM_of_qmHauptmodul
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1969
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open20_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `sixContactMin_of_open20_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open20_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves14PZC8) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open19_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves15_of_OpenResearchLeaves16_gm_eb_sf_u_y3c_nos_ds r)
      t (openAddedLeaves13_of_OpenAddedLeaves14_pz_c8 l) g hYu
    (_root_.HDec.HSyn.GR9.raynaudCriterionNF_of14_hf_gm_eb_sf_u_y3c_nos_ds
      (_root_.HDec.HSyn.GR9.openResearchLeaves14_of_OpenResearchLeaves15_gm_eb_sf_u_y3c_nos_ds
          (_root_.HDec.HSyn.GR9.openResearchLeaves15_of_OpenResearchLeaves16_gm_eb_sf_u_y3c_nos_ds
          r)) t)
    (_root_.HDec.HSyn.GR9.ss1_ss3_of14NF_hf_gm_pz_eb_sf_u_c8_y3c_nos_ds
        (_root_.HDec.HSyn.GR9.openResearchLeaves14_of_OpenResearchLeaves15_gm_eb_sf_u_y3c_nos_ds
        (_root_.HDec.HSyn.GR9.openResearchLeaves15_of_OpenResearchLeaves16_gm_eb_sf_u_y3c_nos_ds
        r)) t
      (addedLeaves12_of_open13_pz_c8 (openAddedLeaves13_of_OpenAddedLeaves14_pz_c8 l))) hY3
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:1994
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open21_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `sixContactMin_of_open21_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open21_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves14PZC8) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open20_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves16_of_OpenResearchLeaves17_gm_eb_sf_u_y3c_nos_ds r)
      t l g hYu hY3
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:2015
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open22_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `sixContactMin_of_open22_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open22_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves14PZC8) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open21_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves17_of_OpenResearchLeaves18_gm_eb_sf_u_y3c_nos_ds r)
      t l g hYu hY3
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:2036
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open23_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `sixContactMin_of_open23_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open23_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves14PZC8) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open22_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves18_of_OpenResearchLeaves19_gm_eb_sf_u_y3c_nos_ds r)
      t l g hYu hY3
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:2057
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open24_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `sixContactMin_of_open24_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open24_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves15PZC8) (g : OpenGlue7)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open23_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c) r t
      (openAddedLeaves14_of_OpenAddedLeaves15_hf_pz_c8 l t) g
    (QMLattice.yuB6Alg_of' t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed) hY3
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:2079
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open25_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `sixContactMin_of_open25_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open25_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves10HF) (l :
    OpenAddedLeaves16PZC8) (g : OpenGlue7)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open24_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c) r t
      (openAddedLeaves15_of_OpenAddedLeaves16_pz_c8 l) g hY3
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:2100
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open26_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `sixContactMin_of_open26_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open26_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves16PZC8) (g : OpenGlue7)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open25_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c) r
      (openTextbookLeaves10_of_OpenTextbookLeaves11_hf t) l g hY3
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:2121
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open27_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `sixContactMin_of_open27_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open27_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves16PZC8) (g : OpenGlue7)
    (hY3 : TSHecke.Y3Connected) (c : _root_.HDec.CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open26_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves19_of_OpenResearchLeaves20_hf_gm_eb_sf_u_y3c_nos_ds
      r t) t l g hY3
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:2142
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open28_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `sixContactMin_of_open28_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open28_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves17PZC8) (g : OpenGlue7) (c : _root_.HDec.CMBranch.CMInputs3) :
    ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open27_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves20_of_OpenResearchLeaves21_hf_gm_eb_sf_u_y3c_nos_ds
      r t) t (openAddedLeaves16_of_OpenAddedLeaves17_pz_c8 l) g
    (_root_.DCY3Used.y3Connected_of_ab_gl (_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr
        r.mumfordGroupLaw)
      (_root_.DCY3Used.y3ConnectedAb_of_U r.shimuraMainThmIDeligneY3AbU))
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:2164
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open29_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `sixContactMin_of_open29_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open29_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves17PZC8) (g : OpenGlue7) (c : _root_.HDec.CMBranch.CMInputs3) :
    ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open28_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves21_of_OpenResearchLeaves22_hf_gm_eb_sf_u_y3c_nos_ds
      r t) t l g
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy5.lean:2184
-- (_root_.HDec.HSyn.GR9.sixContactMin_of_open30_hf_gm_pz_eb_sf_u_c8_cm_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
set_option linter.unusedVariables false
/-- `sixContactMin_of_open30_hf_gm_pz_eb_sf_u_c8` with the base switched to the manuscript's CM
  branch (`_root_.HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8_cm_y3c_nos_ds`); generated by
  `scratch/fold-cm/gen/mk_top_live.py`. -/
theorem _root_.HDec.HSyn.GR9.sixContactMin_of_open30_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (r :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves11HF) (l :
    OpenAddedLeaves17PZC8) (g : OpenGlue7) (c : _root_.HDec.CMBranch.CMInputs3) :
    ZInQ.SixContactMin :=
  _root_.HDec.HSyn.GR9.sixContactMin_of_open29_hf_gm_pz_eb_sf_u_c8_cm_y3c_nos_ds (c := c)
      (_root_.HDec.HSyn.GR9.openResearchLeaves22_of_OpenResearchLeaves23_gm_eb_sf_u_y3c_nos_ds r)
      t l g
end HDec.HSyn.GR9
end

