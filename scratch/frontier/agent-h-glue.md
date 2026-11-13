# h-glue: status of the 46 fields of `HSyn.GluePieces4` (g0-assemble3 357f5d9e), 2026-11-13 ~10:55 PST

Base: `HSyn.sixContactMin_of_leaves4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) : ZInQ.SixContactMin`
(`scratch/g0-assemble3/G0Assemble3.lean`, structure at L90286; field list = report §2). Read-only survey. No Lean was run.
- **VERIFIED**: read in a Lean file or log on the named commit. For defs, "verbatim" means I diffed the def text against
  g0-assemble3's flat file. Compile claims are the task's own logs or out files.
- **REPORTED**: a report or log says so; Lean not read.

Full names were resolved by parsing the namespaces of the flat file (VERIFIED). Def files are g0-assemble3 `parts/*.lean`
(VERIFIED, git grep). Fields 1-3, 6-18 and 34-41 were done by a fork (Appendix A), 19-32 by a fork (Appendix B), and the
assembly/running survey by a fork (Appendix D). I checked their key claims where they overlapped my reads. Fields 4-5, 33 and
42-46 are mine (section 2).

## 0. Worlds (needed for "can it be combined")

| tag | what | who |
|---|---|---|
| **W0** | root-namespace `Leaves.lean` (blob e97e01ef). The same blob is in g0-assemble2, g0-assemble3 and linked-tate (VERIFIED, `git rev-parse`) | g0-assemble3, cpts-transport, lt-goodred, linked-ram, linked-frob (re-copies the frob chain into it) |
| **W0-old** | W0 with g0-assemble2's `G7Data`, which lacks the clause `finrank ℚ L ≤ heightD` | linked-tate, lt-goodred, linked-frob |
| **W-fqm** | fibre-qm-period/period-map files. Defs are textually identical to W0, so porting = paste the proof plus fix opens | period-glue, period-glue-b, period-num |
| **W-kern** | `import ZInQKernel.HDecomp.*` plus verbatim copies of slices | hodge-bc2 (`HDecomp.Faltings.Leaves`), prop-ts-glue/ts-*, frob-trace → alg-frob-red/afr-absfrob/frob-pieces, local-glue/lg-kerwild/lt-local, g8-object/g8-tate, conj-pieces, unif-dims, hom-unify, unram-roots (Mathlib + vendored Tau Ceti) |
| **W-HDec** | `scratch/h-decomposition/Leaves.lean` in `namespace HDec` | leaf-fold2, assemble-port (both running) |

linked-frob's log (VERIFIED) says the frob-trace chain (W-kern) and linked-tate (W0) "cannot be imported together". So any
W-kern result enters W0 only by re-copying the files, as g0-assemble3 did for infra-stalks, prop-ts-glue and others.

## 1. Master table (46 rows)

Legend:
- **P** = PROVED, **R** = REDUCED, **O** = OPEN, **B** = bypassed by an alternative route (section 3).
- "strict" = LEAF/GLUE under the strict rule, for fields still open.
- "run?" = a task is working on it now. A branch that committed in the last hour counts as possibly running.

| # | field : full Lean name (def part) | status | by (theorem · branch@commit · world) | strict (report label) | run? |
|---|---|---|---|---|---|
| 1 | `cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding` (a60_fs5) | O | — | GLUE (LEAF; docstring "a consequence of the published statement") | no |
| 2 | `x6ConicModel : X6Kummer.X6ConicModel` (f20_x6kummer) | O | — | GLUE (LEAF, "consequence of the published model") | no |
| 3 | `analyticUniformizationOfDim : ZInQ.Metrization.AnalyticUniformizationOfDim` (e30_unifdims) | O in W0; B in W-kern/W-HDec | bypassed by existing leaf T35: unif-dims@65c2c8db `productMetrizationOfProductUnif_of_tangentDim` (W-kern); leaf-fold2@b38ee0c4 `productMetrizationOfProductUnif_of_t35` (W-HDec, via the `abVarEquiv` coercion) | GLUE (LEAF; restated form) | leaf-fold2 possibly |
| 4 | `hodgeBCInjective : ZInQ.HeightBC.HodgeBCInjective` (a20_heightbc) | **P** | `ZInQ.HeightBC.hodgeBCInjective : HodgeBCInjective`, hodge-bc2@708e3eda (newest 116dc2f2), `scratch/hodge-bc2/HodgeBCInjective.lean` and OmegaBC.lean L2127; W-kern (`import ZInQKernel.HDecomp.Faltings.Leaves` + verbatim height-bc lines). Def verbatim (my diff; also verbatim_check.py ALL OK) | — | heightbc-contrib (b091f2a6 10:50) is porting it to Contrib |
| 5 | `omegaBaseChange : ZInQ.HeightBC.OmegaBaseChange` (a20_heightbc) | **P** | `theorem omegaBaseChange : OmegaBaseChange := omegaBaseChange_of_localization omegaLocalization` (OmegaBC.lean L2856), hodge-bc2@14260388 (newest 116dc2f2), W-kern. Def verbatim. The helper `ZInQ.HeightBC.OmegaLocalization` is proved | — | heightbc-contrib, as for 4 |
| 6 | `thetaRatiosAlgebraic : HSyn.G0Split.ThetaPt.ThetaRatiosAlgebraic` (80_theta) | O | — | GLUE (LEAF?) | no |
| 7 | `qmHauptmodul : PkgI1.QMHauptmodul` (Leaves.lean L304) | O | — | GLUE (LEAF?, "COMPOSITE … not printed as one theorem") | no |
| 8 | `qmClassNumberOne : HSyn.G0Split.FibreQM.QMClassNumberOne` (a80_fqm) | O | — | GLUE (LEAF; lattice form) | no |
| 9 | `r1bFamily : ∀ h, HSyn.G0Split.FibreQM.R1bFamily …` (a80_fqm) | O | in W-HDec moved into research leaves (`OpenResearchLeaves2.r1b`, assemble-port z99) | GLUE (LEAF; composite for the choice-extracted triple) | assemble-port possibly |
| 10 | `baseChangeClassUnique : HSyn.G0Split.FibreQM.PeriodMapH.BaseChangeClassUnique` (e20) | **P** | `HSyn.G0Split.FibreQM.PeriodMapH.baseChangeClassUnique_proof`, cpts-transport@93a1e33c, BCUnique.lean L46, **W0** (`import TailF`). Also period-glue@4f838f32 `PeriodGlue.baseChangeClassUnique_proof` (W-fqm) and period-glue-b@86188f5a (stopped) | — | finished |
| 11 | `piTwistC : ∀ h, …PeriodMapH.PiTwistC …` (e20) | R | `PeriodGlue.piTwistC_of … (hT : TwistOrbitFinite Y Φ) (hF : FibreTransferC Y π)`, period-glue@8797e3cc, W-fqm. Not instantiated at the own triple | GLUE (GLUE) | period-glue possibly |
| 12 | `qmTwistLattice : …PeriodMapH.QMTwistLattice` (e20) | R | `PeriodGlue.qmTwistLattice_of (hH : T11aRiemannHom) (hA : QMLatticeTwistAlg)`, period-glue@61534bf0, W-fqm | GLUE (GLUE) | possibly |
| 13 | `cmDescends : …PeriodMapH.CMDescends` (e20) | O | — | GLUE (LEAF?) | period-glue lists it as a target (nothing committed) |
| 14 | `s8Nonzero : …PeriodMap.S8Nonzero` (e20) | **P** | `PeriodGlue.s8Nonzero_proof`, period-glue@cbe9fe4c, S8.lean L530 (W-fqm, Mathlib only). Also period-num@b519646d `PeriodNum.s8Nonzero_proof` (stopped) | — | period-glue possibly |
| 15 | `sphereFactorAffine : …PeriodMap.SphereFactorAffine` (e20) | **P** (stopped run) | `PeriodGlue.sphereFactorAffine_proof`, period-glue-b@80af6547, part_sphere.lean L151 (W-fqm). Not on the live period-glue | — | stopped |
| 16 | `s8WeightExact : …PeriodMap.S8WeightExact` (e20) | R | (a) `PeriodGlue.s8WeightExact_of (hT : PkgI1.ThetaModularity) (hG : GammaStarGen)`, period-glue@8c38907b; (b) `PeriodNum.s8WeightExact_of (hT) (hN : NormalizerDecomp)`, period-num@e2e6b18c (stopped). r4 = ThetaModularity is in ResearchLeaves4 | GLUE (GLUE) | period-glue possibly |
| 17 | `valenceBoundGammaStar : …PeriodMap.ValenceBoundGammaStar` (e20) | O | — | GLUE (LEAF, "consequence of published") | period-glue target, nothing committed |
| 18 | `cPtsTransport : HSyn.G0Split.FibreQM.CPtsTransport` (a80_fqm) | **P** | `HSyn.G0Split.FibreQM.cPtsTransport_proof : CPtsTransport`, cpts-transport@97f7f638 (newest 93a1e33c), CPtsTransport.lean L116, **W0** | — | finished |
| 19 | `verticalResidueSeparable : PropTSGlue.VerticalResidueSeparable` (e10_propts) | **P** | `verticalResidueSeparable_of_degree verticalResidueDegree`, prop-ts-glue@3d41b3d5 (L2754/L2938); also `PropTSGlue.verticalResidueSeparable`, ts-sn@1b8a3b3d. W-kern; folded by assemble-port (W-HDec) | — | no |
| 20 | `snSpecialize : PropTSGlue.SNSpecialize` (e10) | **P** | `snSpecialize_of_unram snSpecializeUnram`, prop-ts-glue@3d41b3d5 (L3008/L3543); `PropTSGlue.snSpecialize`, ts-sn@1b8a3b3d L4178. W-kern; folded by assemble-port | — | no |
| 21 | `kummerCompositum : PropTSGlue.KummerCompositum` (e10) | O | — | GLUE (glue) | **ts-kummer** running (28f72b65 10:42, Core.lean stage 1 with `sorry`) |
| 22 | `kummerAbhyankarFinGlue : PropTSGlue.KummerAbhyankarFinGlue` (e10) | **P** | `TsKummer.kummerAbhyankarFinGlue`, ts-kummer@d9c06585, KummerTS.lean L3917 (W-kern) | — | no |
| 23 | `kummerOtherBranchFin : PropTSGlue.KummerOtherBranchFin` | **P** | `TsKummer.kummerOtherBranchFin` (L5723, via proved `unramCompositum`), ts-kummer@d9c06585 | — | no |
| 24 | `kummerVerticalFin : PropTSGlue.KummerVerticalFin` | **P** | `TsKummer.kummerVerticalFin` (L5731), ts-kummer@d9c06585 | — | no |
| 25 | `kummerAbhyankarInfGlue : PropTSGlue.KummerAbhyankarInfGlue` | **P** | `TsKummer.kummerAbhyankarInfGlue` (L4017), ts-kummer@d9c06585 | — | no |
| 26 | `kummerOtherBranchInf : PropTSGlue.KummerOtherBranchInf` | **P** | `TsKummer.kummerOtherBranchInf` (L5727), ts-kummer@d9c06585 | — | no |
| 27 | `kummerVerticalInf : PropTSGlue.KummerVerticalInf` | **P** | `TsKummer.kummerVerticalInf` (L5734), ts-kummer@d9c06585 | — | no |
| 28 | `heckeIrreducible : PropTSGlue.HeckeIrreducible` | R | `TSHecke.heckeIrreducible_of_connected (hC : Y3Connected)`, ts-hecke@ff8e6731 L6129 (W-kern); converse proved | GLUE (GLUE; "SPECULATIVE" label now stale) | hecke-rest possibly (merge only) |
| 29 | `heckeNormalizationIrr : PropTSGlue.HeckeNormalizationIrr` | R | `TSHecke.heckeNormalizationIrr_of (hC : CurveGaloisChart) (hT : ObjBridge.TorsionStructure)` + `curveGaloisChart_of (hN : CurveNormChart)`, ts-hecke@ff8e6731 | GLUE | hecke-rest possibly |
| 30 | `heckeDegree : PropTSGlue.HeckeDegree` | **P** (from bundle leaf `t.t5`) | `TSHecke.heckeDegree_of_torsion (hT : ObjBridge.TorsionStructure)`, ts-hecke@ff8e6731 L6335 | — | no |
| 31 | `heckeBranch : PropTSGlue.HeckeBranch` | R | `TSHecke.heckeBranch_of' (hRR : R1R2fp) (hCI : CurveChartInf) (hF : HeckeFibreSizes) (hT : ObjBridge.TorsionStructure)`, ts-hecke@ff8e6731 L7085 | GLUE | hecke-rest possibly |
| 32 | `heckeNoVertRam : PropTSGlue.HeckeNoVertRam` | O | — (ts-hecke §6: two routes, Lemma NV or good reduction) | GLUE (glue, "Lemma NV") | hecke-rest possibly (no own commit) |
| 33 | `twistDescent : G0ModField.KernelField.TwistDescent` (d20_kfglue) | O | — | GLUE (GLUE; kf-glue: truth SPECULATIVE; twist-descent log: "TRUE as stated") | **twist-descent** running (ec237d31 10:52) |
| 34 | `r14Det : G0Galois.R14Det` (70_galois) | O | in W-HDec moved into research leaves (`r.r14`, assemble-port z99) | **LEAF** (Shimura 1971 Thm 7.14; Deligne 1971; Deligne–Serre; UNVERIFIED) | assemble-port possibly |
| 35 | `homLinearLift : G0Galois.HomLinearLift` (a30_g10) | R (W-kern) | `G0Galois.homLinearLift_of_holoHomLift (hL : HoloHomLift)`, conj-pieces@110ae272 Holo.lean L80. hom-unify@cf987ee4: `homLinearLift_of_corr (h : HomLatticeCorr) := h.1`, where `HomLatticeCorr` is stronger | GLUE (LEAF; composite of Birkenhake–Lange and GAGA) | hom-unify running |
| 36 | `senTwist : G0Galois.SenTwist` (a35_g12det) | O | — | GLUE (LEAF; "consequence of the published theorems") | no |
| 37 | `finiteImageHT : G0Galois.FiniteImageHT` (a35) | O | — | GLUE (LEAF; composite) | no |
| 38 | `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` (a35) | O | — | GLUE (LEAF; "a consequence") | no |
| 39 | `isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse` (a35) | O | — | GLUE (LEAF; K̄-points form). Name clash with `HSyn.G0RevIsog.IsogenyQuasiInverse` | no |
| 40 | `divisiblePoints : WeilPairing.DivisiblePoints` (a35) | O | — | GLUE (LEAF, derived) | no |
| 41 | `carayolR17 : LadicCond.CarayolR17'` (72_ladiccond) | O | in W-HDec moved into research leaves (`r.r17`) | **LEAF** (Carayol 1986 Thm (A); docstring says the locator audit read it) | assemble-port possibly |
| 42 | `goodRedTorsion : HSyn.LinkedTate.GoodRedTorsion` (c15_lt98_g3tate) | **P** | `theorem LTGoodRed.goodRedTorsion : HSyn.LinkedTate.GoodRedTorsion`, lt-goodred@e8297eea (newest 53ba766f), parts/20_goodred.lean L155, integ/99d_proofs.lean L229. W0-old (same Leaves blob). Def verbatim vs g0-assemble3 (my diff). It does not mention `G7Data`, so the G7Data fix is irrelevant. No hypothesis (NOS is the antecedent) | — | finished |
| 43 | `qmEndRank : HSyn.LinkedTate.QMEndRank` (c10_lt95_linked) | **P** (from bundle leaves `t.t6`, `t.t27`) | `theorem LTGoodRed.QM.qmEndRank_of_leaves (hM1 : PkgI3.HomFreeFinite) (hT27 : PkgI3.QMDichotomyYu) : HSyn.LinkedTate.QMEndRank`, lt-goodred@7b162a6f (newest 53ba766f), parts/50_split.lean L226. W0-old. Def verbatim, no `G7Data` | — | finished |
| 44 | `linkedFrob : UnramTate.LinkedFrob` (c11_lt97_linkeddata) | R (uncompiled) / B | `LinkedFrobRed.linkedFrob_of_algFrobRed (hR : FrobTrace.AlgFrobRed) : UnramTate.LinkedFrob` and `linkedFrob_of_algFrobLink (hF : FrobTrace.AlgFrobLink)`, linked-frob@2261dfb7 `parts/10_linkedfrob.lean` L31/L49, W0-old with the frob chain re-copied. **No compile logged yet.** `AlgFrobRed` ⇐ frob-pieces@60340bed `FrobPiecesGood.algFrobRed_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut) (hc : FrobPiecesNeron.ProperSmoothGenConnected) (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0})` (W-kern, compiled). Here hRed = `t.t4`, hN = `t.t3` | GLUE (GLUE; truth SPECULATIVE per linked-tate §4.3; linked-frob's log argues it follows from AlgFrobLink) | **linked-frob** running (10:36) |
| 45 | `kernelFieldBreaks : UnramTate.KernelFieldBreaks` (c12_lt98b_ram) | R / B | `UnramTate.kernelFieldBreaks_of (hB : UpperBreakBound) (hW : UpperAbsWild) (h2 : BetaTrivialAtTwo) : KernelFieldBreaks` (= `kernelFieldBreaks_of_halves (kernelFieldBreaksLow_of …) kernelFieldBreaksHigh`; the tame half `kernelFieldBreaksHigh` is proved), linked-ram@42677d89, `scratch/linked-ram/olean/Tail.lean` L608, **W0** (`import TailD` from g0-assemble3's oleans; log says 0 errors, standard axioms) | GLUE (GLUE) | **linked-ram** running (10:48) |
| 46 | `tateRamAtThree : UnramTate.TateRamAtThree` (c12) | O, **statement problem** / B | linked-ram@42677d89 F1: the field is not quantified over `G7Data`, so g0-assemble3's fix does not reach it; "likely false" for unbounded K (SPECULATIVE). Proposed replacement `UnramTate.TateRamAtThreeD` (Tail.lean L618, adds `Module.finrank ℚ L ≤ ZInQ.heightD`), with `tateRamAtThreeD_of : TateRamAtThree → TateRamAtThreeD` and `linkedRam_of' (hG3 : HSyn.LinkedTate.QMModelG3) (hK : KernelFieldBreaks) (hLI : LocalInertiaGlobal) (hUI : UpperAbsInertia) (h3 : TateRamAtThreeD) : LinkedRam` (L633) | GLUE (GLUE; Glazer L814-821) | linked-ram running |

Counts:
- **P = 17**: 4, 5, 10, 14, 15, 18, 19, 20, 22-27, 30, 42, 43. 15 has only a stopped-branch proof. 30 and 43 use existing bundle leaves.
- **R = 9**: 11, 12, 16, 28, 29, 31, 35, 44, 45. 44 is uncompiled. 35 is W-kern only.
- **O = 20**: 1, 2, 3 (O in W0), 6, 7, 8, 9, 13, 17, 21, 32, 33, 34, 36-41, 46 (46 with a proposed statement change).
- Strictly LEAF among the open fields: **34 and 41 only**. All other open fields and all new Props are strict GLUE.

## 2. My rows in detail (4, 5, 33, 42-46)

- **4, 5 (hodge-bc2)**:
  - VERIFIED: defs identical to g0-assemble3's a20 text. The theorems are at OmegaBC.lean L2127/L2856.
  - World: W-kern prefix `HBCPrefix.lean` = `import ZInQKernel.HDecomp.Faltings.Leaves` + infra-stalks' CotangentBaseChange + height-bc lines. This is the same world as infra-stalks, whose `cotangentSpanBC`/`uniformizationLiftAnalytic` g0-assemble3 already pasted into W0 (part b10). So the port is a paste of `hbc_proof.lean.part`, `omega_proof.lean.part`, `ExtFrac`.
  - No bridge written.
  - heightbc-contrib's step 1 (VERIFIED log) confirms that no kernel file defines either Prop.
- **33 TwistDescent**:
  - OPEN. twist-descent (VERIFIED log) has so far built `ZInQKernel/Contrib/TwistDescent/GaloisDescent.lean` (Mathlib only; `TwistDescentGD.descend`, `exists_open_gal`, …) and "xc comparisons and Hom-field descent hfd (compiles against KfGlue olean)" (ec237d31 10:52).
  - No proof of the Prop yet. No statement change.
- **42, 43 (lt-goodred)**:
  - lt-goodred's own file `GoodRed.lean` = Leaves.lean L1-14993 + parts. It is W0-old, but neither Prop uses `G7Data`, so the defs and proofs paste into g0-assemble3 unchanged. That is a (my judgement) mechanical port; not done in W0-new.
  - linked-ram merged lt-goodred and g0-assemble3 (VERIFIED log) but does not fold them.
- **44 LinkedFrob**:
  - Def verbatim between linked-tate and g0-assemble3, but it is quantified over `G7Data`. A proof over W0-old's `G7Data` gives the W0 field via the projection new `G7Data` → old `G7Data` (drop the last conjunct). That bridge is not written. If the proof compiles textually over the new def it is not needed (linked-tate's c10 needed `.2^11` → `.2^11.1` edits).
  - Chain: `LinkedFrob ⇐ AlgFrobLink ⇐ AlgFrobOne ⇐ AlgFrobRed` (frob-trace, proved), `AlgFrobRed ⇐ AbVarSpreadsOut + ProperSmoothGenConnected + t4 + t3` (frob-pieces, using afr-absfrob's `absFrob` and `fExtendGen_of_nmp`, and frob-pieces' `smoothGeomConnIntegral` via vendored Tau Ceti).
- **45 KernelFieldBreaks**: linked-ram, W0 proper (g0-assemble3's oleans, new `G7Data`). Running.
- **46 TateRamAtThree**: see the finding in the master table. g0-assemble3's own docstring caveat ("justified only under `[L:ℚ] ≤ D`, which G7Data now carries") is wrong for this field, per linked-ram F1 (VERIFIED by reading linked-ram's log and the TateRamAtThreeD def). Location of the proposed text: `scratch/linked-ram/olean/Tail.lean` L612-631 on linked-ram@42677d89.

## 3. Alternative routes that bypass fields 44-46 (the `linkedTateLocal` block)

g0-assemble3 rebuilt g0-assemble2's field 39 `HSyn.G0AssembleMod.LinkedTateLocal` from fields 42-46 (linked-tate route). Two routes on other branches need fewer fields:

| route | theorem (VERIFIED signature in report; Lean read where noted) | remaining open inputs after today's proofs | world / bridge |
|---|---|---|---|
| **T (lt-local)** | `LTLocal.linkedTateLocal_of_tateBridge35 (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5) (hU3 : G15Ram.UnramRoots 2 3) (hB : G14Bridge.TateBridge35) (hFS : HSyn.G0Split.FibreSimple) (hR : HSyn.LinkedTate.QMEndRank) : HSyn.G0AssembleMod.LinkedTateLocal` (lt-local@3d1b90b5, `LtLocal4.lean`, over g0-assemble3's `G7Data` ported by `mk_base4.py`; also `linkedTateLocal_of_algFrobRed`) | `UnramRoots p ℓ` is **proved** for all p, ℓ (`UnramRootsTask.unramRoots`, unram-roots@b066d686; statement diff-empty vs local-glue). `TateBridge35` ⇐ `FrobPiecesGood.tateBridge35_of_neron_nmp (hT : PkgI3.TateModuleFree) (hsp) (hc) (hRed) (hN)` (frob-pieces@60340bed). QMEndRank is proved (lt-goodred). R6 = `r.r6`, T5 = `t.t5`, T26 = `t.t26`, t3, t4 are in the bundles. **Net open: `FrobPiecesNeron.AbVarSpreadsOut`, `FrobPiecesNeron.ProperSmoothGenConnected`**. That replaces fields 44, 45, 46, and also the need for 42 on this half (42 is still used by `modelG3`) | W-kern + copies (lg-kerwild's KerWild.lean + G0Assemble2/LinkedTate line copies). No bridge into W0 is written. lt-local §5 gives the fold recipe. assemble-port merged lt-local but no part uses `LTLocal` (Appendix D). rv-fast (REPORTED): lg-kerwild's every-ℓ theorem is inert, but the ℓ = 5, 3 route used here is unaffected; KerWild.lean no longer rebuilds from the current local-glue sources (integration issue) |
| **G (g8-tate)** | `G8Tate.linkedTateDataD_of_frob (hM : PkgI3.CharPolyIndepOfEll) (hR6) (hTors) (hU) (hT) (hRk : EndRank4) (hF : UnramTate.LinkedFrob) : G8Object.LinkedTateDataD` and `linkedTateObjS_of_frob` (g8-tate@9c9064e8). g8-tate-b@120fc20a (stopped; contains 72c0894f, not on g8-tate): `tateBridge35OnL_of_algFrobLink (hT : PkgI3.TateModuleFree) (hF : FrobTrace.AlgFrobLink)`, `tateBridge35OnL_of_algFrobRed` (REPORTED, Dev.lean) | `EndRank4` (= FibreSimple + QMEndRank, port needed) and `LinkedFrob`, or via g8-tate-b `AlgFrobRed`, i.e. AbVarSpreadsOut + ProperSmoothGenConnected. Eliminates 45 and 46 | W-kern (g8-object's G8Object.lean). Target is g8-object's restated `GluePieces2` field, not g0-assemble3's route. g0-assemble3 §3: needs a bridge Prop, none written |

New Props of these routes (strict GLUE):

| Prop | def | branch@commit | report label |
|---|---|---|---|
| `FrobPiecesNeron.AbVarSpreadsOut` | verbatim copy of neron-lg's N1-g1 (`scratch/neron-lg/NeronLG.lean` L449-469) | frob-pieces@60340bed | "glue / candidate textbook leaf (EGA IV₃ 8.8.2, 8.10.5, IV₄ 17.7.8)", UNVERIFIED |
| `FrobPiecesNeron.ProperSmoothGenConnected` | `scratch/frob-pieces/…`, quoted in the report §(b) | frob-pieces@60340bed | "leaf candidate (Zariski's connectedness theorem)", EGA III₁ 4.3.1-4.3.4, Hartshorne III 11.3, UNVERIFIED; stated over `IsLocalization.Away f` of `𝓞 L`, so not the printed form |
| `FrobPiecesGood.AbSchemeSpreadsOut` (alternative single input) | frob-pieces | 60340bed | "leaf candidate (the two above combined)" |
| `G14Bridge.TateBridge35`, `FrobTrace.AlgFrobRed`, `AlgFrobLink` | intermediate; now theorems from the above | frob-trace/alg-frob-red/afr-absfrob/frob-pieces | — |

spread-out has no commits of its own yet (it points at frob-pieces 60340bed). Its target is presumably `AbVarSpreadsOut`, inferred from the name only.

## 4. Every new open Prop introduced by today's reductions (recursive; none was later proved elsewhere)

| new Prop (full name) | def file · branch@commit | from field | report label → strict |
|---|---|---|---|
| `HSyn.G0Split.FibreQM.PeriodGlue.TwistOrbitFinite` | period-glue PiTwist.lean L36 · 8797e3cc | 11 | GLUE → GLUE |
| `HSyn.G0Split.FibreQM.PeriodGlue.FibreTransferC` | PiTwist.lean L61 · 8797e3cc | 11 | GLUE (false without the built-in properness/smoothness) → GLUE |
| `HSyn.G0Split.FibreQM.PeriodGlue.T11aRiemannHom` | QMTwist.lean L29 · 61534bf0 | 12 | LEAF (textbook; BL 1.2.1 + GAGA) → GLUE |
| `HSyn.G0Split.FibreQM.PeriodGlue.QMLatticeTwistAlg` | QMTwist.lean L59 · 61534bf0 | 12 | GLUE → GLUE |
| `HSyn.G0Split.FibreQM.PeriodGlue.GammaStarGen` | W8.lean L415 · 8c38907b | 16 (alt a) | LEAF candidate (Takeuchi 1977) → GLUE |
| `HSyn.G0Split.FibreQM.PeriodNum.NormalizerDecomp` | part_weight.lean L341 · period-num e2e6b18c (stopped) | 16 (alt b) | LEAF (Vignéras, Voight) → GLUE (specialised) |
| `TSHecke.Y3Connected` | TSHecke.lean L6101 · ts-hecke ff8e6731 | 28 | leaf R1conn (Deligne Bourbaki 389; Milne) → GLUE (consequence plus computation) |
| `TSHecke.CurveNormChart` | L6469 · ff8e6731 | 29 | glue, STANDARD (Hartshorne II.6), unreviewed → GLUE |
| `TSHecke.CurveChartInf` | L6565 · ff8e6731 | 31 | glue → GLUE |
| `TSHecke.HeckeFibreSizes` | L6591 · ff8e6731 | 31 | glue from leaves (Baba–Granath §3.1) → GLUE |
| `G0Galois.HoloHomLift` | conj-pieces Holo.lean L52 · 110ae272 | 35 | textbook LEAF → GLUE |
| `ZInQ.HomUnify.HomLatticeCorr` | hom-unify Contrib/HomUnify/Corr.lean L84 · cf987ee4 | 35 (stronger; `↔ HomLinearLift ∧ HomRealize`) | leaf → GLUE |
| `FrobPiecesNeron.AbVarSpreadsOut` | frob-pieces · 60340bed | 44 (via linked-frob, uncompiled); also route T | glue / candidate leaf → GLUE |
| `FrobPiecesNeron.ProperSmoothGenConnected` | frob-pieces · 60340bed | 44; route T | leaf candidate → GLUE |
| `UnramTate.UpperBreakBound` | linked-ram Tail.lean L518 · 42677d89 | 45 | LEAF? (Serre III §6, IV §1-3 via Glazer L796-811) → GLUE |
| `UnramTate.UpperAbsWild` | L525 · 42677d89 | 45 | GLUE (definitions) → GLUE |
| `UnramTate.BetaTrivialAtTwo` | L533 · 42677d89 | 45 | GLUE (Glazer L826-843) → GLUE |
| `UnramTate.TateRamAtThreeD` | L618 · 42677d89 | 46 (corrected statement) | GLUE → GLUE |

Proved helpers (no open input): `OmegaLocalization`; `SNSpecializeUnram`; `VerticalResidueDegree`; `TsKummer.UnramCompositum`; `RamOfFibreCount`; `GenericFibreCount`; `KernelFieldBreaksHigh`; `G15Ram.UnramRoots`; `AbsFrob`; `FExtendGen` (from t3); `SmoothGeomConnIntegral`; `LTLocal.ModelEndRank4`/`G7DegreeBound` (over g0-assemble3's `G7Data`).

## 5. Findings: false, vacuous, or needs a statement change

- **46 `TateRamAtThree`**: needs `[L:ℚ] ≤ D`. The GluePieces4 form is "likely false" (linked-ram F1, SPECULATIVE). Replace with `TateRamAtThreeD` (linked-ram Tail.lean L618).
- **11 `FibreTransferC`** (new): false without its built-in hypotheses. They are in the def (PiTwist.lean docstring L49-60).
- 28: the "SPECULATIVE" labels on `HeckeIrreducible` are stale. ts-hecke settled truth by computation; docstrings to update are g0-assemble3 e10 and the field docstring, plus PropTSGlue.lean ~L708.
- 24/27: the hypothesis `n < p` is unused (ts-kummer, REPORTED). No change needed.
- 36: the full-size hypothesis is needed (docstring); the def has it.
- 35: conj-pieces F4, `A.dim = g` is unused.
- lg-kerwild `exists_localGlue_of_tateModuleFree` is inert (rv-fast, REPORTED). It does not affect route T.

## 6. Assemblies that compose several of these results

- **cpts-transport@93a1e33c**, W0, compiled (flat check standard axioms):
  - `HSyn.GluePieces5` = GluePieces4 minus {10 `baseChangeClassUnique`, 18 `cPtsTransport`}, 44 fields;
  - `HSyn.gluePieces4_of_gluePieces5 (gp : GluePieces5) : GluePieces4` (Bundle5.lean L1302);
  - `HSyn.sixContactMin_of_leaves5 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces5) : ZInQ.SixContactMin` (L1351).
  - This is the only W0 assembly newer than g0-assemble3.
- **assemble-port@52e2caf1**, W-HDec, running:
  - `HDec.HSyn.GluePieces5`, a DIFFERENT structure with the same name: GluePieces4 minus {19, 20 (filled by prop-ts-glue's proofs), 9, 34, 41 (moved to `OpenResearchLeaves2` as `r.r1b`, `r.r14`, `r.r17`)}, 41 fields;
  - `sixContactMin_of_leaves5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (gp : GluePieces5)` (z99_bundle5.lean L179), no compile logged at HEAD. The earlier 43-field version at f5ba81ea (`r : ResearchLeaves5`, `t : OpenTextbookLeaves`) compiled per its log.
- **lt-goodred@53ba766f** `integ/`, W0-old, compiled (flat 686 s):
  - `HSyn.GluePieces4`, a DIFFERENT structure from g0-assemble3's: linked-tate's 29-field `GluePieces3` minus `goodRedTorsion`, `qmEndRank`, so 27 fields;
  - `HSyn.gluePieces3_of_gluePieces4 (t : TextbookLeaves) (gp4 : GluePieces4) : GluePieces3` (99e_bundle4.lean L92);
  - `HSyn.sixContactMin_of_leaves4 (r : ResearchLeaves) (t : TextbookLeaves) (gp4 : GluePieces4) : ZInQ.SixContactMin` (L124);
  - linked-tate's `GluePieces3` is the one g0-assemble3 renamed `HSyn.LinkedTate.GluePieces3`.
- **leaf-fold2@b38ee0c4**, W-HDec: `HDec.HSyn.sixContactMin_of_open2 (r) (t) (l : OpenAddedLeaves2) (g : OpenGlue2)`, on g0-assemble2's reductions (66 fields), compiled per its log.
- **hom-unify@cf987ee4**: `HSyn.sixContactMin_of_leaves3Hom` over a 29-field `GluePieces3Hom` (linked-tate world), not logged as compiled.
- **Composites inside one area, not full assemblies**:
  - Prop. TS: `PropTSGlue.propTSAll_final''` (12 hyps), `TsKummer.propTSAll_ts`, `TSHecke.propTSAll_of_tsHecke'`. No file combines all three; combined, 14 fields become 6 GLUE Props (Appendix B).
  - `LTLocal.linkedTateLocal_of_tateBridge35`, `G8Tate.linkedTateDataD_of_frob`, `FrobPiecesGood.tateBridge35_of_neron_nmp`.
- **Not folded anywhere** (no branch composes them with GluePieces4): hodge-bc2, lt-goodred (into W0-new), ts-sn, ts-kummer, ts-hecke, unram-roots, frob-pieces, period-glue/period-num, lt-local, linked-frob, linked-ram, conj-pieces.
- **If all are folded** (my count, SPECULATIVE until compiled), the open set of GluePieces4 would be:
  - fields 1, 2, 3, 6-9, 13, 17, 21, 32, 33, 34, 36-41 (19 fields);
  - plus the new Props of section 4 for 11, 12, 16, 28, 29, 31, 35;
  - plus either {44 via AlgFrobRed, 45's three Props, `TateRamAtThreeD`} or, with route T, just {`AbVarSpreadsOut`, `ProperSmoothGenConnected`} in place of 44-46.

---

# Appendix A (fork: fields 1-3, 6-18, 34-41)


Scope: the 24 fields above of `HSyn.GluePieces4` (g0-assemble3 357f5d9e, `scratch/g0-assemble3/G0Assemble3.lean` L90286).
Full names were resolved by parsing namespaces in the flat file (VERIFIED). "def file" = g0-assemble3 part file (VERIFIED by git grep).
"Verbatim" = the def text in the proving task's base was diffed against the g0-assemble3 flat file (VERIFIED, own diff), unless stated otherwise.
Strict class: LEAF only for a published, refereed statement that the Lean is not stronger than; everything else (consequence, composite, "form", candidate) is GLUE. All citations are UNVERIFIED unless noted.

## Worlds (read this first)
- **W0** = g0-assemble3's world: root-namespace `Leaves.lean` (blob e97e01ef, the same in g0-assemble2 and linked-tate) plus parts; olean chain `LPrefix→TailA…TailF→TailD`.
- **W-fqm** = fibre-qm-period's `FibreQM.lean` L1-20634 + `part_fqm` + period-map parts (imports Mathlib + kernel JHeight, HeightConstant, QMLattice), or period-map's `PMLight` (Mathlib only). period-glue, period-glue-b and period-num build on it. g0-assemble3 part e20 is period-map's text, folded into W0 with open/name fixes only. VERIFIED: the 11 period-map/fibre-qm-period defs are textually identical in W-fqm and W0. So porting means pasting the proof part plus fixing opens; no bridge Prop is needed. Not done yet.
- **W-kern** = imports `ZInQKernel.HDecomp.*` with copies (conj-pieces `Holo.lean`, unif-dims `Combined.lean`, hom-unify `Corr.lean`).
- **W-HDec** = `scratch/h-decomposition/Leaves.lean` in `namespace HDec`: leaf-fold2 (b38ee0c4, last commit 10:38) and assemble-port (52e2caf1, last commit 10:45). Both are possibly running.

## Table

| # | field : full Lean name (def file in g0-assemble3) | status now | proving/reducing theorem (VERIFIED signature) · branch@commit · verbatim? | new open Props (full name · file · branch@commit · report label → strict) | strict class of field | last touch (newest form) | running? | findings / world |
|---|---|---|---|---|---|---|---|---|
| 1 | `cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding` (parts/a60_fs5.lean) | OPEN | — | — | GLUE. Report label LEAF (N1b′). Its docstring says "A consequence of the published statement" (Shimura 1967; Jordan 1981 thesis §3; González–Rotger 2006 §5) | fs5-nocm; newest form g0-assemble3@357f5d9e | no | none |
| 2 | `x6ConicModel : X6Kummer.X6ConicModel` (parts/f20_x6kummer.lean) | OPEN | — | — | GLUE. Label LEAF (N2-L′), "a consequence of the published model" (Kurihara 1979; Elkies 1998 §3) | x6-kummer; g0-assemble3@357f5d9e | no | none |
| 3 | `analyticUniformizationOfDim : ZInQ.Metrization.AnalyticUniformizationOfDim` (parts/e30_unifdims.lean) | OPEN in W0. **REDUCED to the existing `TextbookLeaves.t35` in other worlds** | W-kern: `ZInQ.UnifDims.productMetrizationOfProductUnif_of_tangentDim (hT35 : ZInQ.LeafPush2.UniformizationExists) …` (unif-dims@65c2c8db, `scratch/unif-dims/Combined.lean` L6435). W-HDec: `theorem productMetrizationOfProductUnif_of_t35 (h35 : ZInQ.LeafPush2.UniformizationExists) : ZInQ.ProductHeight.ProductMetrizationOfProductUnif` (leaf-fold2 `parts/b20_fold.lean` L135, b38ee0c4; uses a local `Coe ZInQ.DefFaltings.AbVar → PkgI3.AbVar` = `LeafAdopt.abVarEquiv`, per its log). Both bypass the field rather than prove it | none | GLUE. Label LEAF (Mumford §1, §4 + GAGA). It is the uniformization theorem restated over group models `𝒢(ℂ)_τ` with g = dim A, not the printed form | leaf-fold2@b38ee0c4 (bypass); assemble-port@52e2caf1 still keeps the field | leaf-fold2, assemble-port possibly running | In W0, T35 is stated over a different `AbVar` structure (unif-dims §5), so g0-assemble3 kept the field. leaf-fold2's coercion is a working bridge, but only in W-HDec |
| 6 | `thetaRatiosAlgebraic : HSyn.G0Split.ThetaPt.ThetaRatiosAlgebraic` (parts/80_theta.lean) | OPEN | — | — | GLUE. Label LEAF? (Shimura, Duke 43 (1976); Mumford, Tata II IIIa §8; nonvanishing via Igusa). Composite | g0-thetapoint; g0-assemble3@357f5d9e | no | none |
| 7 | `qmHauptmodul : PkgI1.QMHauptmodul` (Leaves.lean L304) | OPEN | — | — | GLUE. Label "LEAF, COMPOSITE … not printed as one theorem" (Baba–Granath 2008; Lin–Yang 2020 Ex. 29; Igusa 1967) | pkg-I1 / loc-fix; g0-assemble3@357f5d9e | no | r1b-state (bdd6d8e8) uses it as an input to an alternative FibreQMPeriod route. That route is not folded and is over `PkgI3.AbVar`/`FibreOver'`, so it needs a bridge (g0-assemble3 §3) |
| 8 | `qmClassNumberOne : HSyn.G0Split.FibreQM.QMClassNumberOne` (parts/a80_fqm.lean) | OPEN | — | — | GLUE. Label LEAF in g0-assemble3, TEXTBOOK in its docstring. It is the lattice form derived from Eichler class number one (Vignéras Cor. III.5.7; Voight 28.5.17) | fibre-qm-period; g0-assemble3@357f5d9e | no | none |
| 9 | `r1bFamily : ∀ h : LeafAdopt.R1R2fpRep, HSyn.G0Split.FibreQM.R1bFamily (ownY …) (ownΦ …) (ownπ …)` (parts/a80_fqm.lean) | OPEN (moved, not proved) | In W-HDec it is a research-leaf field: leaf-fold2 `OpenResearchLeaves2.r1b`; assemble-port `gluePieces4_of_gluePieces5` uses `r1bFamily := r.r1b` (z99, 52e2caf1, VERIFIED) | — | GLUE. Label LEAF (Shimura 1967 Main Thm I; Deligne Bourbaki 389 §4.15). It is the published statement composed with π, plus qm-pin's comparison for other triples, and it is stated for the triple that `Classical.choice` picks | assemble-port@52e2caf1 | assemble-port possibly running | Caveat from g0-assemble3 §6: stated for the choice-extracted triple. r1b-state's leaf `R01b_ComplexUniformization'` needs two bridges before it implies `R1bFamily` (leaf-fold2 report L115) |
| 10 | `baseChangeClassUnique : HSyn.G0Split.FibreQM.PeriodMapH.BaseChangeClassUnique` (parts/e20_periodmap.lean) | **PROVED** (three independent proofs) | (a) **W0**: `theorem baseChangeClassUnique_proof : BaseChangeClassUnique` in `namespace HSyn.G0Split.FibreQM.PeriodMapH`, cpts-transport@93a1e33c, `scratch/cpts-transport/BCUnique.lean` L46 (`import TailF`) and `Bundle5.lean` L1148. Flat check `Flat5_out.txt` is standard axioms (VERIFIED). Verbatim by construction: it uses g0-assemble3's own def. (b) W-fqm: `HSyn.G0Split.FibreQM.PeriodGlue.baseChangeClassUnique_proof : PeriodMapH.BaseChangeClassUnique`, period-glue@4f838f32 (head cbe9fe4c), `BCU.lean` L249, run_bcu.txt standard axioms. (c) period-glue-b@86188f5a, `part_bc.lean` (log says compiled; REPORTED) | none | n/a | cpts-transport@93a1e33c | cpts-transport finished (fleet summary 10:30) | Mathlib + mul-rigidity's rigidity only |
| 11 | `piTwistC : ∀ h : LeafAdopt.R1R2fpRep, HSyn.G0Split.FibreQM.PeriodMapH.PiTwistC (ownY …) (ownΦ …) (ownπ …)` (e20) | **REDUCED** | `theorem piTwistC_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) (hT : TwistOrbitFinite Y Φ) (hF : FibreTransferC Y π) : PiTwistC Y Φ π` (`HSyn.G0Split.FibreQM.PeriodGlue`), period-glue@8797e3cc (head cbe9fe4c), `scratch/period-glue/PiTwist.lean` L69. Standard axioms (run_pitwist.txt). PiTwistC def is verbatim (W-fqm = W0 text). To fill the field you instantiate it at the own triple, with R1fp/R2fp from the rep (not done) | `HSyn.G0Split.FibreQM.PeriodGlue.TwistOrbitFinite Y Φ` (PiTwist.lean L36): label GLUE (moduli), strict GLUE. `HSyn.G0Split.FibreQM.PeriodGlue.FibreTransferC Y π` (L61): label GLUE (AG, Jacobson), strict GLUE. Both period-glue@8797e3cc. The field needs them `∀ h` at `ownY/ownΦ/ownπ` | GLUE (label GLUE) | period-glue@cbe9fe4c | period-glue possibly running (last commit 10:27) | FibreTransferC: "without the properness/smoothness hypotheses the transfer is false (Y = Spec ℂ)", so those hypotheses are inside the def (PiTwist.lean docstring L49-60) |
| 12 | `qmTwistLattice : HSyn.G0Split.FibreQM.PeriodMapH.QMTwistLattice` (e20) | **REDUCED** | `theorem qmTwistLattice_of (hH : T11aRiemannHom) (hA : QMLatticeTwistAlg) : QMTwistLattice` (`…PeriodGlue`), period-glue@61534bf0, `QMTwist.lean` L80, standard axioms (run_qmtwist.txt). Def is verbatim. Also `t11aRiemannEnd_of_hom : T11aRiemannHom → T11aRiemannEnd`. period-glue-b@946fb35e (snapshot, unchecked) has an unfinished attempt from T11aRiemannHom alone (`part_tl.lean`, no final theorem) | `HSyn.G0Split.FibreQM.PeriodGlue.T11aRiemannHom` (QMTwist.lean L29): label LEAF (textbook; Mumford §1, BL 1.2.1, GAGA), strict **GLUE** (composite of BL and GAGA). `HSyn.G0Split.FibreQM.PeriodGlue.QMLatticeTwistAlg` (L59): label GLUE (pure algebra), strict GLUE | GLUE | period-glue@cbe9fe4c | possibly running | `T11aRiemannHom` overlaps hom-unify's `ZInQ.HomUnify.T11aHom`/`HomLatticeCorr` (same Hom↔lattice content at K = ℂ, σ = id). SPECULATIVE; there is no dedup bridge |
| 13 | `cmDescends : HSyn.G0Split.FibreQM.PeriodMapH.CMDescends` (e20) | OPEN | — (it was among period-glue's restatement targets; no commit yet) | — | GLUE. Label LEAF candidate (Shimura–Taniyama 1961; Shimura 1967) | period-map@1dd4f269; g0-assemble3 | period-glue possibly running | none |
| 14 | `s8Nonzero : HSyn.G0Split.FibreQM.PeriodMap.S8Nonzero` (e20) | **PROVED** (two independent proofs, both W-fqm light) | (a) `theorem s8Nonzero_proof : S8Nonzero` (`HSyn.G0Split.FibreQM.PeriodGlue`), period-glue@cbe9fe4c, `S8.lean` L530, via `s8Nonzero_iff : S8Nonzero ↔ S8Omega0` and `s8Omega0_proof`; run_s8.txt standard axioms. (b) `HSyn.G0Split.FibreQM.PeriodNum.s8Nonzero_proof : S8Nonzero`, period-num@b519646d (head c6d31639), `part_nonzero.lean` L420; run_full1 standard axioms (REPORTED in log). Def is verbatim | none | n/a | period-glue@cbe9fe4c | period-glue possibly running; period-num stopped (snapshot 10:12) | Σθ⁸(Ω(√2+i)) = −9ϑ00(i)^16 ≈ −33.908. Port to W0 = paste the proof part (PGLight is Mathlib only) |
| 15 | `sphereFactorAffine : HSyn.G0Split.FibreQM.PeriodMap.SphereFactorAffine` (e20) | **PROVED** (stopped run) | `theorem sphereFactorAffine_proof : PeriodMap.SphereFactorAffine` (`HSyn.G0Split.FibreQM.PeriodGlue`), period-glue-b@80af6547 (head 946fb35e), `scratch/period-glue/part_sphere.lean` L151. Mathlib only; run_light1.txt standard axioms (VERIFIED file). It uses period-map's def directly (verbatim). Also `hauptmodulUnique_of_S8 (hS : PeriodMap.S8Nonzero) : HauptmodulUnique` (L335) | none | n/a (label TEXTBOOK/GLUE) | period-glue-b@80af6547 | stopped (snapshot "task was stopped") | Not on the live period-glue branch (cbe9fe4c). Combining needs both branches' parts |
| 16 | `s8WeightExact : HSyn.G0Split.FibreQM.PeriodMap.S8WeightExact` (e20) | **REDUCED** (two alternative reductions) | (a) `theorem s8WeightExact_of (hT : PkgI1.ThetaModularity) (hG : GammaStarGen) : S8WeightExact`, period-glue@8c38907b, `W8.lean` L422, run_w8.txt standard. (b) `theorem s8WeightExact_of (hT : PkgI1.ThetaModularity) (hN : NormalizerDecomp) : S8WeightExact` (`…PeriodNum`), period-num@e2e6b18c, `part_weight.lean` L454, run_full2 standard. `ThetaModularity` is research leaf r4 (in ResearchLeaves4) | (a) `HSyn.G0Split.FibreQM.PeriodGlue.GammaStarGen` (W8.lean L415, period-glue@8c38907b): label "LEAF candidate … flagged for a human check" (Takeuchi 1977; Elkies 1998 §3; Beardon §9.8). Strict GLUE (derived from the published signature plus Poincaré's theorem). (b) `HSyn.G0Split.FibreQM.PeriodNum.NormalizerDecomp` (part_weight.lean L341, period-num@e2e6b18c): label "LEAF (published …)" (Vignéras LNM 800 II §1, III §5; Voight GTM 288 §18.5, Ch. 23). Strict GLUE (the generic Atkin–Lehner statement specialized to explicit generators for D = 6) | GLUE | period-glue@cbe9fe4c | period-glue possibly running; period-num stopped | none false |
| 17 | `valenceBoundGammaStar : HSyn.G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar` (e20) | OPEN | — (a restatement target of period-glue; nothing committed) | — | GLUE. Label "LEAF (consequence of published)". The valence formula (Shimura 1971 §2.4; Rankin Thm 4.1.4) plus the signature (0;2,4,6). period-map: "weaker than the published formulas" | period-map@1dd4f269 | period-glue possibly | none |
| 18 | `cPtsTransport : HSyn.G0Split.FibreQM.CPtsTransport` (parts/a80_fqm.lean) | **PROVED** | `theorem cPtsTransport_proof : CPtsTransport` (`HSyn.G0Split.FibreQM`, file namespaces `HSyn`/`G0Split`/`FibreQM`), cpts-transport@97f7f638 (head 93a1e33c), `scratch/cpts-transport/CPtsTransport.lean` L116 (`import TailF`, **W0**) and `Bundle5.lean` L1072. Flat5 standard axioms (VERIFIED file). Verbatim by construction | none | n/a | cpts-transport@93a1e33c | finished | No leaf or glue used (rigidity + unram-tate `bcPt`). A kernel port would need kernel copies of mul-rigidity and `bcPt` |
| 34 | `r14Det : G0Galois.R14Det` (parts/70_galois.lean) | OPEN (moved) | W-HDec: merged into R14 (`OpenResearchLeaves2.r14 : G0Galois.R14Det`, leaf-fold2). assemble-port z99 uses `r14Det := r.r14` (VERIFIED) | — | LEAF (label LEAF: Shimura 1971 Thm 7.14; Deligne 1971; Deligne–Serre 1974). Caveat: Deligne 1971 is a Bourbaki talk | assemble-port@52e2caf1 | possibly | none |
| 35 | `homLinearLift : G0Galois.HomLinearLift` (parts/a30_g10.lean) | **REDUCED** (W-kern) | `theorem homLinearLift_of_holoHomLift (hL : HoloHomLift) : HomLinearLift` (`G0Galois`), conj-pieces@110ae272, `scratch/conj-pieces/Holo.lean` L80 (`import ZInQKernel.HDecomp.LeafPush2.T`). HomLinearLift def is verbatim (diffed). Not folded (g0-assemble3 §6: "a leaf for a leaf"). hom-unify@cf987ee4 (running): `homLinearLift_of_corr (h : HomLatticeCorr) : HomLinearLift := h.1` (`ZInQKernel/Contrib/HomUnify/Corr.lean` L101). That is a merge into a stronger conjunction, not a reduction | `G0Galois.HoloHomLift` (Holo.lean L52, conj-pieces@110ae272): label textbook LEAF (Mumford §1 + GAGA; BL 1.2.1), strict GLUE. `ZInQ.HomUnify.HomLatticeCorr` (Corr.lean L84, hom-unify@cf987ee4): one leaf ⇒ T11aHom, HomLinearLift, T11a_RiemannEnd; `corr_iff_lift_realize : HomLatticeCorr ↔ HomLinearLift ∧ HomRealize`. Strict GLUE | GLUE. Label LEAF, "with holomorphy of algebraic morphisms" (composite of BL and GAGA) | hom-unify@cf987ee4 | hom-unify running (10:47) | conj-pieces F4: the hypothesis `A.dim = g` is unused. World: W-kern, port is a paste |
| 36 | `senTwist : G0Galois.SenTwist` (parts/a35_g12det.lean) | OPEN | — | — | GLUE. Label LEAF. Docstring: "Consequence of the published theorems" (Sen 1980 §2; Fontaine–Ouyang §2.4-2.5) | g12-det; g0-assemble3 | no | Docstring: full size is needed, otherwise false; the def includes it |
| 37 | `finiteImageHT : G0Galois.FiniteImageHT` (a35) | OPEN | — | — | GLUE. Label LEAF. Composite (Tate 1967 §3 Thm 2 + Ax–Sen–Tate + Hilbert 90) | g12-det | no | none |
| 38 | `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` (a35) | OPEN | — | — | GLUE. Label LEAF. "Existential in D, hence a consequence" (Mumford §§6, 8, 13, 20, 23) | weil-pairing | no | none |
| 39 | `isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse` (a35) | OPEN | — | — | GLUE. Label LEAF. "Stated on K̄-points, a consequence" (Mumford §7-8; Milne 1986 7.1). Name clash: `HSyn.G0RevIsog.IsogenyQuasiInverse` also exists (flat L36254) | weil-pairing | no | none |
| 40 | `divisiblePoints : WeilPairing.DivisiblePoints` (a35) | OPEN | — | — | GLUE. Label Leaf, derived: isogeny ⇒ surjective on K̄-points (Mumford §4 Appl. 2, §6) | weil-pairing | no | none |
| 41 | `carayolR17 : LadicCond.CarayolR17'` (parts/72_ladiccond.lean) | OPEN (moved) | W-HDec: research leaf `r17` (leaf-fold2). assemble-port z99 `carayolR17 := r.r17` (VERIFIED) | — | LEAF. Label "R17, published form", Carayol 1986 Théorème (A). The docstring says it was "read by the locator audit" (loc-fix), so this citation is reported as checked | assemble-port@52e2caf1 | possibly | none |

## Summary for part A
- PROVED: 10 `baseChangeClassUnique` (cpts-transport, W0; also period-glue, period-glue-b), 14 `s8Nonzero` (period-glue; period-num), 15 `sphereFactorAffine` (period-glue-b, stopped), 18 `cPtsTransport` (cpts-transport, W0).
- REDUCED: 11 `piTwistC` → `TwistOrbitFinite`, `FibreTransferC` (∀ own triple). 12 `qmTwistLattice` → `T11aRiemannHom`, `QMLatticeTwistAlg`. 16 `s8WeightExact` → `GammaStarGen` (period-glue) or `NormalizerDecomp` (period-num), plus r4. 35 `homLinearLift` → `HoloHomLift` (W-kern). 3 `analyticUniformizationOfDim` → existing T35, but only in W-kern/W-HDec.
- OPEN: 1, 2, 6, 7, 8, 9, 13, 17, 34, 36-41. 9, 34 and 41 move into leaf-fold2/assemble-port's research bundle in W-HDec.
- Strict count for the 24 fields: LEAF = 34 `r14Det` and 41 `carayolR17` only. All others are GLUE or done.
- New open Props (all strict GLUE): `PeriodGlue.TwistOrbitFinite`, `PeriodGlue.FibreTransferC`, `PeriodGlue.T11aRiemannHom`, `PeriodGlue.QMLatticeTwistAlg`, `PeriodGlue.GammaStarGen` | `PeriodNum.NormalizerDecomp` (alternatives), `G0Galois.HoloHomLift` (and hom-unify's stronger `ZInQ.HomUnify.HomLatticeCorr`). None was later proved on another branch.
- Assemblies that touch these fields: cpts-transport's **`HSyn.GluePieces5`** (W0, 44 fields = GluePieces4 − {10, 18}). Its theorems: `gluePieces4_of_gluePieces5 (gp : GluePieces5) : GluePieces4` and `sixContactMin_of_leaves5 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces5) : ZInQ.SixContactMin`, in `Bundle5.lean` L1302/L1351, with flat check VERIFIED. assemble-port's **`HDec.HSyn.GluePieces5`** is a DIFFERENT structure (W-HDec, 41 fields = GluePieces4 − {verticalResidueSeparable, snSpecialize, r14Det, r1bFamily, carayolR17}): `sixContactMin_of_leaves5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (gp : GluePieces5)` (z99, 52e2caf1, running). Neither folds the period-glue, period-num or conj-pieces results.
- Not relevant to these fields (checked report/log greps): cm-numeric, tyz-cm, curve-infra, t40-tate, t40-igusa, dim-contrib, unif-dims (beyond field 3), rleaf-elliptic, x1-dirichlet, g8-local (consumers of CarayolR17' only).

---

# Appendix B (fork: fields 19-32)


Scope: `HSyn.GluePieces4` fields 19-32 (g0-assemble3 357f5d9e, part `scratch/g0-assemble3/parts/e10_propts.lean`, which is
prop-ts-glue@15d4197e's `PropTSGlue.lean` lines 25-29, 64-end pasted verbatim over g0-assemble3's root-namespace
`Leaves.lean`). VERIFIED = read in the Lean file / report on the named commit; REPORTED = report says so, Lean not seen.

## World / verbatim facts (VERIFIED)

- prop-ts-glue@3d41b3d5, ts-sn@1b8a3b3d, ts-kummer@d9c06585/28f72b65 and ts-hecke@ff8e6731 all compile over the
  kernel world: `import ZInQKernel.HDecomp.QM.Pin` + `import ZInQKernel.HDecomp.Descent.B2Glue` (+ Mathlib), not over
  `Leaves.lean`. ts-sn, ts-kummer, ts-hecke start from prop-ts-glue@d687db84 (09:00; before `snSpecializeUnram`,
  `propTSAll_final''`). Each says its file starts with `PropTSGlue.lean` verbatim (check_prefix/check_identical).
- Every one of the 14 defs (and `KummerAbhyankarFin/Inf`, `PropTSAll`, `NormalizationModel`) is textually identical
  (awk def-block diff) in all four files and g0-assemble3's flat file (`/tmp/hglue-work/g3.lean`). So each field type is
  the same text; only the surrounding world differs.
- Porting: g0-assemble3's e10 shows prop-ts-glue's text compiles in the Leaves world unchanged. No bridge file or port
  exists for ts-kummer/ts-hecke/ts-sn appendices. assemble-port (running, see below) did port prop-ts-glue@3d41b3d5 into
  the HDec world (regenerated e10).
- ts-hecke's file also has verbatim copies of aut-o-finite `AutOFinite.lean`, infra-smooth-dim `SmoothStalk.lean`, and
  curve-glue `ComponentIrreducible`/`CIproof`. Expect duplicate names when you fold it into g0-assemble3, which already has
  b20/e25 copies.
- Hecke reductions use `ObjBridge.TorsionStructure`. In g3 this is the Iff.rfl copy of `PkgI2.TorsionStructure` =
  `TextbookLeaves.t5`. `R1R2fp` is `ResearchLeaves.r1r2` via `R1R2fp_of_rep`, and T2 is `PkgI2.AbhyankarDVR` =
  `TextbookLeaves.t2`. All three are already bundle leaves.

## Field table

All 14 are defined in namespace `PropTSGlue`, in g0-assemble3 `parts/e10_propts.lean` (originally
prop-ts-glue `scratch/prop-ts-glue/PropTSGlue.lean`). g3 kind for all 14 = GLUE.

| # | field / Prop | status | theorem (name, file, branch@commit) | verbatim? | last touched (newest form) | running? |
|---|---|---|---|---|---|---|
| 19 | `PropTSGlue.VerticalResidueSeparable` | **PROVED** | `verticalResidueSeparable_of_degree verticalResidueDegree` (`theorem verticalResidueDegree : VerticalResidueDegree :=` L2938; `theorem verticalResidueSeparable_of_degree (hD : VerticalResidueDegree) :` L2754), `scratch/prop-ts-glue/PropTSGlue.lean`, prop-ts-glue@3d41b3d5. Also named `theorem PropTSGlue.verticalResidueSeparable : VerticalResidueSeparable` (L4182, `scratch/ts-sn/TSSN.lean`, ts-sn@1b8a3b3d). VERIFIED | yes (same file / def identical) | prop-ts-glue 3d41b3d5; ts-sn 1b8a3b3d; assemble-port uses it (z99, 52e2caf1) | no |
| 20 | `PropTSGlue.SNSpecialize` | **PROVED**, two independent proofs | (a) `snSpecialize_of_unram snSpecializeUnram` (`theorem snSpecializeUnram : SNSpecializeUnram :=` L3543, `theorem snSpecialize_of_unram (h : SNSpecializeUnram) : SNSpecialize :=` L3008), prop-ts-glue@3d41b3d5. (b) `theorem PropTSGlue.snSpecialize : SNSpecialize :=` (L4178 TSSN.lean, ts-sn@1b8a3b3d). Consequence `PropTSGlue.specNonMeeting : SpecNonMeeting` in both. VERIFIED | yes | prop-ts-glue 3d41b3d5 / ts-sn 1b8a3b3d | no |
| 21 | `PropTSGlue.KummerCompositum` | **OPEN** | none. ts-kummer: "open glue (true; plan in §4)". Plan: minimal prime of `O ⊗_{ℚ[X]} B`, `E' = Frac(T/𝔫)` | — | ts-kummer 28f72b65 (Core.lean "stage 1 … compiles (sorry)", 10:42) | **yes**, ts-kummer is working on it (commit 10:42) |
| 22 | `PropTSGlue.KummerAbhyankarFinGlue` (= T2 → `KummerAbhyankarFin`) | **PROVED** | `theorem kummerAbhyankarFinGlue : KummerAbhyankarFinGlue` (KummerTS.lean L3917, ns `TsKummer`), ts-kummer@d9c06585. VERIFIED | yes | ts-kummer d9c06585 | no (piece done) |
| 23 | `PropTSGlue.KummerOtherBranchFin` | **PROVED** | `theorem TsKummer.kummerOtherBranchFin : KummerOtherBranchFin := kummerOtherBranchFin_of_unram unramCompositum` (L5723; `unramCompositum : UnramCompositum` L4611 proved). VERIFIED | yes | ts-kummer d9c06585 | no |
| 24 | `PropTSGlue.KummerVerticalFin` | **PROVED** | `theorem TsKummer.kummerVerticalFin : KummerVerticalFin := kummerVerticalFin_proof` (L5731/L5434). VERIFIED | yes | ts-kummer d9c06585 | no |
| 25 | `PropTSGlue.KummerAbhyankarInfGlue` | **PROVED** | `theorem TsKummer.kummerAbhyankarInfGlue : KummerAbhyankarInfGlue` (L4017). VERIFIED | yes | ts-kummer d9c06585 | no |
| 26 | `PropTSGlue.KummerOtherBranchInf` | **PROVED** | `theorem TsKummer.kummerOtherBranchInf : KummerOtherBranchInf := kummerOtherBranchInf_of_unram unramCompositum` (L5727). VERIFIED | yes | ts-kummer d9c06585 | no |
| 27 | `PropTSGlue.KummerVerticalInf` | **PROVED** | `theorem TsKummer.kummerVerticalInf : KummerVerticalInf := kummerVerticalInf_proof` (L5734/L5566). VERIFIED | yes | ts-kummer d9c06585 | no |
| 28 | `PropTSGlue.HeckeIrreducible` | **REDUCED** | `theorem TSHecke.heckeIrreducible_of_connected (hC : Y3Connected) : HeckeIrreducible` (L6129, `scratch/ts-hecke/TSHecke.lean`, ts-hecke@ff8e6731). Converse `connected_of_heckeIrreducible (hR : R1R2fp) (hI : HeckeIrreducible) : Y3Connected` (L6137). VERIFIED | yes | ts-hecke ff8e6731 (also on hecke-rest 50cba553 by merge) | hecke-rest possibly (see below) |
| 29 | `PropTSGlue.HeckeNormalizationIrr` | **REDUCED** | `theorem TSHecke.heckeNormalizationIrr_of (hC : CurveGaloisChart) (hT : ObjBridge.TorsionStructure) : HeckeNormalizationIrr` (L6491) + `theorem curveGaloisChart_of (hN : CurveNormChart) : CurveGaloisChart` (L6482). Net: CurveNormChart + T5. VERIFIED | yes | ts-hecke ff8e6731 | hecke-rest possibly |
| 30 | `PropTSGlue.HeckeDegree` | **PROVED** from an existing bundle leaf | `theorem TSHecke.heckeDegree_of_torsion (hT : ObjBridge.TorsionStructure) : HeckeDegree` (L6335). Hypothesis = `TextbookLeaves.t5`, so no new open Prop. VERIFIED | yes | ts-hecke ff8e6731 | no |
| 31 | `PropTSGlue.HeckeBranch` | **REDUCED** | `theorem TSHecke.heckeBranch_of' (hRR : R1R2fp) (hCI : CurveChartInf) (hF : HeckeFibreSizes) (hT : ObjBridge.TorsionStructure) : HeckeBranch` (L7085). `RamOfFibreCount` is proved (`ramOfFibreCount` L7003). VERIFIED | yes | ts-hecke ff8e6731 | hecke-rest possibly |
| 32 | `PropTSGlue.HeckeNoVertRam` | **OPEN** | none. ts-hecke §6 analyses it with two routes: (NV) h-b1 Lemma NV, or (GR) good reduction of Y₃ over ℤ_(p) for p∤6 (Morita 1981, Carayol 1986, UNVERIFIED). Also gives an example showing branch data alone cannot imply it | — | ts-hecke ff8e6731 (analysis only) | hecke-rest possibly (no own commit yet) |

Strict LEAF/GLUE for the still-open fields: 21 `KummerCompositum` GLUE (report: open glue); 32 `HeckeNoVertRam` GLUE
(report: open glue, "Lemma NV").

## New open Props introduced by the reductions (all in `scratch/ts-hecke/TSHecke.lean`, ts-hecke@ff8e6731, namespace `TSHecke`)

| Prop | def line | report label + citation | strict | status | notes |
|---|---|---|---|---|---|
| `TSHecke.Y3Connected` := `∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ ConnectedSpace Y.left` | L6101 | "leaf R1conn". Cites Deligne, *Travaux de Shimura* (Bourbaki 389) §§2-3; *Variétés de Shimura* 2.1, 2.6.3; Milne, *Intro. Shimura varieties* §5, §13 (UNVERIFIED locators). The published result is π₀ = ℚ>0^×\𝔸_f^×/nrd(K) with reciprocity. The Lean Prop is the "consequence used", plus the pi0_check.py orbit computation | **GLUE** (consequence plus computation, not printed in this form) | OPEN | It is necessary (converse proved). The computation that HeckeIrreducible is true (2 geometric components, swapped by conjugation) is REPORTED as VERIFIED by pi0_check.py |
| `TSHecke.CurveNormChart` | L6469 | glue, STANDARD (Hartshorne II.6.7-6.8; Stacks 02OG; UNVERIFIED) | GLUE | OPEN | not reviewed (ts-hecke §7). Replaces `CurveGaloisChart` (L6453, also glue) through `curveGaloisChart_of` |
| `TSHecke.CurveChartInf` | L6565 | glue (curve theory), STANDARD (Hartshorne II.6.7-6.8) | GLUE | OPEN | |
| `TSHecke.HeckeFibreSizes` | L6591 | "glue from leaves (moduli count)". Cites Shimura uniformization; Baba–Granath, Canad. J. Math. 60 (2008) §3.1 p. 740 "per docs/research/locators.md"; h-b1 M9 (enumeration VERIFIED by rv_checks.py) | GLUE | OPEN | weakened within ts-hecke: the clause "every fibre ≤ M" was removed. M = 144; sizes 144/36/24/72 |
| (proved, no new input) `TSHecke.RamOfFibreCount` L6526, `GenericFibreCount` L6165 | | glue | — | PROVED (`ramOfFibreCount` L7003, `genericFibreCount` L6332) | |
| (prop-ts-glue) `PropTSGlue.SNSpecializeUnram`, `VerticalResidueDegree` | 2995, 2742 | glue | — | PROVED | |
| (ts-kummer) `TsKummer.UnramCompositum` | KummerTS.lean L4089 | glue (general DVR lemma) | — | PROVED (`unramCompositum` L4611) | |

No Prop in this group was found false or vacuous, and no statement change was proposed. Findings:
- ts-kummer §3.3 (REPORTED): the hypothesis `n < p` in `KummerVerticalFin/Inf` is never used. Statements are unchanged.
- ts-hecke §7 (REPORTED): prop-ts's `NormalizationModel` docstring (PropTSGlue.lean ~L708) still calls
  ℚ-irreducibility SPECULATIVE; it is now settled. That file was not edited.
- g3's docstring "truth SPECULATIVE" on `heckeIrreducible` is now stale (ts-hecke).

## Composite theorems (VERIFIED signatures)

- prop-ts-glue@3d41b3d5 `PropTSGlue.propTSAll_final'' (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue) (hC : KummerCompositum) (hA : KummerAbhyankarFinGlue) (hO : KummerOtherBranchFin) (hVF : KummerVerticalFin) (hAI : KummerAbhyankarInfGlue) (hOI : KummerOtherBranchInf) (hVI : KummerVerticalInf) (hI : HeckeIrreducible) (hNI : HeckeNormalizationIrr) (hD : HeckeDegree) (hB : HeckeBranch) (hV : HeckeNoVertRam) : PropTSAll`. That is 12 open glue Props.
- ts-sn@1b8a3b3d `PropTSGlue.propTSAll_final'`: same 12 hypotheses (uses `snSpecialize`). The name collides with
  prop-ts-glue's own `propTSAll_final'`, which takes `SNSpecializeUnram`.
- ts-kummer@d9c06585 `TsKummer.propTSAll_ts (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue) (hS : SNSpecialize) (hC : KummerCompositum) (hI : HeckeIrreducible) (hNI : HeckeNormalizationIrr) (hD : HeckeDegree) (hB : HeckeBranch) (hV : HeckeNoVertRam) : PropTSAll`. Also `TsKummer.kummerMeetGlue_of_compositum (hC : KummerCompositum) : KummerMeetGlue`.
- ts-hecke@ff8e6731 `TSHecke.propTSAll_of_tsHecke' (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue) (hS : SNSpecialize) (hC : KummerCompositum) (hA : KummerAbhyankarFinGlue) (hO : KummerOtherBranchFin) (hVF : KummerVerticalFin) (hAI : KummerAbhyankarInfGlue) (hOI : KummerOtherBranchInf) (hVI : KummerVerticalInf) (hconn : Y3Connected) (hT : ObjBridge.TorsionStructure) (hCN : CurveNormChart) (hCI : CurveChartInf) (hF : HeckeFibreSizes) (hV : HeckeNoVertRam) : PropTSAll`. The unprimed version takes `CurveGaloisChart`. `coverModelOfHecke_of_tsHecke(')` has the same Hecke hypotheses.
- **No branch combines all three** (prop-ts-glue/ts-sn SN proofs + ts-kummer's six + ts-hecke's reductions). All three
  are over the same prefix text, so a combined file is mechanical. Once combined, Prop. TS needs: bundle leaves T2,
  R1R2fp, T5; kernel `MobiusGlue` (proved: `mobiusGlue_of_t5`); open `KummerCompositum`, `Y3Connected`,
  `CurveNormChart`, `CurveChartInf`, `HeckeFibreSizes`, `HeckeNoVertRam`. That is 6 open Props, all strictly GLUE,
  where g3 had 14 fields.
- assemble-port (running; commits 10:37 f5ba81ea and 10:45 52e2caf1) has `HDec.HSyn.GluePieces5` in
  `scratch/assemble-port/parts/z99_bundle5.lean`, i.e. GluePieces4 minus `verticalResidueSeparable`, `snSpecialize`
  (filled by `PropTSGlue.verticalResidueSeparable_of_degree PropTSGlue.verticalResidueDegree` and
  `PropTSGlue.snSpecialize_of_unram PropTSGlue.snSpecializeUnram`), minus `r14Det`, `r1bFamily`, `carayolR17` (moved
  into leaf-fold2's `OpenResearchLeaves2`). The theorem is
  `HDec.HSyn.sixContactMin_of_leaves5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (gp : GluePieces5)`.
  - The log reports TailD VERIFIED (standard axioms) for the 43-field version (f5ba81ea).
  - The 41-field version at 52e2caf1 (base switched to leaf-fold2's prefix) has no compile record in the log yet.
  - World: HDec namespace (full names `HDec.PropTSGlue.*`).
  - The Kummer/Hecke fields are still all 12 present there; ts-kummer and ts-hecke are not folded.

## Running / other branches

- ts-kummer: last commit 28f72b65 10:42 (Core.lean, KummerCompositum stage 1 with `sorry`). Running on field 21.
- hecke-rest: only a merge of ts-hecke (50cba553, 10:24). It has no own files, report or log. Probably just started on
  the remaining Hecke glue; target unknown.
- ts-hecke (ff8e6731 10:26, "final"), ts-sn (1b8a3b3d 09:56, final) and prop-ts-glue (3d41b3d5 09:42, final) are done.
- hecke-all (11-12) is unrelated: Hecke L-function continuation, not these Props.
- No other branch committed today has its own report or log mentioning these names. I grepped docs/.fleet/log.md of all
  wip branches with commits after 06:00. The hits are only inherited copies of prop-ts-glue's docs, plus assemble-port.

---

# Appendix D (fork: assembly / running-task branches)


Scope: the 21 branches assigned to this fork. "Running" means the branch committed within about an hour of 10:50 and has no "stopped" snapshot. "Stopped" means its last commit is "snapshot of uncommitted work when the task was stopped (unchecked)". V = VERIFIED (read in the Lean file or log on the named commit). R = REPORTED (a log or report says so; the Lean was not read). Compile claims are always the task log's own (nothing was run here).

## 1. Per-branch status

| branch | last commit (time) | state | GluePieces4 fields touched | what it says / did |
|---|---|---|---|---|
| assemble-port | 52e2caf1 (10:45) | RUNNING | 4 removed (#19 verticalResidueSeparable, #20 snSpecialize proved; #34 r14Det, #9 r1bFamily, #41 carayolR17 moved into a research bundle) | Ports g0-assemble3 into the `HDec` world (§2). It has merged lt-local, but no part uses `LTLocal`, `LTGoodRed`, hodge-bc2 or unram-roots yet (V, grep) |
| leaf-fold2 | b38ee0c4 (10:38) | RUNNING (last commit is its log) | none of g0-assemble3's reductions. Its base is g0-assemble2 + leaf-fold. It matters for #3: `productMetrizationOfProductUnif_of_t35` (V, parts/b20_fold.lean:135) gets ProductMetrization from T35, so #3 `analyticUniformizationOfDim` is not needed in the HDec world | `HDec.HSyn.sixContactMin_of_open2` (§2). Second flat run failed with 8 errors (part b10, `map` ambiguous); fixed by sectioning, and the olean check FlatTailTest passes (R, log) |
| rv-fast | 6a6ba11f (10:32, "report draft") | probably RUNNING (draft) | indirect: the local route of lt-local / lg-kerwild (the alternative to #44-46) | Review verdicts (R, docs/research/rv-fast.md draft): lg-kerwild is CONCERN with core SOUND; unram-roots, afr-absfrob and curve-infra are SOUND. Finding: `LGKerWild.exists_localGlue_of_tateModuleFree` (every ℓ) keeps the hypothesis `G7Clauses β' ε' L` on data hidden behind `∃`. That hypothesis is false for the TateBridgeK witness whenever some a_σ ≠ 1, so the theorem is inert. The ℓ=5,3 route `localGlue_of_tateBridge35` (used by lt-local) is not affected, but needs `[L:ℚ] ≤ D` and ε5 = 1 on G_L×G_L. lt-local's `g7Clauses_of_transport` supplies these (lt-local §3). Also: the committed KerWild.lean can no longer be rebuilt from current local-glue sources (an integration issue, not a soundness issue) |
| hom-unify | cf987ee4 (10:47) | RUNNING | #35 homLinearLift | New single leaf `HomUnify.HomLatticeCorr` (V, parts/H20_bundle.lean:206). It is the conjunction of HomLinearLift (lifting) and T11aHom-style realization over ℂ, so it is STRONGER than #35. `HomUnify.homLinearLift_of_corr (h : HomLatticeCorr) : G0Galois.HomLinearLift := h.1` (V). Also `G0Galois.g10Glue_of_homLinearLift`, `GaloisPiecesHom`, `HSyn.GluePieces3Hom` (linked-tate's 29-field GluePieces3 with g10Glue → homLinearLift) and `HSyn.sixContactMin_of_leaves3Hom` (V names; the log records no compile of HomUnifyFlat.lean). It also adds a module ZInQKernel/Contrib/HomUnify/Corr.lean |
| infra-hodge | c8b5e7b0 (10:46) | RUNNING | none of the 46 directly | Target is metrization's `ProductHodgeLattice` (V, assemble.py docstring). Parts phl_1 (cotangent maps, L-structure copied from hodge-bc2) and phl_2 (product splitting, ω functoriality). No log.md and no compile record |
| heightbc-contrib | 285c1e37 (10:43, merge of main) | RUNNING, just started | #4, #5 (presumably; inferred from the branch name only) | No own commit. The only Contrib file is hodge-bc2's ZInQKernel/Contrib/HodgeBC2/ExtFrac.lean. `hodgeBCInjective` and `omegaBaseChange` are NOT yet in ZInQKernel/Contrib on any branch read (V, ls-tree) |
| mobius-contrib | 8756167c (10:47) | RUNNING | none (MobiusGlue is a derived input of #2 and of the prop-ts route, not a field) | `ZInQKernel/Contrib/Mobius/*` holds `LeafQM.AV.CurveGlue.mobiusGlue_of_T5/_t5` and `imagePlaneCurveClosed`. lake build passes, axioms standard (R, log) |
| dim-contrib | 33d2ca5d (10:01) | finished (report) | none | Ten modules in ZInQKernel/Contrib/Dim (curve-infra dim=trdeg, infra-smooth-dim) (R, report) |
| frob-contrib | 72097f5a (10:35) | RUNNING | none directly (lt-local / TateBridge35 route) | Adopts AbsFrob (Basic, AlgFrobRed, Sanity) and UnramRoots into ZInQKernel/Contrib. lake build of AbsFrob passes (R, log) |
| spread-out | 60340bed (= frob-pieces final, 10:12) | started, no own commit | presumably frob-pieces' `AbVarSpreadsOut` (N1-g1) on the TateBridge35 route (inferred from the name) | nothing yet |
| twist-descent | 933d94b9 (10:42) | RUNNING | #33 twistDescent | Step 0: "Decision: TRUE as stated". Step 1 (V, file read): Mathlib-only `ZInQKernel/Contrib/TwistDescent/GaloisDescent.lean` (namespace `TwistDescentGD`: `exists_open_gal`, `descend`, `effectiveEpi_of_isPullback_field`), lake build passes (R). `G0ModField.KernelField.TwistDescent` is NOT proved yet and its statement is not changed |
| linked-frob | 2261dfb7 (10:36) | RUNNING | #44 linkedFrob | V (parts/10_linkedfrob.lean): `theorem LinkedFrobRed.linkedFrob_of_algFrobLink (hF : FrobTrace.AlgFrobLink) : UnramTate.LinkedFrob` and `theorem LinkedFrobRed.linkedFrob_of_algFrobRed (hR : FrobTrace.AlgFrobRed) : UnramTate.LinkedFrob`. The log says "assembly setup" and records no compile yet. The frob chain is re-copied over linked-tate's Leaves.lean world (the HDecomp-import world and this world cannot be imported together). Once compiled, LinkedFrob ⇐ AlgFrobRed ⇐ (frob-pieces) AbVarSpreadsOut + ProperSmoothGenConnected + I2-Red + I2-NMP |
| tyz-cm | da1bc29b (10:38); log has a 10:50 entry | RUNNING | none (CR3/TYZ side) | Leaf `ShimuraReciprocityModFn`, `xQExpRational`, `yQExpRational`, `cmFieldOfDefinition_of_modFn'` (R, log) |
| t40-tate | c87d3b9b (10:05) | possibly running | none (textbook T39/T40) | `ZInQ.RLeaf.tateCuspLaurent`, `tateLaurentTorsion` (R, log) |
| t40-igusa | 5ee27509 (10:05, report) | finished | none | `igusaTransitive_iff : IgusaTransitive ↔ X0Transitive ∧ TateMuN` (R, report) |
| alg-frob-red | 94799bde (08:41, "final") | finished (the brief listed it as running; the branch has not moved since 08:41) | TateBridge35 route | `AlgFrobRedRed.algFrobRed_of_leaves`, `tateBridge35_of_leaves` (R); later superseded by afr-absfrob and frob-pieces |
| unif-dims | 65c2c8db (08:10, "final") | finished | #3 (source) | already folded by g0-assemble3 (part e30) |
| g8-local | fba3cf08 (10:12) | STOPPED | alternative local data for #45/#46 (g8-object route) | Contrib/G8Local/{WildLocal, TateFix, LocalFieldF} build (R). Its scratch assembly (`RaynaudNF`, `TorsionFieldBound`, `Char2UpperBreak`, `linkedTateObjS_of_core`) was unfinished when it stopped (log: first attempt failed on a missing module prefix) |
| g8-tate-b | 120fc20a (10:12) | STOPPED | TateBridge35 route | Contains commit 72c0894f (10:02), which is NOT on origin/wip/g8-tate: `tateBridge35OnL_of_algFrobLink (hT : PkgI3.TateModuleFree) (hF : FrobTrace.AlgFrobLink)`, `tateBridge35OnL_of_algFrobRed`, `tateBridge35OnL_of_gen`, `tateBridge35_of_onL`. Dev.lean exit 0, standard axioms (R, log). The snapshot adds part_g7d.lean (`G8Tate.G7DataD`, unchecked); it duplicates g0-assemble3's G7Data fix |
| period-glue-b | 946fb35e (10:12) | STOPPED (the live branch is period-glue, cbe9fe4c 10:27) | #15, #10, #12 | log (R): `sphereFactorAffine_proof : PeriodMap.SphereFactorAffine` and `hauptmodulUnique_of_S8 : S8Nonzero → HauptmodulUnique` (light build, 0 errors); `baseChangeClassUnique_proof : PeriodMapH.BaseChangeClassUnique` (DevBC, 0 errors). QMTwistLattice was in progress in the unchecked snapshot (DevTL.lean, part_tl.lean) |
| period-num | c6d31639 (10:12) | STOPPED | #14, #16 | log (R): `s8Nonzero_proof : S8Nonzero` (run_full1: 0 errors, standard axioms). `s8WeightExact_of : ThetaModularity → NormalizerDecomp → S8WeightExact` (run_full2: 0 errors), with new Prop `NormalizerDecomp` (every normalizer element is r·w·u; the log calls it "published structure of N(𝒪)/ℚ^×𝒪^×"; no citation, so GLUE under the strict rule). ThetaModularity is the existing leaf R4 |

## 2. Theorems that compose several results into one assembly

| theorem (branch, commit) | world | hypotheses | compile |
|---|---|---|---|
| `HDec.HSyn.sixContactMin_of_leaves5 (r : ResearchLeaves5) (t : OpenTextbookLeaves) (gp : GluePieces5) : ZInQ.SixContactMin` (assemble-port f5ba81ea) | HDec: scratch/h-decomposition/Leaves.lean, `namespace HDec` | GluePieces5 = GluePieces4 minus verticalResidueSeparable, snSpecialize, r14Det, so 43 fields; R14 := `G0Galois.R14Det` in ResearchLeaves5 | R: TailA-F and TailD exit 0, axioms standard (log; TailD_out.txt at f5ba81ea lists `HDec.HSyn.sixContactMin_of_leaves5`) |
| `HSyn.sixContactMin_of_leaves5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (gp : GluePieces5) : ZInQ.SixContactMin` := `sixContactMin_of_leaves4 (researchLeaves4_of_open2 r) (textbookLeaves_of_open2 t) (gluePieces4_of_gluePieces5 r gp)` (assemble-port HEAD 52e2caf1, parts/z99_bundle5.lean:179) | HDec, on leaf-fold2's prefix LeavesP | GluePieces5 has 41 fields (fields5.txt, V): GluePieces4 minus #9, #19, #20, #34, #41. Filled by `verticalResidueSeparable_of_degree verticalResidueDegree`, `snSpecialize_of_unram snSpecializeUnram`, `r.r14`, `r.r1b`, `r.r17` (V). Docstring: "41 fields: 14 LEAF, 3 LEAF?, 24 GLUE" | NOT compiled per log (the last compile recorded is the 43-field version). Running |
| `HDec.HSyn.sixContactMin_of_open2 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (l : OpenAddedLeaves2) (g : OpenGlue2) : ZInQ.SixContactMin` (leaf-fold2) | HDec | 26 + 18 + 12 + 10 = 66 fields. Its base is g0-assemble2's GluePieces3, so OpenGlue2 still has the unreduced x6KummerFibre, periodMapGlue, hauptmodulUnique, propTSAll, conjIsogMaps, modelG3, linkedTateLocal, plus hodgeBCInjective, omegaBaseChange, cPtsTransport | R: report "VERIFIED", olean chain. The second flat run failed and was fixed; FlatTailTest exit 0 |
| `HSyn.sixContactMin_of_leaves3Hom` (hom-unify cf987ee4) | linked-tate's Leaves.lean (root namespace) | linked-tate's `GluePieces3` (29 fields) with g10Glue → homLinearLift (`GluePieces3Hom`) | not recorded in the log |
| lt-goodred integ `HSyn.sixContactMin_of_leaves4 (r : ResearchLeaves) (t : TextbookLeaves) (gp4 : GluePieces4)` | linked-tate world | lt-goodred's own 27-field GluePieces4: linked-tate's GluePieces3 minus goodRedTorsion and qmEndRank. A DIFFERENT structure from g0-assemble3's 46-field GluePieces4 | R (lt-goodred report). The parent already covers it |

## 3. Notes for the main table

- **No branch combines g0-assemble3's GluePieces4 with the 2026-11-13 proofs.** That covers hodge-bc2 (#4, #5), lt-goodred (#42, #43), ts-sn, ts-hecke, unram-roots, frob-pieces, period-*, lt-local and linked-frob. The exception is prop-ts-glue's #19 and #20, folded by assemble-port in the HDec world (V).
- **World mismatch for assemble-port.** The HDec port means root-namespace proofs (lt-goodred, linked-frob, and lt-local's LtLocal4 over g0-assemble3's G7Data) need the same mechanical HDec edits that assemble-port's log lists: `_root_.X` → `_root_.HDec.X`, `open ZInQ` → `open _root_.ZInQ ZInQ`, and Mathlib-namespace blocks rooted.
- **#35 homLinearLift.** hom-unify's leaf `HomLatticeCorr` is stronger than the field. It is a unification with T11aHom, not a reduction to something smaller.
- **#3 analyticUniformizationOfDim.** It can be dropped in the HDec world: leaf-fold2's `productMetrizationOfProductUnif_of_t35` uses the existing T35. assemble-port's 41 fields still include #3.
- **Period fields (stopped branches only; check the live period-glue branch for current status).** #15 and #10 are proved on period-glue-b (R). #14 is proved on period-num (R) and also on period-glue cbe9fe4c (commit message). #16 is reduced on period-num to R4 + `NormalizerDecomp` (R).
