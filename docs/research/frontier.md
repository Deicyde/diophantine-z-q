# frontier: every open Prop on the path to `ZInQ.FrozenTarget`

Task frontier, 2026-11-13; refreshes r2 to r7, 2026-11-14 (text checks only, no Lean run). Base of r7:
fork main 4db0a627 (integration w66, ecdb5d84, with r6 merged), on wip/frontier-r7. Branch snapshot: the commits in
`scratch/frontier/refs.txt` (r7 section, read 19:53 PST). Lean: `scratch/frontier/TYZChain.lean`, `TopChain.lean`
(compiled 11-13, unchanged in r2). Mechanical check: `scratch/frontier/chain.py` (with `chainlib.py`), run from the
repository root; output `scratch/frontier/chain_out.txt`. Results log: `scratch/frontier/log.md`. Working notes from
three read-only survey agents (11-13): `scratch/frontier/agent-{h-glue,h-leaves,tyz}.md`. Only this report and
`scratch/frontier/` were edited. Model work; no human review.

Marks: **VERIFIED** (read in a named Lean file or report at a named commit, or compiled here), **REPORTED** (a task's
report or log says so; the Lean was not re-read), **UNVERIFIED** (a theorem number or locator taken from a report or
from memory; this host has no network and no copy of the papers).

**Classification (the integrator's rule, applied strictly).** **LEAF** = a published, refereed statement, and the
Lean Prop is that statement or a specialization of it (fewer cases, weaker constant read off the same display).
Textbook theorems (Mumford, Milne, BLR, …) count as published. Everything else is **GLUE**: the project's own
arguments, statements that are standard but not printed in that form, "consequences" whose derivation needs an
argument, readings of a printed statement, and composites of several published theorems. Where a GLUE Prop is a
consequence or composite of published theorems, the table says so ("lit-composite") and names the nearest sources;
it is still GLUE.

**Form and two counts (r3, the integrator's ruling of 2026-11-14).** Every row has a form: *published form* (the
printed statement, or a specialization read off the same display), *consequence of one theorem* (a short
derivation from one printed theorem), *composite* (several published results) or *project glue*. The **strict
count** (LEAF = published form only) leads: every GLUE row under it is a Lean argument the project still owes. The
**lenient count** follows, "if consequences of one theorem count as leaves". A consequence or composite row
becomes a strict LEAF once its derivation is compiled; the form column says where the derivation is written
(for leaf-fold3's fields, leaf-review-a and leaf-review-b).

## 0. Main result

**The list.** If every proof and reduction that the branches had compiled by 2026-11-14 19:53 PST is folded in
(scenario F, §5), the open Props on the path to `ZInQ.FrozenTarget` are **86: 54 LEAF and 32 GLUE** in the strict
count. If consequences of one theorem count as leaves, they are 68 LEAF and 18 GLUE. Two rows (H-182, H-185),
reduct-glue's leaves over a strictly henselian base, follow the first version of the base review and are tagged
"review v1, v2 pending".

**The library theorem.** `ZInQ.OneProof.frozenTarget` on main (scenario A) has 71 hypotheses, leaf-fold13's 65 fields
and the six TYZ and GZ Props, and its proof uses all of them (x6-fold's scan finds no unused field). Its fields are
now classified in the integrator's table `docs/one-proof/kinds.tsv` (rendered in `docs/one-proof/OPEN.md`), whose
headline follows the integrator's strict convention: a leaf with a flagged plausible weaker reading counts GLUE, a
merely unread leaf stays LEAF, flagged. The fields are then **46 LEAF and 19 GLUE** in the strict count (the strictest
reading, with `gonzalezRotgerCountX6Ab` a composite); 47 and 18 with `gonzalezRotgerCountX6Ab` published (the table's
strict column); by kind alone, 49 published and 16 other. With the top: 48 LEAF and 23 GLUE strict, 59 and 12 lenient.
Scenario F has more rows because it also applies the splits that the folds leave out on purpose: each replaces one
field by a leaf plus smaller statements (leaf-fold9 §5).

| premise | open Props | strict LEAF | strict GLUE | lenient LEAF | lenient GLUE | table |
|---|---|---|---|---|---|---|
| GZ, `Literature.GrossZagier` | 2 | 0 | 2 | 0 | 2 | §2.2 |
| TYZ, `Literature.TYZThm35ReadingA` | 6 | 3 | 3 | 4 | 2 | §3.2 |
| H, `SixContactMin`: research-level fields of r3 | 5 | 3 | 2 | 3 | 2 | §4.2 |
| H: textbook fields of r3 | 0 | 0 | 0 | 0 | 0 | §4.3 |
| H: fields that were glue in C4 | 0 | 0 | 0 | 0 | 0 | §4.4 |
| H: Props introduced by reductions until r3 | 5 | 5 | 0 | 5 | 0 | §4.5 |
| H: fields of the H base introduced in r4 | 29 | 28 | 1 | 28 | 1 | §4.6 |
| H: Props open only in scenario F, introduced in r4 | 9 | 1 | 8 | 3 | 6 | §4.7 |
| H: fields of leaf-fold9 introduced in r5 | 1 | 1 | 0 | 1 | 0 | §4.8 |
| H: Props open only in scenario F, introduced in r5 | 2 | 0 | 2 | 2 | 0 | §4.9 |
| H: fields of leaf-fold10 and leaf-fold11 introduced in r6 | 9 | 5 | 4 | 7 | 2 | §4.10 |
| H: Props open only in scenario F, introduced in r6 | 6 | 1 | 5 | 5 | 1 | §4.11 |
| H: fields of leaf-fold13 introduced in r7 | 6 | 4 | 2 | 5 | 1 | §4.12 |
| H: Props open only in scenario F, introduced in r7 | 6 | 3 | 3 | 5 | 1 | §4.13 |
| **total** | **86** | **54** | **32** | **68** | **18** | |

By form: 54 published form, 14 consequences of one theorem, 13 composites, 5 project glue (`CMStabObj`,
`CoverModelOfHeckeN`, `P1SchemeQ`, `RingClassLattice`, `SemiAbelianDescendsSepClosed`).

**Since r6 (11 new rows; 6 LEAF and 5 GLUE strict, 9 and 2 lenient).** One row is proved (H-191 `IgusaAlg`), 2 are
split into smaller statements (H-53, H-184), 3 leave the route (H-183, H-186, H-189) and 5 are replaced by their forms
on abelian schemes (H-142, H-177, H-178, H-179, H-180). The H base is leaf-fold13's `sixContactMin_of_open16` inside
the library (C4''''''', §1): x6-fold folds x6-glue, so `r1r2Ab` and `x6ConicModel` are proved from five printed leaves
restated on abelian schemes, `geomConnOfAlgClosure` and `rayClassCMAb`. On top of it scenario F applies reduct-b (the
three SGA 7 IX DVR fields from their strictly henselian forms with `StrictHenselizationPair`, and
`semistableReductionDVR` from `raynaudSemistable` with two textbook fields), unipotent-b (`semistableUnipotent` from
SGA 7 IX 3.5 as printed), t09-pic (`t09SymmIsogenyExists` from four leaves over the Picard functor), igusa-alg
(`IgusaAlg 5` to `9` proved, so the theta route rests on `LinYangThetaCurve` alone), and r6's edges that still apply.
H-169 (`deligneComponentsY3PrintedAb`) counts GLUE since the integrator's ruling after shimura-cft's review. The count
of rows does not change: 11 go, 11 come.

**Not applied** (§4.1): sh-route's theorems, whose statements add `[CharZero K]` and a perfect residue field to the
strict-henselization leaves and to the fields; shimura-cft's `shimuraFamilyAb_of_mainThmI`, whose leaf implies the
weaker H-154 that scenario F keeps; and gap-triage's probe that `CoverModelOfHeckeN` is not needed, stated over
leaf-fold9's whole bundle (H-95 says so).

**Who works on what** (the integrator's `docs/one-proof/claims.tsv`, w66; the rows say which): rayclass-cft
(`rayClassCMAb`, branch head 7b27f1c3) and a fleet task (`quotientP1Coordinate`) are in flight; the cloud claims mark
21 rows (cloud W11 2; cloud W13 1; cloud W14 1; cloud W15 1; cloud W16 5; cloud W17 3; cloud round 2 8). claims.tsv
still lists reduct-b, unipotent-b, t09-pic and igusa-alg as in progress, but w66 merged their reports, and scenario F
uses them. After w66 the fork's branches carry leaf-fold14 (97579a97; its summary reports the fold done, with
reduct-b's fields), linyang-printed (3bb5a828; `LinYangThetaCurve` from two printed leaves), sh-printed2 (ea486e30;
`blr_1_2_4` and `sga7_IX_3_3` in characteristic 0 from their strictly henselian forms) and sem-prune (15a9a0ae); their
reports are not merged, so this report does not use them, and the rows they name say so.

**The 86 names** (L = LEAF in both counts; c = consequence of one theorem, LEAF only in the lenient count; all others
GLUE; details in the tables):
- GZ: `ZInQ.GZDecomp.FHNonvanishing`; `ZInQ.GZDecomp.GrossZagierHeegner`.
- TYZ: `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` (L); `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2`; `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` (L); `T5Glue.ShimuraMainCM` (L); `T5Glue.X0ModuliGalois` (c); `T5Glue.RingClassLattice`.
- H: `PkgI2.NeronOggShafarevich` (L); `PkgI3.FaltingsSemisimple` (L); `PkgI3.FaltingsTate` (L); `PkgI4.PanBerger`; `LeafModCurves.R16_EichlerShimuraJ1'`; `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` (L); `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` (L); `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` (L); `ZInQ.Contrib.AVB1.PoincareComplement` (L); `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` (L); `AVGlue.CartierSmooth` (L); `AVGlue.GeomConnOfRationalPoint` (L); `AVGlue.GroupSchemeEquidim` (L); `AvSplit.T4.MulEtaleAbelianScheme` (L); `AvSplit.MumfordTorsionAlgClosed` (L); `BPAnalytic.Uniformization.UniformizationLeafAll` (L); `AvSplit.MilneIsogenyQuasiInverse` (L); `ZInQ.HomLattice.GAGAMorphism` (L); `ZInQ.HeightSplit.JavanpeykarBound` (L); `ZInQ.HeightSplit.GaudronRemondThm14` (L); `ZInQ.HeightSplit.BostLowerBound` (L); `ZInQ.HeightSplit.PazukiCor13Upper` (L); `ZInQ.RLeaf.IgusaGL2` (L); `CurveSplit.RegularSmoothPerfect` (L); `CurveSplit.ShimuraGoodReductionNoGuard`; `ZInQ.Contrib.HodgeSplit.TateTwistInvariants` (L); `ZInQ.Contrib.HodgeSplit.AxSenTate` (L); `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` (L); `ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` (L); `ZInQ.Contrib.HodgeSplit.BdRInvariants` (L); `ZInQ.Contrib.HodgeSplit.DSThm965` (L); `ZInQ.Contrib.HodgeSplit.DSThm966` (L); `HDec.QMSplit.Yu.YuThm11` (L); `HDec.QMSplit.Aut.QMCentralizerCMC` (L); `HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar` (L); `HDec.QMSplit.Theta.IgusaPsi4` (L); `HDec.QMSplit.Theta.IgusaChi10` (L); `HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq` (L); `HDec.LeafQCheck.HM.QMSplit.ShimizuCovolumeO1` (L); `MCRGlue.ProperCurveAF`; `MCRGlue.FiniteQuotientExists` (L); `MCRGlue.TameQuotientSmooth`; `MCRGlue.SmoothModelOfP1` (c); `MCRGlue.TameFixedPointsDisjoint` (c); `MCRGlue.TameInertiaCyclic`; `HDec.PropTSRed.CoverModelOfHeckeN`; `MCRQuot.P1SchemeQ`; `MCRQuot.CMStabObj`; `ReductSplit.NeronSchemeModelExistsDVR` (L); `HDec.QMSplit.Moduli.ShimuraHolFamily` (c); `ModularSplit.R17.CarayolRealization` (c); `ShimuraSplit.GonzalezRotgerCountX6Ab`; `ShimuraGlue.DeligneComponentsY3PrintedAb`; `LeafQM.AV.R1UnivRigid.MumfordRigidityCore` (L); `CToPrinted.BLR_1_2_4` (c); `CToPrinted.FaltingsLemma5Printed` (L); `CToPrinted.RaynaudKernelBound` (L); `CToPrinted.SGA3_VIB_3_10` (L); `CToPrinted.SGA7_IX_3_3` (c); `CToPrinted.EGAIV_8_10_5_openImm` (L); `CToPrinted2.KatoRealizationCohSS` (c); `ReductGlue.RaynaudSemistableSH` (L); `ReductGlue.SemistablePersistsSH` (c); `ReductGlue.StrictHenselizationPair` (c); `ReductGlue.StrictHenselizationInside` (c); `HDec.HSyn.G0Split.ThetaPt.ThetaGlue.LinYangThetaCurve`; `HDec.QMSplit.Moduli.GeomConnOfAlgClosure` (L); `ShimuraGlue.DeligneComponentsX6PrintedAb` (L); `HDec.QMSplit.Moduli.BabaGranathRationalAb` (L); `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` (L); `HDec.QMSplit.Moduli.ElkiesEquationsX6Ab`; `ShimuraGlue.Ray.RayClassCMAb` (c); `UnipotentB.SemistableUnipotentPrintedGen` (L); `UnipotentB.SemiAbelianDescendsSepClosed`; `T09Pic.PicRepresentableAbVar` (L); `T09Pic.PicZeroAbVar` (L); `T09Pic.PhiAmpleIsogeny` (c); `T09Pic.WeilPairingMumford` (c).

**How far this is checked.**
- **Scenario A is one compiled theorem.** `ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`, on
  leaf-fold13's bundles since w66) derives `ZInQ.FrozenTarget` from leaf-fold13's four bundles (35 + 15 + 14 + 1 = 65
  fields), the TYZ Props `TYZThm11Integral`, `TYZLemma29Mod2`, `ShimuraReciprocityModFn`, `TYZThm33` and the two GZ
  Props. x6-fold reports `lake build +ZInQKernel.OneProof.Main` passing, standard axioms and no unused field
  (REPORTED, x6-fold §1). `chain.py onep` reads the signature: its hypotheses are scenario A's (the four bundles and
  the six top Props); the bundles' fields are the 65 rows of `kinds.tsv`, with the names and type heads of the build's
  `open-statements.json`, whose six other hypotheses have scenario A's heads.
- **Scenario F.** A plus the edges of §4.1, each compiled on its branch per its report and log. `chain.py` checks
  signatures (0 mismatches over 196 theorem edges, 32 of them followed on the route), route A's transfer and
  theta-split's consumer replacement, and compares definitions where a proof lives in another Lean world (§5.2). F is
  not compiled as one file.

**Declarations proved by this task.** All compile with `lake env lean` (exit 0, no `sorry`), and `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for each (VERIFIED; outputs `scratch/frontier/TYZChain_out.txt`,
`TopChain_out.txt`).

```lean
-- scratch/frontier/TYZChain.lean: tyz-cm's eleven Shimura modules and cm-bridge's Bridge.lean, both as on
-- cm-bridge ed50dc33 (which merges tyz-cm 0ad48a7d), verbatim minus imports (build_tyz.py), then:
theorem ZInQ.GZTheta.Frontier.newCM : ZInQ.GZTheta.NewCM     -- verbatim copy of atkin-li's proof
theorem ZInQ.GZTheta.Frontier.heckeThetaNewform : ZInQ.GZDecomp.HeckeThetaNewform
theorem ZInQ.Frontier.tyzThm35ReadingA_of_open (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hS : ZInQ.Contrib.TYZGenus.Shimura.ShimuraReciprocityModFn)
    (h318 : Lemma318Literal HHprime)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ ZInQ.Contrib.TYZGenus.CMBridge.tyzZ)
    (h5 : ZInQ.Contrib.TYZGenus.CMBridge.Lemma321Five) :
    ZInQ.Literature.TYZThm35ReadingA
theorem ZInQ.Frontier.frozenTarget_of_open (hH : ZInQ.SixContactMin) (h11 …) (h1 …) (h29 …) (hS …)
    (h318 …) (h35 …) (h5 …)                          -- the seven hypotheses above
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
-- scratch/frontier/TopChain.lean: the same over fork main's modules only
theorem ZInQ.Frontier.frozenTarget_of_open_main (hH : ZInQ.SixContactMin)
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hcm : ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition ringClassFieldD)
    (hs : TYZSigmaFixesZn) (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
```
`newCM`/`heckeThetaNewform` show that atkin-li's proof of the GZ leaf `HeckeThetaNewform` compiles verbatim over fork
main's modules; `TYZChain.lean` shows that tyz-cm's and cm-bridge's reductions compose.

**Findings in brief** (§7): since r6, 1 row proved, 2 split, 3 off the route and 5 replaced; scenario A is one library
theorem with 71 hypotheses, all used, its 65 fields 46 LEAF strict by the integrator's table; the 5 project-glue Props
are `CMStabObj`, `CoverModelOfHeckeN`, `P1SchemeQ`, `RingClassLattice`, `SemiAbelianDescendsSepClosed`.

## 1. The chain to `ZInQ.FrozenTarget`

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| C0 (r3) | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` with `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` | `Contrib/GZTheta/NewCMFinal.lean` @ main; `Contrib/TYZChain/Main.lean` @ w54 | `SixContactMin`, the 4 TYZ Props of §3.2, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (r1-r2: this task's `frozenTarget_of_open` in `scratch/frontier/TYZChain.lean`, with cm-bridge's 7 TYZ Props) |
| C1 | `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` | `Contrib/GZDecomp/Decomp.lean` @ main | `SixContactMin`, `TYZThm35ReadingA`, `HeckeThetaNewform`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (via `GrossZagierCd`; `HeckeContinuation`, `FunctionalEquation5` discharged by the proved `ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) |
| C2 | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` | `Contrib/GZTheta/NewCMFinal.lean` @ wip/atkin-li 6f77abb1 | `SixContactMin`, `TYZThm35ReadingA`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` |
| C3 | TYZ: §3.1 | | → `TYZThm35ReadingA` |
| C4''''''' (r7) | H: `HDec.HSyn.sixContactMin_of_open16 (r : OpenResearchLeaves13) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ22.lean` L335 @ main (leaf-fold13 29885092, merged in w66: x6-fold e33b690a, which adds `TailZ20`-`TailZ22` over leaf-fold11 b73da969: `lake build +ZInQKernel.OneProof.Main` passes, standard axioms, no unused field, no existing constant changed, REPORTED by x6-fold §1) | → `ZInQ.SixContactMin`; 35 + 15 + 14 + 1 fields (§4) |
| C4'''''' (r6) | H: `HDec.HSyn.sixContactMin_of_open15 (r : OpenResearchLeaves12) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves11) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ19.lean` L1895 @ main (leaf-fold11 b73da969, merged in w63, with leaf-fold12's `TailZ18`, `TailZ19`; over leaf-fold10 a5df68fe, merged in w61, and the prune 0218a662, merged in w62: `lake build +ZInQKernel.OneProof.Main` passes, standard axioms, no unused field, REPORTED by leaf-fold11 §4) | → `ZInQ.SixContactMin`, 32 + 15 + 13 + 1 fields; superseded: leaf-fold13 fills its bundles inside OneProof |
| C4''''' (r5) | H: `HDec.HSyn.sixContactMin_of_open9 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves9) (l : OpenAddedLeaves8) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ9.lean` L161 @ main (leaf-fold9 cf6914e1, merged in w60; over leaf-fold8's `sixContactMin_of_open8` in `TailZ4.lean`: `lake build +ZInQKernel.OneProof.Main` exit 0, standard axioms, the closure of `sixContactMin_of_open9` without `sorryAx`; REPORTED by its report §1, §4) | → `ZInQ.SixContactMin`, 30 + 18 + 14 + 1 fields; superseded: leaf-fold10 and leaf-fold11 fill its bundles inside OneProof |
| C4'''' (r4) | H: `HDec.HSyn.sixContactMin_of_open8 (r : OpenResearchLeaves8) (t : OpenTextbookLeaves8) (l : OpenAddedLeaves8) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ4.lean` L265 @ main (leaf-fold8 b0f2f6da, merged in w59; over leaf-fold7's `sixContactMin_of_open7` in `TailX.lean`, w58: `lake build +ZInQKernel.OneProof.Main` exit 0, standard axioms, the closure of `sixContactMin_of_open8` without `sorryAx`; REPORTED by its report §1) | → `ZInQ.SixContactMin`, 31 + 20 + 14 + 1 fields; superseded: leaf-fold9 fills its bundles (`researchLeaves8_of_open9`, `textbookLeaves8_of_open9`) inside OneProof |
| C4''' | H: leaf-fold6's `HDec.HSyn.sixContactMin_of_open6` | `scratch/leaf-fold6/parts/f20_fold6.lean` @ main (leaf-fold6 733d8013, in w55; flat file compiled, REPORTED) | superseded: leaf-fold7 fills its bundles (`researchLeaves5_of_open7`, `glue6_of_open7`, …) inside OneProof |
| C4'' (r3) | H: `HDec.HSyn.sixContactMin_of_open5 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves5) (l : OpenAddedLeaves5) (g : OpenGlue5)` | `scratch/leaf-fold5/Leaves5.lean` L121755 @ wip/leaf-fold5 5a7e03d1 (in w54; flat file of the final text, 121 783 lines, md5 5999e1db: `lake env lean` exit 0 in 1570 s, 0 errors, no `sorry`, 349 axiom reports all standard; olean chain and `Check5.lean` compiled; REPORTED by its log) | → `ZInQ.SixContactMin`; 26 + 21 + 21 + 2 fields (§4) |
| C4' (r2) | H: `HDec.HSyn.sixContactMin_of_open4 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4) (l : OpenAddedLeaves4) (g : OpenGlue4)` | `scratch/leaf-fold4/Leaves4.lean` L118447 @ wip/leaf-fold4 9dcf1ca8 (final; flat file, 118 478 lines, md5 6bbeb639: `lake env lean` exit 0 in 1048 s, 0 errors, no `sorry`, 326 axiom reports all standard; olean chain and `Check4.lean`, the kernel conclusion, compiled; REPORTED by its report and log); on fork main since w49 | → `ZInQ.SixContactMin`; 26 + 19 + 20 + 1 fields (§4) |
| C5 | assemble-port's `HDec.HSyn.sixContactMin_of_leaves5` (C4 of the 17:35 report; 26 + 17 + 27 fields) | `scratch/assemble-port/AssemblePort.lean` L116751 @ 92a27877 | C4' is its successor through leaf-fold2-4: the 17:35 scenario-F edges folded, `chartProper`, `chartQuasiFinite`, `hauptmodulUnique` proved, `periodMapGlue`, `abVarSpreadsOut` reduced to leaves, `DivisiblePoints` removed (leaf-fold4 §1.1); g0-assemble3's 46-glue-field `sixContactMin_of_leaves4` before it |
| C6 | H, per field: §4 | | each open field, or the Props it was reduced to |
| **C0 ∘ C4''''''' in the library (r7)** | `ZInQ.OneProof.frozenTarget (r : HDec.HSyn.OpenResearchLeaves13) (t : HDec.HSyn.OpenTextbookLeaves10) (l : HDec.HSyn.OpenAddedLeaves12) (g : HDec.HSyn.OpenGlue7) (h11 …) (h29 …) (hS …) (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33) (hL2 …) (hL3 …) : ZInQ.FrozenTarget` | `ZInQKernel/OneProof/Main.lean` @ main (OneProof since w56; `OneProof/TYZSplit.lean` since w59; leaf-fold13's bundles since w66) | scenario A of this report: C4''''''' with tyz-chain's T0, T-11 from the printed Theorem 3.3, and the kernel's C1 |

The fork's registered headline (`ZInQKernel/MainLiterature.lean`) has five hypotheses; two are proved
(`ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) and C1 already uses them. C4' concludes the kernel's
`ZInQ.SixContactMin` (the flat file imports the kernel's definition; `Leaves.lean` is wrapped in `namespace HDec`), so
C0 and C4''''''' compose by modus ponens. Earlier compiled H assemblies (cpts-transport's 44-field and linked-ram's 45-field
`GluePieces5` in the W0 world, lt-goodred's and linked-frob's variants, leaf-fold2's `sixContactMin_of_open2`) are
superseded by C4, C4', C4'', C4''', C4'''', C4''''' and C4''''''.

## 2. GZ: `ZInQ.Literature.GrossZagier`

Only `C_d`, `d ≡ 5 (mod 8)` squarefree, is used (gz-decomp §0.3): the chain goes through `ZInQ.GZDecomp.GrossZagierCd`,
which `Literature.GrossZagier` implies (`grossZagierCd_of_grossZagier`).

### 2.1 Chain (VERIFIED: signatures read; Z5 compiled here)

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| Z1 | `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagierCd` | `Contrib/GZDecomp/Scope.lean` @ main | `SixContactMin`, `TYZThm35ReadingA`, `GrossZagierCd` → `FrozenTarget` |
| Z2 | `ZInQ.GZDecomp.grossZagierCd_of_leaves'` | `Contrib/GZDecomp/Decomp.lean` @ main | `HeckeThetaNewform`, `FHNonvanishing`, `GrossZagierHeegner` → `GrossZagierCd` (glue G1-G6 proved) |
| Z3 | `ZInQ.GZTheta.heckeThetaNewform : HeckeThetaNewform` | `Contrib/GZTheta/NewCMFinal.lean` @ atkin-li 6f77abb1 | no hypotheses (also `AtkinLiTwistNew`, `NewformUniqueAcrossLevels` proved there) |
| Z5 | `ZInQ.GZTheta.Frontier.heckeThetaNewform` | `scratch/frontier/TYZChain.lean`, `TopChain.lean` | verbatim copy of Z3, compiled over fork main, standard axioms |

### 2.2 Open Props (2, both GLUE)

| # | Lean name | defined in | class | nearest published sources (all numbers UNVERIFIED) | last task; newest commit | running now | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| Z-1 | `ZInQ.GZDecomp.FHNonvanishing` | `Contrib/GZDecomp/Decomp.lean:109` @ main | GLUE (lit-composite: Friedberg–Hoffstein's theorem with chosen local conditions, plus the root number of a twist `ε(f⊗χ_D) = ε(f)χ_D(−N)`; gz-decomp §2.4 argues it is not stronger than the source; **open**: whether FH's printed theorem allows the level `32d²`, even and not squarefree; a human must check) | Friedberg–Hoffstein, Ann. of Math. 142 (1995) 385–423, Thm B; Bump–Friedberg–Hoffstein, Invent. Math. 102 (1990) 543–618; Waldspurger, Compositio Math. 54 (1985); Atkin–Li, Invent. Math. 48 (1978) | gz-decomp; main | no | composite: Friedberg–Hoffstein's theorem with chosen local conditions and the root number of a twist (gz-decomp §2.4) |
| Z-2 | `ZInQ.GZDecomp.GrossZagierHeegner` | `Contrib/GZDecomp/Decomp.lean:131` @ main | GLUE (lit-composite: Gross–Zagier's formula, Gross's `ȳ_K = −ε y_K`, the modular parametrization (Eichler–Shimura, Faltings' isogeny theorem), nondegeneracy of `ĥ` (proved in Tau Ceti), folded into one existential because the Heegner point cannot be named in Lean today; gz-decomp §2.5) | Gross–Zagier, Invent. Math. 84 (1986) 225–320, Thm I.6.3, Ch. V; Gross, *Heegner points on X₀(N)* (Durham 1983), 1984, §5; Shimura 1971 Thm 7.14–7.15; Faltings, Invent. Math. 73 (1983), Kor. 2; Shimura, Nagoya Math. J. 43 (1971) | gz-decomp; main | no | composite: Gross–Zagier's formula, Gross's conjugation relation, the modular parametrization, nondegeneracy of the height (gz-decomp §2.5) |

Already on record, not applied (gz-decomp §0.3): replace the premise `Literature.GrossZagier` by `GZDecomp.GrossZagierCd`.

## 3. TYZ: `ZInQ.Literature.TYZThm35ReadingA`

Caveats attached to every row (tyz-decomp §0): reading A is printed in no refereed text (only in Smith,
arXiv:1603.08479, Thm 2.1, unrefereed); TYZ = Tian–Yuan–Zhang, arXiv:1411.4728v1 = Asian J. Math. 21 (2017) 721–774,
read by AI agents in the arXiv version only; `Lnnnn` are lines of its source `Period7.tex` as quoted by the reports
(not on this host); Proposition N and the encoding were reviewed by AI models only.

### 3.1 Chain (VERIFIED: signatures read by `chain.py`; T0 compiled here)

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| A1 | `ZInQ.Contrib.TYZDecomp.tyzThm35ReadingA_of_leaves` | `Contrib/TYZDecomp/Leaves.lean:380` @ main | `TYZThm11Integral`, `TYZLcalOne`, `TYZLemma29Mod2`, `TYZGenusPackage` |
| A2 | `ZInQ.Contrib.TYZGenus.Package.tyzThm35ReadingA_of_cmLeaves` | `Contrib/TYZGenus/Package.lean:948` @ main | h11, h1, h29, `CMFieldOfDefinitionTYZ`, `IInH4`, `TYZSigmaFixesZn`, `HprimeNormal`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ` |
| A3 (finest in a kernel module on main) | `ZInQ.Contrib.TYZGenus.RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD` | `Contrib/TYZGenus/RingClassBridge.lean:55` @ main | h11, h1, h29, `CM.CMFieldOfDefinition ringClassFieldD`, `TYZSigmaFixesZn`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ` (`IInH4`, `HprimeNormal` proved: `iInH4`, `hprimeNormal`); used by `TopChain.lean` |
| B1 (cm-bridge, scratch) | `ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_lemma321Five` | `scratch/cm-bridge/Bridge.lean` L3201 @ cm-bridge ed50dc33 (final; merges tyz-cm 0ad48a7d) | h11, h1, h29, `Shimura.ShimuraReciprocityModFn`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → Thm35First ℓ tyzZ`, `Lemma321Five` |
| inside B1 | cm-bridge: `GenusFieldLeLni`, `IInHprime`, `BetaOnGenus7`, `tyzThm36Seven_of` (TYZ Thm 3.6(3) from `ShimuraReciprocityPic`, `EtaModelFricke`, `CMAlgebraic`); tyz-cm: `etaModelInvariant`, `etaModelEquation`, `etaModelFricke`, `etaCuspGrowth`, `xQExpRational`, `yQExpRational`, `cmValueRingClass_of_modFn`, `shimuraReciprocityPic_of_shimuraModFn`, `cmFieldOfDefinition_of_cmValueRingClass` (proved) | `ZInQKernel/Contrib/TYZGenus/Shimura*.lean` (11 modules) and `Bridge.lean` @ ed50dc33 | |
| **T0** (this task, compiled) | `ZInQ.Frontier.tyzThm35ReadingA_of_open` (= B1) | `scratch/frontier/TYZChain.lean` (B1 with the 11 tyz-cm modules, verbatim) | the 7 Props of the 17:35 list → `TYZThm35ReadingA`; with B2-B4, the 5 Props of §3.2 |
| B2 (r2) | `ZInQ.Contrib.TYZLcal.tyzLcalOne_of_leaves` | `scratch/tyz-lcal/TYZLcal.lean` L900 @ tyz-lcal 61d0b14e (on main since w52) | `TYZThm11Integral`, `TYZLemma29Mod2` → `TYZLcalOne` (Theorem 1.1 at `m = 1`, Lemma 2.9 mod 2 at `m = 3`, and an analytic bound `‖L(C₁,1)‖ ≤ 3.35` from the fork's Hecke continuation) |
| B3 (r2) | `ZInQ.Contrib.TYZGenus.T321.lemma321Five_of_shimuraModFn'` | `scratch/tyz-321/L321.lean` L5460 @ tyz-321 521eacc0 | `Shimura.ShimuraReciprocityModFn` → `Lemma321Five` (ring class field theory, the kernel's genus theory, cm-bridge's genus characters; no TYZ text) |
| B4 (r2) | `ZInQ.Contrib.TYZGenus.TYZ35.thm35First_of_lcal_thm33` | `scratch/tyz-35/Thm35.lean` L1363 @ tyz-35 a8101726 (on main since w52) | `∀ ℓ, IsTYZLcal ℓ → TYZThm33Pinned ℓ` → `∀ ℓ, IsTYZLcal ℓ → Thm35First ℓ tyzZ` |
| B5 (r3) | `T318.package_lemma318Literal_HHprime_of_sqrtTwoNotIn` with `Sqrt2Glue.sqrtTwoNotInHHprime` | `Contrib/TYZChain/Lemma318.lean`, `Sqrt2Glue.lean` @ w54 (tyz-318 94b05c87, sqrt2-glue 84107b66) | → `Lemma318Literal HHprime`, no hypotheses (ss-exponent proved the supersingular exponent tyz-318 used) |
| **T0 (r3, kernel)** | `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` | `Contrib/TYZChain/Main.lean` @ w54 (tyz-chain; B1 with B2-B5 as kernel modules) | `TYZThm11Integral`, `TYZLemma29Mod2`, `Shimura.ShimuraReciprocityModFn`, `∀ ℓ, IsTYZLcal ℓ → TYZThm33Pinned ℓ` → `TYZThm35ReadingA` |
| T0' (r4) | `ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33` | `ZInQKernel/OneProof/TYZSplit.lean` @ main (tyz-split 99e582b5, compiled into OneProof by leaf-fold8) | `TYZThm33` → T0's hypothesis `∀ ℓ, IsTYZLcal ℓ → TYZThm33Pinned ℓ`, so T-11 follows from the printed Theorem 3.3; both scenarios use it |
| B6 (r4) | `ZInQ.Contrib.TYZGenus.TYZSplitT5.shimuraReciprocityModFn_of_split` | `scratch/tyz-split/T5.lean` @ main | `CMModuli`, `X0RatStructure` → `Shimura.ShimuraReciprocityModFn`; scenario F uses it |
| B7 (r6) | `T5Glue.cmModuli_of_t5'`, `T5Glue.x0RatStructure_of_leaf` | `scratch/t5-glue/T5Glue.lean` @ main (t5-glue 39bb3cd2, merged in w66; r6 read it at the earlier head 405763f6, the same file; the later commits add the report and its second review, which finds `RingClassLattice` true) | `ShimuraMainCM`, `RingClassLattice` → `CMModuli` (the absolute Artin map's surjectivity and `InvertibleColon` proved over Tau Ceti); `X0ModuliGalois` → `X0RatStructure`; scenario F uses them under B6 |

### 3.2 Open Props (6: 3 LEAF, 3 GLUE in the strict count; 4 LEAF, 2 GLUE in the lenient count)

| # | Lean name | defined in | class | citation (UNVERIFIED unless marked) | last task; newest commit | running now | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| T-1 | `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` | `Contrib/TYZDecomp/Leaves.lean` @ main | **LEAF** (specialization: odd `m` only) | TYZ Thm 1.1, first assertion, L371–380 (read by nt-tyz) | tyz-decomp; main (tyz-lcal audit 11-13: faithful, not stronger) | cloud round 2: in progress (T-1); new base case TYZLcalOne proved (claims.tsv) | published form: specialization of TYZ Thm 1.1 to odd `m` (tyz-lcal audit: faithful, not stronger) |
| T-3 | `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2` | same | GLUE (mod-2 composite of Lemma 2.9 and Prop. 2.3) | TYZ Lemma 2.9, L1062–1066 (journal Lemma 2.9 per the AI locator audit); Prop. 2.3, L580–586 | tyz-decomp; main (tyz-lcal audit 11-13: faithful, not stronger) | cloud round 2: in progress (T-3) (claims.tsv) | composite: TYZ Lemma 2.9 with Prop. 2.3, read mod 2 (tyz-lcal audit) |
| T-12 | `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` | `ZInQKernel/OneProof/TYZSplit.lean` L147 @ main | **LEAF** | TYZ Theorem 3.3 over the kernel's definitions, for `n ≡ 5, 7 (mod 8)`, `𝒫(d)` existential | tyz-split | no | published form: TYZ Thm 3.3, Period7.tex L1299-1311, specialized (tyz-split §1), carried along the kernel's eta model of `X₀(32)` by the q-expansion principle (`IsRatModFn 32`), which already sits behind `hS`; a clause-by-clause statement review found the leaf Thm 3.3 or weaker (tyz-split §1 and the docstring, wip/w61 3c241950); the `[i]` sign of the base point is printed (`α = −i` in the Hecke-action proof, about L1564-1566) |
| T-15 | `T5Glue.ShimuraMainCM` | `scratch/t5-glue/T5Glue.lean` L908 @ main | **LEAF** | the main theorem of complex multiplication with torsion, idelic, in Weierstrass coordinates over Mathlib's `PeriodPair`, finite adeles and Tau Ceti's `ideleClassArtinMap` (replaces T-13 (from T-5)) | t5-glue | no | published form: Shimura 1971 Thm 5.4; Lang, Elliptic functions, Ch. 10 Thm 3 (t5-glue §0; numbers UNVERIFIED) |
| T-16 | `T5Glue.X0ModuliGalois` | `scratch/t5-glue/T5Glue.lean` L670 @ main | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count) | the canonical model of `X₀(N)`: `σ(g(τ)) = g(τ')` when `σ ∈ Aut(ℂ)` carries `(E_τ, ⟨1/N⟩)` to `(E_τ', ⟨k/N⟩)`, for `g` regular on `ℍ`; no CM (replaces T-14 (from T-5)) | t5-glue | no | consequence of one theorem: Shimura 1971 §6.7; Deligne–Rapoport VI-VII; Diamond–Shurman §7.5-7.7 (t5-glue §0; numbers UNVERIFIED); the report's label: LEAF, a consequence of the print |
| T-17 | `T5Glue.RingClassLattice` | `scratch/t5-glue/T5Glue.lean` L2303 @ main | GLUE (project glue) | the idelic and the congruence descriptions of `Pic O` agree: the lattice of an idele whose ring class is that of `J ∩ O` is a multiple of `J ∩ O` (replaces T-13 (from T-5)) | t5-glue | no | project glue: t5-glue's named glue (standard: Neukirch I §12 and VI §1, Cox §7 and §9; numbers UNVERIFIED); the absolute Artin map's surjectivity and `InvertibleColon` are proved (Tau Ceti) |

Retired rows: T-2 `TYZLcalOne` (proved, B2), T-4 `Lemma318Literal` (proved, B5), T-6 `Thm35First` (reduced to T-11,
B4), T-7 `Lemma321Five` (proved, B3); r4: T-5 (split by tyz-split into `CMModuli` and `X0RatStructure`), T-11 (from
the printed TYZ Thm 3.3 (`TYZThm33`, tyz-split)); r6: T-13 `CMModuli` and T-14 `X0RatStructure` (split by t5-glue,
B7).

## 4. H: `ZInQ.SixContactMin`

Base (r7): leaf-fold13's compiled C4''''''' (29885092, in w66: x6-fold e33b690a, `TailZ20`-`TailZ22`), inside
OneProof, over leaf-fold11 (b73da969, w63, with leaf-fold12), leaf-fold10 (w61), the prune (w62), leaf-fold9 (w60),
leaf-fold8 (w59) and leaf-fold7 (w58). Bundles: `OpenResearchLeaves13` (35), `OpenTextbookLeaves10` (15),
`OpenAddedLeaves12` (14) and leaf-fold7's `OpenGlue7` (1: `quotientP1Coordinate`). The fields' forms are the
integrator's `kinds.tsv` (with the contributor kit, 46afc732): 49 published, 11 consequences, 4 composites, 1 project
glue by kind; its strict convention counts three published kinds as GLUE, and this report records them as composites:
`gonzalezRotgerCountX6Ab` (the strictest reading), `elkiesEquationsX6Ab` and `deligneComponentsY3PrintedAb`. r6 kept
its own table, `scratch/frontier/fields11.tsv`; r7 drops it. `chain.py` reads the bundles from
`ZInQKernel/OneProof/H/TailZ22.lean`, `TailZ11.lean` and `TailX.lean` at main. Row numbers are kept, retired rows
listed, new rows from H-192 (§4.12, §4.13).

### 4.1 What changed since r6 (signatures VERIFIED by `chain.py`)

Compiled into C4''''''' (scenario A): by x6-fold, `r1r2Ab` and `x6ConicModel` proved from x6-glue's leaves restated on
abelian schemes (`deligneComponentsX6PrintedAb`, `babaGranathRationalAb`, `gonzalezRotgerX6Ab`, `elkiesEquationsX6Ab`,
`rayClassCMAb`), the textbook criterion `geomConnOfAlgClosure` and T5, with the transfers `…_iff_ab` and the field
`mumfordRigidityCore`. r6's rows for x6-glue's leaves are replaced by the new fields (H-142, H-177, H-178, H-179,
H-180), and H-150 is a field now (§4.12). r6's changes are in the r6 report (`git show
f18bcb90:docs/research/frontier.md`, §4.1).

Applied on top by scenario F:

| field of C4''''''' (rows) | now | theorems · task · file |
|---|---|---|
| `shimuraFamilyAb` (H-139) | ⇐ `ShimuraFamily` with route A's transfer and `MumfordRigidityCore`; `ShimuraFamily` ⇐ `ShimuraHolFamily` (H-154) with the GAGA-level step (as in r6; shimura-cft's stronger leaf is not taken) | `LeafQM.AV.R1UnivRigid.shimuraFamily_iff_ab` (route-a-fold); `LeafQM.AV.R1UnivRigid.mumfordRigidity_of_core`; `HDec.QMSplit.Moduli.shimuraFamily_of_hol` · shimura-split · `scratch/shimura-split/ShimuraFam.lean` |
| `r17` (H-21) | ⇐ `CarayolRealization` (H-157); the transport to every attached representation is proved (as in r6) | `ModularSplit.R17.carayolR17'_of_realization` · modular-split · `scratch/modular-split/R17.lean` |
| `eigenformHTNew` (H-127) | ⇐ `KatoRealizationCohSS` (H-181) and the fields `TateTwistInvariants`, `AxSenTate` (as in r6) | `CToPrinted2.eigenformHTNew_of_printedSS` · c-to-printed2 · `scratch/c-to-printed2/CToPrinted2.lean` |
| `raynaudSemistable`, `semistablePersistsDVR` (fields since leaf-fold10; r6: H-186) | ⇐ `RaynaudSemistableSH`, `StrictHenselizationPair` and the field `MulEtaleAbelianScheme` (H-182, H-187, H-101); `SemistablePersistsSH` with `StrictHenselizationPair` (H-185); r6's `StrictHenselizationNeron` is off the route | `ReductB.raynaudSemistable_of_SH_pair`, `ReductB.semistablePersistsDVR_of_SH_pair` · reduct-b · `scratch/reduct-b/ReductB.lean` |
| `semistableReductionDVR` (r6: H-183, H-189) | ⇐ `raynaudSemistable` and the textbook fields `MumfordTorsionAlgClosed`, `MulEtaleAbelianScheme` (H-102, H-101): reduct-b's K1, so `SemistableReductionSH` and the named glue `ReductionFromSH` are off the route | `ReductB.semistableReductionDVR_of_raynaud` · reduct-b · `scratch/reduct-b/ReductB.lean` |
| `semistableUnipotent` (r6: H-184) | ⇐ SGA 7 IX 3.5 as printed (`SemistableUnipotentPrintedGen`, H-197), the glue `SemiAbelianDescendsSepClosed` (H-198; proved for perfect residue fields), the field `MulEtaleAbelianScheme` and `StrictHenselizationInside` (H-188) | `UnipotentB.semistableUnipotent_of_printedGen` · unipotent-b · `scratch/unipotent-b/UnipotentB.lean` |
| `t09SymmIsogenyExists` (r6: H-53) | ⇐ `PicRepresentableAbVar`, `PicZeroAbVar`, `PhiAmpleIsogeny`, `WeilPairingMumford` (H-199, H-200, H-201, H-202), over the vendored relative Picard functor, with ample bundles, `φ_L`, `f^∨` and Mumford's `ē_n` as genuine definitions | `T09Pic.t09SymmIsogenyExists_of_four` · t09-pic · `scratch/t09-pic/Pic.lean` |
| `thetaRatiosAlgebraic` (H-44; r6: H-191) | replaced at its consumer (theta-split, route 1): TailA's `ThetaPointOfFibre` from `FibreQMPeriod`, `ThetaEightSquare` and `QMThetaSymmetricCurve`, in place of `HDec.HSyn.G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios`; theta-glue proves `ThetaEightSquare`, and igusa-alg proves `IgusaAlg 5` to `9`, so `QMThetaSymmetricCurve` follows from `LinYangThetaCurve` alone (H-190) | `HDec.HSyn.G0Split.ThetaPt.ThetaSplit.thetaPointOfFibre_of_qm_curve` · theta-split · `scratch/theta-split/ThetaUse.lean`; `HDec.HSyn.G0Split.ThetaPt.ThetaGlue.thetaEightSquare` · theta-glue · `scratch/theta-glue/ThetaGlue.lean`; `HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal.qmThetaSymmetricCurve_of_linYang` · igusa-alg · `scratch/igusa-alg/IgusaAlg.lean` |
| `quotientP1Coordinate` (the glue field; H-84's successor) | ⇐ mcr-glue's six leaves (H-89..H-94; `TameQuotientSmooth` is L3), T5, and three glue Props: mcr-quot's `P1SchemeQ` and `CMStabObj`, and the decomposition's `CoverModelOfHeckeN` | `HDec.MCRGlue.quotientP1Coordinate_of_leaves` (compiled in `ZInQKernel/OneProof/H/TailW.lean`) with mcr-glue's `coordinateNormalization_of` · mcr-glue · `scratch/mcr-glue/MCRGlue.lean`; `fibreAutTame_of''`, `genericQuotientP1_of''`, `cMSectionsDisjoint_of''`, `coordinateFromSections_of''` and their inputs (namespace `MCRQuot`) · mcr-quot · `scratch/mcr-quot/MCRQuot.lean` |

On the TYZ side F uses B6 and, under it, t5-glue's B7 (§3.1). The leaves on a witness of the moduli clause that carry
`R1fpProps` are now only H-154: x6-fold states x6-glue's leaves on abelian schemes. Route A's transfer makes that leaf
equivalent to the same leaf on abelian schemes once the field `mumfordRigidityCore` (H-170) is given.

mcr-quot proves the four glue Props under the coordinate (`FibreAutTame`, `GenericQuotientP1`, `CMSectionsDisjoint`,
`CoordinateFromSections`) from T5, L3, `CurveBijIso` and three glue Props: `P1SchemeQ` and `CMStabObj`, which are new,
and `CoverModelOfHeckeN`, the decomposition's own glue. The chain derives `CoverModelOfHeckeN` only through
`HeckeNoVertRam`, downstream of the coordinate that mcr-quot feeds, so here it is counted as open glue: the coordinate
still rests on project glue, and mcr-quot does not discharge it. gap-triage (w66) finds it unnecessary: mcr-quot's
`ModelYIrreducible` is the chain's `HeckeIrreducible`, which the chain proves from the field
`deligneComponentsY3PrintedAb`, and mcr-quot's composite compiles with it in place of `CoverModelOfHeckeN`
(`scratch/gap-triage/GlueProbe.lean`, `MCRQuotNV.lean`); the probe takes leaf-fold9's whole bundle, so scenario F does
not apply it yet (H-95).

Off the route since r7 (the edges stay in `chain.py`): x6-glue's `HDec.QMSplit.Moduli.r1r2_of_published` and
`HDec.QMSplit.Moduli.x6ConicModel_of_published` with route A's `LeafQM.AV.R1UnivRigid.r1R2fpRep_iff_ab`, whose
conclusions x6-fold proves in C4'''''''; reduct-glue's `ReductGlue.raynaudSemistable_of_SH'` and the modus-ponens
steps through `ReductionFromSH`, `PersistsFromSH` and `UnipotentFromSH`, which reduct-b's and unipotent-b's theorems
replace; theta-glue's `HDec.HSyn.G0Split.ThetaPt.ThetaGlue.qmThetaSymmetricCurve_of_alg59`, which igusa-alg's theorem
replaces; since r6: `HDec.QMSplit.Moduli.y3Connected_of_deligne` (shimura-split) and
`ModularSplit.DimJac.dimJacobianEqGenus_of_glue` (modular-split), whose fields leaf-fold10 compiles; reduct-split's
`ReductSplit.raynaudCriterion_final'`, `ReductSplit.semistableReductionThm_final`,
`ReductSplit.semistablePersists_final`, `ReductSplit.semistableNeronBaseChange_of_leaves` and
`ReductSplit.faltingsLemma5BC_final`, whose conclusions are no longer fields; shimura-split's
`HDec.QMSplit.Moduli.r1r2fpRep_of_printed_t5` and `HDec.QMSplit.Moduli.x6ConicModel_of_elkies_t5` with shimura-glue's
edges, which x6-glue's theorems replace; modular-split's `ModularSplit.EigenHT.eigenformHTNew_of_coh`; qm-split's
`HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.thetaRatiosAlgebraic_of`, whose field theta-split bypasses; cm24-value's
`CM24.igusaCMValue24_field`, now inside C4''''''; since r5: coarse-factor's `r1r2fpRep_of_canonical''`, which
shimura-split's theorem extends; qm-glue's and coarse-factor's `x6ConicModel` theorems with `ConicCanonical`, which is
`X6Kummer.X6ConicModel` verbatim (shimura-split, `Iff.rfl`); height-glue's `r5fpCount_of_t11b`; the cloud-w07 proofs,
now inside C4'''''. The r2-r4 edges compiled inside C4'''' are off the route as well. Retired rows (r2, r3): H-23,
H-26, H-27, H-28, H-29, H-31, H-37, H-39, H-40, H-45, H-47, H-48, H-50, H-55, H-58, H-62; r4: H-1, H-2, H-3, H-8,
H-10, H-14..H-20, H-22, H-24, H-25, H-32, H-33, H-35, H-36, H-38, H-41..H-44, H-46, H-51, H-52, H-54, H-61, H-63,
H-64, H-66, H-67, H-69, H-73..H-76, H-80..H-88, T-5, T-11; r5: H-4, H-12, H-21, H-59, H-78, H-106, H-107, H-108,
H-111, H-114, H-115, H-116, H-127, H-137, H-138, H-139, H-140, H-141, H-143; r6: H-79, H-133, H-134, H-144, H-145,
H-146, H-147, H-149, H-151, H-152, H-153, H-155, H-156, H-158, H-159, H-160, H-161, H-162, H-163, H-164, H-165, H-166,
H-167, T-13, T-14; r7: H-53, H-142, H-177, H-178, H-179, H-180, H-183, H-184, H-186, H-189, H-191. Not applied: the
variants each report keeps aside (r7: sh-route's `strictHenselizationNeron0_final`, `strictHenselizationPair0_final`,
`strictHenselizationInside0_final` and `route_final` from `NeronBaseChangeSH`, whose statements add `[CharZero K]` and
a perfect residue field; reduct-b's Route B-cp, `ss1_ss3_of_cp`, over the restricted leaf `SemistablePersistsSHcp`;
unipotent-b's `semistableUnipotent0_of_printed`, which concludes the field with two instances added; t09-pic's split
of `WeilPairingMumford` into one printed property per leaf (L4a-L4f, `t09SymmIsogenyExists_of_split`) and its weaker
variants; shimura-cft's `shimuraFamilyAb_of_mainThmI`, whose leaf implies H-154; gap-triage's
`modelYIrreducible_of_open9`, over leaf-fold9's bundle; r6: c-to-printed's `shimuraFamily_of_mainThmI`, whose leaf
`ShimuraMainThmIY3` implies H-154 and is still a consequence; c-to-printed2's `eigenformHTNew_of_realization` with the
leaf `KatoRealization`; theta-split's route 2, `thetaRatiosAtQM_of_cm` through Shimura's theorem on theta-nulls at CM
points; reduct-glue's `strictHenselizationNeron_of` from the pair `StrictHenselizationDVR`,
`NeronBaseChangeUnramifiedDVR`, whose second member may exceed the print; reduct-glue's `SerreTateFromComplete`, whose
field `serreTateThm2` the prune removed; r4: height-split's `r20_of_leaves` with `IsogenySemistableBaseChange`;
curve-split's `x0Transitive_of_igusaSL2X`; qm-split's `qmHauptmodulBase3_of_shimizu` and `y3Connected_of`;
hodge-split's `panBerger_of_templates`; r5: shimura-split's `r1r2fpRep_of_split6`, which keeps `r1rec` and `r5` as
inputs; modular-split's weaker `KatoRealization` leaf; reduct-split's `raynaudCriterion_final`, which
`raynaudCriterion_final'` supersedes by proving the perfect case of its glue).

### 4.2 Research-level fields of r3 still open (5: 3 LEAF, 2 GLUE strict; 3 LEAF, 2 GLUE lenient)

| # | field : Lean name | leaf | class | citation | flags | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| H-5 | `r7a : PkgI2.NeronOggShafarevich` | R7(a) | **LEAF** | Serre–Tate, Ann. of Math. 88 (1968), Thm 1 | UNVERIFIED | pkg-I2; cloud round 2: in progress (H-5, Néron–Ogg–Shafarevich) (claims.tsv) | published form: Serre–Tate 1968 Thm 1 (leaf-review-b §2.2) |
| H-6 | `r9a : PkgI3.FaltingsSemisimple` | R9(a) | **LEAF** | Faltings, Invent. Math. 73 (1983), Satz 3 (erratum 75 (1984)) | UNVERIFIED | pkg-I3 | published form: Faltings 1983 (leaf-review-b §2.3) |
| H-7 | `r9b : PkgI3.FaltingsTate` | R9(b) | **LEAF** | Faltings 1983, Satz 4, Kor. 1 | UNVERIFIED | pkg-I3 | published form: Faltings 1983 (leaf-review-b §2.3) |
| H-9 | `r11r12 : PkgI4.PanBerger` | R11 + R12 | GLUE (joint consequence of two theorems) | Berger, Invent. Math. 148 (2002), Thm 0.7; Pan, JAMS 35 (2022), Thm 1.0.4 | JAMS numbering UNVERIFIED | pkg-I4 | composite: Pan and Berger (leaf-review-b §2.4) |
| H-13 | `r16 : LeafModCurves.R16_EichlerShimuraJ1'` | R16 | GLUE (three suppliers) | Shimura 1971 Thm 7.9; Shimura 1973 Thm 1 | | leaf-modcurves | composite: Shimura 1973, Shimura 1971 §7.4, Diamond–Shurman (leaf-review-a §3.3) |

### 4.3 Textbook fields of r3 still open (0: 0 LEAF, 0 GLUE strict; 0 LEAF, 0 GLUE lenient)

None left: each is proved or split (§4.1).

T6, T7, T8, T9, T11(b), T3, T41, T34 and T38 are proved or reduced (r2); their replacements are rows of §4.5.
T4, T5, T23, T24, T27, T33, T35, T40 and the normal model of a function field are proved or split in r4 (§4.1).

### 4.4 Fields that were glue in C4, still open (in C4''''''' they are `OpenAddedLeaves12` fields) (0: 0 LEAF, 0 GLUE strict; 0 LEAF, 0 GLUE lenient)

| # | field : Lean name | def part | content; nearest published sources (UNVERIFIED) | report's label | last task; running | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|

### 4.5 Props introduced by reductions until r3, still open (5: 5 LEAF, 0 GLUE strict; 5 LEAF, 0 GLUE lenient)

| # | Lean name | def file @ commit | from field | class; content; sources (UNVERIFIED) | last task; running | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-65 | `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` | `ZInQKernel/Contrib/SpreadOut/Spread.lean` L49 @ main | 44-46 | **LEAF** (descent of properness; EGA IV₃ 8.10.5(xii), Stacks 081F) | spread-out; cloud round 2: in progress: repairing round 1's vendored port (H-65) (claims.tsv) | published form: EGA IV₃ 8.10.5(xii) (spread-out) |
| H-70 | `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` | `Contrib/AVB1/AlgClosed.lean` L38 @ main | t6 (H-26) | **LEAF** (T6 over algebraically closed fields only: Mumford, *Abelian varieties* §19 Thm 3 in Mumford's own setting; Milne 1986 Thm 12.5) | av-b1; cloud round 2: in progress (H-70) (claims.tsv) | published form: Mumford §19 Thm 3 in its own setting (av-b1 §3.1) |
| H-71 | `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` | same, L51 | t7 (H-27) | **LEAF** (specialization: T7 over algebraically closed fields, without `deg P = 2g` and `P(n) = deg(n − φ)`; Mumford §19 Thm 4) | av-b1; cloud round 2: in progress (H-71); supplier PR Deicyde/diophantine-z-q#13 held until it lands (claims.tsv) | published form: specialization of Mumford §19 Thm 4 (av-b1 §3.2) |
| H-72 | `ZInQ.Contrib.AVB1.PoincareComplement` | `Contrib/AVB1/Poincare.lean` L42 @ main | t8 (H-28) | **LEAF** (Poincaré's complete reducibility in its complement form, weakened; Milne 1986 Prop. 12.1; Mumford §19 Thm 1) | av-b1; cloud round 2: in progress (H-72) (claims.tsv) | published form: Milne 1986 Prop. 12.1, weakened (av-b1 §3.3) |
| H-77 | `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` | `Contrib/NeronC/NeronGroup.lean` L82 @ main | t41 (H-39) | **LEAF** (a smooth separated quasi-compact model with the extension property and no group law: weaker than BLR §1.4 Thm 3; the group law, `gen` a homomorphism and uniqueness are proved) | neron-c; cloud round 2: in progress (H-77) (claims.tsv) | published form: BLR §1.4 Thm 3 without the group law (neron-c §1) |

Proved and gone from the tables: r7, `IgusaAlg` (igusa-alg); r6, `IgusaCMValue24` (cm24-value), `HTDual`
(c-to-printed2), `FixedTorsionRationalImperfect`, `SemistableAlmostAll`, `SemistableLocalGlobal` and
`SemistableNeronBaseChangeLocalGlobal` (reduct-glue, the last two through c-to-printed's printed fields); r5,
`DeligneSerreConseq` (modular-split); r4, `EigenformTwist`, the two EGA IV descents, `ZariskiConnectedness`,
`T11bExists`, `NeronMappingAbelianSchemeSurj` (PRs #6-#10), `JacobianExists ℚ`, `NormalModelOfFunctionFieldQ`
(cloud-w07), `QMClassNumberOne` (qm-split), `CurveBijIso` (curve-split); r3, `GammaStarGen`; r2, `SerreRigidity3`,
`T09_WeilPairing` (av-b2), and in the chain below `HeckeVertWitness`: `SmoothFibreReduced` (smooth-fibre),
`SpecialFibreMaxIdeal`, `SpecialFibreUniformizer`, `SpecialFibreDVR` (vert-witness), `ModelGenericFibre`,
`GermOfQbarValues`, `ModelIntegral`, `ModelFunctionField` (model-glue). Props that r4's own tasks introduced and
proved were never rows: height-split's glue (`AnalyticUniformizationExists`, `AnalyticUniformizationUnique`,
`UniformizationDim`, `MetrizationOfUniformization`, `NeronMetrizable`, proved from T35 by height-glue), qm-split's
`GammaStarFromO1` (qm-glue), qm-glue's `CoarseFactor` (coarse-factor), mcr-glue's four glue Props (mcr-quot, from
three others). Proved before 17:35: see the 17:35 report (`git show d8c95123:docs/research/frontier.md`). Props that
r5's tasks introduced and proved were never rows: reduct-split's `TorsionFieldOfDefinition`, `DVRFiniteExtension`,
`DVRComapFinite` and `IsogenyBaseChangeDeg`; shimura-split's `PairsLift` (from T5). Props that r6's tasks introduced
and proved or reduced were never rows: shimura-glue's `MobiusCompose` (proved); reduct-glue's `UnipotentFromSH` and
`PersistsFromSH` (from the strict-henselization leaves); x6-glue's `ConicModelT` (from its charts); t5-glue's
`AbsArtinSurjectiveQNeg` and `InvertibleColon` (proved over Tau Ceti); theta-glue's `ThetaEightSquare`,
`IgusaThetaSymmetric` (from `IgusaAlg`) and `IgusaAlg 3`, `IgusaAlg 4` (proved); genus-route's `DimJ1Le5` (proved);
route A's `MumfordRigidity` (from `mumfordRigidityCore`). Props that r7's tasks introduced and proved were never rows:
t09-pic's `veryAmpleIsAmple` (formerly a leaf, EGA II 4.5.10) and its genuine definitions; igusa-alg's `IgusaAlg 3` to
`IgusaAlg 9` and its two theta-route theorems; sh-route's commutative algebra (`SHExists0`, `SHInside0`, `SHPair0`);
unipotent-b's two `K^s` versus `K̄` Props.

### 4.6 Fields of the H base introduced in r4 (29: 28 LEAF, 1 GLUE strict; 28 LEAF, 1 GLUE lenient)

Each row is a field of C4''''''' (its name is in the 'last task' column; leaf-fold9 to leaf-fold13 keep leaf-fold8's
fields) and the hypothesis of a compiled theorem in the task's file. Its form is the kind in the integrator's
`kinds.tsv`, which keeps leaf-fold8's; where this report's reading differs the pointer says so. Theorem numbers are
the reports' and UNVERIFIED unless a report read the source.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-98 | `AVGlue.CartierSmooth` | `scratch/av-glue/Combined.lean` L297 @ main | H-73, H-74 | **LEAF**; a group scheme locally of finite type over a field of characteristic 0 is smooth | av-glue; field `cartierSmooth` of leaf-fold13; cloud W16: briefed, not yet claimed on the issue (claims.tsv) | published form: Cartier's theorem; Mumford AV §11 Thm 1; Stacks 047N (av-glue §5) |
| H-99 | `AVGlue.GeomConnOfRationalPoint` | `scratch/av-glue/Combined.lean` L902 @ main | H-74 | **LEAF**; a connected scheme of finite type over `k` with a rational point is geometrically connected | av-glue; field `geomConnOfRationalPoint` of leaf-fold13; cloud W16: briefed, not yet claimed on the issue (claims.tsv) | published form: Stacks 04KV, specialized to finite type with a rational point (av-glue §5) |
| H-100 | `AVGlue.GroupSchemeEquidim` | `scratch/av-glue/Combined.lean` L913 @ main | H-74 | **LEAF**; the irreducible components of a group scheme of finite type over a field have its dimension | av-glue; field `groupSchemeEquidim` of leaf-fold13; cloud W16: briefed, not yet claimed on the issue (claims.tsv) | published form: Stacks, group schemes over a field; SGA 3 VI_A 2.4, finite type (av-glue §5) |
| H-101 | `AvSplit.T4.MulEtaleAbelianScheme` | `scratch/av-split/AvSplitAll.lean` L1835 @ main | H-24 | **LEAF**; `[m]` on an abelian scheme over `Spec O` is étale if `m ∈ O×` | av-split; field `mulEtaleAbelianScheme` of leaf-fold13; cloud W16: briefed, not yet claimed on the issue (claims.tsv) | published form: BLR §7.3 Lemma 2; Mumford GIT §6 (av-split §1) |
| H-102 | `AvSplit.MumfordTorsionAlgClosed` | `scratch/av-split/AvSplitAll.lean` L1411 @ main | H-25, H-38 | **LEAF**; over `k = k̄`, `A(k)[n] ≅ (ℤ/n)^{2g}` for `char k ∤ n` | av-split; field `mumfordTorsionAlgClosed` of leaf-fold13; cloud W16: briefed, not yet claimed on the issue (claims.tsv) | published form: Mumford AV §6 Application 2 (iv) (the integrator's correction of av-split's §4; UNVERIFIED) |
| H-103 | `BPAnalytic.Uniformization.UniformizationLeafAll` | `ZInQKernel/HDecomp/Analytic/Uniformization.lean` L91 @ main | H-38, H-69 | **LEAF**; the kernel's AN3 leaf: `A^an` in coordinate form | av-split; field `uniformizationLeafAll` of leaf-fold13; cloud W17: briefed behind a feasibility check (claims.tsv) | published form: Mumford §1 in coordinate form (bp-analytic §4; av-split §1 shares the judgement) |
| H-104 | `AvSplit.MilneIsogenyQuasiInverse` | `scratch/av-split/AvSplitAll.lean` L1361 @ main | H-54 | **LEAF**; `fg = [d]`, `gf = [d]` as morphisms for some `d ≥ 1` | av-split; field `milneIsogenyQuasiInverse` of leaf-fold13; cloud W17: briefed (CharZero form), after the two above (claims.tsv) | published form: Milne 1986 Rem. 8.4; Mumford §7 (av-split §1) |
| H-105 | `ZInQ.HomLattice.GAGAMorphism` | `scratch/av-split/AvSplitAll.lean` L1029 @ main | H-69 | **LEAF**; GAGA for homomorphisms of complex abelian varieties | av-split; field `gagaMorphism` of leaf-fold13; cloud W17: briefed behind a feasibility check (claims.tsv) | published form: Serre, GAGA, in the form of homlattice §3.2 (av-split §1) |
| H-109 | `ZInQ.HeightSplit.JavanpeykarBound` | `scratch/height-split/HeightSplit.lean` L508 @ main | H-14 | **LEAF**; Javanpeykar's bound over the published stable height | height-split; field `javanpeykarBound` of leaf-fold13 | published form: specialization of Javanpeykar 2014 Thm 1.1.1 to `K` with a `K`-rational Belyi function (height-split §4; leaf-fold8 §2; height-split §7 notes that a stricter reader may call it a consequence) |
| H-110 | `ZInQ.HeightSplit.GaudronRemondThm14` | `scratch/height-split/HeightSplit.lean` L773 @ main | H-15 | **LEAF**; Gaudron–Rémond's bound over the published stable height | height-split; field `gaudronRemondThm14` of leaf-fold13 | published form: Gaudron–Rémond 2014 Thm 1.4 (height-split table) |
| H-112 | `ZInQ.HeightSplit.BostLowerBound` | `scratch/height-split/HeightSplit.lean` L429 @ main | H-17 | **LEAF**; `h_D ≥ −(g/2) log 2π` (Deligne's normalization) | height-split; field `bostLowerBound` of leaf-fold13 | published form: Bost, Sém. Bourbaki 795 (display unread; height-split §2) |
| H-113 | `ZInQ.HeightSplit.PazukiCor13Upper` | `scratch/height-split/HeightSplit.lean` L717 @ main | H-18 | **LEAF**; the upper side of Pazuki's comparison of theta and Faltings heights | height-split; field `pazukiCor13Upper` of leaf-fold13 | published form: Pazuki 2012 Cor. 1.3(2), read off the same display (height-split §3) |
| H-117 | `ZInQ.RLeaf.IgusaGL2` | `ZInQKernel/Contrib/RLeaf/IgusaSL2.lean` L120 @ main | H-41 | **LEAF**; Igusa's theorem: `GL₂(ℤ/N)` is the Galois image on `E_j[N]` | curve-split; field `igusaGL2` of leaf-fold13; cloud W14: briefed (via X0Transitive), not yet claimed on the issue (claims.tsv) | published form: Igusa 1959; Shimura 1971 Thm 6.6 (curve-split §3.1) |
| H-118 | `CurveSplit.RegularSmoothPerfect` | `scratch/curve-split/CurvesGSplit.lean` L81 @ main | H-81 | **LEAF**; a finite type algebra over a perfect field is smooth at a prime with regular local ring | curve-split; field `regularSmoothPerfect` of leaf-fold13; cloud W15: briefed, not yet claimed on the issue (claims.tsv) | published form: Stacks 00TV, the ⇐ half (curve-split §3.3) |
| H-119 | `CurveSplit.ShimuraGoodReductionNoGuard` | `scratch/curve-split/ShimuraGR.lean` L162 @ main | H-83 | GLUE (composite); `ShimuraGoodReduction` without its guard clause | curve-split; field `shimuraGoodReductionNoGuard` of leaf-fold13; cloud W13: briefed, not yet claimed on the issue (claims.tsv) | composite: Morita, Carayol, Kottwitz, Buzzard; not statable in published form today (curve-split §3.6) |
| H-120 | `ZInQ.Contrib.HodgeSplit.TateTwistInvariants` | `scratch/hodge-split/HodgeSplit.lean` L65 @ main | H-8, H-51, H-52 | **LEAF**; `ℂ_p(i)^{G_K} = 0` for `i ≠ 0` | hodge-split; field `tateTwistInvariants` of leaf-fold13; cloud W11: briefed, not yet claimed on the issue (claims.tsv) | published form: Tate 1967 §3.3 Thm 2 (hodge-split §1) |
| H-121 | `ZInQ.Contrib.HodgeSplit.AxSenTate` | `scratch/hodge-split/HodgeSplit.lean` L75 @ main | H-8, H-51, H-52 | **LEAF**; `ℂ_p^{G_K} ⊆ K` | hodge-split; field `axSenTate` of leaf-fold13; cloud W11: briefed, not yet claimed on the issue (claims.tsv) | published form: Tate 1967 §3.3 Thm 1; Sen 1969; Ax 1970 (hodge-split §1) |
| H-122 | `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` | `scratch/hodge-split/HodgeSplit.lean` L343 @ main | H-8 | **LEAF**; the Hodge–Tate decomposition of `ℂ_p ⊗ V_p(A)` | hodge-split; field `hodgeTateDecompAbVar` of leaf-fold13 | published form: Fontaine 1982; Faltings 1988 (hodge-split §1) |
| H-123 | `ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` | `scratch/hodge-split/HodgeSplit.lean` L1988 @ main | H-8 | **LEAF**; `Hom(V_p A, ℚ_p)` is de Rham | hodge-split; field `deRhamH1AbVarT` of leaf-fold13 | published form: Faltings 1989; Tsuji 1999; Scholze 2013 Cor. 1.8, Hom form (hodge-split §1) |
| H-124 | `ZInQ.Contrib.HodgeSplit.BdRInvariants` | `scratch/hodge-split/HodgeSplit.lean` L3611 @ main | H-32 | **LEAF**; `B_dR^{G_{ℚ_p}} = ℚ_p` | hodge-split; field `bdRInvariants` of leaf-fold13 | published form: Fontaine, Astérisque 223 Exp. II; Brinon–Conrad §4 (hodge-split §1) |
| H-125 | `ZInQ.Contrib.HodgeSplit.DSThm965` | `scratch/hodge-split/HodgeSplit.lean` L1106 @ main | H-10, H-22 | **LEAF**; `k ≥ 2`: the Galois representation of an eigenform and its Frobenius polynomials | hodge-split; field `dsThm965` of leaf-fold13 | published form: Diamond–Shurman Thm 9.6.5 (Deligne 1971; Shimura 1971 Thm 7.14) (hodge-split §1) |
| H-126 | `ZInQ.Contrib.HodgeSplit.DSThm966` | `scratch/hodge-split/HodgeSplit.lean` L1124 @ main | H-10, H-22 | **LEAF**; `k = 1`: the Artin representation of an eigenform | hodge-split; field `dsThm966` of leaf-fold13 | published form: Deligne–Serre 1974 Thm 4.1; Diamond–Shurman Thm 9.6.6 (hodge-split §1) |
| H-128 | `HDec.QMSplit.Yu.YuThm11` | `scratch/qm-split/YuLeaf.lean` L34 @ main | H-35 | **LEAF**; Yu's dichotomy for QM abelian surfaces, with the splitting clause | qm-split; field `yuThm11` of leaf-fold13 | published form: Yu 2013 Thm 1.1, case labels dropped (qm-split §1) |
| H-129 | `HDec.QMSplit.Aut.QMCentralizerCMC` | `scratch/qm-split/QMAut.lean` L1018 @ main | H-42, H-61, H-63 | **LEAF**; over `ℂ`, `End_𝒪(A)` is `ℤ` or an optimally embedded `Φ⁻¹(𝒪)` | qm-split; field `qmCentralizerCMC` of leaf-fold13 | published form: Shimura 1967 §§1-3; Jordan 1981 §3; González–Rotger 2006 §5 (qm-split §1) |
| H-130 | `HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar` | `scratch/qm-split/STQM.lean` L66 @ main | H-86 | **LEAF**; a surface over `ℂ` with a degree-4 field in `End⁰` has a model over `ℚ̄` | qm-split; field `shimuraTaniyamaQbar` of leaf-fold13 | published form: Milne, CM notes §7; Shimura–Taniyama 1961 §12.4 print a number-field model (qm-split §4) |
| H-131 | `HDec.QMSplit.Theta.IgusaPsi4` | `scratch/qm-split/ThetaSplit.lean` L42 @ main | H-2 | **LEAF**; `2⁻²Σθ⁸` is Siegel modular of weight 4 | qm-split; field `igusaPsi4` of leaf-fold13 | published form: Igusa 1962-1967 (leaf-fold7's form; qm-split §4 flags that Igusa prints it as an identity of Eisenstein series) |
| H-132 | `HDec.QMSplit.Theta.IgusaChi10` | `scratch/qm-split/ThetaSplit.lean` L52 @ main | H-2 | **LEAF**; `−2⁻¹⁴∏θ²` is Siegel modular of weight 10 | qm-split; field `igusaChi10` of leaf-fold13 | published form: Igusa 1962-1967, as for `IgusaPsi4` (leaf-fold7's form; flag of qm-split §4) |
| H-135 | `HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq` | `scratch/qm-split/Haupt.lean` L2244 @ main | H-87, H-88 | **LEAF**; the valence formula for cocompact Fuchsian groups | qm-split; field `valenceFormulaCocompactEq` of leaf-fold13 | published form: Shimura 1971 Prop. 2.16, Thm 2.20; Rankin Thm 4.1.4 (qm-split §1) |
| H-136 | `HDec.LeafQCheck.HM.QMSplit.ShimizuCovolumeO1` | `scratch/qm-split/Haupt.lean` L3205 @ main | H-87, H-88 | **LEAF**; `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` | qm-split; field `shimizuCovolumeO1` of leaf-fold13 | published form: Shimura 1971 Prop. 9.2; Shimizu 1965 (qm-split §1) |

### 4.7 Props open only in scenario F, introduced in r4 (9: 1 LEAF, 8 GLUE strict; 3 LEAF, 6 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4'''''''. Its form is the task
report's label, or my reading where the report's own text (docstring or review) names more than one source; the
pointer says which.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-89 | `MCRGlue.ProperCurveAF` | `scratch/mcr-glue/MCRGlue.lean` L4044 @ main | H-84 | GLUE (composite); L1: finite sets of points of a proper smooth curve over `ℤ_(p)` lie in an affine open | mcr-glue; in flight: a fleet task (`quotientP1Coordinate`) | composite: Lichtenbaum 1968 Thm 2.8 with EGA II 4.5.4 (mcr-glue §3: composite of two results) |
| H-90 | `MCRGlue.FiniteQuotientExists` | `scratch/mcr-glue/MCRGlue.lean` L4057 @ main | H-84 | **LEAF**; L2: the quotient by a finite group of `ℤ_(p)`-automorphisms exists and is finite | mcr-glue; being attempted (cloud); in flight: a fleet task (`quotientP1Coordinate`) | published form: SGA 1 Exp. V Prop. 1.8 and 1.1, special case (mcr-glue §3) |
| H-91 | `MCRGlue.TameQuotientSmooth` | `scratch/mcr-glue/MCRGlue.lean` L4072 @ main | H-84 | GLUE (composite); L3: a tame quotient of a proper smooth relative curve is proper and smooth | mcr-glue; in flight: a fleet task (`quotientP1Coordinate`) | composite: SGA 1 Exp. V, Mumford AV §7 Thm 3, EGA IV 17.5.1 (mcr-glue §3: composite of three results) |
| H-92 | `MCRGlue.SmoothModelOfP1` | `scratch/mcr-glue/MCRGlue.lean` L4086 @ main | H-84 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); L4: a proper smooth `ℤ_(p)`-curve with generic fibre `P¹_ℚ` is `P¹_{ℤ_(p)}` | mcr-glue; in flight: a fleet task (`quotientP1Coordinate`) | consequence of one theorem: Liu, AGAC §8.3, §10.1 (mcr-glue §3: STANDARD; reading) |
| H-93 | `MCRGlue.TameFixedPointsDisjoint` | `scratch/mcr-glue/MCRGlue.lean` L4100 @ main | H-84 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); L5: fixed points of a tame automorphism with distinct underlying points have disjoint closures | mcr-glue; in flight: a fleet task (`quotientP1Coordinate`) | consequence of one theorem: Edixhoven 1992 Prop. 3.4 with finite étale over a DVR (mcr-glue §3: leaf consequence) |
| H-94 | `MCRGlue.TameInertiaCyclic` | `scratch/mcr-glue/MCRGlue.lean` L4119 @ main | H-84 | GLUE (composite); L6: a finite tame inertia group as in L5 is cyclic | mcr-glue; in flight: a fleet task (`quotientP1Coordinate`) | composite: Serre, Local Fields IV §2 Cor. 1 of Prop. 7, with L5's source (mcr-glue §3: composite of two results) |
| H-95 | `HDec.PropTSRed.CoverModelOfHeckeN` | `ZInQKernel/OneProof/H/TailG.lean` L743 @ main | H-84 | GLUE (project glue); the decomposition's own glue: a model of the Hecke cover of level `N` (gives `ModelYIrreducible` with T5) | mcr-quot; in flight: a fleet task (`quotientP1Coordinate`) | project glue: open here: the chain derives it only through `HeckeNoVertRam`, downstream of the coordinate that mcr-quot feeds (mcr-quot §1); gap-triage (finding 3, compiled probe): not needed, since `ModelYIrreducible` is the chain's `HeckeIrreducible`, which follows from the field `deligneComponentsY3PrintedAb` (`scratch/gap-triage/GlueProbe.lean`, `MCRQuotNV.lean`); not applied, as the probe takes leaf-fold9's whole bundle `OpenAddedLeaves9` |
| H-96 | `MCRQuot.P1SchemeQ` | `scratch/mcr-quot/MCRQuot.lean` L8549 @ main | H-84 | GLUE (project glue); `P¹_ℚ` exists, is proper and smooth, and represents maps to `P¹` by charts | mcr-quot; in flight: a fleet task (`quotientP1Coordinate`) | project glue: foundations: `Proj ℚ[X₀, X₁]` with its functor of points, not in Mathlib (mcr-quot §1) |
| H-97 | `MCRQuot.CMStabObj` | `scratch/mcr-quot/MCRQuot.lean` L7648 @ main | H-84 | GLUE (project glue); each CM class is fixed by a Hecke operation of order exactly 2 on classes (QM objects over `ℚ̄`) | mcr-quot; in flight: a fleet task (`quotientP1Coordinate`) | project glue: object-level glue on CM points, no schemes (mcr-quot §1) |

### 4.8 Fields of leaf-fold9 introduced in r5 (1: 1 LEAF, 0 GLUE strict; 1 LEAF, 0 GLUE lenient)

The row left is a field of C4''''''' that leaf-fold9 introduced, and the hypothesis of a compiled theorem in
reduct-split's `Reduction.lean` (`TailZ7`, verbatim); it is used in both scenarios since leaf-fold10 (r5: only in
scenario F). r5's other three rows here are gone: H-145 is restated on abelian schemes (route-a-fold), and H-146 and
H-147 are fields that scenario F replaces by their strictly henselian forms (§4.1). Form: kinds.tsv's, which the
integrator kept after the base review.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-148 | `ReductSplit.NeronSchemeModelExistsDVR` | `ZInQKernel/OneProof/H/TailZ7.lean` L238 @ main | H-4, H-106, H-108 | **LEAF**; Néron's existence theorem over a discrete valuation ring, scheme form | reduct-split; field `neronSchemeModelExistsDVR` of leaf-fold13 | published form: BLR §1.4 Thm 3 with §1.2 Def. 1 (reduct-split §2); kept a published form by the integrator after the base review (printed over an arbitrary DVR, reduct-glue §4; UNVERIFIED) |

### 4.9 Props open only in scenario F, introduced in r5 (2: 0 LEAF, 2 GLUE strict; 2 LEAF, 0 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4'''''''. Its form is the task
report's label, or my reading where the report's own text names more than one source or gives no label; the pointer
says which. Its H-150 is a field since leaf-fold13 and moved to §4.12.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-154 | `HDec.QMSplit.Moduli.ShimuraHolFamily` | `scratch/shimura-split/ShimuraFam.lean` L258 @ main | H-139 (from H-20) | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); one holomorphic family `φ : ℍ → Y₃(ℂ)` with the moduli clause; the step to every `π : Y₃ → P¹` is proved | shimura-split | consequence of one theorem: Shimura 1967 Main Thm I, through Deligne 1971 §4 for the `ℚ`-model (shimura-split §3.4 and its review §7); carries `R1fpProps`; with the field `mumfordRigidityCore` (H-170) a leaf on `R1fpProps` is equivalent to the same leaf on abelian schemes (r1univ-rigid's `…_iff_ab`), so r5's open check on this row rests on that one leaf; shimura-cft derives `shimuraFamilyAb` from Shimura's Main Theorem I in Deligne's adelic form (`ShimuraMainThmIDeligneY3Ab`, a consequence by its report and a composite by its review), which implies this row's leaf (`mainThmIY3_of_mainThmI` with c-to-printed's `shimuraHolFamily_of_mainThmI`), so scenario F keeps this one |
| H-157 | `ModularSplit.R17.CarayolRealization` | `scratch/modular-split/R17.lean` L127 @ main | H-21 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); some semisimple `ρ` attached to the newform has conductor exponent `v_p(N)` at every `p ≠ ℓ`; the transport to every attached `ρ` is proved | modular-split | consequence of one theorem: Carayol 1986 Thm (A) at his realization (audit), with Casselman's `a(π_p) = v_p(N)` and Ribet's irreducibility (modular-split §2: still a consequence) |

### 4.10 Fields of leaf-fold10 and leaf-fold11 introduced in r6 (9: 5 LEAF, 4 GLUE strict; 7 LEAF, 2 GLUE lenient)

Each row is a field of C4''''''' that leaf-fold10 or leaf-fold11 introduced, and the hypothesis of a compiled theorem
in its file (`TailZ16`, `TailZ17`: route-a-fold; `TailZ19`: c-to-printed's printed leaves). Forms: kinds.tsv's, with
the integrator's convention for `gonzalezRotgerCountX6Ab` and `deligneComponentsY3PrintedAb` (r7: GLUE after
shimura-cft's review). leaf-fold10's other new fields are not rows: `neronLocalizesDVR` is proved since leaf-fold11,
and scenario F replaces the four DVR fields.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-168 | `ShimuraSplit.GonzalezRotgerCountX6Ab` | `ZInQKernel/OneProof/H/TailZ17.lean` L31 @ main | H-145 | GLUE (composite); `GonzalezRotgerCountX6` restated on abelian schemes (`R1fpPropsAb`, the printed fine-moduli problem): some witness has exactly `2^{inertCount6 k}·#Pic(R)` points with CM by `R` | route-a-fold; field `gonzalezRotgerCountX6Ab` of leaf-fold13 | composite: González–Rotger 2006 Prop. 5.6 at `(D, N) = (6, 1)` (audit read it) together with the canonical models it is stated on (Shimura 1967, Deligne 1971), so a composite by the integrator's ruling (kinds.tsv: published kind, LEAF in its strict column, GLUE in its strictest); open check: `inertCount6 k` is González–Rotger's `b(k)` |
| H-169 | `ShimuraGlue.DeligneComponentsY3PrintedAb` | `ZInQKernel/OneProof/H/TailZ17.lean` L54 @ main | H-155 (from H-59) | GLUE (composite); Deligne's theorem on the connected components of `Sh_K` in printed form, for `G = B^×`, `B = (2, −3 \| ℚ)`, at level `K₃`, over Mathlib's finite adeles, quaternion algebra and cyclotomic character, on abelian schemes (leaf-fold10 folds shimura-glue's printed leaf; route-a-fold restates it) | route-a-fold; field `deligneComponentsY3PrintedAb` of leaf-fold13 | composite: Deligne, Sém. Bourbaki 389 (1971) Thm 2.4 and §3; PSPM 33 (1979) 2.1.3, 2.6.3; Milne 2005 Thms 5.17, 13.6 (shimura-glue §2, §4; locators UNVERIFIED), specialized to one witness; GLUE by the integrator's ruling after shimura-cft's review (kinds.tsv, 11-14): it depends on whether one display states that the PEL moduli scheme with its uniformization is the canonical model at `B = (2, −3 \| ℚ)`, level `K₃` (Deligne 389 §5, Milne 2005 §14), and is otherwise Deligne's theorem with that identification |
| H-170 | `LeafQM.AV.R1UnivRigid.MumfordRigidityCore` | `ZInQKernel/OneProof/H/TailZ16.lean` L463 @ main | none (closes r5's open check on the rows stated on `R1fpProps`) | **LEAF**; a smooth proper geometrically connected family with a section whose field fibres are abelian varieties carries a group law with that identity, and maps that fix the identity are homomorphisms | route-a-fold; field `mumfordRigidityCore` of leaf-fold13 | published form: Mumford, GIT Thm 6.14 with Cor. 6.4 (r1univ-rigid §5.2; numbers UNVERIFIED); counted LEAF by leaf-fold11 and the integrator; r1univ-rigid calls it a consequence of printed statements |
| H-171 | `CToPrinted.BLR_1_2_4` | `ZInQKernel/OneProof/H/TailZ19.lean` L63 @ main | H-163 (through `neronLocalizesDVR`) | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); BLR §1.2 Prop. 4, the full "iff": over a Dedekind domain, a smooth separated scheme of finite type is a Néron model iff it is one over every local ring | c-to-printed; field `blr_1_2_4` of leaf-fold13; in flight: sh-printed2 (`blr_1_2_4`) | consequence of one theorem: BLR, Néron models, §1.2 Prop. 4 (c-to-printed §2; UNVERIFIED); a consequence by the integrator's convention: it may be printed with strict henselizations, a plausible weaker reading |
| H-172 | `CToPrinted.FaltingsLemma5Printed` | `ZInQKernel/OneProof/H/TailZ19.lean` L387 @ main | H-167 (through `faltingsLemma5BC`) | **LEAF**; Faltings' Lemma 5, the identity with the correction term `[K:ℚ]⁻¹ log #s*Ω¹_{G/S}` | c-to-printed; field `faltingsLemma5Printed` of leaf-fold13 | published form: Faltings, Invent. Math. 73 (1983) Lemma 5 (c-to-printed §3; not read, so LEAF and flagged) |
| H-173 | `CToPrinted.RaynaudKernelBound` | `ZInQKernel/OneProof/H/TailZ19.lean` L399 @ main | H-167 (through `faltingsLemma5BC`) | **LEAF**; Raynaud's bound on the kernel term of an isogeny of semistable abelian varieties | c-to-printed; field `raynaudKernelBound` of leaf-fold13 | published form: Raynaud, Astérisque 127 (1985) VII 2.1.3 (c-to-printed §3; number unconfirmed, flagged) |
| H-174 | `CToPrinted.SGA3_VIB_3_10` | `ZInQKernel/OneProof/H/TailZ19.lean` L199 @ main | H-166 (through `semistableNeronBaseChange`) | **LEAF**; for a smooth group scheme over a base, the union of the identity components of the fibres is open | c-to-printed; field `sga3_VIB_3_10` of leaf-fold13 | published form: SGA 3 I Exp. VI_B Thm 3.10 (c-to-printed §4; number unconfirmed, flagged) |
| H-175 | `CToPrinted.SGA7_IX_3_3` | `ZInQKernel/OneProof/H/TailZ19.lean` L249 @ main | H-165 (through `semistableNeronBaseChange`) | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); SGA 7 IX 3.3, second assertion: for semistable reduction the identity component of the Néron model base changes, `N⁰ ⊗ R' ≅ N'⁰` | c-to-printed; field `sga7_IX_3_3` of leaf-fold13; in flight: sh-printed2 (`sga7_IX_3_3`) | consequence of one theorem: SGA 7 I Exp. IX 3.3 (c-to-printed §4; UNVERIFIED); a consequence by the integrator's convention, as the SGA 7 IX DVR fields (the base ring may be printed strictly henselian) |
| H-176 | `CToPrinted.EGAIV_8_10_5_openImm` | `ZInQKernel/OneProof/H/TailZ19.lean` L281 @ main | H-166 (through `semistableNeronBaseChange`) | **LEAF**; open immersions spread out: a morphism of finite presentation that is an open immersion over the generic points of a limit is one over some stage | c-to-printed; field `egaIV_8_10_5_openImm` of leaf-fold13 | published form: EGA IV₃ 8.10.5, the open-immersion item (c-to-printed §4; UNVERIFIED) |

### 4.11 Props open only in scenario F, introduced in r6 (6: 1 LEAF, 5 GLUE strict; 5 LEAF, 1 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4''''''' (§4.1). Its form is the
task report's label, or my reading where the report gives none or names more than one source (the pointer says
"reading"). The two strictly henselian rows left follow the base review's first version ("review v1, v2 pending").
r6's branch heads are merged (w66), so the rows point at main; r6's rows for x6-glue's leaves are replaced by fields
(§4.12).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-181 | `CToPrinted2.KatoRealizationCohSS` | `scratch/c-to-printed2/CToPrinted2.lean` L618 @ main | H-158 (from H-127) | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); some semisimple `ρ` attached to the newform, with Kato's Hodge–Tate weights; with the fields `tateTwistInvariants` and `axSenTate` it gives `eigenformHTNew`, and is equivalent to it over the bundle | c-to-printed2 | consequence of one theorem: Kato, Astérisque 295 (2004) §8.3 and §§9.2-9.4 at his `V_{F_λ}(f)`, quantified existentially (c-to-printed2 §2.1; locators read by locators.md row R13): the report's label, a consequence |
| H-182 | `ReductGlue.RaynaudSemistableSH` | `ZInQKernel/OneProof/H/TailZ14.lean` L1099 @ main | H-160 | **LEAF**; Raynaud's criterion over a strictly henselian DVR; the general-DVR field follows with the strict henselization and the field `mulEtaleAbelianScheme` | reduct-glue | published form: SGA 7 I Exp. IX Prop. 4.7 over a strictly henselian DVR (reduct-glue §4; locator UNVERIFIED); review v1, v2 pending |
| H-185 | `ReductGlue.SemistablePersistsSH` | `ZInQKernel/OneProof/H/TailZ14.lean` L1117 @ main | H-162 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); SGA 7 IX 3.3, first assertion (semistable reduction persists in finite extensions), strictly henselian | reduct-glue | consequence of one theorem: SGA 7 I Exp. IX 3.3, first assertion, over a strictly henselian DVR; depends on the reading (review v1); review v1, v2 pending |
| H-187 | `ReductGlue.StrictHenselizationPair` | `ZInQKernel/OneProof/H/TailZ14.lean` L2021 @ main | H-162 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); the same for `O ⊆ O'` over a finite `K'/K`: strict henselizations `P ⊆ P'` with `[E' : E]` finite | reduct-glue | consequence of one theorem: EGA IV 18.8.10 and 18.6.8, Stacks 05WR, BLR §1.2 Prop. 2 (reduct-glue §2; UNVERIFIED); review v1 reads it as a consequence; sh-route proves its characteristic-0 form (`[CharZero K]` and a perfect residue field added) from the one Néron leaf `NeronBaseChangeSH`, not applied: the fields' consumers take the general form |
| H-188 | `ReductGlue.StrictHenselizationInside` | `ZInQKernel/OneProof/H/TailZ14.lean` L2103 @ main | H-147 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); inside an algebraic closure at a place `w`: the inertia field, on which `w` is a strict henselization of `O` | reduct-glue | consequence of one theorem: Stacks 0BSK-0BSL; Raynaud, Anneaux locaux henséliens, VIII; BLR §1.2 Prop. 2 (reduct-glue §2; UNVERIFIED); review v1 reads it as a consequence; sh-route proves its characteristic-0 form from `NeronBaseChangeSH`, not applied (as H-187) |
| H-190 | `HDec.HSyn.G0Split.ThetaPt.ThetaGlue.LinYangThetaCurve` | `scratch/theta-glue/ThetaGlue.lean` L593 @ main | H-133, H-134 (from H-44) | GLUE (composite); along the explicit QM curve `τ ↦ Ω(τ)`: `ψ₄ψ₆ = 2¹²3⁵χ₁₀` and `ψ₄³ + ψ₆² = 2¹²3⁶χ₁₂` in Igusa's theta expressions | theta-glue; in flight: linyang-printed (`LinYangThetaCurve`) | composite: Lin–Yang, Math. Z. 295 (2020), Example 29 with eqs. (13)-(14), after eliminating `j` (so weaker than the print), with Igusa's theta expressions (Amer. J. Math. 89 (1967) §4); locators UNVERIFIED; numerically VERIFIED (80 digits at 12 points); theta-glue's label: a composite; igusa-alg proves `IgusaAlg 5` to `9`, so the route rests on this leaf alone (`qmThetaSymmetricCurve_of_linYang`) |

### 4.12 Fields of leaf-fold13 introduced in r7 (6: 4 LEAF, 2 GLUE strict; 5 LEAF, 1 GLUE lenient)

Each row is a field of C4''''''' that leaf-fold13 introduced (x6-fold), and the hypothesis of a compiled theorem in
`TailZ20`-`TailZ22`. Five restate x6-glue's leaves on abelian schemes (r6's rows H-142, H-177, H-178, H-179, H-180);
H-150 keeps its row from r5 (until r6 open only in scenario F). Forms: kinds.tsv's, with the integrator's convention
for `elkiesEquationsX6Ab`.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-150 | `HDec.QMSplit.Moduli.GeomConnOfAlgClosure` | `ZInQKernel/OneProof/H/TailZ20.lean` L1842 @ main | H-140 (from H-1) | **LEAF**; a proper `X → Spec k` with `X ×_k k̄` connected is geometrically connected | shimura-split; field `geomConnOfAlgClosure` of leaf-fold13 | published form: EGA IV₂ 4.5.1-4.5.2; Stacks 0389, weakened by `IsProper` and characteristic 0 (shimura-split §2, §3.2) |
| H-192 | `ShimuraGlue.DeligneComponentsX6PrintedAb` | `ZInQKernel/OneProof/H/TailZ22.lean` L33 @ main | H-177 | **LEAF**; Deligne's theorem on `π₀` in printed form at level `𝒪̂^×`, on one coarse witness `X₆`, on abelian schemes; with `ℚ^×_{>0}\𝔸_f^×/nrd(𝒪̂^×) = 1` (compiled) it gives `DeligneComponentsX6` | x6-fold; field `deligneComponentsX6PrintedAb` of leaf-fold13 | published form: Deligne, Sém. Bourbaki 389 (1971) Thm 2.4 and §3; PSPM 33 (1979) 2.1.3, 2.6.3 (shimura-glue §2, x6-glue §2; UNVERIFIED), at level `𝒪̂^×`; x6-fold restates it on abelian schemes (`R1fpPropsAb`, the printed fine-moduli problem; `deligneComponentsX6Printed_iff_ab` with the field `mumfordRigidityCore`, H-170) |
| H-193 | `HDec.QMSplit.Moduli.BabaGranathRationalAb` | `ZInQKernel/OneProof/H/TailZ22.lean` L91 @ main | H-178 | **LEAF**; Baba–Granath's fibre clause on abelian schemes: three distinct rational points that are exactly the images of `CM(−4)`, `CM(−3)`, `CM(−24)`; no `j`-normalization (the Möbius glue is proved) | x6-fold; field `babaGranathRationalAb` of leaf-fold13 | published form: Baba–Granath 2008 Thm 2.1 and Lemma 3.1 (audit YES), with the CM assignment read from their §3.1 table, an UNVERIFIED reading (kinds.tsv flags it; shimura-glue §5.3, x6-glue §4); x6-fold restates it on abelian schemes (`R1fpPropsAb`, the printed fine-moduli problem; `babaGranathRational_iff_ab` with the field `mumfordRigidityCore`, H-170) |
| H-194 | `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` | `ZInQKernel/OneProof/H/TailZ22.lean` L64 @ main | H-142 | **LEAF**; some coarse witness, on abelian schemes, has the residue fields of CM points (`R5ptProps`) | x6-fold; field `gonzalezRotgerX6Ab` of leaf-fold13 | published form: González–Rotger 2006 Thm 5.12 (qm-glue §4.2; UNVERIFIED); x6-fold restates it on abelian schemes (`R1fpPropsAb`, the printed fine-moduli problem; `gonzalezRotgerX6_iff_ab` with the field `mumfordRigidityCore`, H-170) |
| H-195 | `HDec.QMSplit.Moduli.ElkiesEquationsX6Ab` | `ZInQKernel/OneProof/H/TailZ22.lean` L72 @ main | H-180 | GLUE (composite); Elkies' model of `X₆` as a statement about the scheme, on abelian schemes: over `t ≠ ∞` the affine curve `s² = −t`, `r² = 3(t − 1)`, over `t ≠ 0` the same chart in `1/s`, `r/s`, `1/t`, glued on the overlap; with the fibre clause of `t` | x6-fold; field `elkiesEquationsX6Ab` of leaf-fold13 | composite: Elkies, ANTS-III (1998) §3 (x6-glue §3-§4; UNVERIFIED); a composite by the integrator's strict convention (kinds.tsv): its fibre clause reads Elkies' "`t` is a coordinate on `X₆/W`" with the moduli meaning of `W` (x6-glue §5.2); x6-fold counts it published; x6-fold restates it on abelian schemes (`R1fpPropsAb`, the printed fine-moduli problem; `elkiesEquationsX6_iff_ab` with the field `mumfordRigidityCore`, H-170) |
| H-196 | `ShimuraGlue.Ray.RayClassCMAb` | `ZInQKernel/OneProof/H/TailZ22.lean` L48 @ main | H-179 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); on one fine witness, on abelian schemes, the residue field of a CM point by the maximal order of `ℚ(i)`, `ℚ(ζ₃)` or `ℚ(√−6)` embeds into Tau Ceti's ray class field of conductor 3 | x6-fold; field `rayClassCMAb` of leaf-fold13; in flight: rayclass-cft (`rayClassCMAb`) | consequence of one theorem: Shimura 1967 Main Thm I and Deligne 1971 §3, ray-class form (shimura-glue §5.1, x6-glue §5.1; locators UNVERIFIED); stronger than `ReciprocityCanonical`, weaker than the printed reciprocity law; x6-fold restates it on abelian schemes (`R1fpPropsAb`, the printed fine-moduli problem; `rayClassCM_iff_ab` with the field `mumfordRigidityCore`, H-170); gap-triage reads `R1recProps`, the clause it serves, as probably unread (finding 8, SPECULATIVE): if so, the field drops |

### 4.13 Props open only in scenario F, introduced in r7 (6: 3 LEAF, 3 GLUE strict; 5 LEAF, 1 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4''''''' (§4.1): unipotent-b's
printed SGA 7 IX 3.5 and its glue, and t09-pic's four leaves. Its form is the task report's label, or my reading where
the report gives none (the pointer says "reading").

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-197 | `UnipotentB.SemistableUnipotentPrintedGen` | `scratch/unipotent-b/UnipotentB.lean` L275 @ main | H-184 (from H-147) | **LEAF**; SGA 7 IX 3.5 as printed, over every field: `O` strictly henselian, `Ω = K^s`, semistability over `k(s)`, `ℓ` invertible in `O`; semistable iff inertia acts unipotently, and then `(σ - 1)(τ - 1) = 0` on `T_ℓ` | unipotent-b | published form: SGA 7 I Exp. IX Prop. 3.5 (unipotent-b §2; wording UNVERIFIED, no network): the printed strictly henselian base, so the base reading of the four DVR fields does not arise here |
| H-198 | `UnipotentB.SemiAbelianDescendsSepClosed` | `scratch/unipotent-b/UnipotentB.lean` L298 @ main | H-184 (from H-147) | GLUE (project glue); for a DVR with separably closed residue field `k`, a group model whose special fibre over `k̄` has semi-abelian identity component has one over `k` already | unipotent-b | project glue: unipotent-b's named glue (§3.3: maximal tori over `k`, SGA 3 XIV 1.1; properness descends, EGA IV₂ 2.7.1; UNVERIFIED); proved when `k` is perfect, so needed only for imperfect residue fields; not in Mathlib |
| H-199 | `T09Pic.PicRepresentableAbVar` | `scratch/t09-pic/Pic.lean` L307 @ main | H-53 | **LEAF**; the relative Picard fppf sheaf of an abelian variety is representable | t09-pic | published form: Murre (1964), Oort (1962); FGA Exp. 232 Thm 3.1; Kleiman, The Picard scheme, Thm 9.4.8 with Thm 9.2.5 (t09-pic §3; UNVERIFIED) |
| H-200 | `T09Pic.PicZeroAbVar` | `scratch/t09-pic/Pic.lean` L320 @ main | H-53 | **LEAF**; the identity component of the Picard scheme is an abelian variety, by an open immersion that is a homomorphism | t09-pic | published form: Mumford, Abelian Varieties §13; Kleiman Prop. 9.5.1 and 9.5.3; Milne 1986 §§9-10 (t09-pic §3; UNVERIFIED) |
| H-201 | `T09Pic.PhiAmpleIsogeny` | `scratch/t09-pic/Pic.lean` L384 @ main | H-53 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); for an ample `L`, the homomorphism `λ` with `λ ≫ ι = φ_L` is finite and surjective | t09-pic | consequence of one theorem: Mumford §6 Application 1 and §8 Thm 1, over an algebraically closed field (t09-pic §3; UNVERIFIED); my reading: a consequence, since the leaf is over any field `K` and needs descent from `K̄` (the report counts its four leaves published) |
| H-202 | `T09Pic.WeilPairingMumford` | `scratch/t09-pic/Pic.lean` L726 @ main | H-53 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); for `n` invertible in `K`, a perfect, `G_K`-equivariant, compatible pairing `A[n] × Pic⁰[n] → μ_n` with Mumford's values (`weilScalar`), adjoint for the genuine `f^∨`, with `e_n(x, λ_L x) = 1` for ample `L` | t09-pic | consequence of one theorem: Mumford §20 and §23; Milne 1986 Lemma 16.2(c) and §16 (t09-pic §3; UNVERIFIED): the report's label, a consequence of the print; it also compiles the split into one printed property per leaf (L4a-L4f, `t09SymmIsogenyExists_of_split`) |

### 4.14 Bundle fields never projected, and the prune (not on the list)

r7: none. x6-fold's scan (`scratch/x6-fold/PruneScan.lean`, genus-fold's scan) finds no unused field at w66, and
`chain.py`'s `UNUSED` is empty. gap-triage finds two fields used only syntactically, which a scan of projections
cannot see: `bdRInvariants` (passed on by `g8_g11`, `g8_g12`, whose only proofs ignore it) and `raynaudKernelBound`
(`faltingsLemma5_of_printed` needs only the half that `faltingsLemma5Printed` gives); its attack list ranks removing
both first (gap-triage §1, A1).

Until r6:
r6: none. The integrator's prune (0218a662, merged in w62) removed `r3 : ZInQ.LeafPush2.R03_LinYang`, `serreTateThm2`
and `t10 : T10Etale.T10_TateDuality` from every bundle generation: the three fields that its fixed Lean scan
(wip/prune-scan e3045e7d) found unused at w61 (the prune's diff only removes lines: 63, with one structure-literal
line rewrapped). genus-fold (w63) removed `genusX1Field` and `t34` the same way, with their dead readers, after
genus-route made them unnecessary (H-79). The other three of r5's never-projected fields (`semistableReductionDVR`,
`semistableUnipotent`, `neronSchemeModelExistsDVR`) are used since leaf-fold10, whose proofs of `r6`,
`semistableReductionThm` and `semistablePersists` take them. leaf-fold11's scan finds no unused field at w63, and
`chain.py`'s `UNUSED` is empty.

Until r5:
r5: `r3 : ZInQ.LeafPush2.R03_LinYang`, `t10 : T10Etale.T10_TateDuality` and reduct-split's four leaves
`serreTateThm2`, `semistableReductionDVR`, `semistableUnipotent`, `neronSchemeModelExistsDVR`. In OneProof/H the four
are used only in `TailZ9`'s `researchLeaves8_of_open9`, as arguments of `serreTatePotentialGood_final` and
`grothendieckMonodromy_final'`, which fill leaf-fold8's never-projected `r7b` and `r8`; in `TailZ5`-`TailZ9`, `r3` and
`t10` occur only as `r3 := r.r3` and `t10 := t.t10` (VERIFIED, grep at main), and below `TailZ5` as in r4. Scenario F
uses three of the four (§4.8; `chain.py F` recomputes the set). The integrator has approved removing all six after
leaf-fold10. `r1rec` and `r5` left the list of unused fields: leaf-fold9 proves them from `r1r2`.

Until r4 the six were `r1rec`, `r3`, `r5`, `r7b`, `r8` and `t10`:
`r1rec : LeafQM.AV.R1rec`, `r3 : ZInQ.LeafPush2.R03_LinYang`, `r5 : LeafQM.AV.R5fp`, `r7b : PkgI2.SerreTatePotentialGood`,
`r8 : PkgI2.GrothendieckMonodromy`, `t10 : T10Etale.T10_TateDuality`. VERIFIED (agent-h-leaves and my grep) for
g0-assemble3's flat file: they occur only in the structure literals that convert the bundles (and `t10` only in the
unused `HSyn.TextbookLeaves.t10_groupIso`); C4 converts its bundles to g0-assemble3's and uses the same consumers
(REPORTED by assemble-port's report; not re-grepped, its flat file has more conversions). assemble-port already deleted
the unused textbook fields T1, T3, T4 (as textbook fields), T16(b), T20, T21, T28, T29.
r2-r4: in leaf-fold4's and leaf-fold5's flat files `r1rec`, `r7b`, `r8` occur only as `f := r.f` in three structure literals, and `t10` only
there and in `T10_groupIso_of_tateDuality` (VERIFIED, grep of `Leaves4.lean` @ 9dcf1ca8 and `Leaves5.lean` @ 5a7e03d1); `r3` and `r5` were not
re-grepped (their names collide with local variables).
r4: leaf-fold8 keeps the six (`r1rec`, `r3`, `r5`, `r7b`, `r8` in `OpenResearchLeaves8`, `t10` in `OpenTextbookLeaves8`). In
OneProof/H they occur only as `f := r.f` or `f := t.f`, or a transport `_ofK5` of it, in the bundle conversions of
`TailD`, `TailE`, `TailI`, `TailK`, `TailN`, `TailO` and `TailX`, and `t10` in LPrefix's `T10_groupIso_of_tateDuality`
(VERIFIED, grep at main); leaf-fold7 and leaf-fold8 left the chain from LPrefix to TailO unchanged.

### 4.15 Statement reviews of the leaves (leaf-review-a, leaf-review-b, leafq-check, the r4 to r7 tasks)

leaf-review-a (groups A, A′, F: 21 fields) and leaf-review-b (groups B, C, D, E, G: 41 fields) read every leaf-fold3
field with the definitions it uses: 8 PUBLISHED-FORM (`t11b`, `serreRigidity3`, `r7a`, `t41`, `r9a`, `r9b`, `r19`, `t33`),
54 CONSEQUENCE, none STRONGER-THAN-SOURCE or NOT-A-PUBLISHED-STATEMENT; no statement repair proposed. Since r3 the
form column carries their verdicts: a CONSEQUENCE is a consequence of one theorem or a composite, with the review's
derivation named, and is GLUE in the strict count until that derivation is compiled. leafq-check (r3) checked
leaf-fold4's seven LEAF? fields: `GammaStarGen` proved, three replaced by smaller statements (H-86..H-88), and
`ThetaRatiosAlgebraic`, `X6ConicModel`, `Y3Connected` unchanged (true, each a consequence of published results, not
splittable in Lean today). Premises the reviews flag across rows: Lemma QP (its existence half may be glue), the
specialization of Deligne's PEL model to `R1fpProps` (an open human check, inherited by `r1r2`, `r1b`, `y3Connected`,
`x6ConicModel`), and the definition of `stableFaltingsHeight` (group D).

The r4 split tasks each checked their rows against the sources they could read, and none found a row false, vacuous
or stronger than its sources. height-split, mcr-glue and height-glue add an independent model review of their new
statements (no defect; height-glue's RISKs: `QMUniformizationC` bundles the algebraicity of QM tori, GAGA and the
unpolarized form with the published moduli statements, and `CMDescent` bundles the classification of endomorphism
algebras). tyz-split read TYZ's source and settled tyz-35's three HUMAN CHECK items; the `[i]` sign of the base point,
the one input it left unprinted, was found printed later (`α = −i` in the proof of the Hecke action, about
Period7.tex L1564-1566). Flags kept in the form column: `PazukiCor13Upper` is half of Pazuki's corollary, and the
comparison of normalizations is in height-split §3; `EichlerOptimalEmbeddingCount` may be printed modulo `𝒪¹`; Igusa
prints `ψ₄`, `χ₁₀` as identities of Eisenstein series; `CanonicalModelY3`, `ShimuraFamily` and `CanonicalCoarseX6`
keep the Lemma QP caveat.

The r5 split tasks checked their rows against the sources they could read (reduct-split could read none of its
sources, so its locators are UNVERIFIED); none reports a row false or vacuous. shimura-split's independent review
found `GonzalezRotgerCountX6` OK, and Eichler's count gives 2, 2, 2 points at discriminants −4, −3, −24, matching the
conic model's fibres (REPORTED, leaf-fold9 §1.1); the open check is that the kernel's `inertCount6 k` (`p·𝒪_k` prime
for `p = 2, 3`) is González–Rotger's `b(k)`. reduct-split's reading risks: SGA 7 IX 4.7 may be printed over a strictly
henselian base (`RaynaudSemistable`), and Serre–Tate Thm 2 for a complete `K` (`SerreTateThm2`, never projected); its
leaves count as published forms pending the integrator's review of the printed base ring. modular-split's two
realization leaves are consequences: Carayol's and Kato's objects cannot be defined in Mathlib. tyz-split's T-12
passed a clause-by-clause statement review: TYZ Theorem 3.3 or weaker, carried along the kernel's eta model (§3.2).
Every leaf stated on a witness of the moduli clause lists carries `R1fpProps`, whose clause `R1univProps` classifies
families without a group law, while the published moduli theorem classifies abelian schemes; r5 put the open check on
the step between them (rigidity, extension of the polarization) in those rows. Since r6 it rests on one field,
`mumfordRigidityCore` (H-170): with it r1univ-rigid compiles, for 18 leaves, that the leaf on `R1fpProps` is
equivalent to the same leaf on abelian schemes, and route-a-fold restates four fields that way. The row that still
carries `R1fpProps` says so (H-154); since r7, x6-fold states x6-glue's leaves on abelian schemes (§4.12),
`RayClassCMAb` included.

The r6 tasks checked their rows against the sources they could read; none reports a row false or vacuous.
reduct-glue's base review, first version, with the integrator's rulings (11-14): `NeronSchemeModelExistsDVR` (H-148)
and `MumfordTorsionAlgClosed` (H-102) stay published forms, the latter with Mumford's locator corrected to §6
Application 2 (iv); the four SGA 7 IX DVR fields count as consequences (a plausible weaker reading: a strictly
henselian base) until a human reads SGA 7 IX (its head, the openings of §2-§4, the displays of 4.7 and 3.5) and
Serre–Tate §1-§2; of their strictly henselian forms, `RaynaudSemistableSH` and `SemistableReductionSH` are published
forms and the other two consequences, tagged "review v1, v2 pending"; the three strict-henselization leaves are
consequences. c-to-printed's reading risks: BLR 1.2 Prop. 4 may be printed with strict henselizations (so `blr_1_2_4`
counts as a consequence, as does `sga7_IX_3_3`), the numbers of SGA 3 VI_B 3.10 and of Raynaud's bound are
unconfirmed, and Faltings' Lemma 5 was not read (those stay LEAF, flagged). reduct-glue's "no project glue is left"
for reduct-split's seven rows holds for `r7b` and `r8` only over perfect fields (`K^s → K̄` needs
`MulEtaleAbelianScheme`); neither is a hypothesis of the library theorem. x6-glue's independent review found no false,
vacuous or too-strong statement; the fibre clause of `ElkiesEquationsX6` is a composite of Elkies' statement and the
moduli meaning of `W`, and the CM assignment in `BabaGranathRational` is an UNVERIFIED reading of Baba–Granath's
table. c-to-printed2's review found no mathematical error, and its two realization leaves stay consequences: the
printed objects are quantified existentially. t5-glue's `ShimuraMainCM` is Shimura's Theorem 5.4 in Lang's idelic form
(numbers UNVERIFIED). theta-glue's `LinYangThetaCurve` is numerically VERIFIED (80 digits at 12 points) and `IgusaAlg`
by exact expansion, neither proved.

The r7 tasks checked their rows against the sources they could read; none reports a row false or vacuous, and none had
network access, so every locator is UNVERIFIED. reduct-b changes no statement: its three theorems prove the DVR fields
from the strictly henselian leaves already on the list. unipotent-b's `SemistableUnipotentPrintedGen` is 3.5 over the
printed strictly henselian base, with the echelon clause as recalled; its glue is needed only when the residue field
is imperfect. t09-pic states its four leaves over genuine definitions (Picard sheaf, `Pic⁰`, ample and very ample
bundles, Mumford's `ē_n` as `weilScalar`) and argues that `WeilPairingMumford` is a consequence of the print, not
stronger: each clause is one printed property and holds under either sign convention. shimura-cft's leaf (not used
here) is a consequence by its report, a composite by its review. kinds.tsv flags `deligneComponentsY3PrintedAb`
(depends on one display, Deligne 389 §5 and Milne 2005 §14) and `elkiesEquationsX6Ab` (its fibre clause), both GLUE by
the integrator's convention, and keeps the reading of Baba–Granath's table flagged on `babaGranathRationalAb`, LEAF.
igusa-alg's proofs replace theta-glue's exact expansions by Lean theorems with standard axioms; `LinYangThetaCurve`
stays a composite, numerically VERIFIED.

## 5. Completeness check

### 5.1 Scenario A (compiled composite)

`python3 scratch/frontier/chain.py A` (from the repository root): 0 signature mismatches; 71 open nodes = the 35 + 15
+ 14 + 1 = 65 fields of C4'''''''s four bundles (each expanded from the structure as read at main) plus the 6 TYZ and
GZ hypotheses of the top: the hypothesis list of the composite of C2, T0 with T0', and C4''''''', all of them used
(§4.14). With kinds.tsv's forms (strictest reading) and this report's forms for the top: 48 LEAF and 23 GLUE strict,
59 and 12 lenient; with `gonzalezRotgerCountX6Ab` published (kinds.tsv's strict column): 49 LEAF and 22 GLUE strict.
`chain.py onep`: its hypotheses are scenario A's (the four bundles and the six top Props); the bundles' fields are the
65 rows of `kinds.tsv`, with the names and type heads of the build's `open-statements.json`, whose six other
hypotheses have scenario A's heads.

### 5.2 Scenario F (frontier)

`python3 scratch/frontier/chain.py F`: 0 signature mismatches over 196 theorem edges in the file (32 followed on the
route, among them 1 transfer along an equivalence and 1 consumer replacement; no modus-ponens step is followed since
reduct-b's and unipotent-b's theorems replace r6's three); 86 open nodes = the 86 of §0 (no never-projected field is
left). Where a followed edge's file is not the H base, the check compares the Prop it proves with the one the route
uses (`defcheck`):
- `X0RatStructure`: identical (vs scratch/tyz-split/T5.lean, which takes it).
- `CMModuli`: identical (vs scratch/tyz-split/T5.lean, which takes it).
- `CoordinateNormalization`: identical.
- `CoordinateFromSections`: identical (vs scratch/mcr-glue/MCRGlue.lean, which takes it).
- `TorsionStructure`: the kernel's own constant (ZInQKernel/HDecomp/Objects.lean), which OneProof/H imports.
- `FibreAutTame`: identical.
- `CurveBijIso`: identical.
- `CMSectionsDisjoint`: identical (vs scratch/mcr-glue/MCRGlue.lean, which takes it).
- `GenericQuotientP1`: identical.
- `QMThetaSymmetricCurve`: identical (vs scratch/theta-split/ThetaUse.lean, which takes it).
- `ThetaEightSquare`: identical (vs scratch/theta-split/ThetaUse.lean, which takes it).
- `SemistablePersistsDVR`: identical.
- `RaynaudSemistable`: identical.
- `SemistableReductionDVR`: identical.
The F-only edges in library files outside OneProof/H (shimura-split, modular-split, tyz-split's T-5 split,
c-to-printed2, unipotent-b, t09-pic) prove the library's own constants: each file imports ZInQKernel modules, has no
definition of the Prop it proves (or only a copy for an `rfl` check), and imports the module that defines it, which
`OneProof/Main.lean` imports too (`worldcheck`):
- `ShimuraReciprocityModFn` (`scratch/tyz-split/T5.lean`): defined in `ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean`.
- `T09_SymmIsogenyExists` (`scratch/t09-pic/Pic.lean`, which has only a `Verbatim` copy for an `rfl` check): defined in `ZInQKernel/OneProof/H/TailB.lean`.
- `SemistableUnipotent` (`scratch/unipotent-b/UnipotentB.lean`): defined in `ZInQKernel/OneProof/H/TailZ7.lean`.
- `CarayolR17'` (`scratch/modular-split/R17.lean`): defined in `ZInQKernel/HDecomp/Conductor/LadicCond.lean`.
- `EigenformHTNew` (`scratch/c-to-printed2/CToPrinted2.lean`, which has only a `Verbatim` copy for an `rfl` check): defined in `ZInQKernel/OneProof/H/TailS.lean`.
- `ShimuraFamily` (`scratch/shimura-split/ShimuraFam.lean`): defined in `ZInQKernel/OneProof/H/TailU.lean`.
No followed edge concludes a kernel constant written with `_root_` in the bundles, so `rootcheck` has nothing to
check, and no followed edge's file is over leaf-fold4's chain, so `chaincheck` has nothing to compare either.
The transfer (`LeafQM.AV.R1UnivRigid.shimuraFamily_iff_ab`) is checked on the two sides of its `↔` and on its
hypothesis `MumfordRigidity`. The consumer replacement (`bypass_check`: the signatures of the old and the new
consumer):
- `ThetaRatiosAlgebraic`: ok; ok (TailA's `thetaPointOfFibre_of_qm_ratios` and theta-split's `thetaPointOfFibre_of_qm_curve` conclude the same `ThetaPointOfFibre`).
Each F-only row's definition (the file in its row) is identical to the definition in the file of every followed edge
that takes it and has its own copy (13 comparisons; 1 more edge imports the Prop instead).
The pairwise checks of r2 still pass. The eight kernel leaf copies that the flat files carried are gone: OneProof/H
imports `ZInQKernel/HDecomp/Objects.lean` itself. mcr-quot's and shimura-split's T5 is the kernel's
`ObjBridge.TorsionStructure` or `PkgI2.TorsionStructure.{0}`, which `Objects.lean` proves equal by `Iff.rfl`
(`torsionStructure_iff`).

`python3 scratch/frontier/chain.py doc` compares the rows `Z-n`, `T-n`, `H-n` with the scenario-F open set: 86 rows
with 86 distinct heads, equal to the open set.

What the script does not check: that the edges compose in one Lean environment; argument instantiation (for example
`heckeVertWitness_of_leaves5` takes `R1R2fp`, extracted from `r1r2` by `Classical.choice`); section variables that a
theorem takes through `include` (none on the route since qm-glue replaced qm-split's `qmHauptmodulBase3_of_O1`); and
the defs that a Prop's def mentions (only the top-level def text is compared).

## 6. Integration state

### 6.1 Composites that exist
- **`ZInQ.OneProof.frozenTarget`** (main; leaf-fold13's bundles since w66; T0' since w59): scenario A as one library
  theorem (§1).
- **C4''''''', leaf-fold13** (29885092, in w66: x6-fold e33b690a; over leaf-fold11 b73da969, w63): 35 + 15 + 14 + 1
  fields inside OneProof (`TailZ20`-`TailZ22` over leaf-fold11's `TailZ16`-`TailZ19` and `OneProof/Genus/*`,
  leaf-fold10's `TailZ10`-`TailZ15`, leaf-fold9's `TailZ5`-`TailZ9`, leaf-fold8's `TailY`-`TailZ4` and leaf-fold7's
  `TailP`-`TailX`); lake build, axioms and the unused-field scan REPORTED.
- **The top in the kernel**: C2 (atkin-li) and tyz-chain's T0, with T0' (tyz-split) in `OneProof/TYZSplit.lean`.
- **The contributor kit** (46afc732, w66): `docs/one-proof/OPEN.md`, generated from the build's
  `open-statements.json`, `kinds.tsv` and `claims.tsv`, and `ZInQKernel/OneProof/Discharges.lean`, whose `#discharges`
  names the hypotheses of `frozenTarget` that a contribution proves.
- Superseded: C4'''''' (leaf-fold11), C4''''' (leaf-fold9), C4'''' (leaf-fold8), C4''' (leaf-fold6), C4''
  (leaf-fold5), C4' (leaf-fold4), C4 (assemble-port) and the variants listed in r2.

### 6.2 What folding scenario F into C4''''''' needs
leaf-fold7 to leaf-fold13 take a fold only if neither GLUE count rises and the fold lowers the strict GLUE count or
replaces a consequence or composite by published-form leaves (leaf-fold9 §5). With this report's forms (SPECULATIVE
until compiled):
- reduct-b: the three DVR fields (consequences) go, the strictly henselian leaves `RaynaudSemistableSH` (published)
  and `SemistablePersistsSH`, `StrictHenselizationPair` (consequences) come: strict GLUE −1, lenient GLUE unchanged;
- unipotent-b: the consequence `semistableUnipotent` goes, the published `SemistableUnipotentPrintedGen`, the glue
  `SemiAbelianDescendsSepClosed` and the consequence `StrictHenselizationInside` come: both GLUE counts +1, so the
  rule keeps it out until the glue is proved (it is, for perfect residue fields);
- t09-pic: the consequence `t09SymmIsogenyExists` goes, two published leaves and two consequences come: strict GLUE +1
  by this report's reading, −1 by the report's (all four published);
- igusa-alg with theta-split: the composite `thetaRatiosAlgebraic` → the composite `LinYangThetaCurve`: neutral, with
  every closed identity proved;
- rayclass-cft (in flight) works on `rayClassCMAb`; shimura-cft's leaf for `shimuraFamilyAb` awaits a rating;
  c-to-printed2 (`eigenformHTNew` → `KatoRealizationCohSS`) is neutral; t5-glue (B7) changes the TYZ hypothesis `hS`
  (§6.3).

### 6.3 The library theorem
`ZInQ.OneProof.frozenTarget` has exactly the hypotheses of scenario A, and its proof uses all of them. Each F edge
removes or replaces a field once folded; B6 with B7 would change its TYZ hypothesis `hS` to `ShimuraMainCM`,
`RingClassLattice` and `X0ModuliGalois`.

## 7. Findings

**Refresh r7 (2026-11-14).**

1. **One row proved, two split, three off the route, five replaced** (§0, §4.1). The 11 new rows are 6 published
   forms, 3 consequences of one theorem, 1 composite and 1 project glue. The total (86) and the strict count (54/32)
   are r6's; the lenient count goes from 69/17 to 68/18.
2. **Scenario A is one compiled theorem** on main, `ZInQ.OneProof.frozenTarget`, now over leaf-fold13: 71 hypotheses,
   all used. Its 65 fields are 46 LEAF and 19 GLUE strict by the integrator's table (47 and 18 with
   `gonzalezRotgerCountX6Ab` published); with the top, 48 LEAF and 23 GLUE strict, 59 and 12 lenient. `chain.py onep`
   reads its hypotheses from `Main.lean` and finds scenario A's, and the bundles agree with `kinds.tsv` and the
   build's `open-statements.json`.
3. **One field table.** The forms of the fields come from the integrator's `kinds.tsv`; r6's own `fields11.tsv` is
   gone. The table's strictest column is this report's strict count, and its strict column the alternative.
4. **x6-glue's leaves are on abelian schemes now**, so the rows that carry `R1fpProps` shrink to H-154; their open
   check rests on `mumfordRigidityCore` (H-170).
5. **The SGA 7 IX rows**: reduct-b takes `SemistableReductionSH`, `ReductionFromSH` and `StrictHenselizationNeron` off
   the route, and unipotent-b replaces `SemistableUnipotentSH` by the printed 3.5; the base reading of the DVR fields
   (a human reading of SGA 7 IX) still decides whether they count as consequences.
6. **The theta route rests on one leaf**: igusa-alg proves `IgusaAlg 5` to `9` in Lean, so `QMThetaSymmetricCurve`
   follows from `LinYangThetaCurve` alone.
7. **claims.tsv lags w66**: it lists reduct-b, unipotent-b, t09-pic and igusa-alg as in progress, but their reports
   are merged and scenario F uses them.
8. **Project glue** is 5 Props: `CMStabObj`, `CoverModelOfHeckeN`, `P1SchemeQ`, `RingClassLattice`,
   `SemiAbelianDescendsSepClosed`.
9. **chain.py**: the H base is leaf-fold13 (bundles in `TailZ22`, `TailZ11`, `TailX`); the field table is `kinds.tsv`,
   and `onep` also compares the bundles with `open-statements.json`; r6's branch heads are read at main; `worldcheck`
   accepts a copy for an `rfl` check in a `section Verbatim` and at main.

**Refresh r6** (unchanged):

1. **6 rows proved, 10 split, 6 off the route, 3 replaced** (§0, §4.1). The 27 new rows are 12 published forms, 10
   consequences of one theorem, 2 composites and 3 project glue.
2. **Scenario A is one compiled theorem** on main, `ZInQ.OneProof.frozenTarget`, now over leaf-fold11: 67 hypotheses,
   all used. Its 61 fields are 43 LEAF and 18 GLUE strict by the integrator's convention (44 and 17 with
   `gonzalezRotgerCountX6Ab` published; leaf-fold11's own count 50 and 11); with the top, 45 LEAF and 22 GLUE strict,
   56 and 11 lenient. `chain.py onep` reads its hypotheses from `Main.lean` and finds scenario A's.
3. **The strict convention changes counts, not rows.** A leaf with a flagged plausible weaker reading counts GLUE (the
   four SGA 7 IX DVR fields, `blr_1_2_4`, `sga7_IX_3_3`); a merely unread leaf stays LEAF, flagged
   (`faltingsLemma5Printed`, `raynaudKernelBound`, `sga3_VIB_3_10`). The strictly henselian rows (H-182, H-183, H-184,
   H-185) keep the first version of the base review.
4. **The moduli-witness rows rest on one field.** r5's open check on the rows stated on `R1fpProps` (rigidity,
   extension of the polarization) now rests on the field `mumfordRigidityCore` (H-170), which route-a-fold added;
   scenario F reaches `r1r2Ab` and `shimuraFamilyAb` from the old forms through route A's transfers. `RayClassCM` is
   not among the 18 transfers r1univ-rigid compiled.
5. **`thetaRatiosAlgebraic` leaves by replacing its consumer**, and its curve part is now a composite leaf plus closed
   polynomial identities: theta-glue proves `ThetaEightSquare` and `IgusaAlg 3`, `IgusaAlg 4`; `IgusaAlg 5` to `9` are
   VERIFIED by exact expansion and not yet in Lean.
6. **Project glue** is 6 Props: `CMStabObj`, `CoverModelOfHeckeN`, `IgusaAlg`, `P1SchemeQ`, `ReductionFromSH`,
   `RingClassLattice`.
7. **chain.py**: the H base is leaf-fold11 (bundles in `TailZ19`, `TailZ11`, `TailZ18`, `TailX`); leaf-fold11 has no
   field table, so this report keeps `fields11.tsv`; edges along an equivalence (`iff`) are checked on both sides of
   the `↔`; the w62 draft's genus-route bypass and rigidity form leaf are gone with the fields; `UNUSED` and
   `USED_IN_F` are empty.

**Refresh r5** (unchanged):

1. **1 row proved, 14 split, 3 off the route, 1 dropped** (§0, §4.1). The 23 new rows are 7 published forms, 9
   consequences of one theorem, 1 composite and 6 project glue.
2. **Scenario A is one compiled theorem** on main, `ZInQ.OneProof.frozenTarget`, now over leaf-fold9: 69 hypotheses,
   63 used by its proof (39 LEAF and 24 GLUE strict, 49 and 14 lenient). `chain.py onep` reads its hypotheses from
   `Main.lean` and finds scenario A's.
3. **H-43 had not been reduced in r4.** qm-glue's `ConicCanonical` is `X6Kummer.X6ConicModel` verbatim (shimura-split,
   `Iff.rfl`), so r4's F route for H-43 was a renaming; scenario F now takes H-43 from shimura-split's smaller leaf
   `ElkiesConicX6`, with `r1r2` and T5.
4. **Forms.** `GonzalezRotgerCountX6` (the new field under `r5count`) counts as a composite, by the integrator's ruling
   and my reading of its existential witness (leaf-fold9 lists it as a published form); open check: `inertCount6` is
   González–Rotger's `b`. reduct-split's three leaves on the list are published forms pending the review of the
   printed base ring (§0 gives the count without them). modular-split's `HTDual`, which the report calls a named glue,
   counts as project glue.
5. **Project glue** is 9 Props: the coordinate's three, reduct-split's four (local-to-global steps, and
   `FixedTorsionRationalImperfect`, which only imperfect fields need), and modular-split's `H0DifferentialsEqHolo`
   (the last step of `dimJacobianEqGenus`, no literature left) and `HTDual`.
6. **Not splittable today** (rows kept): H-9 (Pan and Berger need `B_st`), H-53 (the dual abelian variety), H-79 (no
   `Γ₁(N)\ℍ*` in Lean), H-13 (`r16`, modular-split §4.1), `ShimuraGoodReductionNoGuard` (abelian schemes over a base),
   `T10_TateDuality` (never projected; reduct-split §4).
7. **chain.py**: the H base is leaf-fold9 (bundles in `TailZ9`, `TailZ4`, `TailX`); a declaration can be picked by
   occurrence (`nth`); `USED_IN_F` is recomputed; `worldcheck` checks that the library files of shimura-split and
   modular-split prove the library's own constants.

**Refresh r4** (unchanged):

1. **10 rows proved, 39 split** (§0, §4.1). The new rows are 35 published forms, 13 consequences of one theorem,
   8 composites and 3 project glue.
2. **Scenario A is one compiled theorem** on main, `ZInQ.OneProof.frozenTarget`, with 66 used hypotheses: 41 LEAF and
   25 GLUE strict, 52 and 14 lenient. `chain.py onep` reads its hypotheses from `Main.lean` and finds scenario A's.
3. **T-11 is a published form and compiled**: TYZ Theorem 3.3 as printed (Period7.tex read by tyz-split), restricted
   to `n ≡ 5, 7 (mod 8)`; leaf-fold8 put tyz-split's derivation of the pinned form into OneProof. T-5 stays GLUE: no
   printed form of Shimura reciprocity can be stated over Lean's definitions today, and the split gives a CM part (a
   consequence of Shimura Thm 5.4) and a modular-curve part.
4. **Forms.** A field of C4'''' has leaf-fold8's form (its §2): SS1, SS2, SS3 and `FaltingsLemma5BC` are
   consequences (height-split's own caveats and review), `JavanpeykarBound` and `IgusaCMValue24` published forms, and
   Igusa's `ψ₄`, `χ₁₀` published forms with qm-split's flag. Four F-only leaves of height-glue and qm-glue whose own
   docstrings or reviews name more than one source are counted by my reading, not as published forms: `CMDescent` and
   `ConicCanonical` (consequences), `QMUniformizationC` and `CanonicalCoarseX6` (composites).
5. **The project glue left is under the coordinate**: `QuotientP1Coordinate` in scenario A; in scenario F,
   `P1SchemeQ`,
   `CMStabObj` and the decomposition's `CoverModelOfHeckeN` (§4.1: counted open, since the chain derives it only
   downstream of the coordinate).
6. **Not splittable today** (rows kept): H-9 (Pan and Berger need `B_st`), H-53 (the dual abelian variety), H-78
   (`H¹(X, 𝒪_X)` on schemes), H-79 (no `Γ₁(N)\ℍ*` in Lean; its consumers could use Riemann–Hurwitz instead, curve-split
   §3.5), `ShimuraGoodReductionNoGuard` (abelian schemes over a base), `EigenformHTNew` (Kato's objects), H-59
   (`Y3Connected`: qm-glue reads it as the existential statement about the canonical model itself).
7. **chain.py**: the H base is read from OneProof/H at main; the def check tells the kernel's own constants (which
   OneProof/H imports) from copies and compares Props an F edge introduces with the files that take them; new checks
   for the files over leaf-fold4's `TailK` and for `_root_` kernel fields; `onep` compares the library theorem with
   scenario A and leaf-fold8's field table; a block ends at the next docstring; binders a consumer quantifies over
   can be listed (`bound`).

**Refresh r3** (unchanged):

1. **Form column and two counts** (the integrator's ruling): 17 published-form rows are LEAF in both counts; 24
   consequences of one theorem are LEAF only in the lenient count. Each names the derivation to compile.
2. **The TYZ premise is four Props in the kernel** (tyz-chain): `TYZThm11Integral` (published form), `TYZLemma29Mod2`,
   the CM leaf and `TYZThm33Pinned` (composites); `TYZLcalOne`, `Lemma321Five`, `Lemma318Literal`, `Thm35First` and
   `SqrtTwoNotInHHprime` are proved or reduced in kernel modules.
3. **leaf-fold5 compiles r2's H list**, except that it keeps av-b1's glue `SimpleImageIsogeny` (the frontier splits it
   into H-73, H-74 again; leaf-fold5 §1.3 gives the variant with T8 kept as a leaf, 69 Props with one glue).
4. **leafq-check** proves `GammaStarGen` and replaces three LEAF? fields by smaller statements (H-86..H-88).

**Refresh r2 and the 17:35 report** (unchanged):


1. **leaf-fold4 compiles the 17:35 frontier.** Scenario A's 69 projected Props are the 17:35 list minus
   `DivisiblePoints` (VERIFIED by chain.py). What was a textual composite of branch results at 17:35 is now one compiled
   theorem.
2. **Fork main carried the 11:21 version of this report** (79 open) until integration w51 merged wip/frontier d8c95123
   at 22:32. The upstream issues had been built from wip/frontier 249195fd, whose rows equal the 17:35 list.
3. **The statement reviews and this report's classes differ on five open rows** (H-3, H-16, H-21, H-25, H-38; §4.7).
4. **Reductions recorded but not folded.** tyz-318 reduces the LEAF T-4 to the GLUE `SqrtTwoNotInHHprime` (TYZ's Step 3)
   and proves T-4 outright when `n` is the only divisor `≡ 5 (mod 8)`; sqrt2-glue works on the rest. shimura-modfn
   splits the CM leaf T-5 but recommends keeping it: at Heegner points where the plane model `(j, j_N)` is singular,
   `j(τ)` and `j(Nτ)` do not determine `g(τ)` (its example `Q = [32,10,1]`, `D = −28`, numerically VERIFIED there).
5. **chain.py repair.** The 17:35 script read ts-kummer at d9c06585, which is not on the fork; r2 reads ts-kummer's final
   1bbe3543, which has the same six theorems. Those edges are off the route since C4'.
6. **av-b1's head 02ae2421 is an unchecked snapshot** from a host shutdown; r2 uses av-b1's files as merged into main.

**From the 17:35 report** (unchanged; for item 1, T3, T6-T9, T11(b), T26, T34, T38 and T41 are now proved or reduced,
and the open textbook rows are those of §4.3 and §4.5):

1. **The brief's "every textbook leaf T1-T32 is proved" is false** (VERIFIED: agent grep of the 150 newest refs, my grep
   of 80 refs for six of the Props). Proved: T2, T14(a′), T14(b′), T15, T16(a), T17, T18, T20, T21, T25, T28, T31 (and
   T36, T37 inside `x1`). Open: T1, T3, T4, T5, T6, T7, T8, T9, T10, T11(a), T11(b), T16(b), T23, T24, T26, T27, T29(a),
   T29(b); of these T1, T10, T16(b), T29 are never used. Since 12:45, T26 follows from T5 (t5-torsion), so T26 is no
   longer on the list.
2. **`GluePieces4.tateRamAtThree` is likely false as stated** (linked-ram finding F1, SPECULATIVE there): it is not
   quantified over `G7Data`, so g0-assemble3's `[L:ℚ] ≤ D` fix does not reach it. If so, g0-assemble3's
   `sixContactMin_of_leaves4` is vacuous. C4 (assemble-port) replaces it by linked-ram's `UnramTate.TateRamAtThreeD`
   (adds `Module.finrank ℚ L ≤ ZInQ.heightD`), which is proved there; route T does not need it either.
3. **Stale status texts.** STATUS.md and README say `HeckeThetaNewform` is "reduced to Atkin–Li"; it is proved
   (atkin-li, now on fork main w45). h-decomposition §2.2 on main marks T14, T28, T36, T37 open (proved) and lists T39
   as a leaf (it follows from T40). g0-assemble3's docstrings call `heckeIrreducible` "truth SPECULATIVE" (settled by
   ts-hecke) and its §6 misses the unused fields `r1rec, r3, r4, r5, r7b, r8, t10`. cm-numeric's report still lists
   `IInH4`, `HprimeNormal`, `GenusFieldLeLni` as leaves (all proved). The reports of ts-kummer and prop-ts-glue still call
   `KummerCompositum` open (kummer-comp's note). assemble-port's LEAF/GLUE labels are not the strict ones (§6.1).
4. **TYZ.** `CMNumeric.tyzZ` and `CMBridge.tyzZ` are two constants with the same body (an integration must keep one; T-6
   is stated at `CMBridge.tyzZ`). T-6, T-7 and the CM leaf are stated through the eta model `X0.phiC`; x0-32's eta
   leaves `EtaModelInvariant`, `EtaModelFricke` are now proved (tyz-cm), but the identification of `X0.phiC` with the
   modular parametrization also rests on x0-32's analytic-model statements, which are not hypotheses of the chain.
5. **Name collisions to resolve when folding**: three structures named `GluePieces5` (cpts-transport, linked-ram,
   assemble-port) and two named `HSyn.GluePieces4` (g0-assemble3, lt-goodred); `WeilPairing.IsogenyQuasiInverse` vs
   `HSyn.G0RevIsog.IsogenyQuasiInverse`; `PropTSGlue.propTSAll_final'` (prop-ts-glue vs ts-sn).
6. **Statement changes proposed here: none.** (Finding 2 is linked-ram's proposal, adopted by assemble-port; gz-decomp's
   `GrossZagierCd` and gz-statements' restricted GZ leaves are on record.)

## 8. Tasks (snapshot 2026-11-14 19:53 PST; heads in `scratch/frontier/refs.txt`)

Finished, with results used in r7: leaf-fold13 (29885092) with x6-fold (e33b690a) and the contributor kit (46afc732);
reduct-b (85495b37), unipotent-b (24c44f3d), t09-pic (3d0f47a8), igusa-alg (c9360203). Finished, read, not applied:
sh-route (89c75e42), shimura-cft (c1f76fc2), gap-triage (33bd9eb5). Used in r6 and merged in w66 (the same files):
theta-glue (336ec1fd), c-to-printed2 (dbeaecf7), t5-glue (39bb3cd2; r6 read 405763f6), x6-glue (685a56e1, folded by
x6-fold), c-to-printed (ba24fa83) and cm24-value (d8d1363a), both inside OneProof since w63. In flight: rayclass-cft
(7b27f1c3) and a fleet task on `quotientP1Coordinate` (claims.tsv); after w66, not used: leaf-fold14 (97579a97),
linyang-printed (3bb5a828), sh-printed2 (ea486e30), sem-prune (15a9a0ae). Used in r6 and compiled inside C4''''''' or
applied by scenario F: leaf-fold11, leaf-fold10, the prune, genus-fold, route-a-fold, shimura-glue, reduct-glue,
dimjac-glue, theta-split, genus-route, r1univ-rigid (heads in the r6 section of `refs.txt`). Used in r5: leaf-fold9,
shimura-split, reduct-split, modular-split and tyz-split's statement review. Used in r4: leaf-fold8, mcr-quot,
coarse-factor, cloud-w07 (fork PR #11), leaf-fold7, height-glue, qm-glue, leaf-fold6, mcr-glue, av-glue, av-split,
height-split, curve-split, hodge-split, qm-split, tyz-split, fork PRs #6-#10. Used in r3: leaf-fold5, leafq-check,
tyz-chain and the r2 tasks. Read, not folded: leaf-review-a, leaf-review-b. Cloud claims: claims.tsv (§0).

Running tasks are on the fork's tracker issue #3.

gz-statements (Contrib modules `ZInQKernel/Contrib/GZStatements/{Weak,Level,Compat,Hensel}.lean` on its branch) proves
that the narrower `ZInQ.GZStatements.FHNonvanishingCd` and `GrossZagierHeegnerCd` (restricted to `C_d`, `d ≡ 5 mod 8`,
`D < −4`) are implied by Z-1, Z-2 and still give `ZInQ.FrozenTarget`
(`frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`); they could replace Z-1, Z-2
(both remain GLUE). Not adopted here (not compiled together with `TYZChain.lean`).

This branch is fork main 4db0a627 (w66 with r6) plus this refresh.
