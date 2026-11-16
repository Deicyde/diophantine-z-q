# frontier: every open Prop on the path to `ZInQ.FrozenTarget`

Task frontier, 2026-11-13; refreshes r2 to r8, 2026-11-14 and 11-15 (text checks only, no Lean run). Base of r8: fork
main 37391b11 (11-15: integration w70, 6edf020d, with leaf-fold19 and the merge-bar commits), on wip/frontier-r8.
Branch snapshot: the commits in `scratch/frontier/refs.txt` (r8 section, read 04:33 PST). Lean:
`scratch/frontier/TYZChain.lean`, `TopChain.lean` (compiled 11-13, unchanged in r2). Mechanical check:
`scratch/frontier/chain.py` (with `chainlib.py`), run from the repository root; output
`scratch/frontier/chain_out.txt`. Results log: `scratch/frontier/log.md`. Working notes from three read-only survey
agents (11-13): `scratch/frontier/agent-{h-glue,h-leaves,tyz}.md`. Only this report and `scratch/frontier/` were
edited. Model work; no human review.

**Counts.** This report's counts describe the snapshot named above. The public count of open statements is the count
line of `docs/one-proof/OPEN.md`, which the integrator regenerates from the Lean build at every fold.

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

**The list.** If every proof and reduction that the branches had compiled by 2026-11-15 04:33 PST is folded in
(scenario F, §5), the open Props on the path to `ZInQ.FrozenTarget` are **75: 49 LEAF and 26 GLUE** in the strict
count. If consequences of one theorem count as leaves, they are 59 LEAF and 16 GLUE.

**The library theorem.** `ZInQ.OneProof.frozenTarget` on main (scenario A) has 65 hypotheses, leaf-fold19's 58 fields
and the seven TYZ and GZ Props, and its proof uses all of them (sem-prune's scan found no unused field, and each later
fold removes a field or adds only leaves its proof takes). Its fields and its seven other hypotheses are classified in
the integrator's table `docs/one-proof/kinds.tsv` (rendered in `docs/one-proof/OPEN.md`), whose headline follows the
integrator's strict convention: a leaf with a flagged plausible weaker reading counts GLUE, a merely unread leaf stays
LEAF, flagged. The fields are then **44 LEAF and 14 GLUE** in the strict count (the strictest reading, with
`weilPairingMumford` a composite), as OPEN.md's count line says; 45 and 13 with `weilPairingMumford` published (the
table's strict column); by kind alone, 46 published and 12 other. With the top: 47 LEAF and 18 GLUE strict, 55 and 10
lenient. Scenario F has more rows because it also applies the splits that the folds leave out on purpose: each
replaces one field by a leaf plus smaller statements (leaf-fold9 §5).

| premise | open Props | strict LEAF | strict GLUE | lenient LEAF | lenient GLUE | table |
|---|---|---|---|---|---|---|
| GZ, `Literature.GrossZagier` | 2 | 0 | 2 | 0 | 2 | §2.2 |
| TYZ, `Literature.TYZThm35ReadingA` | 5 | 3 | 2 | 4 | 1 | §3.2 |
| H, `SixContactMin`: research-level fields of r3 | 5 | 3 | 2 | 3 | 2 | §4.2 |
| H: textbook fields of r3 | 0 | 0 | 0 | 0 | 0 | §4.3 |
| H: fields that were glue in C4 | 0 | 0 | 0 | 0 | 0 | §4.4 |
| H: Props introduced by reductions until r3 | 5 | 5 | 0 | 5 | 0 | §4.5 |
| H: fields of the H base introduced in r4 | 22 | 21 | 1 | 21 | 1 | §4.6 |
| H: Props open only in scenario F, introduced in r4 | 9 | 1 | 8 | 3 | 6 | §4.7 |
| H: fields of leaf-fold9 introduced in r5 | 1 | 1 | 0 | 1 | 0 | §4.8 |
| H: Props open only in scenario F, introduced in r5 | 2 | 0 | 2 | 2 | 0 | §4.9 |
| H: fields of leaf-fold10 and leaf-fold11 introduced in r6 | 5 | 3 | 2 | 4 | 1 | §4.10 |
| H: Props open only in scenario F, introduced in r6 | 3 | 0 | 3 | 2 | 1 | §4.11 |
| H: fields of leaf-fold13 introduced in r7 | 5 | 4 | 1 | 5 | 0 | §4.12 |
| H: Props open only in scenario F, introduced in r7 | 2 | 1 | 1 | 1 | 1 | §4.13 |
| H: fields of leaf-fold14 to leaf-fold19 introduced in r8 | 9 | 7 | 2 | 8 | 1 | §4.14 |
| **total** | **75** | **49** | **26** | **59** | **16** | |

By form: 49 published form, 10 consequences of one theorem, 12 composites, 4 project glue (`CMStabObj`,
`CoverModelOfHeckeN`, `P1SchemeQ`, `SemiAbelianDescendsSepClosed`).

**Since r7 (4 new rows; 3 LEAF and 1 GLUE strict, 4 and 0 lenient).** Nine rows are proved (H-101, H-129, H-131,
H-132, H-135, H-136, H-171, H-176, T-17), two are pruned (H-124, H-173) and four are replaced by smaller statements
(H-168, H-185, H-187, H-195); five rows that r7 listed as open only in scenario F are fields now (H-182, H-199, H-200,
H-201, H-202). The H base is leaf-fold19's `sixContactMin_of_open26` inside the library (C4'''''''', §1): leaf-fold14
folds reduct-b's Route B-cp and t09-pic, sem-prune removes two fields that were used only syntactically, and the
integrator's `autofold.py` folds the contributions of gt-ega, gt-blr, gt-gamma, gt-theta, gt-grcount, gt-shpair,
gt-elkies, gt-qm, gt-valence and fork PR #19 (leaf-fold15 to leaf-fold19). gt-ringclass proves `RingClassLattice`, so
the library theorem takes its CM hypothesis from the two printed leaves T-15 and T-16 (B8, §3.1). The count of rows
goes from 86 to 75: 15 go, 4 come.

**Not applied** (§4.1): the reports of the branches after main (below), which are not merged; gt-qm's reroute of
`yuThm11`'s four live uses, a scratch check that no fold takes yet (H-128 says so); unipotent-b's split of
`semistableUnipotent`, which raises both GLUE counts (§6.2); and, as in r7, sh-route's theorems, shimura-cft's leaf
for `shimuraFamilyAb` and gap-triage's probe for `CoverModelOfHeckeN` (H-95).

**Who works on what** (the integrator's `docs/one-proof/claims.tsv` with the crowd kit's columns; the rows say which):
rayclass-cft on `rayClassCMAb` and mcr-quot on `quotientP1Coordinate` are in progress; shimura-cft's leaf for
`shimuraFamilyAb` awaits a rating; the cloud claims mark 28 rows (12 by cloud batch 2, 8 by cloud batch 3, 8 by cloud
round 2). claims.tsv still lists unipotent-b and igusa-alg as in progress: w66 merged their reports and scenario F
uses them, but no fold has taken them. After main the fork's branches carry gt-rayclass (28ec5c91; `rayClassCMAb` and
`shimuraFamilyAb` from Shimura's Main Theorem I in Deligne's adelic form on `Y₃`), gt-rigidity (762ea48b;
`mumfordRigidityCore` from two published leaves, with Mumford's Cor. 6.4 proved), gt-sga3 (deba22d7; `sga3_VIB_3_10`
from a weaker published leaf and `geomConnOfRationalPoint`), gt-sga7 (70a16c4c; `sga7_IX_3_3` from its strictly
henselian form and three bundle fields), gt-unip (42e1af66; `semistableUnipotent` from the forward half of SGA 7 IX
3.5 and two bundle fields, with no glue), gt-x6facts (80631ed5; `babaGranathRationalAb` from `elkiesEquationsX6Ab` and
a witness-free leaf, stated over leaf-fold17's bundles), rayclass-cft (7b27f1c3; `rayClassCMAb` from Shimura's Main
Theorem I, in flight in r7), linyang-printed (3bb5a828; `LinYangThetaCurve` from two printed leaves), sh-printed2
(ea486e30; `blr_1_2_4` (now proved) and `sga7_IX_3_3` in characteristic 0 from their strictly henselian forms). Their
reports are not merged, so this report does not use them, and the rows they name say so.

**The 75 names** (L = LEAF in both counts; c = consequence of one theorem, LEAF only in the lenient count; all others
GLUE; details in the tables):
- GZ: `ZInQ.GZDecomp.FHNonvanishing`; `ZInQ.GZDecomp.GrossZagierHeegner`.
- TYZ: `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` (L); `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2`; `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` (L); `T5Glue.ShimuraMainCM` (L); `T5Glue.X0ModuliGalois` (c).
- H: `PkgI2.NeronOggShafarevich` (L); `PkgI3.FaltingsSemisimple` (L); `PkgI3.FaltingsTate` (L); `PkgI4.PanBerger`; `LeafModCurves.R16_EichlerShimuraJ1'`; `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` (L); `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` (L); `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` (L); `ZInQ.Contrib.AVB1.PoincareComplement` (L); `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` (L); `AVGlue.CartierSmooth` (L); `AVGlue.GeomConnOfRationalPoint` (L); `AVGlue.GroupSchemeEquidim` (L); `AvSplit.MumfordTorsionAlgClosed` (L); `BPAnalytic.Uniformization.UniformizationLeafAll` (L); `AvSplit.MilneIsogenyQuasiInverse` (L); `ZInQ.HomLattice.GAGAMorphism` (L); `ZInQ.HeightSplit.JavanpeykarBound` (L); `ZInQ.HeightSplit.GaudronRemondThm14` (L); `ZInQ.HeightSplit.BostLowerBound` (L); `ZInQ.HeightSplit.PazukiCor13Upper` (L); `ZInQ.RLeaf.IgusaGL2` (L); `CurveSplit.RegularSmoothPerfect` (L); `CurveSplit.ShimuraGoodReductionNoGuard`; `ZInQ.Contrib.HodgeSplit.TateTwistInvariants` (L); `ZInQ.Contrib.HodgeSplit.AxSenTate` (L); `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` (L); `ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` (L); `ZInQ.Contrib.HodgeSplit.DSThm965` (L); `ZInQ.Contrib.HodgeSplit.DSThm966` (L); `HDec.QMSplit.Yu.YuThm11` (L); `HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar` (L); `MCRGlue.ProperCurveAF`; `MCRGlue.FiniteQuotientExists` (L); `MCRGlue.TameQuotientSmooth`; `MCRGlue.SmoothModelOfP1` (c); `MCRGlue.TameFixedPointsDisjoint` (c); `MCRGlue.TameInertiaCyclic`; `HDec.PropTSRed.CoverModelOfHeckeN`; `MCRQuot.P1SchemeQ`; `MCRQuot.CMStabObj`; `ReductSplit.NeronSchemeModelExistsDVR` (L); `HDec.QMSplit.Moduli.ShimuraHolFamily` (c); `ModularSplit.R17.CarayolRealization` (c); `ShimuraGlue.DeligneComponentsY3PrintedAb`; `LeafQM.AV.R1UnivRigid.MumfordRigidityCore` (L); `CToPrinted.FaltingsLemma5Printed` (L); `CToPrinted.SGA3_VIB_3_10` (L); `CToPrinted.SGA7_IX_3_3` (c); `CToPrinted2.KatoRealizationCohSS` (c); `ReductGlue.StrictHenselizationInside` (c); `HDec.HSyn.G0Split.ThetaPt.ThetaGlue.LinYangThetaCurve`; `HDec.QMSplit.Moduli.GeomConnOfAlgClosure` (L); `ShimuraGlue.DeligneComponentsX6PrintedAb` (L); `HDec.QMSplit.Moduli.BabaGranathRationalAb` (L); `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` (L); `ShimuraGlue.Ray.RayClassCMAb` (c); `UnipotentB.SemistableUnipotentPrintedGen` (L); `UnipotentB.SemiAbelianDescendsSepClosed`; `ReductGlue.RaynaudSemistableSH` (L); `T09Pic.PicRepresentableAbVar` (L); `T09Pic.PicZeroAbVar` (L); `T09Pic.PhiAmpleIsogeny` (L); `T09Pic.WeilPairingMumford`; `ReductB.SemistablePersistsSHcp` (L); `GRCountX6.GonzalezRotgerProp56X6` (L); `GapSHPair.NeronBaseChangeStrictHenselization` (L); `HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted` (c).

**How far this is checked.**
- **Scenario A is one compiled theorem.** `ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`, on
  leaf-fold19's bundles since 11-15) derives `ZInQ.FrozenTarget` from leaf-fold19's four bundles (30 + 13 + 14 + 1 =
  58 fields), the TYZ Props `TYZThm11Integral`, `TYZLemma29Mod2`, `ShimuraMainCM`, `X0ModuliGalois`, `TYZThm33` and
  the two GZ Props. OPEN.md states that the kernel checks it with no `sorry` and only the standard axioms (REPORTED;
  the folds regenerate the build's `open-statements.json`). `chain.py onep` reads the signature: its hypotheses are
  scenario A's (the four bundles and the seven top Props); the bundles' fields are the 58 field rows of `kinds.tsv`,
  with the names and type heads of the build's `open-statements.json`, whose seven other hypotheses have scenario A's
  heads.
- **Scenario F.** A plus the edges of §4.1, each compiled on its branch per its report and log. `chain.py` checks
  signatures (0 mismatches over 198 theorem edges, 27 of them followed on the route), route A's transfer and
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

**Findings in brief** (§7): since r7, nine rows proved, two pruned and four replaced; scenario A is one library
theorem with 65 hypotheses, all used, its 58 fields 44 LEAF strict by the integrator's table, as OPEN.md says; the 4
project-glue Props are `CMStabObj`, `CoverModelOfHeckeN`, `P1SchemeQ`, `SemiAbelianDescendsSepClosed`.

## 1. The chain to `ZInQ.FrozenTarget`

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| C0 (r3) | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` with `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` | `Contrib/GZTheta/NewCMFinal.lean` @ main; `Contrib/TYZChain/Main.lean` @ w54 | `SixContactMin`, the 4 TYZ Props of §3.2, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (r1-r2: this task's `frozenTarget_of_open` in `scratch/frontier/TYZChain.lean`, with cm-bridge's 7 TYZ Props) |
| C1 | `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` | `Contrib/GZDecomp/Decomp.lean` @ main | `SixContactMin`, `TYZThm35ReadingA`, `HeckeThetaNewform`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (via `GrossZagierCd`; `HeckeContinuation`, `FunctionalEquation5` discharged by the proved `ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) |
| C2 | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` | `Contrib/GZTheta/NewCMFinal.lean` @ wip/atkin-li 6f77abb1 | `SixContactMin`, `TYZThm35ReadingA`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` |
| C3 | TYZ: §3.1 | | → `TYZThm35ReadingA` |
| C4'''''''' (r8) | H: `HDec.HSyn.sixContactMin_of_open26 (r : OpenResearchLeaves19) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves16) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ32.lean` L47 @ main (leaf-fold19 c2ad4181, folding fork PR #19, over leaf-fold18 3782dac8, leaf-fold17 be8511f3, leaf-fold16 a454ad64, leaf-fold15 63205204 (gt-ega's `TailZ25`), sem-prune 2b486d04 and leaf-fold14 97579a97: `TailZ23`-`TailZ32` over leaf-fold13's `TailZ22`; leaf-fold14 reports `lake build +ZInQKernel.OneProof.Main` passing with standard axioms, and the later folds are `autofold.py`'s, with the build's `open-statements.json` regenerated, REPORTED) | → `ZInQ.SixContactMin`; 30 + 13 + 14 + 1 fields (§4) |
| C4''''''' (r7) | H: `HDec.HSyn.sixContactMin_of_open16 (r : OpenResearchLeaves13) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ22.lean` L335 @ main (leaf-fold13 29885092, merged in w66: x6-fold e33b690a, which adds `TailZ20`-`TailZ22` over leaf-fold11 b73da969: `lake build +ZInQKernel.OneProof.Main` passes, standard axioms, no unused field, no existing constant changed, REPORTED by x6-fold §1) | → `ZInQ.SixContactMin`, 35 + 15 + 14 + 1 fields; superseded: leaf-fold14's bundles map to leaf-fold9's directly, so `open12` to `open16` are compiled but off the path (leaf-fold14 §1) |
| C4'''''' (r6) | H: `HDec.HSyn.sixContactMin_of_open15 (r : OpenResearchLeaves12) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves11) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ19.lean` L1895 @ main (leaf-fold11 b73da969, merged in w63, with leaf-fold12's `TailZ18`, `TailZ19`; over leaf-fold10 a5df68fe, merged in w61, and the prune 0218a662, merged in w62: `lake build +ZInQKernel.OneProof.Main` passes, standard axioms, no unused field, REPORTED by leaf-fold11 §4) | → `ZInQ.SixContactMin`, 32 + 15 + 13 + 1 fields; superseded: leaf-fold13 fills its bundles inside OneProof |
| C4''''' (r5) | H: `HDec.HSyn.sixContactMin_of_open9 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves9) (l : OpenAddedLeaves8) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ9.lean` L161 @ main (leaf-fold9 cf6914e1, merged in w60; over leaf-fold8's `sixContactMin_of_open8` in `TailZ4.lean`: `lake build +ZInQKernel.OneProof.Main` exit 0, standard axioms, the closure of `sixContactMin_of_open9` without `sorryAx`; REPORTED by its report §1, §4) | → `ZInQ.SixContactMin`, 30 + 18 + 14 + 1 fields; superseded: leaf-fold10 and leaf-fold11 fill its bundles inside OneProof |
| C4'''' (r4) | H: `HDec.HSyn.sixContactMin_of_open8 (r : OpenResearchLeaves8) (t : OpenTextbookLeaves8) (l : OpenAddedLeaves8) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ4.lean` L265 @ main (leaf-fold8 b0f2f6da, merged in w59; over leaf-fold7's `sixContactMin_of_open7` in `TailX.lean`, w58: `lake build +ZInQKernel.OneProof.Main` exit 0, standard axioms, the closure of `sixContactMin_of_open8` without `sorryAx`; REPORTED by its report §1) | → `ZInQ.SixContactMin`, 31 + 20 + 14 + 1 fields; superseded: leaf-fold9 fills its bundles (`researchLeaves8_of_open9`, `textbookLeaves8_of_open9`) inside OneProof |
| C4''' | H: leaf-fold6's `HDec.HSyn.sixContactMin_of_open6` | `scratch/leaf-fold6/parts/f20_fold6.lean` @ main (leaf-fold6 733d8013, in w55; flat file compiled, REPORTED) | superseded: leaf-fold7 fills its bundles (`researchLeaves5_of_open7`, `glue6_of_open7`, …) inside OneProof |
| C4'' (r3) | H: `HDec.HSyn.sixContactMin_of_open5 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves5) (l : OpenAddedLeaves5) (g : OpenGlue5)` | `scratch/leaf-fold5/Leaves5.lean` L121755 @ wip/leaf-fold5 5a7e03d1 (in w54; flat file of the final text, 121 783 lines, md5 5999e1db: `lake env lean` exit 0 in 1570 s, 0 errors, no `sorry`, 349 axiom reports all standard; olean chain and `Check5.lean` compiled; REPORTED by its log) | → `ZInQ.SixContactMin`; 26 + 21 + 21 + 2 fields (§4) |
| C4' (r2) | H: `HDec.HSyn.sixContactMin_of_open4 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4) (l : OpenAddedLeaves4) (g : OpenGlue4)` | `scratch/leaf-fold4/Leaves4.lean` L118447 @ wip/leaf-fold4 9dcf1ca8 (final; flat file, 118 478 lines, md5 6bbeb639: `lake env lean` exit 0 in 1048 s, 0 errors, no `sorry`, 326 axiom reports all standard; olean chain and `Check4.lean`, the kernel conclusion, compiled; REPORTED by its report and log); on fork main since w49 | → `ZInQ.SixContactMin`; 26 + 19 + 20 + 1 fields (§4) |
| C5 | assemble-port's `HDec.HSyn.sixContactMin_of_leaves5` (C4 of the 17:35 report; 26 + 17 + 27 fields) | `scratch/assemble-port/AssemblePort.lean` L116751 @ 92a27877 | C4' is its successor through leaf-fold2-4: the 17:35 scenario-F edges folded, `chartProper`, `chartQuasiFinite`, `hauptmodulUnique` proved, `periodMapGlue`, `abVarSpreadsOut` reduced to leaves, `DivisiblePoints` removed (leaf-fold4 §1.1); g0-assemble3's 46-glue-field `sixContactMin_of_leaves4` before it |
| C6 | H, per field: §4 | | each open field, or the Props it was reduced to |
| **C0 ∘ C4'''''''' in the library (r8)** | `ZInQ.OneProof.frozenTarget (r : HDec.HSyn.OpenResearchLeaves19) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves16) (g : HDec.HSyn.OpenGlue7) (h11 …) (h29 …) (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois) (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33) (hL2 …) (hL3 …) : ZInQ.FrozenTarget` | `ZInQKernel/OneProof/Main.lean` @ main (OneProof since w56; `OneProof/TYZSplit.lean` since w59; B8 since leaf-fold17; leaf-fold19's bundles since 11-15) | scenario A of this report: C4'''''''' with tyz-chain's T0, T-11 from the printed Theorem 3.3, the CM hypothesis from B8, and the kernel's C1 |

The fork's registered headline (`ZInQKernel/MainLiterature.lean`) has five hypotheses; two are proved
(`ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) and C1 already uses them. C4' concludes the kernel's
`ZInQ.SixContactMin` (the flat file imports the kernel's definition; `Leaves.lean` is wrapped in `namespace HDec`), so
C0 and C4'''''''' compose by modus ponens. Earlier compiled H assemblies (cpts-transport's 44-field and linked-ram's
45-field `GluePieces5` in the W0 world, lt-goodred's and linked-frob's variants, leaf-fold2's
`sixContactMin_of_open2`) are superseded by C4, C4', C4'', C4''', C4'''', C4''''', C4'''''' and C4'''''''.

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
| B6 (r4) | `ZInQ.Contrib.TYZGenus.TYZSplitT5.shimuraReciprocityModFn_of_split` | `scratch/tyz-split/T5.lean` @ main | `CMModuli`, `X0RatStructure` → `Shimura.ShimuraReciprocityModFn`; scenario F used it until r7 (r8: off the route, B8) |
| B7 (r6) | `T5Glue.cmModuli_of_t5'`, `T5Glue.x0RatStructure_of_leaf` | `scratch/t5-glue/T5Glue.lean` @ main (t5-glue 39bb3cd2, merged in w66; r6 read it at the earlier head 405763f6, the same file; the later commits add the report and its second review, which finds `RingClassLattice` true) | `ShimuraMainCM`, `RingClassLattice` → `CMModuli` (the absolute Artin map's surjectivity and `InvertibleColon` proved over Tau Ceti); `X0ModuliGalois` → `X0RatStructure`; scenario F used them under B6 until r7 (r8: off the route, B8) |
| B8 (r8) | `T5Glue.shimuraReciprocityModFn_of_printed` | `ZInQKernel/Contrib/OneProof/RingClassLattice.lean` L3352 @ main (gt-ringclass 06f03bd4, folded by leaf-fold17: t5-glue's development verbatim, with `RingClassLattice` proved as `T5Glue.ringClassLattice`) | `ShimuraMainCM`, `X0ModuliGalois` → `Shimura.ShimuraReciprocityModFn`; the library theorem takes T-15 and T-16 in place of `hS`, so both scenarios use it |

### 3.2 Open Props (5: 3 LEAF, 2 GLUE in the strict count; 4 LEAF, 1 GLUE in the lenient count)

| # | Lean name | defined in | class | citation (UNVERIFIED unless marked) | last task; newest commit | running now | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| T-1 | `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` | `Contrib/TYZDecomp/Leaves.lean` @ main | **LEAF** (specialization: odd `m` only) | TYZ Thm 1.1, first assertion, L371–380 (read by nt-tyz) | tyz-decomp; main (tyz-lcal audit 11-13: faithful, not stronger) | cloud round 2: in progress (T-1); new base case TYZLcalOne proved (claims.tsv) | published form: specialization of TYZ Thm 1.1 to odd `m` (tyz-lcal audit: faithful, not stronger) |
| T-3 | `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2` | same | GLUE (mod-2 composite of Lemma 2.9 and Prop. 2.3) | TYZ Lemma 2.9, L1062–1066 (journal Lemma 2.9 per the AI locator audit); Prop. 2.3, L580–586 | tyz-decomp; main (tyz-lcal audit 11-13: faithful, not stronger) | cloud round 2: in progress (T-3) (claims.tsv) | composite: TYZ Lemma 2.9 with Prop. 2.3, read mod 2 (tyz-lcal audit) |
| T-12 | `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` | `ZInQKernel/OneProof/TYZSplit.lean` L157 @ main | **LEAF** | TYZ Theorem 3.3 over the kernel's definitions, for `n ≡ 5, 7 (mod 8)`, `𝒫(d)` existential | tyz-split | no | published form: TYZ Thm 3.3, Period7.tex L1299-1311, specialized (tyz-split §1), carried along the kernel's eta model of `X₀(32)` by the q-expansion principle (`IsRatModFn 32`), which already sits behind `hS`; a clause-by-clause statement review found the leaf Thm 3.3 or weaker (tyz-split §1 and the docstring, wip/w61 3c241950); the `[i]` sign of the base point is printed (`α = −i` in the Hecke-action proof, about L1564-1566) |
| T-15 | `T5Glue.ShimuraMainCM` | `ZInQKernel/Contrib/OneProof/RingClassLattice.lean` L911 @ main | **LEAF** | the main theorem of complex multiplication with torsion, idelic, in Weierstrass coordinates over Mathlib's `PeriodPair`, finite adeles and Tau Ceti's `ideleClassArtinMap` (replaces T-13 (from T-5)) | t5-glue; hypothesis `hCM` of the library theorem since leaf-fold17 (gt-ringclass) | no | published form: Shimura 1971 Thm 5.4; Lang, Elliptic functions, Ch. 10 Thm 3 (t5-glue §0; numbers UNVERIFIED); leaf-fold17's statement review: the docstring cites the Artin-map lemmas that fix the normalization (kinds.tsv: unread, a new printed leaf) |
| T-16 | `T5Glue.X0ModuliGalois` | `ZInQKernel/Contrib/OneProof/RingClassLattice.lean` L673 @ main | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count) | the canonical model of `X₀(N)`: `σ(g(τ)) = g(τ')` when `σ ∈ Aut(ℂ)` carries `(E_τ, ⟨1/N⟩)` to `(E_τ', ⟨k/N⟩)`, for `g` regular on `ℍ`; no CM (replaces T-14 (from T-5)) | t5-glue; hypothesis `hX` of the library theorem since leaf-fold17 (gt-ringclass) | cloud batch 3 (W18, on its leaf VeluCyclic): briefed 2026-11-15, not yet claimed on the issue (claims.tsv) | consequence of one theorem: Shimura 1971 §6.7; Deligne–Rapoport VI-VII; Diamond–Shurman §7.5-7.7 (t5-glue §0; numbers UNVERIFIED); the report's label: LEAF, a consequence of the print; leaf-fold17's statement review: a consequence, with the theorem numbers aligned to `IsRatModFn`'s (kinds.tsv: unread, numbers UNVERIFIED) |

Retired rows: T-2 `TYZLcalOne` (proved, B2), T-4 `Lemma318Literal` (proved, B5), T-6 `Thm35First` (reduced to T-11,
B4), T-7 `Lemma321Five` (proved, B3); r4: T-5 (split by tyz-split into `CMModuli` and `X0RatStructure`), T-11 (from
the printed TYZ Thm 3.3 (`TYZThm33`, tyz-split)); r6: T-13 `CMModuli` and T-14 `X0RatStructure` (split by t5-glue,
B7); r8: T-17 `RingClassLattice` (proved by gt-ringclass, B8). Since r8 T-15 and T-16 are hypotheses of the library
theorem, defined in gt-ringclass's verbatim copy of t5-glue's file.

## 4. H: `ZInQ.SixContactMin`

Base (r8): leaf-fold19's compiled C4'''''''' (c2ad4181, on main since 11-15), inside OneProof: leaf-fold14 (97579a97)
with reduct-b's Route B-cp and t09-pic, sem-prune (2b486d04), leaf-fold15 (63205204, gt-ega's fold), leaf-fold16
(a454ad64), leaf-fold17 (be8511f3), leaf-fold18 (3782dac8) and leaf-fold19, over leaf-fold13 (29885092, w66),
leaf-fold11 (w63), leaf-fold10 (w61), the prune (w62), leaf-fold9 (w60), leaf-fold8 (w59) and leaf-fold7 (w58).
Bundles: `OpenResearchLeaves19` (30), `OpenTextbookLeaves11` (13), `OpenAddedLeaves16` (14) and leaf-fold7's
`OpenGlue7` (1: `quotientP1Coordinate`). The fields' forms are the integrator's `kinds.tsv` (with the crowd kit,
1c791eb1): 46 published, 7 consequences, 4 composites, 1 project glue by kind; its strict convention counts two
published kinds as GLUE, and this report records them as composites: `deligneComponentsY3PrintedAb` and
`weilPairingMumford` (the strictest reading). Its seven rows with bundle `frozenTarget` give the forms of the top
(§2.2, §3.2). `chain.py` reads the bundles from `ZInQKernel/OneProof/H/TailZ29.lean`, `TailZ32.lean`, `TailZ31.lean`
and `TailX.lean` at main. Row numbers are kept, retired rows listed, new rows from H-203 (§4.14).

### 4.1 What changed since r7 (signatures VERIFIED by `chain.py`)

Compiled into C4'''''''' (scenario A), fold by fold. leaf-fold14: reduct-b's Route B-cp replaces the DVR fields
`semistableReductionDVR`, `raynaudSemistable`, `semistablePersistsDVR` by `raynaudSemistableSH` (H-182), the
restricted `semistablePersistsSHcp` (H-203) and `strictHenselizationPair` (H-187); t09-pic's four leaves replace
`t09SymmIsogenyExists` (H-199 to H-202); unipotent-b is not taken. sem-prune: `bdRInvariants` and `raynaudKernelBound`
go (H-124, H-173). leaf-fold15: `egaIV_8_10_5_openImm` (gt-ega) proved (H-176). leaf-fold16: `blr_1_2_4` (gt-blr),
`shimizuCovolumeO1` (gt-gamma), `igusaPsi4` and `igusaChi10` (gt-theta) proved (H-171, H-136, H-131, H-132).
leaf-fold17: gt-ringclass's B8 (T-17 proved; the top takes T-15 and T-16), and gt-grcount's `GonzalezRotgerProp56X6`
(H-204) in place of `gonzalezRotgerCountX6Ab` (H-168). leaf-fold18: gt-shpair's `NeronBaseChangeStrictHenselization`
(H-205) in place of `strictHenselizationPair`, gt-elkies's `ElkiesX6StarPrinted` (H-206) in place of
`elkiesEquationsX6Ab` (H-195), and `qmCentralizerCMC` (gt-qm) and `valenceFormulaCocompactEq` (gt-valence) proved
(H-129, H-135). leaf-fold19: `mulEtaleAbelianScheme` proved over every commutative base (fork PR #19; H-101). r7's
changes are in the r7 report (`git show 3691994d:docs/research/frontier.md`, §4.1).

Applied on top by scenario F:

| field of C4'''''''' (rows) | now | theorems · task · file |
|---|---|---|
| `shimuraFamilyAb` (H-139) | ⇐ `ShimuraFamily` with route A's transfer and `MumfordRigidityCore`; `ShimuraFamily` ⇐ `ShimuraHolFamily` (H-154) with the GAGA-level step (as in r6 and r7; shimura-cft's stronger leaf is not taken) | `LeafQM.AV.R1UnivRigid.shimuraFamily_iff_ab` (route-a-fold); `LeafQM.AV.R1UnivRigid.mumfordRigidity_of_core`; `HDec.QMSplit.Moduli.shimuraFamily_of_hol` · shimura-split · `scratch/shimura-split/ShimuraFam.lean` |
| `r17` (H-21) | ⇐ `CarayolRealization` (H-157); the transport to every attached representation is proved (as in r6 and r7) | `ModularSplit.R17.carayolR17'_of_realization` · modular-split · `scratch/modular-split/R17.lean` |
| `eigenformHTNew` (H-127) | ⇐ `KatoRealizationCohSS` (H-181) and the fields `TateTwistInvariants`, `AxSenTate` (as in r6 and r7) | `CToPrinted2.eigenformHTNew_of_printedSS` · c-to-printed2 · `scratch/c-to-printed2/CToPrinted2.lean` |
| `semistableUnipotent` (r6: H-184) | ⇐ SGA 7 IX 3.5 as printed (`SemistableUnipotentPrintedGen`, H-197), the glue `SemiAbelianDescendsSepClosed` (H-198; proved for perfect residue fields), `StrictHenselizationInside` (H-188) and `MulEtaleAbelianScheme`, proved since leaf-fold19 (as in r7, which had it as a field) | `UnipotentB.semistableUnipotent_of_printedGen` · unipotent-b · `scratch/unipotent-b/UnipotentB.lean`; `ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof` · fork PR #19 · `ZInQKernel/Contrib/OneProof/MulEtale.lean` |
| `thetaRatiosAlgebraic` (H-44; r6: H-191) | replaced at its consumer (theta-split, route 1): TailA's `ThetaPointOfFibre` from `FibreQMPeriod`, `ThetaEightSquare` and `QMThetaSymmetricCurve`, in place of `HDec.HSyn.G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios`; theta-glue proves `ThetaEightSquare`, and igusa-alg proves `IgusaAlg 5` to `9`, so `QMThetaSymmetricCurve` follows from `LinYangThetaCurve` alone (H-190) | `HDec.HSyn.G0Split.ThetaPt.ThetaSplit.thetaPointOfFibre_of_qm_curve` · theta-split · `scratch/theta-split/ThetaUse.lean`; `HDec.HSyn.G0Split.ThetaPt.ThetaGlue.thetaEightSquare` · theta-glue · `scratch/theta-glue/ThetaGlue.lean`; `HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal.qmThetaSymmetricCurve_of_linYang` · igusa-alg · `scratch/igusa-alg/IgusaAlg.lean` |
| `quotientP1Coordinate` (the glue field; H-84's successor) | ⇐ mcr-glue's six leaves (H-89..H-94; `TameQuotientSmooth` is L3), T5, and three glue Props: mcr-quot's `P1SchemeQ` and `CMStabObj`, and the decomposition's `CoverModelOfHeckeN` | `HDec.MCRGlue.quotientP1Coordinate_of_leaves` (compiled in `ZInQKernel/OneProof/H/TailW.lean`) with mcr-glue's `coordinateNormalization_of` · mcr-glue · `scratch/mcr-glue/MCRGlue.lean`; `fibreAutTame_of''`, `genericQuotientP1_of''`, `cMSectionsDisjoint_of''`, `coordinateFromSections_of''` and their inputs (namespace `MCRQuot`) · mcr-quot · `scratch/mcr-quot/MCRQuot.lean` |

On the TYZ side both scenarios use B8 (§3.1): the CM hypothesis rests on T-15 and T-16, and tyz-split's B6 and
t5-glue's B7 are off the route. The leaves on a witness of the moduli clause that carry `R1fpProps` are still only
H-154; route A's transfer makes that leaf equivalent to the same leaf on abelian schemes once the field
`mumfordRigidityCore` (H-170) is given.

mcr-quot proves the four glue Props under the coordinate (`FibreAutTame`, `GenericQuotientP1`, `CMSectionsDisjoint`,
`CoordinateFromSections`) from T5, L3, `CurveBijIso` and three glue Props: `P1SchemeQ` and `CMStabObj`, which are new,
and `CoverModelOfHeckeN`, the decomposition's own glue. The chain derives `CoverModelOfHeckeN` only through
`HeckeNoVertRam`, downstream of the coordinate that mcr-quot feeds, so here it is counted as open glue: the coordinate
still rests on project glue, and mcr-quot does not discharge it. gap-triage (w66) finds it unnecessary: mcr-quot's
`ModelYIrreducible` is the chain's `HeckeIrreducible`, which the chain proves from the field
`deligneComponentsY3PrintedAb`, and mcr-quot's composite compiles with it in place of `CoverModelOfHeckeN`
(`scratch/gap-triage/GlueProbe.lean`, `MCRQuotNV.lean`); the probe takes leaf-fold9's whole bundle, so scenario F does
not apply it yet (H-95).

Off the route since r8 (the edges stay in `chain.py`): reduct-b's `ReductB.raynaudSemistable_of_SH_pair`,
`ReductB.semistablePersistsDVR_of_SH_pair` and `ReductB.semistableReductionDVR_of_raynaud`, whose fields leaf-fold14
replaces by their strictly henselian forms; t09-pic's `T09Pic.t09SymmIsogenyExists_of_four`, which leaf-fold14
compiles; tyz-split's `ZInQ.Contrib.TYZGenus.TYZSplitT5.shimuraReciprocityModFn_of_split` (B6) with t5-glue's
`T5Glue.cmModuli_of_t5'` and `T5Glue.x0RatStructure_of_leaf` (B7), which B8 replaces; since r7: x6-glue's
`HDec.QMSplit.Moduli.r1r2_of_published` and `HDec.QMSplit.Moduli.x6ConicModel_of_published` with route A's
`LeafQM.AV.R1UnivRigid.r1R2fpRep_iff_ab`, whose conclusions x6-fold proves in C4'''''''; reduct-glue's
`ReductGlue.raynaudSemistable_of_SH'` and the modus-ponens steps through `ReductionFromSH`, `PersistsFromSH` and
`UnipotentFromSH`, which reduct-b's and unipotent-b's theorems replace; theta-glue's
`HDec.HSyn.G0Split.ThetaPt.ThetaGlue.qmThetaSymmetricCurve_of_alg59`, which igusa-alg's theorem replaces; since r6:
`HDec.QMSplit.Moduli.y3Connected_of_deligne` (shimura-split) and `ModularSplit.DimJac.dimJacobianEqGenus_of_glue`
(modular-split), whose fields leaf-fold10 compiles; reduct-split's `ReductSplit.raynaudCriterion_final'`,
`ReductSplit.semistableReductionThm_final`, `ReductSplit.semistablePersists_final`,
`ReductSplit.semistableNeronBaseChange_of_leaves` and `ReductSplit.faltingsLemma5BC_final`, whose conclusions are no
longer fields; shimura-split's `HDec.QMSplit.Moduli.r1r2fpRep_of_printed_t5` and
`HDec.QMSplit.Moduli.x6ConicModel_of_elkies_t5` with shimura-glue's edges, which x6-glue's theorems replace;
modular-split's `ModularSplit.EigenHT.eigenformHTNew_of_coh`; qm-split's
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
H-167, T-13, T-14; r7: H-53, H-142, H-177, H-178, H-179, H-180, H-183, H-184, H-186, H-189, H-191; r8: H-101, H-124,
H-129, H-131, H-132, H-135, H-136, H-168, H-171, H-173, H-176, H-185, H-187, H-195, T-17. Not applied: the variants
each report keeps aside (r8: the reports of the branches after main (§0); gt-qm's reroute of `yuThm11`'s four live
uses (H-128); unipotent-b's split, which leaf-fold14 leaves out (§6.2); r7: sh-route's
`strictHenselizationNeron0_final`, `strictHenselizationPair0_final`, `strictHenselizationInside0_final` and
`route_final` from `NeronBaseChangeSH`, whose statements add `[CharZero K]` and a perfect residue field; reduct-b's
Route B-cp, `ss1_ss3_of_cp`, over the restricted leaf `SemistablePersistsSHcp`, which leaf-fold14 compiles;
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

### 4.4 Fields that were glue in C4, still open (in C4'''''''' they are `OpenAddedLeaves16` fields) (0: 0 LEAF, 0 GLUE strict; 0 LEAF, 0 GLUE lenient)

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

Proved and gone from the tables: r8, `RingClassLattice` (gt-ringclass), `MulEtaleAbelianScheme` (fork PR #19),
`QMCentralizerCMC` (gt-qm), `ValenceFormulaCocompactEq` (gt-valence), `IgusaPsi4`, `IgusaChi10` (gt-theta),
`ShimizuCovolumeO1` (gt-gamma), `BLR_1_2_4` (gt-blr), `EGAIV_8_10_5_openImm` (gt-ega), and from new leaves
`GonzalezRotgerCountX6Ab`, `StrictHenselizationPair` and `ElkiesEquationsX6Ab`; r7, `IgusaAlg` (igusa-alg); r6,
`IgusaCMValue24` (cm24-value), `HTDual` (c-to-printed2), `FixedTorsionRationalImperfect`, `SemistableAlmostAll`,
`SemistableLocalGlobal` and `SemistableNeronBaseChangeLocalGlobal` (reduct-glue, the last two through c-to-printed's
printed fields); r5, `DeligneSerreConseq` (modular-split); r4, `EigenformTwist`, the two EGA IV descents,
`ZariskiConnectedness`, `T11bExists`, `NeronMappingAbelianSchemeSurj` (PRs #6-#10), `JacobianExists ℚ`,
`NormalModelOfFunctionFieldQ` (cloud-w07), `QMClassNumberOne` (qm-split), `CurveBijIso` (curve-split); r3,
`GammaStarGen`; r2, `SerreRigidity3`, `T09_WeilPairing` (av-b2), and in the chain below `HeckeVertWitness`:
`SmoothFibreReduced` (smooth-fibre), `SpecialFibreMaxIdeal`, `SpecialFibreUniformizer`, `SpecialFibreDVR`
(vert-witness), `ModelGenericFibre`, `GermOfQbarValues`, `ModelIntegral`, `ModelFunctionField` (model-glue). Props
that r4's own tasks introduced and proved were never rows: height-split's glue (`AnalyticUniformizationExists`,
`AnalyticUniformizationUnique`, `UniformizationDim`, `MetrizationOfUniformization`, `NeronMetrizable`, proved from T35
by height-glue), qm-split's `GammaStarFromO1` (qm-glue), qm-glue's `CoarseFactor` (coarse-factor), mcr-glue's four
glue Props (mcr-quot, from three others). Proved before 17:35: see the 17:35 report (`git show
d8c95123:docs/research/frontier.md`). Props that r5's tasks introduced and proved were never rows: reduct-split's
`TorsionFieldOfDefinition`, `DVRFiniteExtension`, `DVRComapFinite` and `IsogenyBaseChangeDeg`; shimura-split's
`PairsLift` (from T5). Props that r6's tasks introduced and proved or reduced were never rows: shimura-glue's
`MobiusCompose` (proved); reduct-glue's `UnipotentFromSH` and `PersistsFromSH` (from the strict-henselization leaves);
x6-glue's `ConicModelT` (from its charts); t5-glue's `AbsArtinSurjectiveQNeg` and `InvertibleColon` (proved over Tau
Ceti); theta-glue's `ThetaEightSquare`, `IgusaThetaSymmetric` (from `IgusaAlg`) and `IgusaAlg 3`, `IgusaAlg 4`
(proved); genus-route's `DimJ1Le5` (proved); route A's `MumfordRigidity` (from `mumfordRigidityCore`). Props that r7's
tasks introduced and proved were never rows: t09-pic's `veryAmpleIsAmple` (formerly a leaf, EGA II 4.5.10) and its
genuine definitions; igusa-alg's `IgusaAlg 3` to `IgusaAlg 9` and its two theta-route theorems; sh-route's commutative
algebra (`SHExists0`, `SHInside0`, `SHPair0`); unipotent-b's two `K^s` versus `K̄` Props. Props that r8's tasks
introduced and proved were never rows: sem-prune's `G9GlueNoT23` and `FaltingsLemma5BCLower`; gt-shpair's commutative
algebra (`IsSHSep` pins the strict henselization in every characteristic); gt-elkies's Atkin–Lehner group, a
definition, and its moduli step `orbit_iff_twist`; gt-grcount's passage from `R5fpCount`.

### 4.6 Fields of the H base introduced in r4 (22: 21 LEAF, 1 GLUE strict; 21 LEAF, 1 GLUE lenient)

Each row is a field of C4'''''''' (its name is in the 'last task' column; leaf-fold9 to leaf-fold19 keep leaf-fold8's
fields, less those proved or pruned since) and the hypothesis of a compiled theorem in the task's file. Its form is
the kind in the integrator's `kinds.tsv`, which keeps leaf-fold8's; where this report's reading differs the pointer
says so. Theorem numbers are the reports' and UNVERIFIED unless a report read the source.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-98 | `AVGlue.CartierSmooth` | `scratch/av-glue/Combined.lean` L297 @ main | H-73, H-74 | **LEAF**; a group scheme locally of finite type over a field of characteristic 0 is smooth | av-glue; field `cartierSmooth` of leaf-fold19; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Cartier's theorem; Mumford AV §11 Thm 1; Stacks 047N (av-glue §5) |
| H-99 | `AVGlue.GeomConnOfRationalPoint` | `scratch/av-glue/Combined.lean` L902 @ main | H-74 | **LEAF**; a connected scheme of finite type over `k` with a rational point is geometrically connected | av-glue; field `geomConnOfRationalPoint` of leaf-fold19; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Stacks 04KV, specialized to finite type with a rational point (av-glue §5) |
| H-100 | `AVGlue.GroupSchemeEquidim` | `scratch/av-glue/Combined.lean` L913 @ main | H-74 | **LEAF**; the irreducible components of a group scheme of finite type over a field have its dimension | av-glue; field `groupSchemeEquidim` of leaf-fold19; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Stacks, group schemes over a field; SGA 3 VI_A 2.4, finite type (av-glue §5) |
| H-102 | `AvSplit.MumfordTorsionAlgClosed` | `scratch/av-split/AvSplitAll.lean` L1411 @ main | H-25, H-38 | **LEAF**; over `k = k̄`, `A(k)[n] ≅ (ℤ/n)^{2g}` for `char k ∤ n` | av-split; field `mumfordTorsionAlgClosed` of leaf-fold19; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Mumford AV §6 Application 2 (iv) (the integrator's correction of av-split's §4; UNVERIFIED) |
| H-103 | `BPAnalytic.Uniformization.UniformizationLeafAll` | `ZInQKernel/HDecomp/Analytic/Uniformization.lean` L91 @ main | H-38, H-69 | **LEAF**; the kernel's AN3 leaf: `A^an` in coordinate form | av-split; field `uniformizationLeafAll` of leaf-fold19; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Mumford §1 in coordinate form (bp-analytic §4; av-split §1 shares the judgement) |
| H-104 | `AvSplit.MilneIsogenyQuasiInverse` | `scratch/av-split/AvSplitAll.lean` L1361 @ main | H-54 | **LEAF**; `fg = [d]`, `gf = [d]` as morphisms for some `d ≥ 1` | av-split; field `milneIsogenyQuasiInverse` of leaf-fold19; cloud batch 2: briefed (characteristic-zero form); the batch-2 comment of 2026-11-15 02:14Z mentions it only as a possible follow-on (claims.tsv) | published form: Milne 1986 Rem. 8.4; Mumford §7 (av-split §1) |
| H-105 | `ZInQ.HomLattice.GAGAMorphism` | `scratch/av-split/AvSplitAll.lean` L1029 @ main | H-69 | **LEAF**; GAGA for homomorphisms of complex abelian varieties | av-split; field `gagaMorphism` of leaf-fold19; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Serre, GAGA, in the form of homlattice §3.2 (av-split §1) |
| H-109 | `ZInQ.HeightSplit.JavanpeykarBound` | `scratch/height-split/HeightSplit.lean` L508 @ main | H-14 | **LEAF**; Javanpeykar's bound over the published stable height | height-split; field `javanpeykarBound` of leaf-fold19 | published form: specialization of Javanpeykar 2014 Thm 1.1.1 to `K` with a `K`-rational Belyi function (height-split §4; leaf-fold8 §2; height-split §7 notes that a stricter reader may call it a consequence) |
| H-110 | `ZInQ.HeightSplit.GaudronRemondThm14` | `scratch/height-split/HeightSplit.lean` L773 @ main | H-15 | **LEAF**; Gaudron–Rémond's bound over the published stable height | height-split; field `gaudronRemondThm14` of leaf-fold19 | published form: Gaudron–Rémond 2014 Thm 1.4 (height-split table) |
| H-112 | `ZInQ.HeightSplit.BostLowerBound` | `scratch/height-split/HeightSplit.lean` L429 @ main | H-17 | **LEAF**; `h_D ≥ −(g/2) log 2π` (Deligne's normalization) | height-split; field `bostLowerBound` of leaf-fold19 | published form: Bost, Sém. Bourbaki 795 (display unread; height-split §2) |
| H-113 | `ZInQ.HeightSplit.PazukiCor13Upper` | `scratch/height-split/HeightSplit.lean` L717 @ main | H-18 | **LEAF**; the upper side of Pazuki's comparison of theta and Faltings heights | height-split; field `pazukiCor13Upper` of leaf-fold19 | published form: Pazuki 2012 Cor. 1.3(2), read off the same display (height-split §3) |
| H-117 | `ZInQ.RLeaf.IgusaGL2` | `ZInQKernel/Contrib/RLeaf/IgusaSL2.lean` L120 @ main | H-41 | **LEAF**; Igusa's theorem: `GL₂(ℤ/N)` is the Galois image on `E_j[N]` | curve-split; field `igusaGL2` of leaf-fold19 | published form: Igusa 1959; Shimura 1971 Thm 6.6 (curve-split §3.1) |
| H-118 | `CurveSplit.RegularSmoothPerfect` | `scratch/curve-split/CurvesGSplit.lean` L81 @ main | H-81 | **LEAF**; a finite type algebra over a perfect field is smooth at a prime with regular local ring | curve-split; field `regularSmoothPerfect` of leaf-fold19; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Stacks 00TV, the ⇐ half (curve-split §3.3) |
| H-119 | `CurveSplit.ShimuraGoodReductionNoGuard` | `scratch/curve-split/ShimuraGR.lean` L162 @ main | H-83 | GLUE (composite); `ShimuraGoodReduction` without its guard clause | curve-split; field `shimuraGoodReductionNoGuard` of leaf-fold19; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | composite: Morita, Carayol, Kottwitz, Buzzard; not statable in published form today (curve-split §3.6) |
| H-120 | `ZInQ.Contrib.HodgeSplit.TateTwistInvariants` | `scratch/hodge-split/HodgeSplit.lean` L65 @ main | H-8, H-51, H-52 | **LEAF**; `ℂ_p(i)^{G_K} = 0` for `i ≠ 0` | hodge-split; field `tateTwistInvariants` of leaf-fold19; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Tate 1967 §3.3 Thm 2 (hodge-split §1) |
| H-121 | `ZInQ.Contrib.HodgeSplit.AxSenTate` | `scratch/hodge-split/HodgeSplit.lean` L75 @ main | H-8, H-51, H-52 | **LEAF**; `ℂ_p^{G_K} ⊆ K` | hodge-split; field `axSenTate` of leaf-fold19; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Tate 1967 §3.3 Thm 1; Sen 1969; Ax 1970 (hodge-split §1) |
| H-122 | `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` | `scratch/hodge-split/HodgeSplit.lean` L343 @ main | H-8 | **LEAF**; the Hodge–Tate decomposition of `ℂ_p ⊗ V_p(A)` | hodge-split; field `hodgeTateDecompAbVar` of leaf-fold19 | published form: Fontaine 1982; Faltings 1988 (hodge-split §1) |
| H-123 | `ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` | `scratch/hodge-split/HodgeSplit.lean` L1988 @ main | H-8 | **LEAF**; `Hom(V_p A, ℚ_p)` is de Rham | hodge-split; field `deRhamH1AbVarT` of leaf-fold19 | published form: Faltings 1989; Tsuji 1999; Scholze 2013 Cor. 1.8, Hom form (hodge-split §1) |
| H-125 | `ZInQ.Contrib.HodgeSplit.DSThm965` | `scratch/hodge-split/HodgeSplit.lean` L1106 @ main | H-10, H-22 | **LEAF**; `k ≥ 2`: the Galois representation of an eigenform and its Frobenius polynomials | hodge-split; field `dsThm965` of leaf-fold19 | published form: Diamond–Shurman Thm 9.6.5 (Deligne 1971; Shimura 1971 Thm 7.14) (hodge-split §1) |
| H-126 | `ZInQ.Contrib.HodgeSplit.DSThm966` | `scratch/hodge-split/HodgeSplit.lean` L1124 @ main | H-10, H-22 | **LEAF**; `k = 1`: the Artin representation of an eigenform | hodge-split; field `dsThm966` of leaf-fold19 | published form: Deligne–Serre 1974 Thm 4.1; Diamond–Shurman Thm 9.6.6 (hodge-split §1) |
| H-128 | `HDec.QMSplit.Yu.YuThm11` | `scratch/qm-split/YuLeaf.lean` L34 @ main | H-35 | **LEAF**; Yu's dichotomy for QM abelian surfaces, with the splitting clause | qm-split; field `yuThm11` of leaf-fold19 | published form: Yu 2013 Thm 1.1, case labels dropped (qm-split §1); gt-qm compiles the chain's four live uses, all at `(2, −3)` over `ℚ̄`, with `YuB6Alg` in place of it, which follows from the textbook fields `uniformizationLeafAll`, `gagaMorphism` and `mumfordTorsionAlgClosed` (`scratch/gt-qm/Reroute.lean`); not applied: no fold takes it yet |
| H-130 | `HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar` | `scratch/qm-split/STQM.lean` L66 @ main | H-86 | **LEAF**; a surface over `ℂ` with a degree-4 field in `End⁰` has a model over `ℚ̄` | qm-split; field `shimuraTaniyamaQbar` of leaf-fold19 | published form: Milne, CM notes §7; Shimura–Taniyama 1961 §12.4 print a number-field model (qm-split §4) |

### 4.7 Props open only in scenario F, introduced in r4 (9: 1 LEAF, 8 GLUE strict; 3 LEAF, 6 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4''''''''. Its form is the task
report's label, or my reading where the report's own text (docstring or review) names more than one source; the
pointer says which.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-89 | `MCRGlue.ProperCurveAF` | `scratch/mcr-glue/MCRGlue.lean` L4044 @ main | H-84 | GLUE (composite); L1: finite sets of points of a proper smooth curve over `ℤ_(p)` lie in an affine open | mcr-glue; in flight: mcr-quot (`quotientP1Coordinate`) | composite: Lichtenbaum 1968 Thm 2.8 with EGA II 4.5.4 (mcr-glue §3: composite of two results) |
| H-90 | `MCRGlue.FiniteQuotientExists` | `scratch/mcr-glue/MCRGlue.lean` L4057 @ main | H-84 | **LEAF**; L2: the quotient by a finite group of `ℤ_(p)`-automorphisms exists and is finite | mcr-glue; being attempted (cloud); in flight: mcr-quot (`quotientP1Coordinate`) | published form: SGA 1 Exp. V Prop. 1.8 and 1.1, special case (mcr-glue §3) |
| H-91 | `MCRGlue.TameQuotientSmooth` | `scratch/mcr-glue/MCRGlue.lean` L4072 @ main | H-84 | GLUE (composite); L3: a tame quotient of a proper smooth relative curve is proper and smooth | mcr-glue; in flight: mcr-quot (`quotientP1Coordinate`) | composite: SGA 1 Exp. V, Mumford AV §7 Thm 3, EGA IV 17.5.1 (mcr-glue §3: composite of three results) |
| H-92 | `MCRGlue.SmoothModelOfP1` | `scratch/mcr-glue/MCRGlue.lean` L4086 @ main | H-84 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); L4: a proper smooth `ℤ_(p)`-curve with generic fibre `P¹_ℚ` is `P¹_{ℤ_(p)}` | mcr-glue; in flight: mcr-quot (`quotientP1Coordinate`) | consequence of one theorem: Liu, AGAC §8.3, §10.1 (mcr-glue §3: STANDARD; reading) |
| H-93 | `MCRGlue.TameFixedPointsDisjoint` | `scratch/mcr-glue/MCRGlue.lean` L4100 @ main | H-84 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); L5: fixed points of a tame automorphism with distinct underlying points have disjoint closures | mcr-glue; in flight: mcr-quot (`quotientP1Coordinate`) | consequence of one theorem: Edixhoven 1992 Prop. 3.4 with finite étale over a DVR (mcr-glue §3: leaf consequence) |
| H-94 | `MCRGlue.TameInertiaCyclic` | `scratch/mcr-glue/MCRGlue.lean` L4119 @ main | H-84 | GLUE (composite); L6: a finite tame inertia group as in L5 is cyclic | mcr-glue; in flight: mcr-quot (`quotientP1Coordinate`) | composite: Serre, Local Fields IV §2 Cor. 1 of Prop. 7, with L5's source (mcr-glue §3: composite of two results) |
| H-95 | `HDec.PropTSRed.CoverModelOfHeckeN` | `ZInQKernel/OneProof/H/TailG.lean` L743 @ main | H-84 | GLUE (project glue); the decomposition's own glue: a model of the Hecke cover of level `N` (gives `ModelYIrreducible` with T5) | mcr-quot; in flight: mcr-quot (`quotientP1Coordinate`) | project glue: open here: the chain derives it only through `HeckeNoVertRam`, downstream of the coordinate that mcr-quot feeds (mcr-quot §1); gap-triage (finding 3, compiled probe): not needed, since `ModelYIrreducible` is the chain's `HeckeIrreducible`, which follows from the field `deligneComponentsY3PrintedAb` (`scratch/gap-triage/GlueProbe.lean`, `MCRQuotNV.lean`); not applied, as the probe takes leaf-fold9's whole bundle `OpenAddedLeaves9` |
| H-96 | `MCRQuot.P1SchemeQ` | `scratch/mcr-quot/MCRQuot.lean` L8549 @ main | H-84 | GLUE (project glue); `P¹_ℚ` exists, is proper and smooth, and represents maps to `P¹` by charts | mcr-quot; in flight: mcr-quot (`quotientP1Coordinate`) | project glue: foundations: `Proj ℚ[X₀, X₁]` with its functor of points, not in Mathlib (mcr-quot §1) |
| H-97 | `MCRQuot.CMStabObj` | `scratch/mcr-quot/MCRQuot.lean` L7648 @ main | H-84 | GLUE (project glue); each CM class is fixed by a Hecke operation of order exactly 2 on classes (QM objects over `ℚ̄`) | mcr-quot; in flight: mcr-quot (`quotientP1Coordinate`) | project glue: object-level glue on CM points, no schemes (mcr-quot §1) |

### 4.8 Fields of leaf-fold9 introduced in r5 (1: 1 LEAF, 0 GLUE strict; 1 LEAF, 0 GLUE lenient)

The row left is a field of C4'''''''' that leaf-fold9 introduced, and the hypothesis of a compiled theorem in
reduct-split's `Reduction.lean` (`TailZ7`, verbatim); it is used in both scenarios since leaf-fold10 (r5: only in
scenario F). r5's other three rows here are gone: H-145 is restated on abelian schemes (route-a-fold), and H-146 and
H-147 are fields that scenario F replaces by their strictly henselian forms (§4.1). Form: kinds.tsv's, which the
integrator kept after the base review.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-148 | `ReductSplit.NeronSchemeModelExistsDVR` | `ZInQKernel/OneProof/H/TailZ7.lean` L238 @ main | H-4, H-106, H-108 | **LEAF**; Néron's existence theorem over a discrete valuation ring, scheme form | reduct-split; field `neronSchemeModelExistsDVR` of leaf-fold19 | published form: BLR §1.4 Thm 3 with §1.2 Def. 1 (reduct-split §2); kept a published form by the integrator after the base review (printed over an arbitrary DVR, reduct-glue §4; UNVERIFIED) |

### 4.9 Props open only in scenario F, introduced in r5 (2: 0 LEAF, 2 GLUE strict; 2 LEAF, 0 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4''''''''. Its form is the task
report's label, or my reading where the report's own text names more than one source or gives no label; the pointer
says which. Its H-150 is a field since leaf-fold13 and moved to §4.12.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-154 | `HDec.QMSplit.Moduli.ShimuraHolFamily` | `scratch/shimura-split/ShimuraFam.lean` L258 @ main | H-139 (from H-20) | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); one holomorphic family `φ : ℍ → Y₃(ℂ)` with the moduli clause; the step to every `π : Y₃ → P¹` is proved | shimura-split; in flight: gt-rayclass (`shimuraFamilyAb`) | consequence of one theorem: Shimura 1967 Main Thm I, through Deligne 1971 §4 for the `ℚ`-model (shimura-split §3.4 and its review §7); carries `R1fpProps`; with the field `mumfordRigidityCore` (H-170) a leaf on `R1fpProps` is equivalent to the same leaf on abelian schemes (r1univ-rigid's `…_iff_ab`), so r5's open check on this row rests on that one leaf; shimura-cft derives `shimuraFamilyAb` from Shimura's Main Theorem I in Deligne's adelic form (`ShimuraMainThmIDeligneY3Ab`, a consequence by its report and a composite by its review), which implies this row's leaf (`mainThmIY3_of_mainThmI` with c-to-printed's `shimuraHolFamily_of_mainThmI`), so scenario F keeps this one |
| H-157 | `ModularSplit.R17.CarayolRealization` | `scratch/modular-split/R17.lean` L127 @ main | H-21 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); some semisimple `ρ` attached to the newform has conductor exponent `v_p(N)` at every `p ≠ ℓ`; the transport to every attached `ρ` is proved | modular-split | consequence of one theorem: Carayol 1986 Thm (A) at his realization (audit), with Casselman's `a(π_p) = v_p(N)` and Ribet's irreducibility (modular-split §2: still a consequence) |

### 4.10 Fields of leaf-fold10 and leaf-fold11 introduced in r6 (5: 3 LEAF, 2 GLUE strict; 4 LEAF, 1 GLUE lenient)

Each row is a field of C4'''''''' that leaf-fold10 or leaf-fold11 introduced, and the hypothesis of a compiled theorem
in its file (`TailZ16`, `TailZ17`: route-a-fold; `TailZ19`: c-to-printed's printed leaves). Forms: kinds.tsv's, with
the integrator's convention for `deligneComponentsY3PrintedAb` (GLUE since r7, after shimura-cft's review). r8:
`gonzalezRotgerCountX6Ab` is replaced (gt-grcount), `blr_1_2_4` and `egaIV_8_10_5_openImm` are proved and
`raynaudKernelBound` is pruned (§4.1). leaf-fold10's other new fields are not rows: `neronLocalizesDVR` is proved
since leaf-fold11, and leaf-fold14 replaces the DVR fields.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-169 | `ShimuraGlue.DeligneComponentsY3PrintedAb` | `ZInQKernel/OneProof/H/TailZ17.lean` L54 @ main | H-155 (from H-59) | GLUE (composite); Deligne's theorem on the connected components of `Sh_K` in printed form, for `G = B^×`, `B = (2, −3 \| ℚ)`, at level `K₃`, over Mathlib's finite adeles, quaternion algebra and cyclotomic character, on abelian schemes (leaf-fold10 folds shimura-glue's printed leaf; route-a-fold restates it) | route-a-fold; field `deligneComponentsY3PrintedAb` of leaf-fold19 | composite: Deligne, Sém. Bourbaki 389 (1971) Thm 2.4 and §3; PSPM 33 (1979) 2.1.3, 2.6.3; Milne 2005 Thms 5.17, 13.6 (shimura-glue §2, §4; locators UNVERIFIED), specialized to one witness; GLUE by the integrator's ruling after shimura-cft's review (kinds.tsv, 11-14): it depends on whether one display states that the PEL moduli scheme with its uniformization is the canonical model at `B = (2, −3 \| ℚ)`, level `K₃` (Deligne 389 §5, Milne 2005 §14), and is otherwise Deligne's theorem with that identification |
| H-170 | `LeafQM.AV.R1UnivRigid.MumfordRigidityCore` | `ZInQKernel/OneProof/H/TailZ16.lean` L463 @ main | none (closes r5's open check on the rows stated on `R1fpProps`) | **LEAF**; a smooth proper geometrically connected family with a section whose field fibres are abelian varieties carries a group law with that identity, and maps that fix the identity are homomorphisms | route-a-fold; field `mumfordRigidityCore` of leaf-fold19; in flight: gt-rigidity (`mumfordRigidityCore`); cloud batch 3 (W20, on MumfordGroupLaw, which replaces this field in leaf-fold23): briefed 2026-11-15, not yet claimed on the issue (claims.tsv) | published form: Mumford, GIT Thm 6.14 with Cor. 6.4 (r1univ-rigid §5.2; numbers UNVERIFIED); counted LEAF by leaf-fold11 and the integrator; r1univ-rigid calls it a consequence of printed statements |
| H-172 | `CToPrinted.FaltingsLemma5Printed` | `ZInQKernel/OneProof/H/TailZ19.lean` L387 @ main | H-167 (through `faltingsLemma5BC`) | **LEAF**; Faltings' Lemma 5, the identity with the correction term `[K:ℚ]⁻¹ log #s*Ω¹_{G/S}` | c-to-printed; field `faltingsLemma5Printed` of leaf-fold19 | published form: Faltings, Invent. Math. 73 (1983) Lemma 5 (c-to-printed §3; not read, so LEAF and flagged) |
| H-174 | `CToPrinted.SGA3_VIB_3_10` | `ZInQKernel/OneProof/H/TailZ19.lean` L199 @ main | H-166 (through `semistableNeronBaseChange`) | **LEAF**; for a smooth group scheme over a base, the union of the identity components of the fibres is open | c-to-printed; field `sga3_VIB_3_10` of leaf-fold19; in flight: gt-sga3 (`sga3_VIB_3_10`); cloud batch 3 (W19): briefed 2026-11-15, not yet claimed on the issue (claims.tsv) | published form: SGA 3 I Exp. VI_B Thm 3.10 (c-to-printed §4; number unconfirmed, flagged) |
| H-175 | `CToPrinted.SGA7_IX_3_3` | `ZInQKernel/OneProof/H/TailZ19.lean` L249 @ main | H-165 (through `semistableNeronBaseChange`) | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); SGA 7 IX 3.3, second assertion: for semistable reduction the identity component of the Néron model base changes, `N⁰ ⊗ R' ≅ N'⁰` | c-to-printed; field `sga7_IX_3_3` of leaf-fold19; in flight: gt-sga7 (`sga7_IX_3_3`); sh-printed2 (`sga7_IX_3_3`) | consequence of one theorem: SGA 7 I Exp. IX 3.3 (c-to-printed §4; UNVERIFIED); a consequence by the integrator's convention, as the SGA 7 IX DVR fields (the base ring may be printed strictly henselian) |

### 4.11 Props open only in scenario F, introduced in r6 (3: 0 LEAF, 3 GLUE strict; 2 LEAF, 1 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4'''''''' (§4.1). Its form is the
task report's label, or my reading where the report gives none or names more than one source (the pointer says
"reading"). r8: H-182 is a field since leaf-fold14 (§4.14), and H-185 and H-187 are replaced (§4.1); H-188 stays a
consequence by the base review. r6's branch heads are merged (w66), so the rows point at main; r6's rows for x6-glue's
leaves are replaced by fields (§4.12).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-181 | `CToPrinted2.KatoRealizationCohSS` | `scratch/c-to-printed2/CToPrinted2.lean` L618 @ main | H-158 (from H-127) | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); some semisimple `ρ` attached to the newform, with Kato's Hodge–Tate weights; with the fields `tateTwistInvariants` and `axSenTate` it gives `eigenformHTNew`, and is equivalent to it over the bundle | c-to-printed2 | consequence of one theorem: Kato, Astérisque 295 (2004) §8.3 and §§9.2-9.4 at his `V_{F_λ}(f)`, quantified existentially (c-to-printed2 §2.1; locators read by locators.md row R13): the report's label, a consequence |
| H-188 | `ReductGlue.StrictHenselizationInside` | `ZInQKernel/OneProof/H/TailZ14.lean` L2137 @ main | H-147 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); inside an algebraic closure at a place `w`: the inertia field, on which `w` is a strict henselization of `O` | reduct-glue; in flight: gt-unip (`semistableUnipotent`) | consequence of one theorem: Stacks 0BSK-0BSL; Raynaud, Anneaux locaux henséliens, VIII; BLR §1.2 Prop. 2 (reduct-glue §2; UNVERIFIED); review v1 reads it as a consequence; sh-route proves its characteristic-0 form from `NeronBaseChangeSH`, not applied; it does not follow from `StrictHenselizationPair` (it asks for the inertia field inside a fixed algebraic closure; leaf-fold14 §1) |
| H-190 | `HDec.HSyn.G0Split.ThetaPt.ThetaGlue.LinYangThetaCurve` | `scratch/theta-glue/ThetaGlue.lean` L593 @ main | H-133, H-134 (from H-44) | GLUE (composite); along the explicit QM curve `τ ↦ Ω(τ)`: `ψ₄ψ₆ = 2¹²3⁵χ₁₀` and `ψ₄³ + ψ₆² = 2¹²3⁶χ₁₂` in Igusa's theta expressions | theta-glue; in flight: linyang-printed (`LinYangThetaCurve`) | composite: Lin–Yang, Math. Z. 295 (2020), Example 29 with eqs. (13)-(14), after eliminating `j` (so weaker than the print), with Igusa's theta expressions (Amer. J. Math. 89 (1967) §4); locators UNVERIFIED; numerically VERIFIED (80 digits at 12 points); theta-glue's label: a composite; igusa-alg proves `IgusaAlg 5` to `9`, so the route rests on this leaf alone (`qmThetaSymmetricCurve_of_linYang`) |

### 4.12 Fields of leaf-fold13 introduced in r7 (5: 4 LEAF, 1 GLUE strict; 5 LEAF, 0 GLUE lenient)

Each row is a field of C4'''''''' that leaf-fold13 introduced (x6-fold), and the hypothesis of a compiled theorem in
`TailZ20`-`TailZ22`. Four restate x6-glue's leaves on abelian schemes (r6's rows H-142, H-177, H-178, H-179); H-150
keeps its row from r5 (until r6 open only in scenario F). Forms: kinds.tsv's. r8: H-195 is replaced by gt-elkies's
leaf (H-206, §4.14).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-150 | `HDec.QMSplit.Moduli.GeomConnOfAlgClosure` | `ZInQKernel/OneProof/H/TailZ20.lean` L1842 @ main | H-140 (from H-1) | **LEAF**; a proper `X → Spec k` with `X ×_k k̄` connected is geometrically connected | shimura-split; field `geomConnOfAlgClosure` of leaf-fold19; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: EGA IV₂ 4.5.1-4.5.2; Stacks 0389, weakened by `IsProper` and characteristic 0 (shimura-split §2, §3.2) |
| H-192 | `ShimuraGlue.DeligneComponentsX6PrintedAb` | `ZInQKernel/OneProof/H/TailZ22.lean` L33 @ main | H-177 | **LEAF**; Deligne's theorem on `π₀` in printed form at level `𝒪̂^×`, on one coarse witness `X₆`, on abelian schemes; with `ℚ^×_{>0}\𝔸_f^×/nrd(𝒪̂^×) = 1` (compiled) it gives `DeligneComponentsX6` | x6-fold; field `deligneComponentsX6PrintedAb` of leaf-fold19 | published form: Deligne, Sém. Bourbaki 389 (1971) Thm 2.4 and §3; PSPM 33 (1979) 2.1.3, 2.6.3 (shimura-glue §2, x6-glue §2; UNVERIFIED), at level `𝒪̂^×`; x6-fold restates it on abelian schemes (`R1fpPropsAb`, the printed fine-moduli problem; `deligneComponentsX6Printed_iff_ab` with the field `mumfordRigidityCore`, H-170) |
| H-193 | `HDec.QMSplit.Moduli.BabaGranathRationalAb` | `ZInQKernel/OneProof/H/TailZ22.lean` L91 @ main | H-178 | **LEAF**; Baba–Granath's fibre clause on abelian schemes: three distinct rational points that are exactly the images of `CM(−4)`, `CM(−3)`, `CM(−24)`; no `j`-normalization (the Möbius glue is proved) | x6-fold; field `babaGranathRationalAb` of leaf-fold19; in flight: gt-x6facts (`babaGranathRationalAb`) | published form: Baba–Granath 2008 Thm 2.1 and Lemma 3.1 (audit YES), with the CM assignment read from their §3.1 table, an UNVERIFIED reading (kinds.tsv flags it; shimura-glue §5.3, x6-glue §4); x6-fold restates it on abelian schemes (`R1fpPropsAb`, the printed fine-moduli problem; `babaGranathRational_iff_ab` with the field `mumfordRigidityCore`, H-170) |
| H-194 | `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` | `ZInQKernel/OneProof/H/TailZ22.lean` L64 @ main | H-142 | **LEAF**; some coarse witness, on abelian schemes, has the residue fields of CM points (`R5ptProps`) | x6-fold; field `gonzalezRotgerX6Ab` of leaf-fold19 | published form: González–Rotger 2006 Thm 5.12 (qm-glue §4.2; UNVERIFIED); x6-fold restates it on abelian schemes (`R1fpPropsAb`, the printed fine-moduli problem; `gonzalezRotgerX6_iff_ab` with the field `mumfordRigidityCore`, H-170) |
| H-196 | `ShimuraGlue.Ray.RayClassCMAb` | `ZInQKernel/OneProof/H/TailZ22.lean` L48 @ main | H-179 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); on one fine witness, on abelian schemes, the residue field of a CM point by the maximal order of `ℚ(i)`, `ℚ(ζ₃)` or `ℚ(√−6)` embeds into Tau Ceti's ray class field of conductor 3 | x6-fold; field `rayClassCMAb` of leaf-fold19; in flight: rayclass-cft (`rayClassCMAb`); gt-rayclass (`rayClassCMAb`) | consequence of one theorem: Shimura 1967 Main Thm I and Deligne 1971 §3, ray-class form (shimura-glue §5.1, x6-glue §5.1; locators UNVERIFIED); stronger than `ReciprocityCanonical`, weaker than the printed reciprocity law; x6-fold restates it on abelian schemes (`R1fpPropsAb`, the printed fine-moduli problem; `rayClassCM_iff_ab` with the field `mumfordRigidityCore`, H-170); gap-triage reads `R1recProps`, the clause it serves, as probably unread (finding 8, SPECULATIVE): if so, the field drops |

### 4.13 Props open only in scenario F, introduced in r7 (2: 1 LEAF, 1 GLUE strict; 1 LEAF, 1 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4'''''''' (§4.1): unipotent-b's
printed SGA 7 IX 3.5 and its glue. Its form is the task report's label. r8: t09-pic's four leaves are fields since
leaf-fold14 (§4.14).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-197 | `UnipotentB.SemistableUnipotentPrintedGen` | `scratch/unipotent-b/UnipotentB.lean` L275 @ main | H-184 (from H-147) | **LEAF**; SGA 7 IX 3.5 as printed, over every field: `O` strictly henselian, `Ω = K^s`, semistability over `k(s)`, `ℓ` invertible in `O`; semistable iff inertia acts unipotently, and then `(σ - 1)(τ - 1) = 0` on `T_ℓ` | unipotent-b; in flight: gt-unip (`semistableUnipotent`) | published form: SGA 7 I Exp. IX Prop. 3.5 (unipotent-b §2; wording UNVERIFIED, no network): the printed strictly henselian base, so the base reading of the four DVR fields does not arise here |
| H-198 | `UnipotentB.SemiAbelianDescendsSepClosed` | `scratch/unipotent-b/UnipotentB.lean` L298 @ main | H-184 (from H-147) | GLUE (project glue); for a DVR with separably closed residue field `k`, a group model whose special fibre over `k̄` has semi-abelian identity component has one over `k` already | unipotent-b; in flight: gt-unip (`semistableUnipotent`) | project glue: unipotent-b's named glue (§3.3: maximal tori over `k`, SGA 3 XIV 1.1; properness descends, EGA IV₂ 2.7.1; UNVERIFIED); proved when `k` is perfect, so needed only for imperfect residue fields; not in Mathlib |

### 4.14 Fields of leaf-fold14 to leaf-fold19 introduced in r8 (9: 7 LEAF, 2 GLUE strict; 8 LEAF, 1 GLUE lenient)

Each row is a field of C4'''''''' that leaf-fold14 to leaf-fold19 introduced, and the hypothesis of a compiled theorem
in its file: leaf-fold14's fold 1, reduct-b's Route B-cp (H-182, H-203; the third, `strictHenselizationPair`, is
replaced by gt-shpair's H-205 in leaf-fold18), and fold 2, t09-pic's four leaves (H-199 to H-202); gt-grcount's H-204
(leaf-fold17); gt-elkies's H-206 (leaf-fold18). The five that r7 listed as open only in scenario F keep their rows.
Forms: kinds.tsv's, with the integrator's convention for `weilPairingMumford` (a composite in the strictest reading);
r7 read H-201 and H-202 as consequences.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-182 | `ReductGlue.RaynaudSemistableSH` | `ZInQKernel/OneProof/H/TailZ14.lean` L1105 @ main | H-160 | **LEAF**; Raynaud's criterion over a strictly henselian DVR; with `strictHenselizationPair` (from H-205) and `mulEtaleAbelianScheme` (proved since leaf-fold19) it gives the general-DVR form | reduct-glue; field `raynaudSemistableSH` of leaf-fold19 (since leaf-fold14) | published form: SGA 7 I Exp. IX Prop. 4.7 over a strictly henselian DVR (reduct-glue §4; locator UNVERIFIED); kinds.tsv: a reading risk (the print may assume an algebraically closed residue field, reduct-b §5), rated low by the next-fold review |
| H-199 | `T09Pic.PicRepresentableAbVar` | `ZInQKernel/OneProof/H/TailZ24.lean` L289 @ main | H-53 | **LEAF**; the relative Picard fppf sheaf of an abelian variety is representable | t09-pic; field `picRepresentableAbVar` of leaf-fold19 (since leaf-fold14); cloud batch 3 (W22): briefed 2026-11-15, not yet claimed on the issue (claims.tsv) | published form: Murre (1964), Oort (1962); FGA Exp. 232 Thm 3.1; Kleiman, The Picard scheme, Thm 9.4.8 with Thm 9.2.5 (t09-pic §3; UNVERIFIED) |
| H-200 | `T09Pic.PicZeroAbVar` | `ZInQKernel/OneProof/H/TailZ24.lean` L302 @ main | H-53 | **LEAF**; the identity component of the Picard scheme is an abelian variety, by an open immersion that is a homomorphism | t09-pic; field `picZeroAbVar` of leaf-fold19 (since leaf-fold14); cloud batch 3 (W22): briefed 2026-11-15, not yet claimed on the issue (claims.tsv) | published form: Mumford, Abelian Varieties §13; Kleiman Prop. 9.5.1 and 9.5.3; Milne 1986 §§9-10 (t09-pic §3; UNVERIFIED) |
| H-201 | `T09Pic.PhiAmpleIsogeny` | `ZInQKernel/OneProof/H/TailZ24.lean` L366 @ main | H-53 | **LEAF**; for an ample `L`, the homomorphism `λ` with `λ ≫ ι = φ_L` is finite and surjective | t09-pic; field `phiAmpleIsogeny` of leaf-fold19 (since leaf-fold14); cloud batch 3 (W22): briefed 2026-11-15, not yet claimed on the issue (claims.tsv) | published form: Mumford §6 Application 1 and §8 Thm 1 (t09-pic §3; UNVERIFIED), the kind in kinds.tsv, flagged: finiteness over a non-closed `K` descends from `K̄`, and Mumford states Application 1 for effective `D` (r7 read it as a consequence) |
| H-202 | `T09Pic.WeilPairingMumford` | `ZInQKernel/OneProof/H/TailZ24.lean` L708 @ main | H-53 | GLUE (composite); for `n` invertible in `K`, a perfect, `G_K`-equivariant, compatible pairing `A[n] × Pic⁰[n] → μ_n` with Mumford's values (`weilScalar`), adjoint for the genuine `f^∨`, with `e_n(x, λ_L x) = 1` for ample `L` | t09-pic; field `weilPairingMumford` of leaf-fold19 (since leaf-fold14); cloud batch 3 (W22): briefed 2026-11-15, not yet claimed on the issue (claims.tsv) | composite: Mumford §20 and §23; Milne 1986 Lemma 16.2(c) and §16 (t09-pic §3; UNVERIFIED); kinds.tsv: published kind, LEAF in its strict column, GLUE in its strictest (one leaf bundling several printed properties of `e_n`), so a composite by the integrator's convention; t09-pic's label: a consequence of the print; it also compiles the split into one printed property per leaf (L4a-L4f, `t09SymmIsogenyExists_of_split`) |
| H-203 | `ReductB.SemistablePersistsSHcp` | `ZInQKernel/OneProof/H/TailZ23.lean` L315 @ main | H-185 | **LEAF**; SGA 7 IX 3.3, first assertion (semistable reduction persists in finite extensions), over a strictly henselian DVR of a field of characteristic 0 with perfect (hence algebraically closed) residue field; a specialization of `SemistablePersistsSH`; with `strictHenselizationPair` it gives SS1 and SS3 at number fields (`ReductB.ss1_ss3_of_cp`) | reduct-b; field `semistablePersistsSHcp` of leaf-fold19 (since leaf-fold14) | published form: SGA 7 I Exp. IX Prop. 3.3, first assertion, restricted to characteristic 0 and an algebraically closed residue field (number UNVERIFIED; reduct-b's Route B-cp); kinds.tsv: a specialization of every reading of the print, rated (a) by the next-fold review |
| H-204 | `GRCountX6.GonzalezRotgerProp56X6` | `ZInQKernel/Contrib/OneProof/GRCountX6.lean` L72 @ main | H-168 | **LEAF**; González–Rotger's count on every witness of the moduli description of `X₀(6,1)`, with no existence claim: the CM points by an order `R` that occurs as some `End_𝒪(A)` number `2^{inertCount6 k}·#Pic(R)`; with the field `gonzalezRotgerX6Ab` it gives `gonzalezRotgerCountX6Ab` | gt-grcount; field `gonzalezRotgerProp56X6` of leaf-fold19 (since leaf-fold17) | published form: González–Rotger, J. Math. Soc. Japan 58 (2006) Prop. 5.6, p. 943 (read by the locator audit), at `(D, N) = (6, 1)` (gt-grcount; statement review 11-14, two lenses: faithful); kinds.tsv flags that `D(R)`, the product of the `p ∣ D` with `(R/p) = −1`, is to be confirmed against the paper |
| H-205 | `GapSHPair.NeronBaseChangeStrictHenselization` | `ZInQKernel/Contrib/OneProof/StrictHenselizationPair.lean` L1527 @ main | H-187 | **LEAF**; Néron models commute with strict henselization: for a DVR `O` and an unramified strictly henselian extension `O₁` with `K₁/K` separable (`IsSHSep`, which pins `O₁` as `O^sh` in every characteristic), the base change of a Néron model is a Néron model; gt-shpair proves `StrictHenselizationPair` from it | gt-shpair; field `neronBaseChangeStrictHenselization` of leaf-fold19 (since leaf-fold18); cloud batch 3 (W21): briefed 2026-11-15, not yet claimed on the issue (claims.tsv) | published form: Bosch–Lütkebohmert–Raynaud, Néron models, §1.2 Prop. 2 (gt-shpair; locator UNVERIFIED; statement review 11-14, two lenses: published form); a specialization of the chain's `NeronBaseChangeUnramifiedDVR` |
| H-206 | `HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted` | `ZInQKernel/Contrib/OneProof/ElkiesX6Star.lean` L67 @ main | H-195 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); Elkies' coordinate `t` on `X*(6) = X₆/W` on one witness of the moduli clause: `t(x) = t(x′)` iff `x′ = w(x)` for some `w ∈ W = {1, w₂, w₃, w₆}`, with `W` defined by its moduli action; the CM values `t = 0, 1, ∞` at discriminants −24, −4, −3; the two charts of `X₆` over the `t`-line; gt-elkies proves the moduli step (`orbit_iff_twist`) | gt-elkies; field `elkiesX6StarPrinted` of leaf-fold19 (since leaf-fold18) | consequence of one theorem: Elkies, ANTS-III (1998) §3 on `X*(6)` (section, display and the `0/∞` orientation UNVERIFIED); the statement review (11-14, two lenses) reads it as a consequence, the `ℚ̄`-point form of the printed coordinate statement, and the integrator ruled it GLUE under the strict rule |

### 4.15 Bundle fields never projected, and the prune (not on the list)

r8: sem-prune (`docs/research/sem-prune.md`) removes the two fields that gap-triage found used only syntactically,
`bdRInvariants` (H-124) and `raynaudKernelBound` (H-173), from every bundle generation, after re-proving their
consumers without them (`G0Galois.G9GlueNoT23`; `HeightSplit.FaltingsLemma5BCLower` from the field
`faltingsLemma5Printed`). Its PruneScan finds no unused field before and after, and `chain.py`'s `UNUSED` is empty.

Until r7:
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

### 4.16 Statement reviews of the leaves (leaf-review-a, leaf-review-b, leafq-check, the r4 to r8 tasks)

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

The r8 tasks and folds checked their new leaves with an AI statement review (two lenses, from memory, 11-14; recorded
in kinds.tsv's `rated_by`); none had network access, so every locator is UNVERIFIED. `GonzalezRotgerProp56X6` is
faithful, with `D(R)` to be confirmed against the paper; `NeronBaseChangeStrictHenselization` is a published form;
`ElkiesX6StarPrinted` is a consequence (the `ℚ̄`-point form of Elkies' coordinate statement), GLUE by the integrator's
ruling. Of the top's two new hypotheses, `X0ModuliGalois` is a consequence, and `ShimuraMainCM` cites the Artin-map
lemmas that fix its normalization. leaf-fold14's next-fold review rates `raynaudSemistableSH` and
`semistablePersistsSHcp` (a): kinds.tsv calls the first's reading risk (the print may assume an algebraically closed
residue field) low and the second a specialization of every reading of the print. t09-pic's four leaves are pending a
review (one model review, no errors), and kinds.tsv counts `weilPairingMumford` a composite in its strictest reading.
gt-valence's proof of the valence formula settles its statement: the volume is Mathlib's invariant measure, so it is
the genuine formula, neither vacuous nor stronger than its source.

## 5. Completeness check

### 5.1 Scenario A (compiled composite)

`python3 scratch/frontier/chain.py A` (from the repository root): 0 signature mismatches; 65 open nodes = the 30 + 13
+ 14 + 1 = 58 fields of C4'''''''''s four bundles (each expanded from the structure as read at main) plus the 7 TYZ
and GZ hypotheses of the top: the hypothesis list of the composite of C2, T0 with T0' and B8, and C4'''''''', all of
them used (§4.15). With kinds.tsv's forms (strictest reading, and its `frozenTarget` rows for the top): 47 LEAF and 18
GLUE strict, 55 and 10 lenient; with `weilPairingMumford` published (kinds.tsv's strict column): 48 LEAF and 17 GLUE
strict. `chain.py onep`: its hypotheses are scenario A's (the four bundles and the seven top Props); the bundles'
fields are the 58 field rows of `kinds.tsv`, with the names and type heads of the build's `open-statements.json`,
whose seven other hypotheses have scenario A's heads.

### 5.2 Scenario F (frontier)

`python3 scratch/frontier/chain.py F`: 0 signature mismatches over 198 theorem edges in the file (27 followed on the
route, among them 1 transfer along an equivalence and 1 consumer replacement; no modus-ponens step is followed); 75
open nodes = the 75 of §0 (no never-projected field is left). Where a followed edge's file is not the H base, the
check compares the Prop it proves with the one the route uses (`defcheck`):
- `CoordinateNormalization`: identical.
- `CoordinateFromSections`: identical (vs scratch/mcr-glue/MCRGlue.lean, which takes it).
- `TorsionStructure`: the kernel's own constant (ZInQKernel/HDecomp/Objects.lean), which OneProof/H imports.
- `FibreAutTame`: identical.
- `CurveBijIso`: identical.
- `CMSectionsDisjoint`: identical (vs scratch/mcr-glue/MCRGlue.lean, which takes it).
- `GenericQuotientP1`: identical.
- `QMThetaSymmetricCurve`: identical (vs scratch/theta-split/ThetaUse.lean, which takes it).
- `ThetaEightSquare`: identical (vs scratch/theta-split/ThetaUse.lean, which takes it).
The F-only edges in library files outside OneProof/H (shimura-split, modular-split, c-to-printed2, unipotent-b, fork
PR #19) prove the library's own constants: each file imports ZInQKernel modules, has no definition of the Prop it
proves (or only a copy for an `rfl` check), and imports the module that defines it, which `OneProof/Main.lean` imports
too (`worldcheck`):
- `SemistableUnipotent` (`scratch/unipotent-b/UnipotentB.lean`): defined in `ZInQKernel/OneProof/H/TailZ7.lean`.
- `MulEtaleAbelianScheme` (`ZInQKernel/Contrib/OneProof/MulEtale.lean`): defined in `ZInQKernel/OneProof/H/TailQ.lean`.
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
that takes it and has its own copy (9 comparisons; 1 more edge imports the Prop instead).
The pairwise checks of r2 still pass. The eight kernel leaf copies that the flat files carried are gone: OneProof/H
imports `ZInQKernel/HDecomp/Objects.lean` itself. mcr-quot's and shimura-split's T5 is the kernel's
`ObjBridge.TorsionStructure` or `PkgI2.TorsionStructure.{0}`, which `Objects.lean` proves equal by `Iff.rfl`
(`torsionStructure_iff`).

`python3 scratch/frontier/chain.py doc` compares the rows `Z-n`, `T-n`, `H-n` with the scenario-F open set: 75 rows
with 75 distinct heads, equal to the open set.

What the script does not check: that the edges compose in one Lean environment; argument instantiation (for example
`heckeVertWitness_of_leaves5` takes `R1R2fp`, extracted from `r1r2` by `Classical.choice`); section variables that a
theorem takes through `include` (none on the route since qm-glue replaced qm-split's `qmHauptmodulBase3_of_O1`); and
the defs that a Prop's def mentions (only the top-level def text is compared).

## 6. Integration state

### 6.1 Composites that exist
- **`ZInQ.OneProof.frozenTarget`** (main; leaf-fold19's bundles since 11-15; B8 since leaf-fold17; T0' since w59):
  scenario A as one library theorem (§1).
- **C4'''''''', leaf-fold19** (c2ad4181, over leaf-fold18 3782dac8, leaf-fold17 be8511f3, leaf-fold16 a454ad64,
  leaf-fold15 63205204, sem-prune 2b486d04 and leaf-fold14 97579a97): 30 + 13 + 14 + 1 fields inside OneProof
  (`TailZ23`-`TailZ32` over leaf-fold13's `TailZ20`-`TailZ22`, leaf-fold11's `TailZ16`-`TailZ19` and
  `OneProof/Genus/*`, leaf-fold10's `TailZ10`-`TailZ15`, leaf-fold9's `TailZ5`-`TailZ9`, leaf-fold8's `TailY`-`TailZ4`
  and leaf-fold7's `TailP`-`TailX`); the contributions it folds are in `ZInQKernel/Contrib/OneProof/`; lake build and
  axioms REPORTED.
- **The top in the kernel**: C2 (atkin-li) and tyz-chain's T0, with T0' (tyz-split) in `OneProof/TYZSplit.lean` and B8
  (gt-ringclass) in `Contrib/OneProof/RingClassLattice.lean`.
- **The contributor and crowd kits** (contrib-kit 46afc732, w66; crowd kit 1c791eb1): `docs/one-proof/OPEN.md` and
  `pages-wanted.md`, generated from the build's `open-statements.json`, `kinds.tsv` (with packets, labels, tiers and
  flag classes), `claims.tsv` (with public holders), `reviews.tsv`, `credits.tsv` and `issues.json`;
  `ZInQKernel/OneProof/Discharges.lean`, whose `#discharges` names the hypotheses of `frozenTarget` that a
  contribution proves; and `scripts/one_proof/autofold.py`, which writes the fold that removes them and refuses a rise
  of either GLUE count.
- Superseded: C4''''''' (leaf-fold13), C4'''''' (leaf-fold11), C4''''' (leaf-fold9), C4'''' (leaf-fold8), C4'''
  (leaf-fold6), C4'' (leaf-fold5), C4' (leaf-fold4), C4 (assemble-port) and the variants listed in r2.

### 6.2 What folding scenario F into C4'''''''' needs
leaf-fold7 to leaf-fold19 take a fold only if neither GLUE count rises and the fold lowers the strict GLUE count or
replaces a consequence or composite by published-form leaves (leaf-fold9 §5; `autofold.py` refuses a rise). With this
report's forms (SPECULATIVE until compiled):
- unipotent-b: the consequence `semistableUnipotent` goes, the published `SemistableUnipotentPrintedGen`, the glue
  `SemiAbelianDescendsSepClosed` and the consequence `StrictHenselizationInside` come (`mulEtaleAbelianScheme` is
  proved since leaf-fold19): both GLUE counts +1, so the rule keeps it out (leaf-fold14 §1); gt-unip, after main,
  reports a route with no glue;
- igusa-alg with theta-split: the composite `thetaRatiosAlgebraic` → the composite `LinYangThetaCurve`: neutral, with
  every closed identity proved; linyang-printed, after main, reduces the leaf to two printed leaves;
- modular-split (`r17` → `CarayolRealization`) and c-to-printed2 (`eigenformHTNew` → `KatoRealizationCohSS`): neutral
  (consequences both); shimura-split (`shimuraFamilyAb` → `ShimuraHolFamily`): neutral; mcr-glue and mcr-quot
  (`quotientP1Coordinate` → nine Props, three of them project glue): both GLUE counts rise;
- in flight on fields: rayclass-cft and gt-rayclass (`rayClassCMAb`, and gt-rayclass also `shimuraFamilyAb`),
  gt-rigidity (`mumfordRigidityCore`), gt-sga3 (`sga3_VIB_3_10`), gt-sga7 and sh-printed2 (`sga7_IX_3_3`), gt-x6facts
  (`babaGranathRationalAb`); shimura-cft's leaf for `shimuraFamilyAb` awaits a rating.

### 6.3 The library theorem
`ZInQ.OneProof.frozenTarget` has exactly the hypotheses of scenario A, and its proof uses all of them. Since
leaf-fold17 its TYZ hypothesis `hS` is replaced by `hCM` and `hX` (B8). Each F edge removes or replaces a field once
folded.

## 7. Findings

**Refresh r8 (2026-11-15).**

1. **Nine rows proved, two pruned, four replaced** (§0, §4.1). The 4 new rows are 3 published forms and 1 consequence
   of one theorem, and five rows that were open only in scenario F are fields now. The total goes from 86 to 75, the
   strict count from 54/32 to 49/26 and the lenient count from 68/18 to 59/16.
2. **Scenario A is one compiled theorem** on main, `ZInQ.OneProof.frozenTarget`, now over leaf-fold19: 65 hypotheses,
   all used. Its 58 fields are 44 LEAF and 14 GLUE strict by the integrator's table, as OPEN.md's count line says (45
   and 13 with `weilPairingMumford` published); with the top, 47 LEAF and 18 GLUE strict, 55 and 10 lenient. `chain.py
   onep` reads its hypotheses from `Main.lean` and finds scenario A's, and the bundles and the top agree with
   `kinds.tsv` and the build's `open-statements.json`.
3. **The CM hypothesis rests on two printed leaves**: gt-ringclass proves `RingClassLattice`, so the library theorem
   takes `ShimuraMainCM` and `X0ModuliGalois` (T-15, T-16) in place of `hS`, and tyz-split's and t5-glue's splits are
   off the route.
4. **Three of the four SGA 7 IX DVR fields are gone from the library theorem**: leaf-fold14 folds reduct-b's Route
   B-cp, so the strictly henselian `raynaudSemistableSH` and the restricted `semistablePersistsSHcp` are fields in
   their place, and gt-shpair proves the strict-henselization pair from BLR §1.2 Prop. 2 in every characteristic; the
   fourth, `semistableUnipotent`, stays a field.
5. **Contributions fold mechanically**: since gt-ega, the integrator's `autofold.py` writes each fold (the next bundle
   generation, its conversion, the top, `kinds.tsv`, `claims.tsv`), and refuses a rise of either GLUE count. sem-prune
   removes the two fields that gap-triage found used only syntactically.
6. **One field table for the whole theorem**: kinds.tsv's rows with bundle `frozenTarget` give the forms of the seven
   TYZ and GZ hypotheses, and they agree with this report's rows (§2.2, §3.2).
7. **claims.tsv** (crowd kit): the cloud claims are batch and round labels with public holders; it still lists
   unipotent-b and igusa-alg as in progress, merged in w66 and not folded.
8. **Nine branches after main** (gt-rayclass, gt-rigidity, gt-sga3, gt-sga7, gt-unip, gt-x6facts, rayclass-cft,
   linyang-printed, sh-printed2) report reductions of fields on the list (§0); this report does not use them until
   they are merged.
9. **Project glue** is 4 Props: `CMStabObj`, `CoverModelOfHeckeN`, `P1SchemeQ`, `SemiAbelianDescendsSepClosed`.
10. **chain.py**: the H base is leaf-fold19 (bundles in `TailZ29`, `TailZ32`, `TailZ31`, `TailX`); B8 is an edge of
   both scenarios; fork PR #19's proof of `mulEtaleAbelianScheme` is an F edge, since unipotent-b's split still takes
   it; `onep` compares the top with kinds.tsv's `frozenTarget` rows through the build's JSON.

**Refresh r7** (unchanged):

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

## 8. Tasks (snapshot 2026-11-15 04:33 PST; heads in `scratch/frontier/refs.txt`)

Finished, with results used in r8: leaf-fold14 (97579a97) with reduct-b (85495b37) and t09-pic (3d0f47a8); sem-prune
(2b486d04); leaf-fold15 (63205204) with gt-ega (cf8e5042); leaf-fold16 (a454ad64) with gt-blr (bca6c158), gt-gamma
(57264686), gt-theta (e32311e5); leaf-fold17 (be8511f3) with gt-ringclass (06f03bd4) and gt-grcount (77774f85);
leaf-fold18 (3782dac8) with gt-shpair (00bfe84a), gt-elkies (0f83a86a), gt-qm (1509a623), gt-valence (36d94c0d);
leaf-fold19 (c2ad4181) with fork PR #19; the crowd kit (1c791eb1). After main, not used: gt-rayclass (28ec5c91),
gt-rigidity (762ea48b), gt-sga3 (deba22d7), gt-sga7 (70a16c4c), gt-unip (42e1af66), gt-x6facts (80631ed5),
rayclass-cft (7b27f1c3), linyang-printed (3bb5a828), sh-printed2 (ea486e30). Used in r7 and still applied by scenario
F: unipotent-b (24c44f3d), igusa-alg (c9360203); read, not applied: shimura-cft (c1f76fc2), sh-route, gap-triage
(heads in the r7 section of `refs.txt`). Used in r6 and compiled inside C4'''''''' or applied by scenario F:
leaf-fold11, leaf-fold10, the prune, genus-fold, route-a-fold, shimura-glue, reduct-glue, dimjac-glue, theta-split,
genus-route, r1univ-rigid, theta-glue, c-to-printed2, t5-glue, x6-glue. Used in r5: leaf-fold9, shimura-split,
reduct-split, modular-split and tyz-split's statement review. Used in r4: leaf-fold8, mcr-quot, coarse-factor,
cloud-w07 (fork PR #11), leaf-fold7, height-glue, qm-glue, leaf-fold6, mcr-glue, av-glue, av-split, height-split,
curve-split, hodge-split, qm-split, tyz-split, fork PRs #6-#10. Used in r3: leaf-fold5, leafq-check, tyz-chain and the
r2 tasks. Read, not folded: leaf-review-a, leaf-review-b. Cloud claims: claims.tsv (§0).

Running tasks are on the fork's tracker issue #3.

gz-statements (Contrib modules `ZInQKernel/Contrib/GZStatements/{Weak,Level,Compat,Hensel}.lean` on its branch) proves
that the narrower `ZInQ.GZStatements.FHNonvanishingCd` and `GrossZagierHeegnerCd` (restricted to `C_d`, `d ≡ 5 mod 8`,
`D < −4`) are implied by Z-1, Z-2 and still give `ZInQ.FrozenTarget`
(`frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`); they could replace Z-1, Z-2
(both remain GLUE). Not adopted here (not compiled together with `TYZChain.lean`).

This branch is fork main 37391b11 plus this refresh.
