# frontier: every open Prop on the path to `ZInQ.FrozenTarget`

Task frontier, 2026-11-13; refreshes r2 to r9, 2026-11-14 to 11-16 (text checks only, no Lean run). Base of r9: fork
main 0e70c94e (leaf-fold29, with leaf-fold20 to leaf-fold29 and leaf-fold-hx over leaf-fold19, and r8 merged), on
wip/frontier-r9. Branch snapshot: the commits in `scratch/frontier/refs.txt` (r9 section: branch heads read 11-15
22:48 PST, main read 11-16 00:38 PST; main moved on to leaf-fold30 after the snapshot). Lean:
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

**The list.** If every proof and reduction that the branches had compiled by the snapshot (11-15 22:48 PST) is folded
in (scenario F, §5), the open Props on the path to `ZInQ.FrozenTarget` are **72: 49 LEAF and 23 GLUE** in the strict
count. If consequences of one theorem count as leaves, they are 60 LEAF and 12 GLUE.

**The library theorem.** `ZInQ.OneProof.frozenTarget` on main (scenario A) has 62 hypotheses, leaf-fold29's 51 fields
and the eleven TYZ and GZ Props, and its proof uses all of them (the folds' prune scans find no unused field). Its
fields and its eleven other hypotheses are classified in the integrator's table `docs/one-proof/kinds.tsv` (rendered
in `docs/one-proof/OPEN.md`), whose headline follows the integrator's strict convention: a leaf with a flagged
plausible weaker reading counts GLUE, a merely unread leaf stays LEAF, flagged. The fields are then **39 LEAF and 12
GLUE** in the strict count (the strictest reading, with `weilPairingMumford` and `dsThm965` composites), as OPEN.md's
count line says; 41 and 10 with those two published (the table's strict column); by kind alone, 42 published and 9
other. With the top: 47 LEAF and 15 GLUE strict, 53 and 9 lenient. Scenario F has more rows because it also applies
the splits that the folds leave out on purpose (each replaces one hypothesis by a leaf plus smaller statements,
leaf-fold9 §5), and it takes the `C_d` form of the top's Gross–Zagier hypotheses (Z7, §2.1).

| premise | open Props | strict LEAF | strict GLUE | lenient LEAF | lenient GLUE | table |
|---|---|---|---|---|---|---|
| GZ, `Literature.GrossZagier` | 5 | 1 | 4 | 5 | 0 | §2.2 |
| TYZ, `Literature.TYZThm35ReadingA` | 9 | 8 | 1 | 9 | 0 | §3.2 |
| H, `SixContactMin`: research-level fields of r3 | 4 | 3 | 1 | 3 | 1 | §4.2 |
| H: textbook fields of r3 | 0 | 0 | 0 | 0 | 0 | §4.3 |
| H: fields that were glue in C4 | 0 | 0 | 0 | 0 | 0 | §4.4 |
| H: Props introduced by reductions until r3 | 5 | 5 | 0 | 5 | 0 | §4.5 |
| H: fields of the H base introduced in r4 | 18 | 16 | 2 | 17 | 1 | §4.6 |
| H: Props open only in scenario F, introduced in r4 | 9 | 1 | 8 | 3 | 6 | §4.7 |
| H: fields of leaf-fold9 introduced in r5 | 0 | 0 | 0 | 0 | 0 | §4.8 |
| H: Props open only in scenario F, introduced in r5 | 1 | 0 | 1 | 1 | 0 | §4.9 |
| H: fields of leaf-fold10 and leaf-fold11 introduced in r6 | 1 | 1 | 0 | 1 | 0 | §4.10 |
| H: Props open only in scenario F, introduced in r6 | 2 | 0 | 2 | 1 | 1 | §4.11 |
| H: fields of leaf-fold13 introduced in r7 | 3 | 3 | 0 | 3 | 0 | §4.12 |
| H: Props open only in scenario F, introduced in r7 | 0 | 0 | 0 | 0 | 0 | §4.13 |
| H: fields of leaf-fold14 to leaf-fold19 introduced in r8 | 8 | 7 | 1 | 7 | 1 | §4.14 |
| H: fields of leaf-fold20 to leaf-fold26 introduced in r9 | 7 | 4 | 3 | 5 | 2 | §4.15 |
| **total** | **72** | **49** | **23** | **60** | **12** | |

By form: 49 published form, 11 consequences of one theorem, 9 composites, 3 project glue (`CMStabObj`,
`CoverModelOfHeckeN`, `P1SchemeQ`).

**Since r8 (18 new rows; 11 LEAF and 7 GLUE strict, 16 and 2 lenient).** Five rows are proved (H-117, H-130, H-172,
H-188, H-193), two pruned (H-128, H-148), eight replaced by smaller statements (H-13, H-119, H-170, H-175, H-196,
H-206, T-3, Z-1), five off the route (H-154, H-169, H-197, H-198, T-16), and one split in scenario F (Z-2). The H base
is leaf-fold29's `sixContactMin_of_open31` inside the library (C4''''''''', §1): gt-sga7 and gt-unip prove
`sga7_IX_3_3` and `semistableUnipotent` from strictly henselian printed forms (leaf-fold20), yu-prune removes
`yuThm11` (leaf-fold21), gt-rayclass and sgr-split replace three fields by two leaves (leaf-fold22), gt-rigidity and
rigid-prune weaken `mumfordRigidityCore` to GIT Thm 6.14 (leaf-fold23), r16-split drops the rank-two clause of `r16`
(leaf-fold25), elkies-coord and flt-cqj2 replace one field and remove another (leaf-fold26, leaf-fold27), and
bg-explicit, st-qbar, faltings5-lower and r6-nf with neron-dvr remove four (leaf-fold29). On the top, gz-fh proves the
twisted functional equation, so `hFH` replaces `hL2` (leaf-fold24), theta-wp8 removes `hX` (leaf-fold-hx), which also
re-rates `hCM` and `uniformizationLeafAll` as consequences, and h29-ne3's six published leaves replace `h29`
(leaf-fold29). Scenario F also takes dcy3-used's consumer replacement for `deligneComponentsY3PrintedAb` (merged, not
folded), and the `C_d` form of the top's `hL3`, which gz-hl3 splits; there gz-weil's parametrization, with Jacobi's
formula proved by jacobi-lambda, leaves no composite, and gz-heegner proves the Heegner point's rationality (all
merged, none folded). The count of rows goes from 75 to 72: 21 go, 18 come.

**Not applied** (§4.1): the reports of the branches after main (below), which are not merged; as in r8, sh-route's
theorems, shimura-cft's leaf and gap-triage's probe for `CoverModelOfHeckeN` (H-95).

**Who works on what** (the integrator's `docs/one-proof/claims.tsv` with the crowd kit's columns): the cloud claims
mark 22 rows (9 by cloud batch 2, 6 by cloud batch 3, 7 by cloud round 2), and the rows say which; the project's own
claims are on 19 fields and hypotheses: `thetaRatiosAlgebraic` (linyang-printed, igusa-alg); `quotientP1Coordinate`
(p1-quot, cm-stab); `uniformizationLeafAll` (H-103: unif-topology); `geomConnOfAlgClosure` (H-150: pi0-prune);
`weilPairingMumford` (H-202: weil-used); `hL3` (gz-weil, gz-heegner, jacobi-lambda); `r17` (r17-bypass);
`eigenformHTNew` (ht-bypass); `r11r12` (H-9: pb-bypass); `shimuraIntegralModelRep` (H-210: sgr-direct);
`deligneComponentsX6PrintedAb` (H-192: pi0-prune); `gaudronRemondThm14` (H-110: gr14-narrow); `semistablePersistsSHcp`
(H-203: persists-dvr); `r9a` (H-6: faltings-cm); `r9b` (H-7: faltings-cm); `gonzalezRotgerProp56X6` (H-204:
gr56-prove); `hFH` (Z-3: fh-printed); `r16CoreY` (H-212: r16-used); `deligneComponentsY3PrintedAb` (dcy3-used). After
main the fork's branches carry results on 24 rows, marked "after main" in the rows; their reports are not merged, so
this report does not use them:
- cm-stab (feff8ecd): the glue `CMStabObj` proved.
- composite-out (822da7b5): the three uses of `shimuraMainThmIDeligneY3AbU` proved, so the composite is not needed.
- faltings-cm (ce696e14): `r9b` from its surjectivity half and `homFreeFiniteAlgClosed`.
- fh-printed (8d0b9b64): `hFH` from Friedberg–Hoffstein's Theorem B over its own objects.
- gr56-prove (90b817cb): `gonzalezRotgerProp56X6` from Eichler's optimal-embedding count.
- gt-sga3 (deba22d7): `sga3_VIB_3_10` from a weaker published leaf and `geomConnOfRationalPoint`.
- gz-weil (ad22e947): a period lattice of every `C_d` constructed, so `WeierstrassUniformization` is not needed on the
  `C_d` route (gz-weil's earlier commits, with the parametrization, are on main through jacobi-lambda).
- hcm-printed (15055182): `hCM` from printed leaves.
- ht-exists (7088f9ed): `eigenformHTNew` from Kato's existence form.
- linyang-printed (3bb5a828): `LinYangThetaCurve` from two printed leaves.
- theta-fold (8e3dbdea): `thetaRatiosAlgebraic` replaced by two printed leaves, one of which (`LinYangEx29All`)
  leaf-audit finds false.
- p1-quot (319fa317): `quotientP1Coordinate` from published leaves and the chain's inputs, with no project glue.
- p1-quot2 (19793c5d): `quotientP1Coordinate` from a printed Lichtenbaum leaf and mcr-glue's leaves.
- p1-quot3 (b533b204): `quotientP1Coordinate` from three printed leaves and chain fields.
- pb-bypass (c1636db9): `r11r12` from Pan's and Berger's printed theorems over Fontaine's `B_st`.
- r16-used (dcf24ac6): `r16CoreY` replaced by one printed-form leaf.
- sga7-cp (0c200c57): `raynaudSemistableSH` and `sga7_IX_3_5_ForwardGeom` weakened to the instance used.
- sgr-direct (56478c75): the consumer of `shimuraIntegralModelRep` with no integral model, from one new glue Prop.
- sir-printed (e5968542): `shimuraIntegralModelRep` replaced by the used form.
- shimura-split2 (838a7430): `rayClassCMAb` and `shimuraFamilyAb` from two new leaves, without
  `shimuraMainThmIDeligneY3AbU`.
- unif-printed (9c2e1809): `uniformizationLeafAll` from four printed leaves.

**The 72 names** (L = LEAF in both counts; c = consequence of one theorem, LEAF only in the lenient count; all others
GLUE; details in the tables):
- GZ: `ZInQ.GZFH.FriedbergHoffsteinB_FE` (c); `ZInQ.GZHL3.WeierstrassUniformization` (L); `ZInQ.GZHL3.GrossZagierFormulaCd` (c); `ZInQ.GZHL3.GrossConjugationCd` (c); `ZInQ.GZHeegner.X0ModuliGaloisMero` (c).
- TYZ: `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` (L); `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` (L); `T5Glue.ShimuraMainCM` (c); `ZInQ.Contrib.TYZDecomp.H29Split.LegendreThreeSquares` (L); `ZInQ.Contrib.TYZDecomp.H29Split.JonesPallX2Y2Z16` (L); `ZInQ.Contrib.TYZDecomp.H29Split.TYZTestVectorExists` (L); `ZInQ.Contrib.TYZDecomp.H29Split.TYZLemma29PrintedNe3` (L); `ZInQ.Contrib.TYZDecomp.H29Split.TYZThm21At31` (L); `ZInQ.Contrib.TYZDecomp.H29Split.TYZProp23Printed` (L).
- H: `PkgI2.NeronOggShafarevich` (L); `PkgI3.FaltingsSemisimple` (L); `PkgI3.FaltingsTate` (L); `PkgI4.PanBerger`; `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` (L); `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` (L); `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` (L); `ZInQ.Contrib.AVB1.PoincareComplement` (L); `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` (L); `AVGlue.CartierSmooth` (L); `AVGlue.GeomConnOfRationalPoint` (L); `AVGlue.GroupSchemeEquidim` (L); `AvSplit.MumfordTorsionAlgClosed` (L); `BPAnalytic.Uniformization.UniformizationLeafAll` (c); `AvSplit.MilneIsogenyQuasiInverse` (L); `ZInQ.HomLattice.GAGAMorphism` (L); `ZInQ.HeightSplit.JavanpeykarBound` (L); `ZInQ.HeightSplit.GaudronRemondThm14` (L); `ZInQ.HeightSplit.BostLowerBound` (L); `ZInQ.HeightSplit.PazukiCor13Upper` (L); `CurveSplit.RegularSmoothPerfect` (L); `ZInQ.Contrib.HodgeSplit.TateTwistInvariants` (L); `ZInQ.Contrib.HodgeSplit.AxSenTate` (L); `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` (L); `ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` (L); `ZInQ.Contrib.HodgeSplit.DSThm965`; `ZInQ.Contrib.HodgeSplit.DSThm966` (L); `MCRGlue.ProperCurveAF`; `MCRGlue.FiniteQuotientExists` (L); `MCRGlue.TameQuotientSmooth`; `MCRGlue.SmoothModelOfP1` (c); `MCRGlue.TameFixedPointsDisjoint` (c); `MCRGlue.TameInertiaCyclic`; `HDec.PropTSRed.CoverModelOfHeckeN`; `MCRQuot.P1SchemeQ`; `MCRQuot.CMStabObj`; `ModularSplit.R17.CarayolRealization` (c); `CToPrinted.SGA3_VIB_3_10` (L); `CToPrinted2.KatoRealizationCohSS` (c); `HDec.HSyn.G0Split.ThetaPt.ThetaGlue.LinYangThetaCurve`; `HDec.QMSplit.Moduli.GeomConnOfAlgClosure` (L); `ShimuraGlue.DeligneComponentsX6PrintedAb` (L); `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` (L); `ReductGlue.RaynaudSemistableSH` (L); `T09Pic.PicRepresentableAbVar` (L); `T09Pic.PicZeroAbVar` (L); `T09Pic.PhiAmpleIsogeny` (L); `T09Pic.WeilPairingMumford`; `ReductB.SemistablePersistsSHcp` (L); `GRCountX6.GonzalezRotgerProp56X6` (L); `GapSHPair.NeronBaseChangeStrictHenselization` (L); `SGA7PersistsNF.SGA7_IX_3_3_SH` (L); `UnipotentForward.SGA7_IX_3_5_ForwardGeom` (L); `RayClassCFT.ShimuraMainThmIDeligneY3AbU`; `SGRSplit.ShimuraIntegralModelRep` (c); `ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw` (L); `R16Split.R16CoreY`; `HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField` (L).

**How far this is checked.**
- **Scenario A is one compiled theorem.** `ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`, on
  leaf-fold29's bundles) derives `ZInQ.FrozenTarget` from leaf-fold29's four bundles (26 + 11 + 13 + 1 = 51 fields)
  and the eleven top Props `TYZThm11Integral`, `LegendreThreeSquares`, `JonesPallX2Y2Z16`, `TYZTestVectorExists`,
  `TYZLemma29PrintedNe3`, `TYZThm21At31`, `TYZProp23Printed`, `ShimuraMainCM`, `TYZThm33`, `FriedbergHoffsteinB_FE`
  and `GrossZagierHeegner`. OPEN.md states that the kernel checks it with no `sorry` and only the standard axioms
  (REPORTED; the folds regenerate the build's `open-statements.json`). `chain.py onep` reads the signature: its
  hypotheses are scenario A's (the four bundles and the eleven top Props); the bundles' fields are the 51 field rows
  of `kinds.tsv`, with the names and type heads of the build's `open-statements.json`, whose eleven other hypotheses
  have scenario A's heads.
- **Scenario F.** A with the top's Gross–Zagier hypotheses restricted to the curves `C_d` (Z7), plus the edges of §2.1
  and §4.1, each compiled on its branch per its report and log. `chain.py` checks signatures (0 mismatches over 207
  theorem edges, 26 of them followed on the route), the two consumer replacements (theta-split's and dcy3-used's), and
  compares definitions where a proof lives in another Lean world (§5.2). F is not compiled as one file.

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

**Findings in brief** (§7): since r8, five rows proved, two pruned, eight replaced, five off the route and one split;
scenario A is one library theorem with 62 hypotheses, all used, its 51 fields 39 LEAF strict by the integrator's
table; the 3 project-glue Props are `CMStabObj`, `CoverModelOfHeckeN`, `P1SchemeQ`.

## 1. The chain to `ZInQ.FrozenTarget`

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| C0 (r3) | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` with `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` | `Contrib/GZTheta/NewCMFinal.lean` @ main; `Contrib/TYZChain/Main.lean` @ w54 | `SixContactMin`, the 4 TYZ Props of §3.2, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (r1-r2: this task's `frozenTarget_of_open` in `scratch/frontier/TYZChain.lean`, with cm-bridge's 7 TYZ Props) |
| C1 | `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` | `Contrib/GZDecomp/Decomp.lean` @ main | `SixContactMin`, `TYZThm35ReadingA`, `HeckeThetaNewform`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (via `GrossZagierCd`; `HeckeContinuation`, `FunctionalEquation5` discharged by the proved `ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) |
| C2 | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` | `Contrib/GZTheta/NewCMFinal.lean` @ wip/atkin-li 6f77abb1 | `SixContactMin`, `TYZThm35ReadingA`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` |
| C3 | TYZ: §3.1 | | → `TYZThm35ReadingA` |
| C4''''''''' (r9) | H: `HDec.HSyn.sixContactMin_of_open31 (r : OpenResearchLeaves24) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ37.lean` L104 @ main (leaf-fold29 0e70c94e, over leaf-fold28b 8961bb09, which merges leaf-fold-hx 862bd440 into leaf-fold27 f3f288d8, over leaf-fold26 86755ad8, leaf-fold25 bc90deac (which merges leaf-fold23 aa9763a1 and leaf-fold24 b2ae6c53), leaf-fold22b 9a100aa7, leaf-fold21 47bba295 and leaf-fold20 24f97774: `TailZ33`-`TailZ37` and rigid-prune's `TailZ40` over leaf-fold19's `TailZ32`; `autofold.py`'s folds, with the build's `open-statements.json` regenerated, REPORTED) | → `ZInQ.SixContactMin`; 26 + 11 + 13 + 1 fields (§4) |
| C4'''''''' (r8) | H: `HDec.HSyn.sixContactMin_of_open26 (r : OpenResearchLeaves19) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves16) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ32.lean` L47 @ main (leaf-fold19 c2ad4181, folding fork PR #19, over leaf-fold18 3782dac8, leaf-fold17 be8511f3, leaf-fold16 a454ad64, leaf-fold15 63205204 (gt-ega's `TailZ25`), sem-prune 2b486d04 and leaf-fold14 97579a97: `TailZ23`-`TailZ32` over leaf-fold13's `TailZ22`; leaf-fold14 reports `lake build +ZInQKernel.OneProof.Main` passing with standard axioms, and the later folds are `autofold.py`'s, with the build's `open-statements.json` regenerated, REPORTED) | → `ZInQ.SixContactMin`, 30 + 13 + 14 + 1 fields; superseded: leaf-fold20 to leaf-fold29 fold the reports of §4.1 into the next generations |
| C4''''''' (r7) | H: `HDec.HSyn.sixContactMin_of_open16 (r : OpenResearchLeaves13) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ22.lean` L335 @ main (leaf-fold13 29885092, merged in w66: x6-fold e33b690a, which adds `TailZ20`-`TailZ22` over leaf-fold11 b73da969: `lake build +ZInQKernel.OneProof.Main` passes, standard axioms, no unused field, no existing constant changed, REPORTED by x6-fold §1) | → `ZInQ.SixContactMin`, 35 + 15 + 14 + 1 fields; superseded: leaf-fold14's bundles map to leaf-fold9's directly, so `open12` to `open16` are compiled but off the path (leaf-fold14 §1) |
| C4'''''' (r6) | H: `HDec.HSyn.sixContactMin_of_open15 (r : OpenResearchLeaves12) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves11) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ19.lean` L1895 @ main (leaf-fold11 b73da969, merged in w63, with leaf-fold12's `TailZ18`, `TailZ19`; over leaf-fold10 a5df68fe, merged in w61, and the prune 0218a662, merged in w62: `lake build +ZInQKernel.OneProof.Main` passes, standard axioms, no unused field, REPORTED by leaf-fold11 §4) | → `ZInQ.SixContactMin`, 32 + 15 + 13 + 1 fields; superseded: leaf-fold13 fills its bundles inside OneProof |
| C4''''' (r5) | H: `HDec.HSyn.sixContactMin_of_open9 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves9) (l : OpenAddedLeaves8) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ9.lean` L161 @ main (leaf-fold9 cf6914e1, merged in w60; over leaf-fold8's `sixContactMin_of_open8` in `TailZ4.lean`: `lake build +ZInQKernel.OneProof.Main` exit 0, standard axioms, the closure of `sixContactMin_of_open9` without `sorryAx`; REPORTED by its report §1, §4) | → `ZInQ.SixContactMin`, 30 + 18 + 14 + 1 fields; superseded: leaf-fold10 and leaf-fold11 fill its bundles inside OneProof |
| C4'''' (r4) | H: `HDec.HSyn.sixContactMin_of_open8 (r : OpenResearchLeaves8) (t : OpenTextbookLeaves8) (l : OpenAddedLeaves8) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ4.lean` L265 @ main (leaf-fold8 b0f2f6da, merged in w59; over leaf-fold7's `sixContactMin_of_open7` in `TailX.lean`, w58: `lake build +ZInQKernel.OneProof.Main` exit 0, standard axioms, the closure of `sixContactMin_of_open8` without `sorryAx`; REPORTED by its report §1) | → `ZInQ.SixContactMin`, 31 + 20 + 14 + 1 fields; superseded: leaf-fold9 fills its bundles (`researchLeaves8_of_open9`, `textbookLeaves8_of_open9`) inside OneProof |
| C4''' | H: leaf-fold6's `HDec.HSyn.sixContactMin_of_open6` | `scratch/leaf-fold6/parts/f20_fold6.lean` @ main (leaf-fold6 733d8013, in w55; flat file compiled, REPORTED) | superseded: leaf-fold7 fills its bundles (`researchLeaves5_of_open7`, `glue6_of_open7`, …) inside OneProof |
| C4'' (r3) | H: `HDec.HSyn.sixContactMin_of_open5 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves5) (l : OpenAddedLeaves5) (g : OpenGlue5)` | `scratch/leaf-fold5/Leaves5.lean` L121755 @ wip/leaf-fold5 5a7e03d1 (in w54; flat file of the final text, 121 783 lines, md5 5999e1db: `lake env lean` exit 0 in 1570 s, 0 errors, no `sorry`, 349 axiom reports all standard; olean chain and `Check5.lean` compiled; REPORTED by its log) | → `ZInQ.SixContactMin`; 26 + 21 + 21 + 2 fields (§4) |
| C4' (r2) | H: `HDec.HSyn.sixContactMin_of_open4 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4) (l : OpenAddedLeaves4) (g : OpenGlue4)` | `scratch/leaf-fold4/Leaves4.lean` L118447 @ wip/leaf-fold4 9dcf1ca8 (final; flat file, 118 478 lines, md5 6bbeb639: `lake env lean` exit 0 in 1048 s, 0 errors, no `sorry`, 326 axiom reports all standard; olean chain and `Check4.lean`, the kernel conclusion, compiled; REPORTED by its report and log); on fork main since w49 | → `ZInQ.SixContactMin`; 26 + 19 + 20 + 1 fields (§4) |
| C5 | assemble-port's `HDec.HSyn.sixContactMin_of_leaves5` (C4 of the 17:35 report; 26 + 17 + 27 fields) | `scratch/assemble-port/AssemblePort.lean` L116751 @ 92a27877 | C4' is its successor through leaf-fold2-4: the 17:35 scenario-F edges folded, `chartProper`, `chartQuasiFinite`, `hauptmodulUnique` proved, `periodMapGlue`, `abVarSpreadsOut` reduced to leaves, `DivisiblePoints` removed (leaf-fold4 §1.1); g0-assemble3's 46-glue-field `sixContactMin_of_leaves4` before it |
| C6 | H, per field: §4 | | each open field, or the Props it was reduced to |
| **C0 ∘ C4''''''''' in the library (r9)** | `ZInQ.OneProof.frozenTarget (r : HDec.HSyn.OpenResearchLeaves24) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17) (g : HDec.HSyn.OpenGlue7) (h11 …) (hL3s …) (hJP …) (hfx …) (hL29 …) (hT21 …) (hP23 …) (hCM : _root_.T5Glue.ShimuraMainCM) (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33) (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 …) : ZInQ.FrozenTarget` | `ZInQKernel/OneProof/Main.lean` @ main (OneProof since w56; `hFH` since leaf-fold24; B9 since leaf-fold-hx; B10 since leaf-fold29; leaf-fold29's bundles) | scenario A of this report: C4''''''''' with theta-wp8's B9 and h29-ne3's B10 (§3.1), gz-fh's Z6 (§2.1) and the kernel's C1 |

The fork's registered headline (`ZInQKernel/MainLiterature.lean`) has five hypotheses; two are proved
(`ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) and C1 already uses them. C4' concludes the kernel's
`ZInQ.SixContactMin` (the flat file imports the kernel's definition; `Leaves.lean` is wrapped in `namespace HDec`), so
C0 and C4''''''''' compose by modus ponens. Earlier compiled H assemblies (cpts-transport's 44-field and linked-ram's
45-field `GluePieces5` in the W0 world, lt-goodred's and linked-frob's variants, leaf-fold2's
`sixContactMin_of_open2`) are superseded by C4, C4', C4'', C4''', C4'''', C4''''', C4'''''', C4''''''' and C4''''''''.

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
| Z6 (r9) | `ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE` | `ZInQKernel/Contrib/OneProof/FHNonvanishing.lean` L25 @ main (gz-fh 75a3c0bd, in the library since leaf-fold24) | `FriedbergHoffsteinB_FE` → `FHNonvanishing` (the twisted functional equation `TwistFunctionalEquation` proved); both scenarios use it |
| Z7 (r9, F) | `ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd` with `ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing` | `ZInQKernel/Contrib/GZStatements/Weak.lean` L138, L94 @ main (gz-statements 0b742fc5, on main since 11-13) | `SixContactMin`, `TYZThm35ReadingA`, `FHNonvanishingCd`, `GrossZagierHeegnerCd` → `FrozenTarget`, and `FHNonvanishing` → `FHNonvanishingCd` (the headline applies `hL2` and `hL3` only at the curves `C_d : y² = x³ − d²x`, `d ≡ 5 (mod 8)` squarefree; scenario F's top in place of C2) |
| Z8 (r9, F) | `ZInQ.GZWeil.grossZagierHeegnerCd_of_leaves4` | `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/JacobiLambdaDeriv.lean` L675 @ main (jacobi-lambda b6fc38e9, over gz-weil's first commits, merged by leaf-fold-hx) | `WeierstrassUniformization`, `HeegnerPointRationalCd`, `GrossZagierFormulaCd`, `GrossConjugationCd` → `GrossZagierHeegnerCd` (gz-hl3's split at the curves `C_d`, the Heegner point built from Mathlib's Weierstrass `℘` and the Eichler integral of the newform; its parametrization leaf `ShimuraCMParamCd` proved by gz-weil's twist and uniformization steps from Jacobi's derivative formula `dλ/dt = πiλθ₄⁴`, which jacobi-lambda proves) |
| Z9 (r9, F) | `ZInQ.GZHeegner.heegnerPointRationalCd_of_printed` | `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/HeegnerCd.lean` L18 @ main (gz-heegner 58a780e4, merged, not folded) | `ShimuraMainCM`, `X0ModuliGaloisMero` → `HeegnerPointRationalCd` (Shimura reciprocity at the Heegner points and the canonical model of `X₀(N)` for functions with poles in `ℍ`) |

Off the route since r9: gz-hl3's general split `ZInQ.GZHL3.grossZagierHeegner_of_leaves` (six leaves, among them the
composites `StrongWeilCurve` and `IsogenyLattice`: Eichler–Shimura and Faltings' isogeny theorem for every elliptic
curve over `ℚ`) and gz-heegner's `ZInQ.GZHeegner.heegnerPointRational_of_printed`. The library theorem's `hL3` is that
general form, so `#discharges` cannot show the `C_d` route as a discharge of `hL3` (gz-weil §0).

### 2.2 Open Props (5: 1 LEAF, 4 GLUE in the strict count; 5 LEAF, 0 GLUE in the lenient count)

| # | Lean name | defined in | class | nearest published sources (all numbers UNVERIFIED) | last task; newest commit | running now | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| Z-3 | `ZInQ.GZFH.FriedbergHoffsteinB_FE` | `ZInQKernel/Contrib/OneProof/FHNonvanishing/FE.lean` L45 @ main | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count): Friedberg–Hoffstein's Theorem B for weight-2 newforms of trivial nebentypus and `χ₀ = χ_{D₀}` unramified on `S`, the root number given as the sign of the functional equation; gz-fh proves the twisted functional equation, so `FHNonvanishing` follows from this leaf alone (replaces Z-1) | Friedberg–Hoffstein, Ann. of Math. 142 (1995) 385–423, Thm B | gz-fh; hypothesis `hFH` of the library theorem since leaf-fold24 | after main: fh-printed (`FriedbergHoffsteinB_FE`) | consequence of one theorem: Friedberg–Hoffstein 1995 Thm B, specialized (gz-fh; locator UNVERIFIED); kinds.tsv: pending a reading of three clauses (the level, the dihedral case, the local data); its statement review (11-15) reads it as a consequence |
| Z-4 | `ZInQ.GZHL3.WeierstrassUniformization` | `ZInQKernel/Contrib/OneProof/GrossZagierHeegner.lean` L101 @ main | **LEAF**: for `a, b ∈ ℂ` with `a³ − 27b² ≠ 0` there is a lattice `L` with `g₂(L) = a`, `g₃(L) = b` (replaces Z-2) | Silverman, The Arithmetic of Elliptic Curves (GTM 106, 2nd ed.), Thm VI.5.1 | gz-hl3 (merged, not folded) | after main: gz-weil (`WeierstrassUniformization`) | published form: Silverman AEC Thm VI.5.1 (gz-hl3) |
| Z-5 | `ZInQ.GZHL3.GrossZagierFormulaCd` | `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Cd.lean` L39 @ main | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count): the Gross–Zagier formula in its Ch. V form with the constant forgotten, `L'(E/K,1) = κ ĥ(y_K)` with `κ > 0`, for the curves `C_d`, `d ≡ 5 (mod 8)` squarefree (gz-hl3's `GrossZagierFormula` restricted to them) (replaces Z-2) | Gross–Zagier, Invent. Math. 84 (1986) 225–320, Thm I.6.3 and Ch. V Thm 2.1 | gz-hl3 (merged, not folded) | no | consequence of one theorem: Gross–Zagier 1986 at the curves `C_d`, the positive constant forgotten; gz-hl3 rates it printed, the integrator's statement review (11-15) a consequence (claims.tsv: the `C_d` leaves rate consequence) |
| Z-6 | `ZInQ.GZHL3.GrossConjugationCd` | `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Cd.lean` L43 @ main | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count): Gross's conjugation relation `ȳ_K = −ε y_K` modulo torsion, `ε` the sign of the functional equation, for the curves `C_d` (gz-hl3's `GrossConjugation` restricted to them) (replaces Z-2) | Gross, *Heegner points on X₀(N)* (Durham 1983), 1984, §5; Gross–Zagier 1986 Ch. V §2 | gz-hl3 (merged, not folded) | no | consequence of one theorem: Gross 1984 §5 at the curves `C_d`; gz-hl3 rates it printed, the integrator's statement review (11-15) a consequence (claims.tsv: the `C_d` leaves rate consequence) |
| Z-7 | `ZInQ.GZHeegner.X0ModuliGaloisMero` | `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Heegner.lean` L503 @ main | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count): the canonical model of `X₀(N)` for every `g ∈ ℚ(X₀(N))` regular at the two points (poles in `ℍ` allowed); with `ShimuraMainCM` (T-15) gz-heegner proves gz-hl3's composite leaf `HeegnerPointRational` and its `C_d` form; it implies the former hypothesis `hX` (`x0ModuliGalois_of_mero`) (replaces Z-2, through `HeegnerPointRationalCd`) | Shimura 1971 §6.7; Deligne–Rapoport VI–VII | gz-heegner (merged, not folded) | no | consequence of one theorem: the printed canonical-model theorem for functions regular at the point (gz-heegner; a human reading of Shimura §6.7 and Deligne–Rapoport VI–VII pending) |

Retired rows: r9: Z-1 `FHNonvanishing` (replaced by Z-3, gz-fh, Z6); Z-2 `GrossZagierHeegner` (split in scenario F
through its `C_d` form, Z7 to Z9; it stays the hypothesis `hL3` of the library theorem).

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
| **T0 (r3, kernel)** | `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` | `Contrib/TYZChain/Main.lean` @ w54 (tyz-chain; B1 with B2-B5 as kernel modules) | `TYZThm11Integral`, `TYZLemma29Mod2`, `Shimura.ShimuraReciprocityModFn`, `∀ ℓ, IsTYZLcal ℓ → TYZThm33Pinned ℓ` → `TYZThm35ReadingA`; both scenarios used it until r8 (r9: off the route, B9) |
| T0' (r4) | `ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33` | `ZInQKernel/OneProof/TYZSplit.lean` @ main (tyz-split 99e582b5, compiled into OneProof by leaf-fold8) | `TYZThm33` → T0's hypothesis `∀ ℓ, IsTYZLcal ℓ → TYZThm33Pinned ℓ`, so T-11 follows from the printed Theorem 3.3; both scenarios used it until r8 (r9: B9 takes `TYZThm33` itself) |
| B6 (r4) | `ZInQ.Contrib.TYZGenus.TYZSplitT5.shimuraReciprocityModFn_of_split` | `scratch/tyz-split/T5.lean` @ main | `CMModuli`, `X0RatStructure` → `Shimura.ShimuraReciprocityModFn`; scenario F used it until r7 (r8: off the route, B8) |
| B7 (r6) | `T5Glue.cmModuli_of_t5'`, `T5Glue.x0RatStructure_of_leaf` | `scratch/t5-glue/T5Glue.lean` @ main (t5-glue 39bb3cd2, merged in w66; r6 read it at the earlier head 405763f6, the same file; the later commits add the report and its second review, which finds `RingClassLattice` true) | `ShimuraMainCM`, `RingClassLattice` → `CMModuli` (the absolute Artin map's surjectivity and `InvertibleColon` proved over Tau Ceti); `X0ModuliGalois` → `X0RatStructure`; scenario F used them under B6 until r7 (r8: off the route, B8) |
| B8 (r8) | `T5Glue.shimuraReciprocityModFn_of_printed` | `ZInQKernel/Contrib/OneProof/RingClassLattice.lean` L3352 @ main (gt-ringclass 06f03bd4, folded by leaf-fold17: t5-glue's development verbatim, with `RingClassLattice` proved as `T5Glue.ringClassLattice`) | `ShimuraMainCM`, `X0ModuliGalois` → `Shimura.ShimuraReciprocityModFn`; the library theorem took T-15 and T-16 in place of `hS`, so both scenarios used it in r8 (r9: off the route, B9) |
| B9 (r9) | `ThetaWP8.tyzThm35ReadingA_noHX` | `ZInQKernel/Contrib/OneProof/ThetaWeierstrass8.lean` L890 @ main (theta-wp8 04afc477, with hx-used's eta route, folded by leaf-fold-hx) | `TYZThm11Integral`, `TYZLemma29Mod2`, `ShimuraMainCM`, `TYZThm33` → `TYZThm35ReadingA`: Shimura reciprocity for modular functions at level 32 from `ShimuraMainCM` alone, with `ThetaWeierstrass8` proved; the library theorem drops `hX`, so both scenarios use it |
| B10 (r9) | `ZInQ.Contrib.TYZDecomp.H29Split.tyzLemma29Mod2_of_sixLeaves` | `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` L864 @ main (h29-ne3 a03caff2, over h29-split and h29-fix, folded by leaf-fold29) | `LegendreThreeSquares`, `JonesPallX2Y2Z16`, `TYZTestVectorExists`, `TYZLemma29PrintedNe3`, `TYZThm21At31`, `TYZProp23Printed` → `TYZLemma29Mod2`: the mod-2 reading of Lemma 2.9 from TYZ's printed statements over genuine definitions (the quaternion algebra's test vectors and genus periods), with Lemma 2.9 at `n = 3` replaced by Theorem 2.1's instance; the library theorem takes the six in place of `h29`, so both scenarios use it |

### 3.2 Open Props (9: 8 LEAF, 1 GLUE in the strict count; 9 LEAF, 0 GLUE in the lenient count)

| # | Lean name | defined in | class | citation (UNVERIFIED unless marked) | last task; newest commit | running now | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| T-1 | `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` | `Contrib/TYZDecomp/Leaves.lean` @ main | **LEAF** (specialization: odd `m` only) | TYZ Thm 1.1, first assertion, L371–380 (read by nt-tyz) | tyz-decomp; main (tyz-lcal audit 11-13: faithful, not stronger) | cloud round 2: in progress (T-1); new base case TYZLcalOne proved (claims.tsv) | published form: specialization of TYZ Thm 1.1 to odd `m` (tyz-lcal audit: faithful, not stronger) |
| T-12 | `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` | `ZInQKernel/OneProof/TYZSplit.lean` L157 @ main | **LEAF** | TYZ Theorem 3.3 over the kernel's definitions, for `n ≡ 5, 7 (mod 8)`, `𝒫(d)` existential | tyz-split | no | published form: TYZ Thm 3.3, Period7.tex L1299-1311, specialized (tyz-split §1), carried along the kernel's eta model of `X₀(32)` by the q-expansion principle (`IsRatModFn 32`), which already sits behind `hS`; a clause-by-clause statement review found the leaf Thm 3.3 or weaker (tyz-split §1 and the docstring, wip/w61 3c241950); the `[i]` sign of the base point is printed (`α = −i` in the Hecke-action proof, about L1564-1566), and h33-sign pins it in Lean by TYZ Thm 3.6(1) (kinds.tsv's flag since leaf-fold22b) |
| T-15 | `T5Glue.ShimuraMainCM` | `ZInQKernel/Contrib/OneProof/RingClassLattice.lean` L912 @ main | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count) | the main theorem of complex multiplication with torsion, idelic, in Weierstrass coordinates over Mathlib's `PeriodPair`, finite adeles and Tau Ceti's `ideleClassArtinMap` (replaces T-13 (from T-5)) | t5-glue; hypothesis `hCM` of the library theorem since leaf-fold17 (gt-ringclass) | after main: hcm-printed (`ShimuraMainCM`) | consequence of one theorem: Shimura 1971 Thm 5.4; Lang, Elliptic functions, Ch. 10 Thm 3 (t5-glue §0; numbers UNVERIFIED); re-rated 11-15 under the integrator's dictionary ruling: the Weierstrass-coordinate form follows from Thm 5.4 through the analytic uniformization (kinds.tsv); leaf-fold17's statement review: the docstring cites the Artin-map lemmas that fix the normalization (kinds.tsv: unread, a new printed leaf) |
| T-18 | `ZInQ.Contrib.TYZDecomp.H29Split.LegendreThreeSquares` | `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` L600 @ main | **LEAF**: Legendre's three-square theorem, the "if" direction: a natural number not of the form `4^a(8b + 7)` is a sum of three squares (not in Mathlib) (replaces T-3) | Legendre, *Essai sur la théorie des nombres* (1798); Gauss, *Disquisitiones Arithmeticae* (1801), art. 291–292; cited by TYZ L533 | h29-ne3, over h29-split and h29-fix; hypothesis `hL3s` of the library theorem since leaf-fold29 | no | published form: Legendre 1798, Gauss art. 291–292 (h29-fix; article numbers UNVERIFIED) |
| T-19 | `ZInQ.Contrib.TYZDecomp.H29Split.JonesPallX2Y2Z16` | `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` L610 @ main | **LEAF**: the form `x² + y² + 16z²` represents every squarefree `n ≡ 1 (mod 8)` (checked up to `10⁶`) (replaces T-3) | Jones–Pall, Acta Math. 70 (1939) 165–191, Thm 5, as cited by TYZ L533 | h29-ne3, over h29-split and h29-fix; hypothesis `hJP` of the library theorem since leaf-fold29 | no | published form: Jones–Pall 1939 Thm 5, restricted to squarefree `n ≡ 1 (mod 8)` (h29-fix; the theorem itself not read) |
| T-20 | `ZInQ.Contrib.TYZDecomp.H29Split.TYZTestVectorExists` | `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` L421 @ main | **LEAF**: for squarefree `1 < n ≡ 1, 3 (mod 8)` and every admissible `τ`, `π_ℤ^{U_n}` has a nonzero generator `f_n` (TYZ: free of rank one) (replaces T-3) | TYZ §2.1, L545–550, with Theorem 2.6 at `χ = 1` (L809–840) | h29-ne3, over h29-split and h29-fix; hypothesis `hfx` of the library theorem since leaf-fold29 | no | published form: TYZ L545–547, restricted to the existence of a nonzero generator (h29-split, h29-fix) |
| T-21 | `ZInQ.Contrib.TYZDecomp.H29Split.TYZLemma29PrintedNe3` | `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` L455 @ main | **LEAF**: TYZ Lemma 2.9 as printed, for squarefree `1 < n ≡ 1, 3 (mod 8)` with `n ≠ 3`: `Q(n) = Σ ε 𝓛(d₁)𝓛(d₂)` over the decompositions `n = d₁d₂` (at `n = 3` the print is false: `Q(3) = ±3` while `𝓛(3)² = 1`) (replaces T-3) | TYZ Lemma 2.9, L1062–1066 | h29-ne3, over h29-split and h29-fix; hypothesis `hL29` of the library theorem since leaf-fold29 | no | published form: TYZ Lemma 2.9, restricted to odd classes, `n > 1`, `n ≠ 3` (h29-ne3) |
| T-22 | `ZInQ.Contrib.TYZDecomp.H29Split.TYZThm21At31` | `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` L474 @ main | **LEAF**: TYZ Theorem 2.1 at `n = 3`, `(d₁, d₂) = (3, 1)`: `P(3, 1) = ±w_K 𝓛(3)𝓛(1)`, `w_K` from the roots of unity of `ℚ(√−3)`; the displayed formula only (replaces T-3) | TYZ Theorem 2.1, L554–559 | h29-ne3, over h29-split and h29-fix; hypothesis `hT21` of the library theorem since leaf-fold29 | no | published form: one instance of TYZ Thm 2.1, the displayed formula without the vanishing clause (h29-ne3) |
| T-23 | `ZInQ.Contrib.TYZDecomp.H29Split.TYZProp23Printed` | `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` L488 @ main | **LEAF**: TYZ Proposition 2.3, first assertion, for squarefree `1 < n ≡ 1, 3 (mod 8)`: `f_n` is odd on the squares `(B̂^×)²` (replaces T-3) | TYZ Proposition 2.3, L580–586 | h29-ne3, over h29-split and h29-fix; hypothesis `hP23` of the library theorem since leaf-fold29 | no | published form: TYZ Prop. 2.3, restricted to odd classes and `n > 1` (h29-split) |

Retired rows: T-2 `TYZLcalOne` (proved, B2), T-4 `Lemma318Literal` (proved, B5), T-6 `Thm35First` (reduced to T-11,
B4), T-7 `Lemma321Five` (proved, B3); r4: T-5 (split by tyz-split into `CMModuli` and `X0RatStructure`), T-11 (from
the printed TYZ Thm 3.3 (`TYZThm33`, tyz-split)); r6: T-13 `CMModuli` and T-14 `X0RatStructure` (split by t5-glue,
B7); r8: T-17 `RingClassLattice` (proved by gt-ringclass, B8); r9: T-16 `X0ModuliGalois` (off the route, B9:
leaf-fold-hx removes `hX`), T-3 `TYZLemma29Mod2` (replaced by T-18 to T-23, B10: leaf-fold29 takes h29-ne3's six
leaves). T-15 is a hypothesis of the library theorem since r8, defined in gt-ringclass's verbatim copy of t5-glue's
file; leaf-fold-hx re-rates it a consequence.

## 4. H: `ZInQ.SixContactMin`

Base (r9): leaf-fold29's compiled C4''''''''' (0e70c94e), inside OneProof: leaf-fold20 (24f97774; gt-sga7, gt-unip),
leaf-fold21 (47bba295; yu-prune), leaf-fold22b (9a100aa7; gt-rayclass, sgr-split, h33-sign), leaf-fold23 (aa9763a1;
gt-rigidity, rigid-prune), leaf-fold24 (b2ae6c53; gz-fh), leaf-fold25 (bc90deac; r16-split), leaf-fold26 (86755ad8;
elkies-coord), leaf-fold27 (f3f288d8; flt-cqj2), leaf-fold-hx (862bd440; theta-wp8, the re-ratings), leaf-fold28b
(8961bb09; claims and locators) and leaf-fold29 (bg-explicit, st-qbar, faltings5-lower, r6-nf with neron-dvr,
h29-ne3), over r8's base 37391b11 (leaf-fold19) and the folds before it. Bundles: `OpenResearchLeaves24` (26),
`OpenTextbookLeaves11` (11), `OpenAddedLeaves17` (13) and leaf-fold7's `OpenGlue7` (1: `quotientP1Coordinate`). The
fields' forms are the integrator's `kinds.tsv`: 42 published, 4 consequences, 4 composites, 1 project glue by kind;
its strict convention counts three published kinds as GLUE, and this report records them as composites:
`deligneComponentsY3PrintedAb`, `weilPairingMumford` and `dsThm965` (the strictest reading). Its eleven rows with
bundle `frozenTarget` give the forms of the top (§2.2, §3.2). `chain.py` reads the bundles from
`ZInQKernel/OneProof/H/TailZ37.lean`, `TailZ32.lean`, `TailZ34.lean` and `TailX.lean` at main. Row numbers are kept,
retired rows listed, new rows from H-207 (§4.15) and T-18 (§3.2).

### 4.1 What changed since r8 (signatures VERIFIED by `chain.py`)

Compiled into C4''''''''' (scenario A), fold by fold. leaf-fold20: gt-sga7 proves `sga7_IX_3_3` (H-175) from its
strictly henselian form H-207, and gt-unip proves `semistableUnipotent` from the forward half of SGA 7 IX 3.5, H-208,
with `StrictHenselizationInside` (H-188) proved. leaf-fold21: yu-prune removes `yuThm11` (H-128). leaf-fold22:
gt-rayclass proves `rayClassCMAb` (H-196) and `shimuraFamilyAb` from H-209, and sgr-split proves
`shimuraGoodReductionNoGuard` (H-119) from H-210; leaf-fold22b updates the flag of `h33` (h33-sign). leaf-fold23:
`mumfordRigidityCore` (H-170) becomes H-211 (gt-rigidity, rigid-prune). leaf-fold24: `hL2` (Z-1) becomes `hFH` (Z-3;
gz-fh, §2.1). leaf-fold25: `r16` (H-13) becomes H-212 (r16-split). leaf-fold26: `elkiesX6StarPrinted` (H-206) becomes
H-213 (elkies-coord). leaf-fold27: flt-cqj2 proves `X0Transitive`, and the field `igusaGL2` (H-117) is deleted.
leaf-fold-hx: theta-wp8 proves `ThetaWeierstrass8`, so the library theorem drops `hX` (T-16; B9, §3.1), and the
integrator's dictionary ruling re-rates `hCM` (T-15) and `uniformizationLeafAll` (H-103) as consequences and flags
`dsThm965` (H-125) in the strictest reading. leaf-fold29: bg-explicit proves `babaGranathRationalAb` (H-193) from four
fields already in the bundles, st-qbar proves `shimuraTaniyamaQbar`'s one use (H-130), faltings5-lower proves the
lower half of Faltings' Lemma 5 (H-172), and r6-nf with neron-dvr restricts `r6` to number fields, so
`neronSchemeModelExistsDVR` (H-148) goes; h29-ne3's six published leaves replace `h29` (T-3; B10, §3.1). r8's changes
are in the r8 report (`git show f96b7323:docs/research/frontier.md`, §4.1).

Applied on top by scenario F:

| field of C4''''''''' (rows) | now | theorems · task · file |
|---|---|---|
| `r17` (H-21) | ⇐ `CarayolRealization` (H-157); the transport to every attached representation is proved (as in r6 to r8) | `ModularSplit.R17.carayolR17'_of_realization` · modular-split · `scratch/modular-split/R17.lean` |
| `eigenformHTNew` (H-127) | ⇐ `KatoRealizationCohSS` (H-181) and the fields `TateTwistInvariants`, `AxSenTate` (as in r6 to r8) | `CToPrinted2.eigenformHTNew_of_printedSS` · c-to-printed2 · `scratch/c-to-printed2/CToPrinted2.lean` |
| `thetaRatiosAlgebraic` (H-44; r6: H-191) | replaced at its consumer (theta-split, route 1): TailA's `ThetaPointOfFibre` from `FibreQMPeriod`, `ThetaEightSquare` and `QMThetaSymmetricCurve`, in place of `HDec.HSyn.G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios`; theta-glue proves `ThetaEightSquare`, and igusa-alg proves `IgusaAlg 5` to `9`, so `QMThetaSymmetricCurve` follows from `LinYangThetaCurve` alone (H-190) | `HDec.HSyn.G0Split.ThetaPt.ThetaSplit.thetaPointOfFibre_of_qm_curve` · theta-split · `scratch/theta-split/ThetaUse.lean`; `HDec.HSyn.G0Split.ThetaPt.ThetaGlue.thetaEightSquare` · theta-glue · `scratch/theta-glue/ThetaGlue.lean`; `HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal.qmThetaSymmetricCurve_of_linYang` · igusa-alg · `scratch/igusa-alg/IgusaAlg.lean` |
| `quotientP1Coordinate` (the glue field; H-84's successor) | ⇐ mcr-glue's six leaves (H-89..H-94; `TameQuotientSmooth` is L3), T5, and three glue Props: mcr-quot's `P1SchemeQ` and `CMStabObj`, and the decomposition's `CoverModelOfHeckeN` | `HDec.MCRGlue.quotientP1Coordinate_of_leaves` (compiled in `ZInQKernel/OneProof/H/TailW.lean`) with mcr-glue's `coordinateNormalization_of` · mcr-glue · `scratch/mcr-glue/MCRGlue.lean`; `fibreAutTame_of''`, `genericQuotientP1_of''`, `cMSectionsDisjoint_of''`, `coordinateFromSections_of''` and their inputs (namespace `MCRQuot`) · mcr-quot · `scratch/mcr-quot/MCRQuot.lean` |
| `deligneComponentsY3PrintedAb` (H-169) | its consumer replaced: the chain reads the field only as `Y3Connected`, which follows from the fields `mumfordGroupLaw` (H-211) and `shimuraMainThmIDeligneY3AbU` (H-209); no new leaf | `DCY3Used.y3Connected_of_leaves` · dcy3-used · `DeligneComponentsY3Used.lean` |
| `hL3` (Z-2) | its `C_d` form ⇐ the published form Z-4, the two Gross–Zagier statements at the curves `C_d` (Z-5, Z-6; consequences) and the Heegner point's rationality, proved by gz-heegner from `ShimuraMainCM` (T-15) and the printed canonical-model theorem `X0ModuliGaloisMero` (Z-7); the parametrization of `C_d` proved (gz-weil, jacobi-lambda) | `ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd` · gz-statements · `Weak.lean`; `ZInQ.GZWeil.grossZagierHeegnerCd_of_leaves4` · jacobi-lambda · `JacobiLambdaDeriv.lean`; `ZInQ.GZHeegner.heegnerPointRationalCd_of_printed` · gz-heegner · `HeegnerCd.lean` |

On the TYZ side both scenarios use B9 (§3.1): the CM hypothesis rests on `ShimuraMainCM` alone, and B8, T0 and T0' are
off the route. Since leaf-fold22 no row is a leaf on `R1fpProps` (H-154 is off the route), and the chain's conversions
between the two moduli problems take rigid-prune's `QMFamilyGroupLaw`, proved from the field `mumfordGroupLaw`
(H-211). On the GZ side scenario F takes the `C_d` form of the top (Z7): the headline uses `hL2` and `hL3` only at the
curves `C_d`, where the parametrization is a theorem, so the split of `hL3` has no composite (Z8, Z9); folding it
needs the library theorem to take that form (§6.2). dcy3-used's replacement is merged but not folded: its used form is
weaker than the field, so `autofold.py` cannot take it, and dcy3-used's hand bypass of the consumer compiles
(REPORTED; §5.2 checks the signatures and every use of the field).

mcr-quot proves the four glue Props under the coordinate (`FibreAutTame`, `GenericQuotientP1`, `CMSectionsDisjoint`,
`CoordinateFromSections`) from T5, L3, `CurveBijIso` and three glue Props: `P1SchemeQ` and `CMStabObj`, which are new,
and `CoverModelOfHeckeN`, the decomposition's own glue. The chain derives `CoverModelOfHeckeN` only through
`HeckeNoVertRam`, downstream of the coordinate that mcr-quot feeds, so here it is counted as open glue: the coordinate
still rests on project glue, and mcr-quot does not discharge it. gap-triage (w66) finds it unnecessary: mcr-quot's
`ModelYIrreducible` is the chain's `HeckeIrreducible`, which the chain proves from the field
`deligneComponentsY3PrintedAb`, and mcr-quot's composite compiles with it in place of `CoverModelOfHeckeN`
(`scratch/gap-triage/GlueProbe.lean`, `MCRQuotNV.lean`); the probe takes leaf-fold9's whole bundle, so scenario F does
not apply it yet (H-95).

Off the route since r9 (the edges stay in `chain.py`): unipotent-b's `UnipotentB.semistableUnipotent_of_printedGen`
with fork PR #19's `ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof`, since leaf-fold20 proves
`semistableUnipotent`; shimura-split's `HDec.QMSplit.Moduli.shimuraFamily_of_hol` with route A's
`LeafQM.AV.R1UnivRigid.shimuraFamily_iff_ab` and `LeafQM.AV.R1UnivRigid.mumfordRigidity_of_core`, since leaf-fold22
proves `shimuraFamilyAb`; the top's `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` (T0),
`T5Glue.shimuraReciprocityModFn_of_printed` (B8) and `ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33`
(T0'), which B9 replaces; since r8: reduct-b's `ReductB.raynaudSemistable_of_SH_pair`,
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
H-129, H-131, H-132, H-135, H-136, H-168, H-171, H-173, H-176, H-185, H-187, H-195, T-17; r9: H-13, H-117, H-119,
H-128, H-130, H-148, H-154, H-169, H-170, H-172, H-175, H-188, H-193, H-196, H-197, H-198, H-206, T-3, T-16, Z-1, Z-2.
Not applied: the variants each report keeps aside (r9: the reports of the branches after main (§0); r8: the reports of
the branches after r8's main; gt-qm's reroute of `yuThm11`'s four live uses (H-128; r9: yu-prune folds it);
unipotent-b's split, which leaf-fold14 left out; r7: sh-route's `strictHenselizationNeron0_final`,
`strictHenselizationPair0_final`, `strictHenselizationInside0_final` and `route_final` from `NeronBaseChangeSH`, whose
statements add `[CharZero K]` and a perfect residue field; reduct-b's Route B-cp, `ss1_ss3_of_cp`, over the restricted
leaf `SemistablePersistsSHcp`, which leaf-fold14 compiles; unipotent-b's `semistableUnipotent0_of_printed`, which
concludes the field with two instances added; t09-pic's split of `WeilPairingMumford` into one printed property per
leaf (L4a-L4f, `t09SymmIsogenyExists_of_split`) and its weaker variants; shimura-cft's `shimuraFamilyAb_of_mainThmI`,
whose leaf implies H-154; gap-triage's `modelYIrreducible_of_open9`, over leaf-fold9's bundle; r6: c-to-printed's
`shimuraFamily_of_mainThmI`, whose leaf `ShimuraMainThmIY3` implies H-154 and is still a consequence; c-to-printed2's
`eigenformHTNew_of_realization` with the leaf `KatoRealization`; theta-split's route 2, `thetaRatiosAtQM_of_cm`
through Shimura's theorem on theta-nulls at CM points; reduct-glue's `strictHenselizationNeron_of` from the pair
`StrictHenselizationDVR`, `NeronBaseChangeUnramifiedDVR`, whose second member may exceed the print; reduct-glue's
`SerreTateFromComplete`, whose field `serreTateThm2` the prune removed; r4: height-split's `r20_of_leaves` with
`IsogenySemistableBaseChange`; curve-split's `x0Transitive_of_igusaSL2X`; qm-split's `qmHauptmodulBase3_of_shimizu`
and `y3Connected_of`; hodge-split's `panBerger_of_templates`; r5: shimura-split's `r1r2fpRep_of_split6`, which keeps
`r1rec` and `r5` as inputs; modular-split's weaker `KatoRealization` leaf; reduct-split's `raynaudCriterion_final`,
which `raynaudCriterion_final'` supersedes by proving the perfect case of its glue).

### 4.2 Research-level fields of r3 still open (4: 3 LEAF, 1 GLUE strict; 3 LEAF, 1 GLUE lenient)

| # | field : Lean name | leaf | class | citation | flags | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| H-5 | `r7a : PkgI2.NeronOggShafarevich` | R7(a) | **LEAF** | Serre–Tate, Ann. of Math. 88 (1968), Thm 1 | UNVERIFIED | pkg-I2; cloud round 2: in progress (H-5, Néron–Ogg–Shafarevich) (claims.tsv) | published form: Serre–Tate 1968 Thm 1 (leaf-review-b §2.2) |
| H-6 | `r9a : PkgI3.FaltingsSemisimple` | R9(a) | **LEAF** | Faltings, Invent. Math. 73 (1983), Satz 3 (erratum 75 (1984)) | UNVERIFIED | pkg-I3 | published form: Faltings 1983 (leaf-review-b §2.3) |
| H-7 | `r9b : PkgI3.FaltingsTate` | R9(b) | **LEAF** | Faltings 1983, Satz 4, Kor. 1 | UNVERIFIED | pkg-I3; after main: faltings-cm (`r9b`) | published form: Faltings 1983 (leaf-review-b §2.3) |
| H-9 | `r11r12 : PkgI4.PanBerger` | R11 + R12 | GLUE (joint consequence of two theorems) | Berger, Invent. Math. 148 (2002), Thm 0.7; Pan, JAMS 35 (2022), Thm 1.0.4 | JAMS numbering UNVERIFIED | pkg-I4; after main: pb-bypass (`r11r12`) | composite: Pan and Berger (leaf-review-b §2.4) |

### 4.3 Textbook fields of r3 still open (0: 0 LEAF, 0 GLUE strict; 0 LEAF, 0 GLUE lenient)

None left: each is proved or split (§4.1).

T6, T7, T8, T9, T11(b), T3, T41, T34 and T38 are proved or reduced (r2); their replacements are rows of §4.5.
T4, T5, T23, T24, T27, T33, T35, T40 and the normal model of a function field are proved or split in r4 (§4.1).

### 4.4 Fields that were glue in C4, still open (in C4''''''''' they are `OpenAddedLeaves17` fields) (0: 0 LEAF, 0 GLUE strict; 0 LEAF, 0 GLUE lenient)

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

Proved and gone from the tables: r9, `X0Transitive` (flt-cqj2; the field `igusaGL2` deleted),
`StrictHenselizationInside` (gt-unip), `ThetaWeierstrass8` (theta-wp8; `hX` dropped), and from new leaves
`SGA7_IX_3_3`, `SemistableUnipotent`, `RayClassCMAb`, `ShimuraFamilyAb`, `ShimuraGoodReductionNoGuard`,
`ElkiesX6StarPrinted`, `R16_EichlerShimuraJ1'`, `FHNonvanishing` and `TYZLemma29Mod2`, and with leaf-fold29
`BabaGranathRationalAb` (bg-explicit), `STQM` (st-qbar) and the lower half of Faltings' Lemma 5 (faltings5-lower); r8,
`RingClassLattice` (gt-ringclass), `MulEtaleAbelianScheme` (fork PR #19), `QMCentralizerCMC` (gt-qm),
`ValenceFormulaCocompactEq` (gt-valence), `IgusaPsi4`, `IgusaChi10` (gt-theta), `ShimizuCovolumeO1` (gt-gamma),
`BLR_1_2_4` (gt-blr), `EGAIV_8_10_5_openImm` (gt-ega), and from new leaves `GonzalezRotgerCountX6Ab`,
`StrictHenselizationPair` and `ElkiesEquationsX6Ab`; r7, `IgusaAlg` (igusa-alg); r6, `IgusaCMValue24` (cm24-value),
`HTDual` (c-to-printed2), `FixedTorsionRationalImperfect`, `SemistableAlmostAll`, `SemistableLocalGlobal` and
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
unipotent-b's two `K^s` versus `K̄` Props. Props that r8's tasks introduced and proved were never rows: sem-prune's
`G9GlueNoT23` and `FaltingsLemma5BCLower`; gt-shpair's commutative algebra (`IsSHSep` pins the strict henselization in
every characteristic); gt-elkies's Atkin–Lehner group, a definition, and its moduli step `orbit_iff_twist`;
gt-grcount's passage from `R5fpCount`. Props that r9's tasks introduced and proved were never rows: gz-fh's
`TwistFunctionalEquation`; gz-hl3's glue (Heegner representatives, the point on `E`, the embedding of `ℚ(√D)`, the Ch.
V corollaries) and its composite leaves `HeegnerPointRational` and `HeegnerPointRationalCd` (gz-heegner) and
`ShimuraCMParamCd` (gz-weil, from `JacobiLambdaDeriv`); theta-wp8's `ThetaWeierstrass8` and hx-used's eta route;
flt-cqj2's `ModularEquationGeneric` and `CyclicQuotientJBijOn`; elkies-coord's step from the fibres of `t` to the
`W`-orbits; r16-split's rank-two clause; sgr-split's `SmoothGeomConnIntegral` and `AbVarEndTorsionFree`; gt-rayclass's
`ClassNumberOneB`; yu-prune's `YuB6Alg`; gz-weil's `JacobiLambdaDeriv` (jacobi-lambda), with x0-32's
`EtaModelDifferential` and `ModularParamC1`; `TYZTauExists` (h29-split's alternative leaf, from the three-square
theorems) and h29-ne3's `TYZLemma29Printed`; neron-dvr's number-field Néron theorem; dcy3-used's `Y3ConnectedAb`.

### 4.6 Fields of the H base introduced in r4 (18: 16 LEAF, 2 GLUE strict; 17 LEAF, 1 GLUE lenient)

Each row is a field of C4''''''''' (its name is in the 'last task' column; leaf-fold9 to leaf-fold29 keep leaf-fold8's
fields, less those proved, pruned or replaced since) and the hypothesis of a compiled theorem in the task's file. Its
form is the kind in the integrator's `kinds.tsv`, which keeps leaf-fold8's; where this report's reading differs the
pointer says so. Theorem numbers are the reports' and UNVERIFIED unless a report read the source.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-98 | `AVGlue.CartierSmooth` | `scratch/av-glue/Combined.lean` L297 @ main | H-73, H-74 | **LEAF**; a group scheme locally of finite type over a field of characteristic 0 is smooth | av-glue; field `cartierSmooth` of leaf-fold29; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Cartier's theorem; Mumford AV §11 Thm 1; Stacks 047N (av-glue §5) |
| H-99 | `AVGlue.GeomConnOfRationalPoint` | `scratch/av-glue/Combined.lean` L902 @ main | H-74 | **LEAF**; a connected scheme of finite type over `k` with a rational point is geometrically connected | av-glue; field `geomConnOfRationalPoint` of leaf-fold29; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Stacks 04KV, specialized to finite type with a rational point (av-glue §5) |
| H-100 | `AVGlue.GroupSchemeEquidim` | `scratch/av-glue/Combined.lean` L913 @ main | H-74 | **LEAF**; the irreducible components of a group scheme of finite type over a field have its dimension | av-glue; field `groupSchemeEquidim` of leaf-fold29; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Stacks, group schemes over a field; SGA 3 VI_A 2.4, finite type (av-glue §5) |
| H-102 | `AvSplit.MumfordTorsionAlgClosed` | `scratch/av-split/AvSplitAll.lean` L1411 @ main | H-25, H-38 | **LEAF**; over `k = k̄`, `A(k)[n] ≅ (ℤ/n)^{2g}` for `char k ∤ n` | av-split; field `mumfordTorsionAlgClosed` of leaf-fold29; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Mumford AV §6 Application 2 (iv) (the integrator's correction of av-split's §4; UNVERIFIED) |
| H-103 | `BPAnalytic.Uniformization.UniformizationLeafAll` | `ZInQKernel/HDecomp/Analytic/Uniformization.lean` L91 @ main | H-38, H-69 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); the kernel's AN3 leaf: `A^an` in coordinate form | av-split; field `uniformizationLeafAll` of leaf-fold29; after main: unif-printed (`uniformizationLeafAll`) | consequence of one theorem: Mumford §1 in coordinate form (bp-analytic §4); re-rated 11-15 under the integrator's dictionary ruling: the coordinate form is reached through analytification and GAGA (kinds.tsv) |
| H-104 | `AvSplit.MilneIsogenyQuasiInverse` | `scratch/av-split/AvSplitAll.lean` L1361 @ main | H-54 | **LEAF**; `fg = [d]`, `gf = [d]` as morphisms for some `d ≥ 1` | av-split; field `milneIsogenyQuasiInverse` of leaf-fold29; cloud batch 2: briefed (characteristic-zero form); the batch-2 comment of 2026-11-15 02:14Z mentions it only as a possible follow-on (claims.tsv) | published form: Milne 1986 Rem. 8.4; Mumford §7 (av-split §1) |
| H-105 | `ZInQ.HomLattice.GAGAMorphism` | `scratch/av-split/AvSplitAll.lean` L1029 @ main | H-69 | **LEAF**; GAGA for homomorphisms of complex abelian varieties | av-split; field `gagaMorphism` of leaf-fold29; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Serre, GAGA, in the form of homlattice §3.2 (av-split §1) |
| H-109 | `ZInQ.HeightSplit.JavanpeykarBound` | `scratch/height-split/HeightSplit.lean` L508 @ main | H-14 | **LEAF**; Javanpeykar's bound over the published stable height | height-split; field `javanpeykarBound` of leaf-fold29 | published form: specialization of Javanpeykar 2014 Thm 1.1.1 to `K` with a `K`-rational Belyi function (height-split §4; leaf-fold8 §2; height-split §7 notes that a stricter reader may call it a consequence) |
| H-110 | `ZInQ.HeightSplit.GaudronRemondThm14` | `scratch/height-split/HeightSplit.lean` L773 @ main | H-15 | **LEAF**; Gaudron–Rémond's bound over the published stable height | height-split; field `gaudronRemondThm14` of leaf-fold29 | published form: Gaudron–Rémond 2014 Thm 1.4 (height-split table) |
| H-112 | `ZInQ.HeightSplit.BostLowerBound` | `scratch/height-split/HeightSplit.lean` L429 @ main | H-17 | **LEAF**; `h_D ≥ −(g/2) log 2π` (Deligne's normalization) | height-split; field `bostLowerBound` of leaf-fold29 | published form: Bost, Sém. Bourbaki 795 (display unread; height-split §2) |
| H-113 | `ZInQ.HeightSplit.PazukiCor13Upper` | `scratch/height-split/HeightSplit.lean` L717 @ main | H-18 | **LEAF**; the upper side of Pazuki's comparison of theta and Faltings heights | height-split; field `pazukiCor13Upper` of leaf-fold29 | published form: Pazuki 2012 Cor. 1.3(2), read off the same display (height-split §3) |
| H-118 | `CurveSplit.RegularSmoothPerfect` | `scratch/curve-split/CurvesGSplit.lean` L81 @ main | H-81 | **LEAF**; a finite type algebra over a perfect field is smooth at a prime with regular local ring | curve-split; field `regularSmoothPerfect` of leaf-fold29; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Stacks 00TV, the ⇐ half (curve-split §3.3) |
| H-120 | `ZInQ.Contrib.HodgeSplit.TateTwistInvariants` | `scratch/hodge-split/HodgeSplit.lean` L65 @ main | H-8, H-51, H-52 | **LEAF**; `ℂ_p(i)^{G_K} = 0` for `i ≠ 0` | hodge-split; field `tateTwistInvariants` of leaf-fold29; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Tate 1967 §3.3 Thm 2 (hodge-split §1) |
| H-121 | `ZInQ.Contrib.HodgeSplit.AxSenTate` | `scratch/hodge-split/HodgeSplit.lean` L75 @ main | H-8, H-51, H-52 | **LEAF**; `ℂ_p^{G_K} ⊆ K` | hodge-split; field `axSenTate` of leaf-fold29; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Tate 1967 §3.3 Thm 1; Sen 1969; Ax 1970 (hodge-split §1) |
| H-122 | `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` | `scratch/hodge-split/HodgeSplit.lean` L343 @ main | H-8 | **LEAF**; the Hodge–Tate decomposition of `ℂ_p ⊗ V_p(A)` | hodge-split; field `hodgeTateDecompAbVar` of leaf-fold29 | published form: Fontaine 1982; Faltings 1988 (hodge-split §1) |
| H-123 | `ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` | `scratch/hodge-split/HodgeSplit.lean` L1988 @ main | H-8 | **LEAF**; `Hom(V_p A, ℚ_p)` is de Rham | hodge-split; field `deRhamH1AbVarT` of leaf-fold29 | published form: Faltings 1989; Tsuji 1999; Scholze 2013 Cor. 1.8, Hom form (hodge-split §1) |
| H-125 | `ZInQ.Contrib.HodgeSplit.DSThm965` | `scratch/hodge-split/HodgeSplit.lean` L1106 @ main | H-10, H-22 | GLUE (composite); `k ≥ 2`: the Galois representation of an eigenform and its Frobenius polynomials | hodge-split; field `dsThm965` of leaf-fold29 | composite: Diamond–Shurman Thm 9.6.5 (Deligne 1971; Shimura 1971 Thm 7.14) (hodge-split §1); kinds.tsv: published kind, LEAF in its strict column, GLUE in its strictest (DS 9.6.5 may print only that Frobenius satisfies the polynomial, not that it is the characteristic polynomial; page check pending), so a composite by the integrator's convention |
| H-126 | `ZInQ.Contrib.HodgeSplit.DSThm966` | `scratch/hodge-split/HodgeSplit.lean` L1124 @ main | H-10, H-22 | **LEAF**; `k = 1`: the Artin representation of an eigenform | hodge-split; field `dsThm966` of leaf-fold29 | published form: Deligne–Serre 1974 Thm 4.1; Diamond–Shurman Thm 9.6.6 (hodge-split §1) |

### 4.7 Props open only in scenario F, introduced in r4 (9: 1 LEAF, 8 GLUE strict; 3 LEAF, 6 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4'''''''''. Its form is the task
report's label, or my reading where the report's own text (docstring or review) names more than one source; the
pointer says which.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-89 | `MCRGlue.ProperCurveAF` | `scratch/mcr-glue/MCRGlue.lean` L4044 @ main | H-84 | GLUE (composite); L1: finite sets of points of a proper smooth curve over `ℤ_(p)` lie in an affine open | mcr-glue; after main: p1-quot (`quotientP1Coordinate`); p1-quot2 (`quotientP1Coordinate`); p1-quot3 (`quotientP1Coordinate`) | composite: Lichtenbaum 1968 Thm 2.8 with EGA II 4.5.4 (mcr-glue §3: composite of two results) |
| H-90 | `MCRGlue.FiniteQuotientExists` | `scratch/mcr-glue/MCRGlue.lean` L4057 @ main | H-84 | **LEAF**; L2: the quotient by a finite group of `ℤ_(p)`-automorphisms exists and is finite | mcr-glue; after main: p1-quot (`quotientP1Coordinate`); p1-quot2 (`quotientP1Coordinate`); p1-quot3 (`quotientP1Coordinate`) | published form: SGA 1 Exp. V Prop. 1.8 and 1.1, special case (mcr-glue §3) |
| H-91 | `MCRGlue.TameQuotientSmooth` | `scratch/mcr-glue/MCRGlue.lean` L4072 @ main | H-84 | GLUE (composite); L3: a tame quotient of a proper smooth relative curve is proper and smooth | mcr-glue; after main: p1-quot (`quotientP1Coordinate`); p1-quot2 (`quotientP1Coordinate`); p1-quot3 (`quotientP1Coordinate`) | composite: SGA 1 Exp. V, Mumford AV §7 Thm 3, EGA IV 17.5.1 (mcr-glue §3: composite of three results) |
| H-92 | `MCRGlue.SmoothModelOfP1` | `scratch/mcr-glue/MCRGlue.lean` L4086 @ main | H-84 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); L4: a proper smooth `ℤ_(p)`-curve with generic fibre `P¹_ℚ` is `P¹_{ℤ_(p)}` | mcr-glue; after main: p1-quot (`quotientP1Coordinate`); p1-quot2 (`quotientP1Coordinate`); p1-quot3 (`quotientP1Coordinate`) | consequence of one theorem: Liu, AGAC §8.3, §10.1 (mcr-glue §3: STANDARD; reading) |
| H-93 | `MCRGlue.TameFixedPointsDisjoint` | `scratch/mcr-glue/MCRGlue.lean` L4100 @ main | H-84 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); L5: fixed points of a tame automorphism with distinct underlying points have disjoint closures | mcr-glue; after main: p1-quot (`quotientP1Coordinate`); p1-quot2 (`quotientP1Coordinate`); p1-quot3 (`quotientP1Coordinate`) | consequence of one theorem: Edixhoven 1992 Prop. 3.4 with finite étale over a DVR (mcr-glue §3: leaf consequence) |
| H-94 | `MCRGlue.TameInertiaCyclic` | `scratch/mcr-glue/MCRGlue.lean` L4119 @ main | H-84 | GLUE (composite); L6: a finite tame inertia group as in L5 is cyclic | mcr-glue; after main: p1-quot (`quotientP1Coordinate`); p1-quot2 (`quotientP1Coordinate`); p1-quot3 (`quotientP1Coordinate`) | composite: Serre, Local Fields IV §2 Cor. 1 of Prop. 7, with L5's source (mcr-glue §3: composite of two results) |
| H-95 | `HDec.PropTSRed.CoverModelOfHeckeN` | `ZInQKernel/OneProof/H/TailG.lean` L743 @ main | H-84 | GLUE (project glue); the decomposition's own glue: a model of the Hecke cover of level `N` (gives `ModelYIrreducible` with T5) | mcr-quot; after main: p1-quot (`quotientP1Coordinate`); p1-quot2 (`quotientP1Coordinate`); p1-quot3 (`quotientP1Coordinate`) | project glue: open here: the chain derives it only through `HeckeNoVertRam`, downstream of the coordinate that mcr-quot feeds (mcr-quot §1); gap-triage (finding 3, compiled probe): not needed, since `ModelYIrreducible` is the chain's `HeckeIrreducible`, which follows from the field `deligneComponentsY3PrintedAb` (`scratch/gap-triage/GlueProbe.lean`, `MCRQuotNV.lean`); not applied, as the probe takes leaf-fold9's whole bundle `OpenAddedLeaves9` |
| H-96 | `MCRQuot.P1SchemeQ` | `scratch/mcr-quot/MCRQuot.lean` L8549 @ main | H-84 | GLUE (project glue); `P¹_ℚ` exists, is proper and smooth, and represents maps to `P¹` by charts | mcr-quot; after main: p1-quot (`quotientP1Coordinate`); p1-quot2 (`quotientP1Coordinate`); p1-quot3 (`quotientP1Coordinate`) | project glue: foundations: `Proj ℚ[X₀, X₁]` with its functor of points, not in Mathlib (mcr-quot §1) |
| H-97 | `MCRQuot.CMStabObj` | `scratch/mcr-quot/MCRQuot.lean` L7648 @ main | H-84 | GLUE (project glue); each CM class is fixed by a Hecke operation of order exactly 2 on classes (QM objects over `ℚ̄`) | mcr-quot; after main: cm-stab (`CMStabObj`); p1-quot (`quotientP1Coordinate`); p1-quot2 (`quotientP1Coordinate`); p1-quot3 (`quotientP1Coordinate`) | project glue: object-level glue on CM points, no schemes (mcr-quot §1) |

### 4.8 Fields of leaf-fold9 introduced in r5 (0: 0 LEAF, 0 GLUE strict; 0 LEAF, 0 GLUE lenient)

r5's rows here are all gone: H-145 is restated on abelian schemes (route-a-fold), H-146 and H-147 are fields that
scenario F replaces by their strictly henselian forms (§4.1), and r9: H-148, the field `neronSchemeModelExistsDVR`
that leaf-fold9 introduced from reduct-split's `Reduction.lean`, is pruned (r6-nf with neron-dvr, leaf-fold29).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|

### 4.9 Props open only in scenario F, introduced in r5 (1: 0 LEAF, 1 GLUE strict; 1 LEAF, 0 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4'''''''''. Its form is the task
report's label, or my reading where the report's own text names more than one source or gives no label; the pointer
says which. Its H-150 is a field since leaf-fold13 and moved to §4.12. r9: H-154 is off the route (§4.1).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-157 | `ModularSplit.R17.CarayolRealization` | `scratch/modular-split/R17.lean` L127 @ main | H-21 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); some semisimple `ρ` attached to the newform has conductor exponent `v_p(N)` at every `p ≠ ℓ`; the transport to every attached `ρ` is proved | modular-split | consequence of one theorem: Carayol 1986 Thm (A) at his realization (audit), with Casselman's `a(π_p) = v_p(N)` and Ribet's irreducibility (modular-split §2: still a consequence) |

### 4.10 Fields of leaf-fold10 and leaf-fold11 introduced in r6 (1: 1 LEAF, 0 GLUE strict; 1 LEAF, 0 GLUE lenient)

Each row is a field of C4''''''''' that leaf-fold10 or leaf-fold11 introduced, and the hypothesis of a compiled
theorem in its file (`TailZ16`, `TailZ17`: route-a-fold; `TailZ19`: c-to-printed's printed leaves). Forms:
kinds.tsv's. r8: `gonzalezRotgerCountX6Ab` is replaced (gt-grcount), `blr_1_2_4` and `egaIV_8_10_5_openImm` are proved
and `raynaudKernelBound` is pruned. r9: `mumfordRigidityCore` (H-170) becomes `mumfordGroupLaw` and `sga7_IX_3_3`
(H-175) is proved from its strictly henselian form (§4.15); faltings5-lower proves `faltingsLemma5Printed` (H-172;
leaf-fold29); and scenario F replaces the consumer of `deligneComponentsY3PrintedAb` (H-169; dcy3-used, §4.1), still a
field and GLUE in the integrator's convention. leaf-fold10's other new fields are not rows: `neronLocalizesDVR` is
proved since leaf-fold11, and leaf-fold14 replaces the DVR fields.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-174 | `CToPrinted.SGA3_VIB_3_10` | `ZInQKernel/OneProof/H/TailZ19.lean` L199 @ main | H-166 (through `semistableNeronBaseChange`) | **LEAF**; for a smooth group scheme over a base, the union of the identity components of the fibres is open | c-to-printed; field `sga3_VIB_3_10` of leaf-fold29; after main: gt-sga3 (`sga3_VIB_3_10`); cloud batch 3: briefed 2026-11-15, not yet claimed on the issue (claims.tsv) | published form: SGA 3 I Exp. VI_B Thm 3.10 (c-to-printed §4; number unconfirmed, flagged) |

### 4.11 Props open only in scenario F, introduced in r6 (2: 0 LEAF, 2 GLUE strict; 1 LEAF, 1 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4''''''''' (§4.1). Its form is the
task report's label, or my reading where the report gives none or names more than one source (the pointer says
"reading"). r8: H-182 is a field since leaf-fold14 (§4.14), and H-185 and H-187 are replaced; r9: H-188 is proved
(gt-unip, leaf-fold20). r6's branch heads are merged (w66), so the rows point at main; r6's rows for x6-glue's leaves
are replaced by fields (§4.12).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-181 | `CToPrinted2.KatoRealizationCohSS` | `scratch/c-to-printed2/CToPrinted2.lean` L618 @ main | H-158 (from H-127) | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); some semisimple `ρ` attached to the newform, with Kato's Hodge–Tate weights; with the fields `tateTwistInvariants` and `axSenTate` it gives `eigenformHTNew`, and is equivalent to it over the bundle | c-to-printed2; after main: ht-exists (`eigenformHTNew`) | consequence of one theorem: Kato, Astérisque 295 (2004) §8.3 and §§9.2-9.4 at his `V_{F_λ}(f)`, quantified existentially (c-to-printed2 §2.1; locators read by locators.md row R13): the report's label, a consequence |
| H-190 | `HDec.HSyn.G0Split.ThetaPt.ThetaGlue.LinYangThetaCurve` | `scratch/theta-glue/ThetaGlue.lean` L593 @ main | H-133, H-134 (from H-44) | GLUE (composite); along the explicit QM curve `τ ↦ Ω(τ)`: `ψ₄ψ₆ = 2¹²3⁵χ₁₀` and `ψ₄³ + ψ₆² = 2¹²3⁶χ₁₂` in Igusa's theta expressions | theta-glue; after main: linyang-printed (`LinYangThetaCurve`); theta-fold (`thetaRatiosAlgebraic`) | composite: Lin–Yang, Math. Z. 295 (2020), Example 29 with eqs. (13)-(14), after eliminating `j` (so weaker than the print), with Igusa's theta expressions (Amer. J. Math. 89 (1967) §4); locators UNVERIFIED; numerically VERIFIED (80 digits at 12 points); theta-glue's label: a composite; igusa-alg proves `IgusaAlg 5` to `9`, so the route rests on this leaf alone (`qmThetaSymmetricCurve_of_linYang`) |

### 4.12 Fields of leaf-fold13 introduced in r7 (3: 3 LEAF, 0 GLUE strict; 3 LEAF, 0 GLUE lenient)

Each row is a field of C4''''''''' that leaf-fold13 introduced (x6-fold), and the hypothesis of a compiled theorem in
`TailZ20`-`TailZ22`: x6-glue's leaves restated on abelian schemes (r6's rows H-142, H-177, H-178, H-179); H-150 keeps
its row from r5 (until r6 open only in scenario F). Forms: kinds.tsv's. r8: H-195 is replaced by gt-elkies's leaf; r9:
H-196 is proved from H-209 (gt-rayclass, §4.15), and bg-explicit proves `babaGranathRationalAb` (H-193; leaf-fold29).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-150 | `HDec.QMSplit.Moduli.GeomConnOfAlgClosure` | `ZInQKernel/OneProof/H/TailZ20.lean` L1842 @ main | H-140 (from H-1) | **LEAF**; a proper `X → Spec k` with `X ×_k k̄` connected is geometrically connected | shimura-split; field `geomConnOfAlgClosure` of leaf-fold29 | published form: EGA IV₂ 4.5.1-4.5.2; Stacks 0389, weakened by `IsProper` and characteristic 0 (shimura-split §2, §3.2) |
| H-192 | `ShimuraGlue.DeligneComponentsX6PrintedAb` | `ZInQKernel/OneProof/H/TailZ22.lean` L33 @ main | H-177 | **LEAF**; Deligne's theorem on `π₀` in printed form at level `𝒪̂^×`, on one coarse witness `X₆`, on abelian schemes; with `ℚ^×_{>0}\𝔸_f^×/nrd(𝒪̂^×) = 1` (compiled) it gives `DeligneComponentsX6` | x6-fold; field `deligneComponentsX6PrintedAb` of leaf-fold29 | published form: Deligne, Sém. Bourbaki 389 (1971) Thm 2.4 and §3; PSPM 33 (1979) 2.1.3, 2.6.3 (shimura-glue §2, x6-glue §2; UNVERIFIED), at level `𝒪̂^×`; x6-fold restates it on abelian schemes (`R1fpPropsAb`, the printed fine-moduli problem; `deligneComponentsX6Printed_iff_ab` with the field `mumfordRigidityCore`, H-170) |
| H-194 | `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` | `ZInQKernel/OneProof/H/TailZ22.lean` L64 @ main | H-142 | **LEAF**; some coarse witness, on abelian schemes, has the residue fields of CM points (`R5ptProps`) | x6-fold; field `gonzalezRotgerX6Ab` of leaf-fold29 | published form: González–Rotger 2006 Thm 5.12 (qm-glue §4.2; UNVERIFIED); x6-fold restates it on abelian schemes (`R1fpPropsAb`, the printed fine-moduli problem; `gonzalezRotgerX6_iff_ab` with the field `mumfordRigidityCore`, H-170) |

### 4.13 Props open only in scenario F, introduced in r7 (0: 0 LEAF, 0 GLUE strict; 0 LEAF, 0 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4''''''''' (§4.1). r7's rows here
were unipotent-b's printed SGA 7 IX 3.5 and its glue; r9: both are off the route (H-197, H-198), since leaf-fold20
proves `semistableUnipotent` from gt-unip's leaf. r8: t09-pic's four leaves are fields since leaf-fold14 (§4.14).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|

### 4.14 Fields of leaf-fold14 to leaf-fold19 introduced in r8 (8: 7 LEAF, 1 GLUE strict; 7 LEAF, 1 GLUE lenient)

Each row is a field of C4''''''''' that leaf-fold14 to leaf-fold19 introduced, and the hypothesis of a compiled
theorem in its file: leaf-fold14's fold 1, reduct-b's Route B-cp (H-182, H-203; the third, `strictHenselizationPair`,
is replaced by gt-shpair's H-205 in leaf-fold18), and fold 2, t09-pic's four leaves (H-199 to H-202); gt-grcount's
H-204 (leaf-fold17). Forms: kinds.tsv's, with the integrator's convention for `weilPairingMumford` (a composite in the
strictest reading). r9: H-206 is replaced by elkies-coord's H-213 (§4.15).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-182 | `ReductGlue.RaynaudSemistableSH` | `ZInQKernel/OneProof/H/TailZ14.lean` L1105 @ main | H-160 | **LEAF**; Raynaud's criterion over a strictly henselian DVR; with `strictHenselizationPair` (from H-205) and `mulEtaleAbelianScheme` (proved since leaf-fold19) it gives the general-DVR form | reduct-glue; field `raynaudSemistableSH` of leaf-fold29 (since leaf-fold14); after main: sga7-cp (`raynaudSemistableSH`) | published form: SGA 7 I Exp. IX Prop. 4.7 over a strictly henselian DVR (reduct-glue §4; locator UNVERIFIED); kinds.tsv: a reading risk (the print may assume an algebraically closed residue field, reduct-b §5), rated low by the next-fold review |
| H-199 | `T09Pic.PicRepresentableAbVar` | `ZInQKernel/OneProof/H/TailZ24.lean` L289 @ main | H-53 | **LEAF**; the relative Picard fppf sheaf of an abelian variety is representable | t09-pic; field `picRepresentableAbVar` of leaf-fold29 (since leaf-fold14); cloud batch 3: briefed 2026-11-15, not yet claimed on the issue (claims.tsv) | published form: Murre (1964), Oort (1962); FGA Exp. 232 Thm 3.1; Kleiman, The Picard scheme, Thm 9.4.8 with Thm 9.2.5 (t09-pic §3; UNVERIFIED) |
| H-200 | `T09Pic.PicZeroAbVar` | `ZInQKernel/OneProof/H/TailZ24.lean` L302 @ main | H-53 | **LEAF**; the identity component of the Picard scheme is an abelian variety, by an open immersion that is a homomorphism | t09-pic; field `picZeroAbVar` of leaf-fold29 (since leaf-fold14); cloud batch 3: briefed 2026-11-15, not yet claimed on the issue (claims.tsv) | published form: Mumford, Abelian Varieties §13; Kleiman Prop. 9.5.1 and 9.5.3; Milne 1986 §§9-10 (t09-pic §3; UNVERIFIED) |
| H-201 | `T09Pic.PhiAmpleIsogeny` | `ZInQKernel/OneProof/H/TailZ24.lean` L366 @ main | H-53 | **LEAF**; for an ample `L`, the homomorphism `λ` with `λ ≫ ι = φ_L` is finite and surjective | t09-pic; field `phiAmpleIsogeny` of leaf-fold29 (since leaf-fold14); cloud batch 3: briefed 2026-11-15, not yet claimed on the issue (claims.tsv) | published form: Mumford §6 Application 1 and §8 Thm 1 (t09-pic §3; UNVERIFIED), the kind in kinds.tsv, flagged: finiteness over a non-closed `K` descends from `K̄`, and Mumford states Application 1 for effective `D` (r7 read it as a consequence) |
| H-202 | `T09Pic.WeilPairingMumford` | `ZInQKernel/OneProof/H/TailZ24.lean` L708 @ main | H-53 | GLUE (composite); for `n` invertible in `K`, a perfect, `G_K`-equivariant, compatible pairing `A[n] × Pic⁰[n] → μ_n` with Mumford's values (`weilScalar`), adjoint for the genuine `f^∨`, with `e_n(x, λ_L x) = 1` for ample `L` | t09-pic; field `weilPairingMumford` of leaf-fold29 (since leaf-fold14) | composite: Mumford §20 and §23; Milne 1986 Lemma 16.2(c) and §16 (t09-pic §3; UNVERIFIED); kinds.tsv: published kind, LEAF in its strict column, GLUE in its strictest (one leaf bundling several printed properties of `e_n`), so a composite by the integrator's convention; t09-pic's label: a consequence of the print; it also compiles the split into one printed property per leaf (L4a-L4f, `t09SymmIsogenyExists_of_split`) |
| H-203 | `ReductB.SemistablePersistsSHcp` | `ZInQKernel/OneProof/H/TailZ23.lean` L317 @ main | H-185 | **LEAF**; SGA 7 IX 3.3, first assertion (semistable reduction persists in finite extensions), over a strictly henselian DVR of a field of characteristic 0 with perfect (hence algebraically closed) residue field; a specialization of `SemistablePersistsSH`; with `strictHenselizationPair` it gives SS1 and SS3 at number fields (`ReductB.ss1_ss3_of_cp`) | reduct-b; field `semistablePersistsSHcp` of leaf-fold29 (since leaf-fold14) | published form: SGA 7 I Exp. IX Prop. 3.3, first assertion, restricted to characteristic 0 and an algebraically closed residue field (number UNVERIFIED; reduct-b's Route B-cp); kinds.tsv: a specialization of every reading of the print, rated (a) by the next-fold review |
| H-204 | `GRCountX6.GonzalezRotgerProp56X6` | `ZInQKernel/Contrib/OneProof/GRCountX6.lean` L72 @ main | H-168 | **LEAF**; González–Rotger's count on every witness of the moduli description of `X₀(6,1)`, with no existence claim: the CM points by an order `R` that occurs as some `End_𝒪(A)` number `2^{inertCount6 k}·#Pic(R)`; with the field `gonzalezRotgerX6Ab` it gives `gonzalezRotgerCountX6Ab` | gt-grcount; field `gonzalezRotgerProp56X6` of leaf-fold29 (since leaf-fold17); after main: gr56-prove (`gonzalezRotgerProp56X6`) | published form: González–Rotger, J. Math. Soc. Japan 58 (2006) Prop. 5.6, p. 943 (read by the locator audit), at `(D, N) = (6, 1)` (gt-grcount; statement review 11-14, two lenses: faithful); kinds.tsv flags that `D(R)`, the product of the `p ∣ D` with `(R/p) = −1`, is to be confirmed against the paper |
| H-205 | `GapSHPair.NeronBaseChangeStrictHenselization` | `ZInQKernel/Contrib/OneProof/StrictHenselizationPair.lean` L1527 @ main | H-187 | **LEAF**; Néron models commute with strict henselization: for a DVR `O` and an unramified strictly henselian extension `O₁` with `K₁/K` separable (`IsSHSep`, which pins `O₁` as `O^sh` in every characteristic), the base change of a Néron model is a Néron model; gt-shpair proves `StrictHenselizationPair` from it | gt-shpair; field `neronBaseChangeStrictHenselization` of leaf-fold29 (since leaf-fold18); cloud batch 3: briefed 2026-11-15, not yet claimed on the issue (claims.tsv) | published form: Bosch–Lütkebohmert–Raynaud, Néron models, §1.2 Prop. 2 (gt-shpair; locator UNVERIFIED; statement review 11-14, two lenses: published form); a specialization of the chain's `NeronBaseChangeUnramifiedDVR` |

### 4.15 Fields of leaf-fold20 to leaf-fold26 introduced in r9 (7: 4 LEAF, 3 GLUE strict; 5 LEAF, 2 GLUE lenient)

Each row is a field of C4''''''''' that leaf-fold20 to leaf-fold26 introduced, and the hypothesis of a compiled
theorem in its contribution file: gt-sga7's H-207 and gt-unip's H-208 (leaf-fold20); gt-rayclass's H-209 and
sgr-split's H-210 (leaf-fold22); gt-rigidity's H-211 (leaf-fold23); r16-split's H-212 (leaf-fold25); elkies-coord's
H-213 (leaf-fold26). Forms: kinds.tsv's. leaf-fold27 to leaf-fold29 introduce no field; leaf-fold29's six new
hypotheses of the top are TYZ rows (T-18 to T-23, §3.2).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-207 | `SGA7PersistsNF.SGA7_IX_3_3_SH` | `ZInQKernel/Contrib/OneProof/SGA7PersistsNF.lean` L60 @ main | H-175 | **LEAF**; SGA 7 IX 3.3, second assertion, over strictly henselian traits: for semistable reduction `N ×_S S' → N'` induces `N⁰ ×_S S' ≅ N'⁰`; the field statement of `sga7_IX_3_3` with both DVRs strictly henselian; with `neronBaseChangeStrictHenselization` and fpqc descent gt-sga7 proves the general-DVR field (`SGA7PersistsNF.sga7_IX_3_3_of_SH`) | gt-sga7; field `sga7_IX_3_3_SH` of leaf-fold29 (since leaf-fold20) | published form: SGA 7 I Exp. IX Prop. 3.3, second assertion, over strictly henselian traits (gt-sga7; number UNVERIFIED); kinds.tsv: the print may assume an algebraically closed residue field, and then the restricted form `SGA7_IX_3_3_SHcp` is the print; statement review 11-15 (two lenses, AI, no print): true for every residue field and characteristic |
| H-208 | `UnipotentForward.SGA7_IX_3_5_ForwardGeom` | `ZInQKernel/Contrib/OneProof/UnipotentForward.lean` L420 @ main | the field `semistableUnipotent` (r8: H-197, H-198 in scenario F) | **LEAF**; SGA 7 IX 3.5, forward direction at `σ = τ`, over a strictly henselian DVR with `Ω = K^s` and `ℓ` invertible: if `A` has semistable reduction (read on the geometric special fibre), every `σ` in inertia satisfies `(σ − 1)² = 0` on `T_ℓ(A)`; gt-unip proves the field `semistableUnipotent` from it, with `StrictHenselizationInside` proved from a Néron leaf of the chain | gt-unip; field `sga7_IX_3_5_ForwardGeom` of leaf-fold29 (since leaf-fold20); after main: sga7-cp (`sga7_IX_3_5_ForwardGeom`) | published form: SGA 7 I Exp. IX Prop. 3.5, forward direction at `σ = τ` (gt-unip; number UNVERIFIED); kinds.tsv: if Prop. 3.5 reads semistability on the `k(s)` fibre, a consequence through `SemiAbelianDescendsSepClosed`, and if its display lacks the echelon clause the square-zero bound comes from IX 2.4; statement review 11-15 (two lenses, AI, no print): yes, a consequence under the alternative readings |
| H-209 | `RayClassCFT.ShimuraMainThmIDeligneY3AbU` | `ZInQKernel/Contrib/OneProof/RayClassShimura.lean` L1152 @ main | H-196 and the field `shimuraFamilyAb` (r8: H-154 in scenario F) | GLUE (composite); Shimura's Main Theorem I in Deligne's adelic form on the fine witness `Y₃`, on abelian schemes, with the moduli clause at every `u ∈ 𝒪̂^×` (`ModuliAtUnits`): the QM pair at `[τ, g]` and reciprocity at CM points; gt-rayclass proves `rayClassCMAb` (without rigidity) and `shimuraFamilyAb` from it, with `ClassNumberOneB` proved | gt-rayclass; field `shimuraMainThmIDeligneY3AbU` of leaf-fold29 (since leaf-fold22); after main: composite-out (`shimuraMainThmIDeligneY3AbU`); shimura-split2 (`shimuraMainThmIDeligneY3AbU`) | composite: Shimura, Ann. of Math. 85 (1967) Main Theorem I; Deligne, Sém. Bourbaki 389 (1971) §§4.9-4.21 and §5 (the PEL model is Cor. 5.7 / Ex. 5.8); Milne, Introduction to Shimura varieties §§12-14 (gt-rayclass; locators UNVERIFIED); the docstring's label: a consequence (the moduli clause only for `g ∈ 𝒪̂^×`); kinds.tsv: a composite, pending review |
| H-210 | `SGRSplit.ShimuraIntegralModelRep` | `ZInQKernel/Contrib/OneProof/ShimuraGoodReductionNoGuard.lean` L94 @ main | H-119 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); the integral model of the Shimura curve of level 3 represents the polarization-free moduli problem of QM abelian surfaces with level structure over locally noetherian bases on which 3 is invertible (only `p > 324` is asserted); sgr-split proves `shimuraGoodReductionNoGuard` from it, with `SmoothGeomConnIntegral` and `AbVarEndTorsionFree` proved from the kernel | sgr-split; field `shimuraIntegralModelRep` of leaf-fold29 (since leaf-fold22); after main: sgr-direct (`shimuraIntegralModelRep`); sir-printed (`shimuraIntegralModelRep`) | consequence of one theorem: Kottwitz, J. AMS 5 (1992) §5; Buzzard, Duke Math. J. 87 (1997) §§1-4; Morita, Hokkaido Math. J. 10 (1981); Lan 2013, Thms 1.4.1.11 and 5.3.3.1 (sgr-split; locators UNVERIFIED); kinds.tsv: pending reading: the printed functor is Kottwitz's PEL form, so this polarization-free integral form needs a relative Lemma P and the comparison of rational with integral level structures, and Buzzard's and Morita's level may have to be prime to `D` |
| H-211 | `ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw` | `ZInQKernel/Contrib/OneProof/MumfordRigidity.lean` L82 @ main | H-170 | **LEAF**; Mumford's GIT Thm 6.14: with the hypotheses of `MumfordRigidityCore` (`S` locally noetherian, `F → S` proper, smooth, geometrically connected, a section `e`, every field fibre an abelian variety with origin `e(s)`), `F` carries a group object structure in `Over S` with identity `e`; the existence half of `MumfordRigidityCore` without its clause (a), so Cor. 6.4 is no longer assumed; rigid-prune routes the chain's conversions through `QMFamilyGroupLaw`, proved from it | gt-rigidity; field `mumfordGroupLaw` of leaf-fold29 (since leaf-fold23); cloud batch 3: briefed 2026-11-15, not yet claimed on the issue (claims.tsv) | published form: Mumford–Fogarty–Kirwan, GIT Thm 6.14, on each connected component of `S` (gt-rigidity; numbers UNVERIFIED); the docstring calls it a consequence (the group laws glued over the components), and kinds.tsv counts it published, pending a statement review |
| H-212 | `R16Split.R16CoreY` | `ZInQKernel/Contrib/OneProof/R16Split.lean` L534 @ main | H-13 | GLUE (composite); R16 without its rank-two clause (Eichler–Shimura on `J₁(N)`, existential form): for a newform `f`, an abelian variety `A/ℚ`, a surjection `J₁(N) → A` and `θ : K_f → End⁰(A)` with `dim A = [K_f:ℚ]`, Frobenius at `p ∤ Nℓ` acting on each `ι`-component of `V_ℓ(A)` with trace `ι(a_p(f))` and determinant `ι(χ(p))p`; r16-split proves `r16` from it (the rank-two clause from `dim A = [K_f:ℚ]` and Mumford §19 Thm 4) | r16-split; field `r16CoreY` of leaf-fold29 (since leaf-fold25); after main: r16-used (`r16CoreY`) | composite: Shimura 1973 Thm 1, unconditional clauses; Shimura 1971 Thm 3.52 and Thm 7.11 (from the congruence relation, Thm 7.9); Diamond–Shurman Thm 9.5.4 (r16-split; locators UNVERIFIED); a composite, like `r16` |
| H-213 | `HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField` | `ZInQKernel/Contrib/OneProof/ElkiesX6StarPrinted.lean` L814 @ main | H-206 | **LEAF**; Elkies' coordinate in function-field form on one witness of the moduli clause: `ℚ(X₆)^W = ℚ(t)` (under the integrality that the charts give), the CM values `t = 0, 1, ∞` at discriminants −24, −4, −3, and the two charts of `X₆` over the `t`-line; elkies-coord proves `elkiesX6StarPrinted` (the fibres of `t` are the `W`-orbits) from it | elkies-coord; field `elkiesX6StarFunctionField` of leaf-fold29 (since leaf-fold26) | published form: Elkies, ANTS-III (1998) §3: `X*(6) = X₆/W` with coordinate `t` (elkies-coord; section, display and the `0/∞` orientation UNVERIFIED); the printed coordinate statement in function-field form, never stronger (the docstring); kinds.tsv: published, pending review |

### 4.16 Bundle fields never projected, and the prune (not on the list)

r9: yu-prune (`docs/research/yu-prune.md`) removes `yuThm11` (H-128) from every bundle generation: its consumers take
`YuB6Alg`, proved from three textbook fields; its scan finds 0 unused of 57 fields after the prune. flt-cqj2's fold
deletes `igusaGL2` (H-117) from generations 7 to 11, since its one consumer takes the proved `X0Transitive`. r6-nf
(`docs/research/r6-nf.md`, with neron-dvr) removes `neronSchemeModelExistsDVR` (H-148; BLR 1.4/3 over every DVR): of
its three uses, `r8` was only copied between bundles and is pruned from every generation, and `r6` and SS1/SS3 are
applied only at number fields, where neron-dvr's theorem gives them from the textbook field N1
(`neronSchemeExtensionExists`, H-77); its scan finds 0 unused fields among the rest. `chain.py`'s `UNUSED` is empty.

Until r8:
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

### 4.17 Statement reviews of the leaves (leaf-review-a, leaf-review-b, leafq-check, the r4 to r9 tasks)

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

The r9 tasks and folds checked their new leaves with AI statement reviews (two lenses, no print, 11-15; recorded in
kinds.tsv's `rated_by`); none had network access, so every locator is UNVERIFIED. leaf-fold20's two SGA 7 IX leaves
pass (`SGA7_IX_3_5_ForwardGeom` is a consequence under the alternative readings); `hFH` is a consequence of
Friedberg–Hoffstein's Theorem B, pending a reading of three clauses; `shimuraIntegralModelRep` is pending a reading of
the PEL functor and the level comparison. The integrator's dictionary ruling (11-15) re-rates `hCM` and
`uniformizationLeafAll` as consequences (each reached from its print through analytification), and `open-leaf-def`
restates OPEN.md's LEAF as the printed form or a direct instance of it. h33-sign verifies the `[i]` sign of `TYZThm33`
from the paper and pins it in Lean. gz-hl3 finds that Heegner rationality with a complex constant `c` is false for CM
curves, so its leaves take `c ∈ ℚ^×`; gz-heegner finds that the former `hX` covers only functions regular on `ℍ`, so
the Heegner point needs `X0ModuliGaloisMero`. After main, leaf-audit finds theta-fold's `LinYangEx29All` false and the
other 15 leaves of 11-15 sound. h29-fix finds TYZ's Lemma 2.9 false as printed at `n = 3` (`Q(3) = ±3` while `𝓛(3)² =
1`, by computation), so h29-ne3 restricts it to `n ≠ 3` and takes Theorem 2.1's instance at `(3, 1)`; kinds.tsv rates
the six leaves published, each restricted from the print, unread, or both. The integrator's statement review (11-15)
rates gz-hl3's two Gross–Zagier statements at the curves `C_d` as consequences (claims.tsv), where gz-hl3 rated them
printed; this report follows the review (Z-5, Z-6).

## 5. Completeness check

### 5.1 Scenario A (compiled composite)

`python3 scratch/frontier/chain.py A` (from the repository root): 0 signature mismatches; 62 open nodes = the 26 + 11
+ 13 + 1 = 51 fields of C4'''''''''s four bundles (each expanded from the structure as read at main) plus the 11 TYZ
and GZ hypotheses of the top: the hypothesis list of the composite of C2, Z6, B9, B10 and C4''''''''', all of them
used (§4.16). With kinds.tsv's forms (strictest reading, and its `frozenTarget` rows for the top): 47 LEAF and 15 GLUE
strict, 53 and 9 lenient; with `weilPairingMumford` and `dsThm965` published (kinds.tsv's strict column): 49 LEAF and
13 GLUE strict. `chain.py onep`: its hypotheses are scenario A's (the four bundles and the eleven top Props); the
bundles' fields are the 51 field rows of `kinds.tsv`, with the names and type heads of the build's
`open-statements.json`, whose eleven other hypotheses have scenario A's heads.

### 5.2 Scenario F (frontier)

`python3 scratch/frontier/chain.py F`: 0 signature mismatches over 207 theorem edges in the file (26 followed on the
route, among them 2 consumer replacements; no modus-ponens step and no transfer along an equivalence is followed); 72
open nodes = the 72 of §0 (no never-projected field is left). Where a followed edge's file is not the H base, the
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
The F-only edges in library files outside OneProof/H (gz-statements, jacobi-lambda, gz-heegner, modular-split,
c-to-printed2) prove library constants: each file imports ZInQKernel modules and has no definition of the Prop it
proves (or only a copy for an `rfl` check), and imports the module that defines it, which `OneProof/Main.lean` imports
too or the file of the edge that takes it; or the file is the library module that defines the Prop, and the edge that
takes it is in that module (`worldcheck`):
- `FrozenTarget` (`ZInQKernel/Contrib/GZStatements/Weak.lean`): defined in `ZInQKernel/Target.lean`.
- `GrossZagierHeegnerCd` (`ZInQKernel/Contrib/OneProof/GrossZagierHeegner/JacobiLambdaDeriv.lean`): defined in `ZInQKernel/Contrib/GZStatements/Weak.lean`, the file that takes it.
- `HeegnerPointRationalCd` (`ZInQKernel/Contrib/OneProof/GrossZagierHeegner/HeegnerCd.lean`): defined in `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Cd.lean`, which `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/JacobiLambdaDeriv.lean` (the file that takes it) imports.
- `FHNonvanishingCd` (`ZInQKernel/Contrib/GZStatements/Weak.lean`): defined there, and taken there.
- `CarayolR17'` (`scratch/modular-split/R17.lean`): defined in `ZInQKernel/HDecomp/Conductor/LadicCond.lean`.
- `EigenformHTNew` (`scratch/c-to-printed2/CToPrinted2.lean`, which has only a `Verbatim` copy for an `rfl` check): defined in `ZInQKernel/OneProof/H/TailS.lean`.
No followed edge concludes a kernel constant written with `_root_` in the bundles, so `rootcheck` has nothing to
check, and no followed edge's file is over leaf-fold4's chain, so `chaincheck` has nothing to compare either. The
consumer replacements (`bypass_check`: the signatures of the old and the new consumer, and for dcy3-used every use of
the field in OneProof/H):
- `ThetaRatiosAlgebraic`: ok; ok (TailA's `thetaPointOfFibre_of_qm_ratios` and theta-split's `thetaPointOfFibre_of_qm_curve` conclude the same `ThetaPointOfFibre`).
- `DeligneComponentsY3PrintedAb`: ok; ok; every use matches (TailZ12's `deligneComponentsY3_of_printed`, the old route to `Y3Connected`, and dcy3-used's `y3Connected_of_leaves`; the field is otherwise only declared and copied between generations, and consumed once on the old route).
Each F-only row's definition (the file in its row) is identical to the definition in the file of every followed edge
that takes it and has its own copy (9 comparisons; 5 more edges import the Prop instead).
The pairwise checks of r2 still pass. The eight kernel leaf copies that the flat files carried are gone: OneProof/H
imports `ZInQKernel/HDecomp/Objects.lean` itself. mcr-quot's and shimura-split's T5 is the kernel's
`ObjBridge.TorsionStructure` or `PkgI2.TorsionStructure.{0}`, which `Objects.lean` proves equal by `Iff.rfl`
(`torsionStructure_iff`).

`python3 scratch/frontier/chain.py doc` compares the rows `Z-n`, `T-n`, `H-n` with the scenario-F open set: 72 rows
with 72 distinct heads, equal to the open set.

What the script does not check: that the edges compose in one Lean environment; argument instantiation (for example
`heckeVertWitness_of_leaves5` takes `R1R2fp`, extracted from `r1r2` by `Classical.choice`); section variables that a
theorem takes through `include` (none on the route since qm-glue replaced qm-split's `qmHauptmodulBase3_of_O1`); and
the defs that a Prop's def mentions (only the top-level def text is compared).

## 6. Integration state

### 6.1 Composites that exist
- **`ZInQ.OneProof.frozenTarget`** (main; leaf-fold29's bundles; B9 since leaf-fold-hx, B10 since leaf-fold29; Z6
  since leaf-fold24): scenario A as one library theorem (§1).
- **C4''''''''', leaf-fold29** (0e70c94e, over leaf-fold28b, leaf-fold27, leaf-fold26, leaf-fold25 with leaf-fold23
  and leaf-fold24, leaf-fold22b, leaf-fold21, leaf-fold20 and leaf-fold-hx): 26 + 11 + 13 + 1 fields inside OneProof
  (`TailZ33`-`TailZ37` and `TailZ40` over leaf-fold19's `TailZ23`-`TailZ32`, leaf-fold13's `TailZ20`-`TailZ22`,
  leaf-fold11's `TailZ16`-`TailZ19` and `OneProof/Genus/*`, leaf-fold10's `TailZ10`-`TailZ15`, leaf-fold9's
  `TailZ5`-`TailZ9`, leaf-fold8's `TailY`-`TailZ4` and leaf-fold7's `TailP`-`TailX`); the contributions it folds are
  in `ZInQKernel/Contrib/OneProof/`; lake build and axioms REPORTED.
- **The top in the kernel**: C2 (atkin-li) with gz-fh's Z6 in `Contrib/OneProof/FHNonvanishing.lean`, theta-wp8's B9
  in `Contrib/OneProof/ThetaWeierstrass8.lean` and h29-ne3's B10 in `Contrib/OneProof/TYZLemma29Mod2.lean`;
  gz-statements' `C_d` form of C2 (Z7) in `Contrib/GZStatements/Weak.lean`.
- **The contributor and crowd kits** (contrib-kit 46afc732, w66; crowd kit 1c791eb1): `docs/one-proof/OPEN.md` and
  `pages-wanted.md`, generated from the build's `open-statements.json`, `kinds.tsv`, `claims.tsv`, `reviews.tsv`,
  `credits.tsv` and `issues.json`; `ZInQKernel/OneProof/Discharges.lean`, whose `#discharges` names the hypotheses of
  `frozenTarget` that a contribution proves; `scripts/one_proof/autofold.py`, which writes the fold that removes them
  and refuses a rise of either GLUE count; and `scripts/one_proof/frontier_crosswalk.py`, which maps this report's row
  IDs to the hypotheses.
- Superseded: C4'''''''' (leaf-fold19), C4''''''' (leaf-fold13), C4'''''' (leaf-fold11), C4''''' (leaf-fold9), C4''''
  (leaf-fold8), C4''' (leaf-fold6), C4'' (leaf-fold5), C4' (leaf-fold4), C4 (assemble-port) and the variants listed in
  r2.

### 6.2 What folding scenario F into C4''''''''' needs
leaf-fold7 to leaf-fold29 take a fold only if neither GLUE count rises and the fold lowers the strict GLUE count or
replaces a consequence or composite by published-form leaves (leaf-fold9 §5; `autofold.py` refuses a rise). With this
report's forms (SPECULATIVE until compiled):
- dcy3-used's consumer replacement: `deligneComponentsY3PrintedAb` (H-169) goes with no new leaf (strict and strictest
  GLUE −1); `autofold.py` cannot write it, since the used form is weaker than the field, so it needs a hand fold like
  dcy3-used's own bypass (REPORTED compiled);
- the `C_d` form of the top (gz-statements) with gz-hl3's split of it, gz-weil's parametrization, jacobi-lambda and
  gz-heegner: the composite `hL3` goes, the published form Z-4 and three consequences (Z-5, Z-6, Z-7) come, `hCM`
  being a hypothesis already: strict GLUE +2, lenient −1, so the rule keeps it out (claims.tsv: the fold is held). It
  needs the library theorem to take `GrossZagierHeegnerCd` in place of `hL3`, which `#discharges` cannot show (gz-weil
  §0, §5). After the snapshot, heegner-32, gz-conj and gz-moduli reduce the `C_d` form to one leaf,
  `GrossZagierModuliCd`: strict −1 if it rates printed, a rating pending (§7);
- igusa-alg with theta-split: the composite `thetaRatiosAlgebraic` → the composite `LinYangThetaCurve`: neutral, with
  every closed identity proved; linyang-printed and theta-fold, after main, reduce it further (one of theta-fold's
  leaves is false by leaf-audit);
- modular-split (`r17` → `CarayolRealization`) and c-to-printed2 (`eigenformHTNew` → `KatoRealizationCohSS`): neutral
  (consequences both); mcr-glue and mcr-quot (`quotientP1Coordinate` → nine Props, three of them project glue): both
  GLUE counts rise, and p1-quot to p1-quot3, after main, rest it on printed leaves;
- after main on the other rows: the branches listed in §0, marked in the rows.

### 6.3 The library theorem
`ZInQ.OneProof.frozenTarget` has exactly the hypotheses of scenario A, and its proof uses all of them. Since
leaf-fold24 `hFH` replaces `hL2` (Z6), since leaf-fold-hx `hX` is gone (B9), and since leaf-fold29 h29-ne3's six
published leaves replace `h29` (B10), so its TYZ hypotheses are `h11`, the six, `hCM` and `h33`. Each F edge removes
or replaces a hypothesis once folded.

## 7. Findings

**Refresh r9 (2026-11-16).**

1. **Five rows proved, two pruned, eight replaced, five off the route, one split** (§0, §4.1). The 18 new rows are 11
   published forms, 5 consequences of one theorem and 2 composites. The total goes from 75 to 72, the strict count
   from 49/26 to 49/23 and the lenient count from 59/16 to 60/12. Main moved on to leaf-fold30 after the snapshot;
   this report describes leaf-fold29.
2. **Scenario A is one compiled theorem** on main, `ZInQ.OneProof.frozenTarget`, now over leaf-fold29: 62 hypotheses,
   all used. Its 51 fields are 39 LEAF and 12 GLUE strict by the integrator's table (41 and 10 with
   `weilPairingMumford` and `dsThm965` published); with the top, 47 LEAF and 15 GLUE strict, 53 and 9 lenient.
   `chain.py onep` reads its hypotheses from `Main.lean` and finds scenario A's, and the bundles and the top agree
   with `kinds.tsv` and the build's `open-statements.json`.
3. **The top has eleven hypotheses**: `hX` is gone (theta-wp8's B9 takes Shimura reciprocity at level 32 from
   `ShimuraMainCM` alone), `hFH`, a single leaf, replaces the composite `hL2` (gz-fh), and h29-ne3's six published
   leaves replace the composite `h29` (B10). TYZ's Lemma 2.9 is false as printed at `n = 3`, so that case is Theorem
   2.1's instance. Two of the eleven are consequences since the dictionary ruling (`hCM`, `hFH`).
4. **leaf-fold29 removes four fields with no new leaf**: bg-explicit, st-qbar and faltings5-lower prove
   `babaGranathRationalAb`, `shimuraTaniyamaQbar`'s one use and the lower half of Faltings' Lemma 5, and r6-nf with
   neron-dvr applies `r6` only at number fields, so BLR's existence theorem is needed only there (from the field N1).
   dcy3-used, merged by the same fold but not folded, shows that `deligneComponentsY3PrintedAb` is used only as
   `Y3Connected`, which two fields give; scenario F replaces its consumer.
5. **The SGA 7 IX fields are strictly henselian now**: leaf-fold20 proves `sga7_IX_3_3` and `semistableUnipotent` from
   the strictly henselian forms, so unipotent-b's split and its glue `SemiAbelianDescendsSepClosed` are off the route;
   every SGA 7 IX field of the library theorem is stated over a strictly henselian base.
6. **On the curves `C_d` the split of `hL3` has no composite.** gz-hl3 makes the Heegner point a Lean object; on
   gz-statements' `C_d` form of the top, gz-weil's parametrization of `C_d`, with Jacobi's derivative formula proved
   by jacobi-lambda (both on main through leaf-fold-hx), removes its composites `StrongWeilCurve` and
   `IsogenyLattice`, and gz-heegner proves the Heegner point's rationality from `hCM` and a printed consequence.
   Scenario F takes that form (Z7 to Z9): `hL3` rests on one published form and three consequences (the integrator's
   ratings). A fold needs the library theorem to take `GrossZagierHeegnerCd`; strict GLUE +2, lenient −1, so the fold
   is held.
7. **After the snapshot the `C_d` route of `hL3` shrinks to one leaf** (not used here; the branches were pushed after
   the branch heads were read): heegner-32 (718d8d4c) proves `GrossZagierHeegnerCd` from `hCM`, `GrossZagierFormulaCd`
   and `GrossConjugationCd`, with no canonical model of `X₀(N)` and no `WeierstrassUniformization`; gz-conj (2c7ce521)
   proves `GrossConjugationCd` outright; gz-moduli (85111fc7) proves `GrossZagierFormulaCd` from the single leaf
   `GrossZagierModuliCd`, the Gross–Zagier formula in its printed moduli form. Folded, `hL3` would be replaced by
   `GrossZagierModuliCd` alone: strict GLUE −1 if it rates printed. The integrator records this as pending that
   rating, expected −1.
8. **The re-ratings**: the dictionary ruling makes `hCM` and `uniformizationLeafAll` consequences, and `dsThm965`
   carries a strictest-reading flag (Diamond–Shurman may print only that Frobenius satisfies the polynomial), so this
   report records it as a composite, as it does `weilPairingMumford` and `deligneComponentsY3PrintedAb`.
9. **After main** 21 branches report results on 24 rows (§0); this report does not use them until they are merged.
   leaf-audit finds one of theta-fold's two leaves (`LinYangEx29All`) false.
10. **Project glue** is 3 Props: `CMStabObj`, `CoverModelOfHeckeN`, `P1SchemeQ`.
11. **chain.py**: the H base is leaf-fold29 (bundles in `TailZ37`, `TailZ32`, `TailZ34`, `TailX`); B9, B10 and Z6 are
   edges of both scenarios; dcy3-used's consumer replacement joins theta-split's; scenario F's top is gz-statements'
   `C_d` form of C2, with jacobi-lambda's and gz-heegner's `C_d` theorems, and gz-hl3's general split stays in the
   file off the route; `worldcheck` accepts a constant defined in the module of the F edge that takes it, or in the
   edge's own library module.

**Refresh r8** (unchanged):

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

## 8. Tasks (snapshot 11-15 22:48 PST; heads in `scratch/frontier/refs.txt`)

Finished, with results used in r9: gt-sga7 (70a16c4c), gt-unip (42e1af66), yu-prune (a162b51a), gt-rayclass
(28ec5c91), sgr-split (990fb6a6), h33-sign (abfc77cf), gt-rigidity (762ea48b), rigid-prune (98a0a37d), gz-fh
(75a3c0bd), r16-split (e1066890), elkies-coord (398043e7), flt-cqj2 (c894d5ba), theta-wp8 (04afc477), gz-hl3
(bbb6c764), gz-heegner (58a780e4), jacobi-lambda (b6fc38e9), open-leaf-def (c0f4abb8), bg-explicit (c47e220c), st-qbar
(0de7c471), faltings5-lower (8391dc2a), neron-dvr (998fa5b5), r6-nf (0bc2446d), h29-split (14503253), h29-fix
(0f61e9c0), h29-ne3 (a03caff2), dcy3-used (36240662); the folds leaf-fold20 (24f97774), leaf-fold21 (47bba295),
leaf-fold22b (9a100aa7), leaf-fold23 (aa9763a1), leaf-fold24 (b2ae6c53), leaf-fold25 (bc90deac), leaf-fold26
(86755ad8), leaf-fold27 (f3f288d8), leaf-fold-hx (862bd440), leaf-fold28b (8961bb09), leaf-fold29 (main 0e70c94e; its
branch is gone). After main, not used: cm-stab (feff8ecd), composite-out (822da7b5), faltings-cm (ce696e14),
fh-printed (8d0b9b64), gr56-prove (90b817cb), gt-sga3 (deba22d7), gz-weil (ad22e947), hcm-printed (15055182),
ht-exists (7088f9ed), linyang-printed (3bb5a828), theta-fold (8e3dbdea), p1-quot (319fa317), p1-quot2 (19793c5d),
p1-quot3 (b533b204), pb-bypass (c1636db9), r16-used (dcf24ac6), sga7-cp (0c200c57), sgr-direct (56478c75), sir-printed
(e5968542), shimura-split2 (838a7430), unif-printed (9c2e1809). Used in r8 and compiled inside C4''''''''' since:
leaf-fold14 to leaf-fold19, sem-prune, the crowd kit and the gt tasks of r8; read in r8, off the route now:
unipotent-b (24c44f3d), shimura-cft (c1f76fc2). Used in r7 and still applied by scenario F: igusa-alg (c9360203). Used
in r6 and compiled inside C4''''''''' or applied by scenario F: leaf-fold11, leaf-fold10, the prune, genus-fold,
route-a-fold, shimura-glue, reduct-glue, dimjac-glue, theta-split, genus-route, r1univ-rigid, theta-glue,
c-to-printed2, t5-glue, x6-glue. Used in r5: leaf-fold9, shimura-split, reduct-split, modular-split and tyz-split's
statement review. Used in r4: leaf-fold8, mcr-quot, coarse-factor, cloud-w07 (fork PR #11), leaf-fold7, height-glue,
qm-glue, leaf-fold6, mcr-glue, av-glue, av-split, height-split, curve-split, hodge-split, qm-split, tyz-split, fork
PRs #6-#10. Used in r3: leaf-fold5, leafq-check, tyz-chain and the r2 tasks. Read, not folded: leaf-review-a,
leaf-review-b. Cloud claims: claims.tsv (§0).

Running tasks are on the fork's tracker issue #3.

gz-statements (Contrib modules `ZInQKernel/Contrib/GZStatements/{Weak,Level,Compat,Hensel}.lean` on its branch) proves
that the narrower `ZInQ.GZStatements.FHNonvanishingCd` and `GrossZagierHeegnerCd` (restricted to `C_d`, `d ≡ 5 mod 8`,
`D < −4`) are implied by Z-1, Z-2 and still give `ZInQ.FrozenTarget`
(`frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`); they could replace Z-1, Z-2
(both remain GLUE). Not adopted here (not compiled together with `TYZChain.lean`).

This branch is fork main 0e70c94e plus this refresh.
