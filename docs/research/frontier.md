# frontier: every open Prop on the path to `ZInQ.FrozenTarget`

Task frontier, 2026-11-13; refreshes r2, r3 and r4, 2026-11-14 (text checks only, no Lean run). Base of r4:
integration w59 (fork main 5da857b0), on wip/frontier-r4. Branch snapshot: the commits in `scratch/frontier/refs.txt`
(r4 section, read 12:40 PST). Lean: `scratch/frontier/TYZChain.lean`, `TopChain.lean`
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

**The list.** If every proof and reduction that the branches had compiled by 2026-11-14 12:40 PST is folded in
(scenario F, §5), the open Props on the path to `ZInQ.FrozenTarget` are **80: 44 LEAF and 36 GLUE** in the strict
count. If consequences of one theorem count as leaves, they are 60 LEAF and 20 GLUE.

**The library theorem.** `ZInQ.OneProof.frozenTarget` on main (scenario A) has 66 hypotheses that its proof uses:
**41 LEAF and 25 GLUE** in the strict count, 52 and 14 in the lenient count (leaf-fold8's forms for its fields).
Scenario F has more rows because it also applies the splits that leaf-fold7 and leaf-fold8 left out on purpose:
each replaces one field by a leaf plus smaller statements (leaf-fold7 §5).

| premise | open Props | strict LEAF | strict GLUE | lenient LEAF | lenient GLUE | table |
|---|---|---|---|---|---|---|
| GZ, `Literature.GrossZagier` | 2 | 0 | 2 | 0 | 2 | §2.2 |
| TYZ, `Literature.TYZThm35ReadingA` | 5 | 2 | 3 | 3 | 2 | §3.2 |
| H, `SixContactMin`: research-level fields of r3 | 8 | 3 | 5 | 5 | 3 | §4.2 |
| H: textbook fields of r3 | 0 | 0 | 0 | 0 | 0 | §4.3 |
| H: fields that were glue in C4 | 1 | 0 | 1 | 1 | 0 | §4.4 |
| H: Props introduced by reductions until r3 | 8 | 5 | 3 | 5 | 3 | §4.5 |
| H: fields of leaf-fold8 introduced since r3 | 36 | 29 | 7 | 35 | 1 | §4.6 |
| H: Props open only in scenario F, introduced since r3 | 20 | 5 | 15 | 11 | 9 | §4.7 |
| **total** | **80** | **44** | **36** | **60** | **20** | |

By form: 44 published form, 16 consequences of one theorem, 17 composites, 3 project glue (`CMStabObj`, `CoverModelOfHeckeN`, `P1SchemeQ`: what is left
under the tame-quotient coordinate, §4.1).

**Since r3 (70 rows; 17 LEAF and 53 GLUE strict, 41 and 29 lenient).** 10 rows are proved outright:
`EigenformTwist` (H-33), `EGAIV_8_8_2_ii` (H-64), `EGAIV_17_7_8_ii` (H-66), `ZariskiConnectedness` (H-67),
`T11bExists` (H-75), `NeronMappingAbelianSchemeSurj` (H-76) (fork PRs #6-#10), `JacobianExists ℚ` (H-36) and
`NormalModelOfFunctionFieldQ` (H-80) (cloud-w07), `QMClassNumberOne` (H-46; qm-split: `𝒪` is norm-Euclidean) and
`CurveBijIso` (H-85; curve-split, Mathlib only). 39 rows are split into smaller statements, most of them published
forms (§4.1). The H base is leaf-fold8's `sixContactMin_of_open8` inside the library (C4'''', §1). It compiles
av-glue, av-split, curve-split, hodge-split, most of qm-split, the height rows of height-split and height-glue, H-87 and
H-88 of qm-glue, the six Contrib proofs of PRs #6-#10, tyz-split's T-11 and mcr-glue's smaller glue field, so
`ZInQ.OneProof.frozenTarget` on main is scenario A as one theorem (§6). On top of it scenario F applies coarse-factor
and qm-glue (H-1, H-43), height-glue (H-3), mcr-quot (the glue under the coordinate), qm-split's H-44 split,
cloud-w07 and tyz-split's T-5 split.

**Being attempted (cloud workers W11-W15):** `TateTwistInvariants`, `AxSenTate`, `X0Transitive` (it would remove
`IgusaGL2`), `RegularSmoothPerfect`, `ShimuraGoodReductionNoGuard`, and the F-only leaves `FiniteQuotientExists` and
`CanonicalModelY3`. The rows say so.

**The 80 names** (L = LEAF in both counts; c = consequence of one theorem, LEAF only in the lenient count; all others
GLUE; details in the tables):
- GZ: `ZInQ.GZDecomp.FHNonvanishing`; `ZInQ.GZDecomp.GrossZagierHeegner`.
- TYZ: `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` (L); `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2`; `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` (L); `ZInQ.Contrib.TYZGenus.TYZSplitT5.CMModuli` (c); `ZInQ.Contrib.TYZGenus.TYZSplitT5.X0RatStructure`.
- H: `PkgI2.RaynaudCriterion` (c); `PkgI2.NeronOggShafarevich` (L); `PkgI3.FaltingsSemisimple` (L); `PkgI3.FaltingsTate` (L); `PkgI4.PanBerger`; `DeligneSerreConseq`; `LeafModCurves.R16_EichlerShimuraJ1'`; `LadicCond.CarayolR17'` (c); `WeilPairing.T09_SymmIsogenyExists` (c); `TSHecke.Y3Connected`; `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` (L); `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` (L); `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` (L); `ZInQ.Contrib.AVB1.PoincareComplement` (L); `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` (L); `ZInQ.Contrib.CurvesG.DimJacobianEqGenus`; `ZInQ.Contrib.CurvesG.GenusX1Field`; `AVGlue.CartierSmooth` (L); `AVGlue.GeomConnOfRationalPoint` (L); `AVGlue.GroupSchemeEquidim` (L); `AvSplit.T4.MulEtaleAbelianScheme` (L); `AvSplit.MumfordTorsionAlgClosed` (L); `BPAnalytic.Uniformization.UniformizationLeafAll` (L); `AvSplit.MilneIsogenyQuasiInverse` (L); `ZInQ.HomLattice.GAGAMorphism` (L); `ZInQ.HeightSplit.SemistableReductionThm` (c); `ZInQ.HeightSplit.SemistableNeronBaseChange` (c); `ZInQ.HeightSplit.SemistablePersists` (c); `ZInQ.HeightSplit.JavanpeykarBound` (L); `ZInQ.HeightSplit.GaudronRemondThm14` (L); `ZInQ.HeightSplit.FaltingsLemma5BC` (c); `ZInQ.HeightSplit.BostLowerBound` (L); `ZInQ.HeightSplit.PazukiCor13Upper` (L); `ZInQ.RLeaf.IgusaGL2` (L); `CurveSplit.RegularSmoothPerfect` (L); `CurveSplit.ShimuraGoodReductionNoGuard`; `ZInQ.Contrib.HodgeSplit.TateTwistInvariants` (L); `ZInQ.Contrib.HodgeSplit.AxSenTate` (L); `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` (L); `ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` (L); `ZInQ.Contrib.HodgeSplit.BdRInvariants` (L); `ZInQ.Contrib.HodgeSplit.DSThm965` (L); `ZInQ.Contrib.HodgeSplit.DSThm966` (L); `ZInQ.Contrib.HodgeSplit.EigenformHTNew` (c); `HDec.QMSplit.Yu.YuThm11` (L); `HDec.QMSplit.Aut.QMCentralizerCMC` (L); `HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar` (L); `HDec.QMSplit.Theta.IgusaPsi4` (L); `HDec.QMSplit.Theta.IgusaChi10` (L); `HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq` (L); `HDec.LeafQCheck.HM.QMSplit.ShimizuCovolumeO1` (L); `HDec.QMSplit.Moduli.ShimuraFamily` (c); `HDec.LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24` (L); `MCRGlue.ProperCurveAF`; `MCRGlue.FiniteQuotientExists` (L); `MCRGlue.TameQuotientSmooth`; `MCRGlue.SmoothModelOfP1` (c); `MCRGlue.TameFixedPointsDisjoint` (c); `MCRGlue.TameInertiaCyclic`; `HDec.PropTSRed.CoverModelOfHeckeN`; `MCRQuot.P1SchemeQ`; `MCRQuot.CMStabObj`; `ZInQ.HeightSplit.R5.EichlerOptimalEmbeddingCount` (L); `ZInQ.HeightGlue.QM.CMDescent` (c); `ZInQ.HeightGlue.QM.QMUniformizationC`; `HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.ThetaNullNonvanishing` (L); `HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.ThetaFourthRatiosAlgebraic`; `HDec.QMSplit.Moduli.CanonicalModelY3` (c); `HDec.QMSplit.Moduli.ReciprocityOfFine` (c); `HDec.QMSplit.Moduli.CanonicalCoarseX6`; `HDec.QMSplit.Moduli.BabaGranathX6` (L); `HDec.QMSplit.Moduli.GonzalezRotgerX6` (L); `HDec.QMSplit.Moduli.ConicCanonical` (c).

Six more bundle fields (R1(d) reciprocity `r1rec`, R3, R5(ii), R7(b), R8, T10) are hypotheses of the compiled H
assembly but are never projected by its proof (§4.8); they are not on the list.

**How far this is checked.**
- **Scenario A is one compiled theorem.** `ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`, on leaf-fold8's
  bundles since w59) derives `ZInQ.FrozenTarget` from leaf-fold8's four bundles (31 + 20 + 14 + 1 = 66 fields), the
  TYZ Props `TYZThm11Integral`, `TYZLemma29Mod2`, `ShimuraReciprocityModFn`, `TYZThm33` and the two GZ Props.
  leaf-fold8 reports `lake build +ZInQKernel.OneProof.Main` exit 0 and standard axioms (REPORTED, leaf-fold8 §1).
  `chain.py onep` reads its signature: its hypotheses are scenario A's (the four bundles and the six top Props), and leaf-fold8's `fields8.tsv` lists the bundles' fields with the same names and types (the table abbreviates `bdRInvariants`'s binders).
- **Scenario F.** A plus the edges of §4.1, each compiled on its branch per its report and log. `chain.py` checks
  signatures (0 mismatches over 154 theorem edges, 26 of them followed on the route) and compares definitions where
  a proof lives in another Lean world (§5.2). F is not compiled as one file.

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

**Findings in brief** (§7): 10 rows proved and 39 split since r3; scenario A is one library theorem with 66
hypotheses (41 LEAF strict); T-11 is the printed TYZ Theorem 3.3; the project glue left is 3 Props, all under
the tame-quotient coordinate.

## 1. The chain to `ZInQ.FrozenTarget`

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| C0 (r3) | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` with `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` | `Contrib/GZTheta/NewCMFinal.lean` @ main; `Contrib/TYZChain/Main.lean` @ w54 | `SixContactMin`, the 4 TYZ Props of §3.2, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (r1-r2: this task's `frozenTarget_of_open` in `scratch/frontier/TYZChain.lean`, with cm-bridge's 7 TYZ Props) |
| C1 | `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` | `Contrib/GZDecomp/Decomp.lean` @ main | `SixContactMin`, `TYZThm35ReadingA`, `HeckeThetaNewform`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (via `GrossZagierCd`; `HeckeContinuation`, `FunctionalEquation5` discharged by the proved `ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) |
| C2 | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` | `Contrib/GZTheta/NewCMFinal.lean` @ wip/atkin-li 6f77abb1 | `SixContactMin`, `TYZThm35ReadingA`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` |
| C3 | TYZ: §3.1 | | → `TYZThm35ReadingA` |
| C4'''' (r4) | H: `HDec.HSyn.sixContactMin_of_open8 (r : OpenResearchLeaves8) (t : OpenTextbookLeaves8) (l : OpenAddedLeaves8) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ4.lean` L265 @ main (leaf-fold8 b0f2f6da, merged in w59; over leaf-fold7's `sixContactMin_of_open7` in `TailX.lean`, w58: `lake build +ZInQKernel.OneProof.Main` exit 0, standard axioms, the closure of `sixContactMin_of_open8` without `sorryAx`; REPORTED by its report §1) | → `ZInQ.SixContactMin`; 31 + 20 + 14 + 1 fields (§4) |
| C4''' | H: leaf-fold6's `HDec.HSyn.sixContactMin_of_open6` | `scratch/leaf-fold6/parts/f20_fold6.lean` @ main (leaf-fold6 733d8013, in w55; flat file compiled, REPORTED) | superseded: leaf-fold7 fills its bundles (`researchLeaves5_of_open7`, `glue6_of_open7`, …) inside OneProof |
| C4'' (r3) | H: `HDec.HSyn.sixContactMin_of_open5 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves5) (l : OpenAddedLeaves5) (g : OpenGlue5)` | `scratch/leaf-fold5/Leaves5.lean` L121755 @ wip/leaf-fold5 5a7e03d1 (in w54; flat file of the final text, 121 783 lines, md5 5999e1db: `lake env lean` exit 0 in 1570 s, 0 errors, no `sorry`, 349 axiom reports all standard; olean chain and `Check5.lean` compiled; REPORTED by its log) | → `ZInQ.SixContactMin`; 26 + 21 + 21 + 2 fields (§4) |
| C4' (r2) | H: `HDec.HSyn.sixContactMin_of_open4 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4) (l : OpenAddedLeaves4) (g : OpenGlue4)` | `scratch/leaf-fold4/Leaves4.lean` L118447 @ wip/leaf-fold4 9dcf1ca8 (final; flat file, 118 478 lines, md5 6bbeb639: `lake env lean` exit 0 in 1048 s, 0 errors, no `sorry`, 326 axiom reports all standard; olean chain and `Check4.lean`, the kernel conclusion, compiled; REPORTED by its report and log); on fork main since w49 | → `ZInQ.SixContactMin`; 26 + 19 + 20 + 1 fields (§4) |
| C5 | assemble-port's `HDec.HSyn.sixContactMin_of_leaves5` (C4 of the 17:35 report; 26 + 17 + 27 fields) | `scratch/assemble-port/AssemblePort.lean` L116751 @ 92a27877 | C4' is its successor through leaf-fold2-4: the 17:35 scenario-F edges folded, `chartProper`, `chartQuasiFinite`, `hauptmodulUnique` proved, `periodMapGlue`, `abVarSpreadsOut` reduced to leaves, `DivisiblePoints` removed (leaf-fold4 §1.1); g0-assemble3's 46-glue-field `sixContactMin_of_leaves4` before it |
| C6 | H, per field: §4 | | each open field, or the Props it was reduced to |
| **C0 ∘ C4'''' in the library (r4)** | `ZInQ.OneProof.frozenTarget (r : HDec.HSyn.OpenResearchLeaves8) (t : HDec.HSyn.OpenTextbookLeaves8) (l : HDec.HSyn.OpenAddedLeaves8) (g : HDec.HSyn.OpenGlue7) (h11 …) (h29 …) (hS …) (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33) (hL2 …) (hL3 …) : ZInQ.FrozenTarget` | `ZInQKernel/OneProof/Main.lean` @ main (OneProof since w56; leaf-fold8's bundles and `OneProof/TYZSplit.lean` since w59) | scenario A of this report: C4'''' with tyz-chain's T0, T-11 from the printed Theorem 3.3, and the kernel's C1 |

The fork's registered headline (`ZInQKernel/MainLiterature.lean`) has five hypotheses; two are proved
(`ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) and C1 already uses them. C4' concludes the kernel's
`ZInQ.SixContactMin` (the flat file imports the kernel's definition; `Leaves.lean` is wrapped in `namespace HDec`), so
C0 and C4'''' compose by modus ponens. Earlier compiled H assemblies (cpts-transport's 44-field and linked-ram's 45-field
`GluePieces5` in the W0 world, lt-goodred's and linked-frob's variants, leaf-fold2's `sixContactMin_of_open2`) are
superseded by C4, C4', C4'' and C4'''.

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

### 3.2 Open Props (5: 2 LEAF, 3 GLUE in the strict count; 3 LEAF, 2 GLUE in the lenient count)

| # | Lean name | defined in | class | citation (UNVERIFIED unless marked) | last task; newest commit | running now | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| T-1 | `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` | `Contrib/TYZDecomp/Leaves.lean` @ main | **LEAF** (specialization: odd `m` only) | TYZ Thm 1.1, first assertion, L371–380 (read by nt-tyz) | tyz-decomp; main (tyz-lcal audit 11-13: faithful, not stronger) | no | published form: specialization of TYZ Thm 1.1 to odd `m` (tyz-lcal audit: faithful, not stronger) |
| T-3 | `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2` | same | GLUE (mod-2 composite of Lemma 2.9 and Prop. 2.3) | TYZ Lemma 2.9, L1062–1066 (journal Lemma 2.9 per the AI locator audit); Prop. 2.3, L580–586 | tyz-decomp; main (tyz-lcal audit 11-13: faithful, not stronger) | no | composite: TYZ Lemma 2.9 with Prop. 2.3, read mod 2 (tyz-lcal audit) |
| T-12 | `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` | `ZInQKernel/OneProof/TYZSplit.lean` L147 @ main | **LEAF** | TYZ Theorem 3.3 over the kernel's definitions, for `n ≡ 5, 7 (mod 8)`, `𝒫(d)` existential | tyz-split | no | published form: TYZ Thm 3.3, Period7.tex L1299-1311, specialized (tyz-split §1); the `[i]` sign of the base point is printed (`α = −i` in the Hecke-action proof, about L1564-1566), docstring fixed on wip/w60 fa7c9d98 |
| T-13 | `ZInQ.Contrib.TYZGenus.TYZSplitT5.CMModuli` | `scratch/tyz-split/T5.lean` L92 @ main | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count) | the CM leaf for `j` and the symmetric functions of Weber values on the level structure | tyz-split | no | consequence of one theorem: Shimura 1971 Thm 5.4 with torsion, by shimura-modfn's lattice computation (tyz-split §1) |
| T-14 | `ZInQ.Contrib.TYZGenus.TYZSplitT5.X0RatStructure` | `scratch/tyz-split/T5.lean` L118 @ main | GLUE (composite) | on `Y₀(N)` the `ℚ`-structure of rational `q`-expansions is the moduli `ℚ`-structure; no CM | tyz-split | no | composite: the canonical model of `X₀(N)` with separation of points by Weber coordinates (tyz-split §1) |

Retired rows: T-2 `TYZLcalOne` (proved, B2), T-4 `Lemma318Literal` (proved, B5), T-6 `Thm35First` (reduced to T-11, B4),
T-7 `Lemma321Five` (proved, B3); r4: T-5 (split by tyz-split into `CMModuli` and `X0RatStructure`), T-11 (from the printed TYZ Thm 3.3 (`TYZThm33`, tyz-split)).

## 4. H: `ZInQ.SixContactMin`

Base (r4): leaf-fold8's compiled C4'''' (b0f2f6da, in w59), inside OneProof. leaf-fold7 (53acb891, w58) folded
av-glue, av-split, curve-split, hodge-split, most of qm-split and mcr-glue's step to `QuotientP1Coordinate` into
leaf-fold6's assembly; leaf-fold8 then folded height-split with height-glue (H-14..H-19), qm-glue's H-87 and H-88, the
six Contrib proofs of PRs #6-#10 and tyz-split's T-11. Bundles: `OpenResearchLeaves8` (31), `OpenTextbookLeaves8` (20),
`OpenAddedLeaves8` (14), `OpenGlue7` (1: `quotientP1Coordinate`). leaf-fold8's count of these 66 fields (its §1, with
frontier r3's forms): 39 published form, 16 consequences, 10 composites, 1 project glue. `chain.py` reads the bundles
from `ZInQKernel/OneProof/H/TailZ4.lean` and `TailX.lean` at main, and the forms of the fields from leaf-fold8's
`scratch/leaf-fold8/fields8.tsv`. Row numbers are kept, retired rows listed, new rows from H-89 (§4.6, §4.7) and T-12
(§3.2).

### 4.1 What changed since r3 (signatures VERIFIED by `chain.py`)

Compiled into C4'''' (scenario A): T8 into four published leaves (av-glue); H-24, H-25, H-38, H-54, H-69 (av-split);
H-41, H-81, H-82, H-83's guard clause, H-85 proved (curve-split); H-2, H-20, H-35, H-42, H-46 proved, H-61, H-63, H-86
(qm-split); H-8, H-10, H-22, H-32, H-51, H-52 (hodge-split); H-84 into the smaller glue field `QuotientP1Coordinate`
(mcr-glue); H-14..H-19 into height-split's eight leaves, the glue proved from T35 (height-split, height-glue); H-87,
H-88 (qm-split, qm-glue); H-33, H-64, H-66, H-67, H-75, H-76 proved (PRs #6-#10); T-11 (tyz-split).

Applied on top by scenario F:

| field of C4'''' (rows) | now | theorems · task · file |
|---|---|---|
| `r1r2`, `x6ConicModel` (H-1, H-43) | ⇐ `CanonicalModelY3`, `ReciprocityOfFine` (qm-split), `CanonicalCoarseX6`, `BabaGranathX6`, `GonzalezRotgerX6`, `ConicCanonical` (qm-glue), and `MobiusGlue`, compiled from T5 in OneProof; coarse-factor proves qm-glue's glue `CoarseFactor` from `CanonicalCoarseX6` | `HDec.QMSplit.Moduli.r1r2fpRep_of_canonical''`, `HDec.QMSplit.Moduli.x6ConicModel_of_canonical''` · coarse-factor, over qm-glue and qm-split · `scratch/coarse-factor/Discharge.lean` |
| `r5count` (H-3) | ⇐ H-115..H-116 with `EichlerOptimalEmbeddingCount` (height-split) and T11(b) (proved: PR #9 with av-b2's uniqueness half) | `ZInQ.HeightGlue.QM.r5fpCount_of_t11b` · height-glue · `scratch/height-glue/QMFull.lean` |
| `thetaRatiosAlgebraic` (H-44) | ⇐ `ThetaNullNonvanishing`, `ThetaFourthRatiosAlgebraic` (a published leaf and a smaller composite; leaf-fold7 §5 kept the field) | `HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.thetaRatiosAlgebraic_of` · qm-split · `scratch/qm-split/ThetaRatios.lean` |
| `quotientP1Coordinate` (the glue field; H-84's successor) | ⇐ mcr-glue's six leaves (H-89..H-94; `TameQuotientSmooth` is L3), T5, and three glue Props: mcr-quot's `P1SchemeQ` and `CMStabObj`, and the decomposition's `CoverModelOfHeckeN` | `HDec.MCRGlue.quotientP1Coordinate_of_leaves` (compiled in `ZInQKernel/OneProof/H/TailW.lean`) with mcr-glue's `coordinateNormalization_of` · mcr-glue · `scratch/mcr-glue/MCRGlue.lean`; `fibreAutTame_of''`, `genericQuotientP1_of''`, `cMSectionsDisjoint_of''`, `coordinateFromSections_of''` and their inputs (namespace `MCRQuot`) · mcr-quot · `scratch/mcr-quot/MCRQuot.lean` |
| `t33`, `normalModelOfFunctionFieldQ` (H-36, H-80) | proved | `JacobianExists_proof`, `NormalModelOfFunctionFieldQ_proof` · cloud-w07 (fork PR #11) · `ZInQKernel/Contrib/CloudW07JacobiansCurves/` |

mcr-quot proves the four glue Props under the coordinate (`FibreAutTame`, `GenericQuotientP1`, `CMSectionsDisjoint`,
`CoordinateFromSections`) from T5, L3, `CurveBijIso` and three glue Props: `P1SchemeQ` and `CMStabObj`, which are
new, and `CoverModelOfHeckeN`, the decomposition's own glue. The chain derives `CoverModelOfHeckeN` only through
`HeckeNoVertRam`, downstream of the coordinate that mcr-quot feeds, so here it is counted as open glue: the coordinate
still rests on project glue, and mcr-quot does not discharge it.

On the TYZ side F uses B6 (§3.1). The r2 and r3 edges compiled inside C4'''' are off the route (they stay in
`chain.py`), and so are the edges of height-split, height-glue, qm-glue's H-87 and H-88, and PRs #6-#10, which
leaf-fold8 compiled. Retired rows (r2, r3): H-23, H-26, H-27, H-28, H-29, H-31, H-37, H-39, H-40, H-45, H-47, H-48,
H-50, H-55, H-58, H-62. Retired in r4: H-1, H-2, H-3, H-8, H-10, H-14, H-15, H-16, H-17, H-18, H-19, H-20, H-22, H-24, H-25, H-32, H-33, H-35, H-36, H-38, H-41, H-42, H-43, H-44, H-46, H-51, H-52, H-54, H-61, H-63, H-64, H-66, H-67, H-69, H-73, H-74, H-75, H-76, H-80, H-81, H-82, H-83, H-84, H-85, H-86, H-87, H-88.
Not applied: the variants each report keeps aside (height-split's `r20_of_leaves` with `IsogenySemistableBaseChange`;
curve-split's `x0Transitive_of_igusaSL2X`; qm-split's `qmHauptmodulBase3_of_shimizu` and `y3Connected_of`, whose
`ConnectedOfFine` qm-glue proves from the row itself; hodge-split's `panBerger_of_templates`, which needs a definition
of potentially semistable).

### 4.2 Research-level fields of r3 still open (8: 3 LEAF, 5 GLUE strict; 5 LEAF, 3 GLUE lenient)

| # | field : Lean name | leaf | class | citation | flags | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| H-4 | `r6 : PkgI2.RaynaudCriterion` | R6 | GLUE (Galois-theoretic consequence) | SGA 7 I, Exp. IX, Prop. 4.7 with 3.5; Silverberg–Zarhin, AIF 45 (1995), Thm 3.5 | case `m = 3` UNVERIFIED | pkg-I2 | consequence of one theorem: SGA 7 IX 4.7 (leaf-review-b §2.2) |
| H-5 | `r7a : PkgI2.NeronOggShafarevich` | R7(a) | **LEAF** | Serre–Tate, Ann. of Math. 88 (1968), Thm 1 | UNVERIFIED | pkg-I2 | published form: Serre–Tate 1968 Thm 1 (leaf-review-b §2.2) |
| H-6 | `r9a : PkgI3.FaltingsSemisimple` | R9(a) | **LEAF** | Faltings, Invent. Math. 73 (1983), Satz 3 (erratum 75 (1984)) | UNVERIFIED | pkg-I3 | published form: Faltings 1983 (leaf-review-b §2.3) |
| H-7 | `r9b : PkgI3.FaltingsTate` | R9(b) | **LEAF** | Faltings 1983, Satz 4, Kor. 1 | UNVERIFIED | pkg-I3 | published form: Faltings 1983 (leaf-review-b §2.3) |
| H-9 | `r11r12 : PkgI4.PanBerger` | R11 + R12 | GLUE (joint consequence of two theorems) | Berger, Invent. Math. 148 (2002), Thm 0.7; Pan, JAMS 35 (2022), Thm 1.0.4 | JAMS numbering UNVERIFIED | pkg-I4 | composite: Pan and Berger (leaf-review-b §2.4) |
| H-12 | `r15 : DeligneSerreConseq` | R15 | GLUE (consequence, with T25, T18, T19) | Deligne–Serre, Ann. Sci. ÉNS 7 (1974), Thm 4.1, Lemma 3.2 | | hdec-faithful | composite: Deligne–Serre with T25, T18, T19, Chebotarev, Brauer–Nesbitt (leaf-review-a §3.2) |
| H-13 | `r16 : LeafModCurves.R16_EichlerShimuraJ1'` | R16 | GLUE (three suppliers) | Shimura 1971 Thm 7.9; Shimura 1973 Thm 1 | | leaf-modcurves | composite: Shimura 1973, Shimura 1971 §7.4, Diamond–Shurman (leaf-review-a §3.3) |
| H-21 | `r17 : LadicCond.CarayolR17'` (research field in C4) | R17 | GLUE in the strict count (was LEAF; a consequence of one theorem, LEAF in the lenient count) | Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A) (read by the audit) | | def-ladic-cond | consequence of one theorem: Carayol 1986 Thm (A) (leaf-review-a §3.4) |

### 4.3 Textbook fields of r3 still open (0: 0 LEAF, 0 GLUE strict; 0 LEAF, 0 GLUE lenient)

None left: each is proved or split (§4.1).




T6, T7, T8, T9, T11(b), T3, T41, T34 and T38 are proved or reduced (r2); their replacements are rows of §4.5.
T4, T5, T23, T24, T27, T33, T35, T40 and the normal model of a function field are proved or split in r4 (§4.1).

### 4.4 Fields that were glue in C4, still open (in C4'''' they are `OpenAddedLeaves8` fields) (1: 0 LEAF, 1 GLUE strict; 1 LEAF, 0 GLUE lenient)

| # | field : Lean name | def part | content; nearest published sources (UNVERIFIED) | report's label | last task; running | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-53 | `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` | a35 | symmetric isogeny to a dual; "existential in D, hence a consequence" (Mumford §§6, 8, 20, 23) | LEAF | weil-pairing; no | consequence of one theorem: Mumford §§6, 8, 20, 23 (leaf-review-b §2.1) |

### 4.5 Props introduced by reductions until r3, still open (8: 5 LEAF, 3 GLUE strict; 5 LEAF, 3 GLUE lenient)

| # | Lean name | def file @ commit | from field | class; content; sources (UNVERIFIED) | last task; running | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-59 | `TSHecke.Y3Connected` | ts-hecke `scratch/ts-hecke/TSHecke.lean` L6101 @ ff8e6731 | 28 | GLUE (π₀ of the Shimura curve, Deligne 389 §§2-3, Milne, plus an orbit computation; report: "leaf R1conn") | ts-hecke | composite: Deligne, Bourbaki 389, with an orbit computation (leaf-review-a §5.12) |
| H-65 | `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` | same, L49 | 44-46 | **LEAF** (descent of properness; EGA IV₃ 8.10.5(xii), Stacks 081F) | spread-out | published form: EGA IV₃ 8.10.5(xii) (spread-out) |
| H-70 | `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` | `Contrib/AVB1/AlgClosed.lean` L38 @ main | t6 (H-26) | **LEAF** (T6 over algebraically closed fields only: Mumford, *Abelian varieties* §19 Thm 3 in Mumford's own setting; Milne 1986 Thm 12.5) | av-b1 | published form: Mumford §19 Thm 3 in its own setting (av-b1 §3.1) |
| H-71 | `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` | same, L51 | t7 (H-27) | **LEAF** (specialization: T7 over algebraically closed fields, without `deg P = 2g` and `P(n) = deg(n − φ)`; Mumford §19 Thm 4) | av-b1 | published form: specialization of Mumford §19 Thm 4 (av-b1 §3.2) |
| H-72 | `ZInQ.Contrib.AVB1.PoincareComplement` | `Contrib/AVB1/Poincare.lean` L42 @ main | t8 (H-28) | **LEAF** (Poincaré's complete reducibility in its complement form, weakened; Milne 1986 Prop. 12.1; Mumford §19 Thm 1) | av-b1 | published form: Milne 1986 Prop. 12.1, weakened (av-b1 §3.3) |
| H-77 | `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` | `Contrib/NeronC/NeronGroup.lean` L82 @ main | t41 (H-39) | **LEAF** (a smooth separated quasi-compact model with the extension property and no group law: weaker than BLR §1.4 Thm 3; the group law, `gen` a homomorphism and uniqueness are proved) | neron-c | published form: BLR §1.4 Thm 3 without the group law (neron-c §1) |
| H-78 | `ZInQ.Contrib.CurvesG.DimJacobianEqGenus` | `Contrib/CurvesG/GenusSplit.lean` L46 @ main | t34 (H-37) | GLUE (lit-composite: `T₀J ≅ H¹(X, 𝒪_X)`, Milne, *Jacobian varieties* Prop. 2.1, with Serre duality; the genus is Mathlib-level `fieldGenus`) | curves-g | composite: Milne, *Jacobian varieties* Prop. 2.1 with Serre duality (curves-g §3) |
| H-79 | `ZInQ.Contrib.CurvesG.GenusX1Field` | same, L59 | t34 (H-37) | GLUE (lit-composite: Shimura's canonical model of `X₁(N)`, Shimura 1971 Prop. 6.9, the genus formula Prop. 1.40, base change of `H⁰(Ω¹)`) | curves-g | composite: Shimura 1971 Prop. 6.9 and Prop. 1.40 (curves-g §3) |

Proved and gone from the tables: r4, `EigenformTwist`, the two EGA IV descents, `ZariskiConnectedness`, `T11bExists`,
`NeronMappingAbelianSchemeSurj` (PRs #6-#10), `JacobianExists ℚ`, `NormalModelOfFunctionFieldQ` (cloud-w07),
`QMClassNumberOne` (qm-split), `CurveBijIso` (curve-split); r3, `GammaStarGen`; r2, `SerreRigidity3`, `T09_WeilPairing`
(av-b2), and in the chain below `HeckeVertWitness`: `SmoothFibreReduced` (smooth-fibre), `SpecialFibreMaxIdeal`,
`SpecialFibreUniformizer`, `SpecialFibreDVR` (vert-witness), `ModelGenericFibre`, `GermOfQbarValues`, `ModelIntegral`,
`ModelFunctionField` (model-glue). Props that r4's own tasks introduced and proved were never rows: height-split's glue
(`AnalyticUniformizationExists`, `AnalyticUniformizationUnique`, `UniformizationDim`, `MetrizationOfUniformization`,
`NeronMetrizable`, proved from T35 by height-glue), qm-split's `GammaStarFromO1` (qm-glue), qm-glue's `CoarseFactor`
(coarse-factor), mcr-glue's four glue Props (mcr-quot, from three others). Proved before 17:35: see the 17:35 report
(`git show d8c95123:docs/research/frontier.md`).

### 4.6 Fields of leaf-fold8 introduced since r3 (36: 29 LEAF, 7 GLUE strict; 35 LEAF, 1 GLUE lenient)

Each row is a field of C4'''' (its name is in the 'last task' column) and the hypothesis of a compiled theorem in
the task's file. Its form is leaf-fold8's (fields8.tsv), which keeps leaf-fold7's and takes a new field's form from
its source report; where this report's reading differs the pointer says so. Theorem numbers are the reports' and
UNVERIFIED unless a report read the source.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-98 | `AVGlue.CartierSmooth` | `scratch/av-glue/Combined.lean` L297 @ main | H-73, H-74 | **LEAF**; a group scheme locally of finite type over a field of characteristic 0 is smooth | av-glue; field `cartierSmooth` of leaf-fold8 | published form: Cartier's theorem; Mumford AV §11 Thm 1; Stacks 047N (av-glue §5) |
| H-99 | `AVGlue.GeomConnOfRationalPoint` | `scratch/av-glue/Combined.lean` L902 @ main | H-74 | **LEAF**; a connected scheme of finite type over `k` with a rational point is geometrically connected | av-glue; field `geomConnOfRationalPoint` of leaf-fold8 | published form: Stacks 04KV, specialized to finite type with a rational point (av-glue §5) |
| H-100 | `AVGlue.GroupSchemeEquidim` | `scratch/av-glue/Combined.lean` L913 @ main | H-74 | **LEAF**; the irreducible components of a group scheme of finite type over a field have its dimension | av-glue; field `groupSchemeEquidim` of leaf-fold8 | published form: Stacks, group schemes over a field; SGA 3 VI_A 2.4, finite type (av-glue §5) |
| H-101 | `AvSplit.T4.MulEtaleAbelianScheme` | `scratch/av-split/AvSplitAll.lean` L1835 @ main | H-24 | **LEAF**; `[m]` on an abelian scheme over `Spec O` is étale if `m ∈ O×` | av-split; field `mulEtaleAbelianScheme` of leaf-fold8 | published form: BLR §7.3 Lemma 2; Mumford GIT §6 (av-split §1) |
| H-102 | `AvSplit.MumfordTorsionAlgClosed` | `scratch/av-split/AvSplitAll.lean` L1411 @ main | H-25, H-38 | **LEAF**; over `k = k̄`, `A(k)[n] ≅ (ℤ/n)^{2g}` for `char k ∤ n` | av-split; field `mumfordTorsionAlgClosed` of leaf-fold8 | published form: Mumford AV §4 Application 2 (iv) (av-split §1) |
| H-103 | `BPAnalytic.Uniformization.UniformizationLeafAll` | `ZInQKernel/HDecomp/Analytic/Uniformization.lean` L91 @ main | H-38, H-69 | **LEAF**; the kernel's AN3 leaf: `A^an` in coordinate form | av-split; field `uniformizationLeafAll` of leaf-fold8 | published form: Mumford §1 in coordinate form (bp-analytic §4; av-split §1 shares the judgement) |
| H-104 | `AvSplit.MilneIsogenyQuasiInverse` | `scratch/av-split/AvSplitAll.lean` L1361 @ main | H-54 | **LEAF**; `fg = [d]`, `gf = [d]` as morphisms for some `d ≥ 1` | av-split; field `milneIsogenyQuasiInverse` of leaf-fold8 | published form: Milne 1986 Rem. 8.4; Mumford §7 (av-split §1) |
| H-105 | `ZInQ.HomLattice.GAGAMorphism` | `scratch/av-split/AvSplitAll.lean` L1029 @ main | H-69 | **LEAF**; GAGA for homomorphisms of complex abelian varieties | av-split; field `gagaMorphism` of leaf-fold8 | published form: Serre, GAGA, in the form of homlattice §3.2 (av-split §1) |
| H-106 | `ZInQ.HeightSplit.SemistableReductionThm` | `scratch/height-split/HeightSplit.lean` L120 @ main | H-14, H-15, H-16, H-17, H-18, H-19 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); SS1: every Néron model of `A_{L₀}` is semistable for some finite `L₀` | height-split; field `semistableReductionThm` of leaf-fold8 | consequence of one theorem: SGA 7 IX Thm 3.6 in global form (height-split §1, §7) |
| H-107 | `ZInQ.HeightSplit.SemistableNeronBaseChange` | `scratch/height-split/HeightSplit.lean` L132 @ main | H-14, H-15, H-16, H-17, H-18, H-19 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); SS2: the identity component of a semistable Néron model commutes with base change | height-split; field `semistableNeronBaseChange` of leaf-fold8 | consequence of one theorem: SGA 7 IX 3.3, open-subgroup form (height-split §1, §7) |
| H-108 | `ZInQ.HeightSplit.SemistablePersists` | `scratch/height-split/HeightSplit.lean` L584 @ main | H-16 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); SS3: semistability persists under finite extension | height-split; field `semistablePersists` of leaf-fold8 | consequence of one theorem: SGA 7 IX 3.3 in global form (height-split §4 and its §7 caveat; leaf-fold8 §2) |
| H-109 | `ZInQ.HeightSplit.JavanpeykarBound` | `scratch/height-split/HeightSplit.lean` L508 @ main | H-14 | **LEAF**; Javanpeykar's bound over the published stable height | height-split; field `javanpeykarBound` of leaf-fold8 | published form: specialization of Javanpeykar 2014 Thm 1.1.1 to `K` with a `K`-rational Belyi function (height-split §4; leaf-fold8 §2; height-split §7 notes that a stricter reader may call it a consequence) |
| H-110 | `ZInQ.HeightSplit.GaudronRemondThm14` | `scratch/height-split/HeightSplit.lean` L773 @ main | H-15 | **LEAF**; Gaudron–Rémond's bound over the published stable height | height-split; field `gaudronRemondThm14` of leaf-fold8 | published form: Gaudron–Rémond 2014 Thm 1.4 (height-split table) |
| H-111 | `ZInQ.HeightSplit.FaltingsLemma5BC` | `scratch/height-split/HeightSplit.lean` L596 @ main | H-16 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); Faltings' Lemma 5 over every number field `L ⊇ K` | height-split; field `faltingsLemma5BC` of leaf-fold8 | consequence of one theorem: Faltings 1983 Lemma 5 is printed as an identity with a correction term; the inequality uses Raynaud, Astérisque 127 VII 2.1.3 (height-split §8 review; leaf-fold8 §2) |
| H-112 | `ZInQ.HeightSplit.BostLowerBound` | `scratch/height-split/HeightSplit.lean` L429 @ main | H-17 | **LEAF**; `h_D ≥ −(g/2) log 2π` (Deligne's normalization) | height-split; field `bostLowerBound` of leaf-fold8 | published form: Bost, Sém. Bourbaki 795 (display unread; height-split §2) |
| H-113 | `ZInQ.HeightSplit.PazukiCor13Upper` | `scratch/height-split/HeightSplit.lean` L717 @ main | H-18 | **LEAF**; the upper side of Pazuki's comparison of theta and Faltings heights | height-split; field `pazukiCor13Upper` of leaf-fold8 | published form: Pazuki 2012 Cor. 1.3(2), read off the same display (height-split §3) |
| H-117 | `ZInQ.RLeaf.IgusaGL2` | `ZInQKernel/Contrib/RLeaf/IgusaSL2.lean` L120 @ main | H-41 | **LEAF**; Igusa's theorem: `GL₂(ℤ/N)` is the Galois image on `E_j[N]` | curve-split; field `igusaGL2` of leaf-fold8; being attempted (cloud as `X0Transitive`, which would remove this row) | published form: Igusa 1959; Shimura 1971 Thm 6.6 (curve-split §3.1) |
| H-118 | `CurveSplit.RegularSmoothPerfect` | `scratch/curve-split/CurvesGSplit.lean` L81 @ main | H-81 | **LEAF**; a finite type algebra over a perfect field is smooth at a prime with regular local ring | curve-split; field `regularSmoothPerfect` of leaf-fold8; being attempted (cloud) | published form: Stacks 00TV, the ⇐ half (curve-split §3.3) |
| H-119 | `CurveSplit.ShimuraGoodReductionNoGuard` | `scratch/curve-split/ShimuraGR.lean` L162 @ main | H-83 | GLUE (composite); `ShimuraGoodReduction` without its guard clause | curve-split; field `shimuraGoodReductionNoGuard` of leaf-fold8; being attempted (cloud) | composite: Morita, Carayol, Kottwitz, Buzzard; not statable in published form today (curve-split §3.6) |
| H-120 | `ZInQ.Contrib.HodgeSplit.TateTwistInvariants` | `scratch/hodge-split/HodgeSplit.lean` L65 @ main | H-8, H-51, H-52 | **LEAF**; `ℂ_p(i)^{G_K} = 0` for `i ≠ 0` | hodge-split; field `tateTwistInvariants` of leaf-fold8; being attempted (cloud) | published form: Tate 1967 §3.3 Thm 2 (hodge-split §1) |
| H-121 | `ZInQ.Contrib.HodgeSplit.AxSenTate` | `scratch/hodge-split/HodgeSplit.lean` L75 @ main | H-8, H-51, H-52 | **LEAF**; `ℂ_p^{G_K} ⊆ K` | hodge-split; field `axSenTate` of leaf-fold8; being attempted (cloud) | published form: Tate 1967 §3.3 Thm 1; Sen 1969; Ax 1970 (hodge-split §1) |
| H-122 | `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` | `scratch/hodge-split/HodgeSplit.lean` L343 @ main | H-8 | **LEAF**; the Hodge–Tate decomposition of `ℂ_p ⊗ V_p(A)` | hodge-split; field `hodgeTateDecompAbVar` of leaf-fold8 | published form: Fontaine 1982; Faltings 1988 (hodge-split §1) |
| H-123 | `ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` | `scratch/hodge-split/HodgeSplit.lean` L1988 @ main | H-8 | **LEAF**; `Hom(V_p A, ℚ_p)` is de Rham | hodge-split; field `deRhamH1AbVarT` of leaf-fold8 | published form: Faltings 1989; Tsuji 1999; Scholze 2013 Cor. 1.8, Hom form (hodge-split §1) |
| H-124 | `ZInQ.Contrib.HodgeSplit.BdRInvariants` | `scratch/hodge-split/HodgeSplit.lean` L3611 @ main | H-32 | **LEAF**; `B_dR^{G_{ℚ_p}} = ℚ_p` | hodge-split; field `bdRInvariants` of leaf-fold8 | published form: Fontaine, Astérisque 223 Exp. II; Brinon–Conrad §4 (hodge-split §1) |
| H-125 | `ZInQ.Contrib.HodgeSplit.DSThm965` | `scratch/hodge-split/HodgeSplit.lean` L1106 @ main | H-10, H-22 | **LEAF**; `k ≥ 2`: the Galois representation of an eigenform and its Frobenius polynomials | hodge-split; field `dsThm965` of leaf-fold8 | published form: Diamond–Shurman Thm 9.6.5 (Deligne 1971; Shimura 1971 Thm 7.14) (hodge-split §1) |
| H-126 | `ZInQ.Contrib.HodgeSplit.DSThm966` | `scratch/hodge-split/HodgeSplit.lean` L1124 @ main | H-10, H-22 | **LEAF**; `k = 1`: the Artin representation of an eigenform | hodge-split; field `dsThm966` of leaf-fold8 | published form: Deligne–Serre 1974 Thm 4.1; Diamond–Shurman Thm 9.6.6 (hodge-split §1) |
| H-127 | `ZInQ.Contrib.HodgeSplit.EigenformHTNew` | `scratch/hodge-split/HodgeSplit.lean` L1271 @ main | H-10 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); Hodge–Tate weights for newforms (open) | hodge-split; field `eigenformHTNew` of leaf-fold8 | consequence of one theorem: Kato 2004 for newforms, transported and dualized (hodge-split §2) |
| H-128 | `HDec.QMSplit.Yu.YuThm11` | `scratch/qm-split/YuLeaf.lean` L34 @ main | H-35 | **LEAF**; Yu's dichotomy for QM abelian surfaces, with the splitting clause | qm-split; field `yuThm11` of leaf-fold8 | published form: Yu 2013 Thm 1.1, case labels dropped (qm-split §1) |
| H-129 | `HDec.QMSplit.Aut.QMCentralizerCMC` | `scratch/qm-split/QMAut.lean` L1018 @ main | H-42, H-61, H-63 | **LEAF**; over `ℂ`, `End_𝒪(A)` is `ℤ` or an optimally embedded `Φ⁻¹(𝒪)` | qm-split; field `qmCentralizerCMC` of leaf-fold8 | published form: Shimura 1967 §§1-3; Jordan 1981 §3; González–Rotger 2006 §5 (qm-split §1) |
| H-130 | `HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar` | `scratch/qm-split/STQM.lean` L66 @ main | H-86 | **LEAF**; a surface over `ℂ` with a degree-4 field in `End⁰` has a model over `ℚ̄` | qm-split; field `shimuraTaniyamaQbar` of leaf-fold8 | published form: Milne, CM notes §7; Shimura–Taniyama 1961 §12.4 print a number-field model (qm-split §4) |
| H-131 | `HDec.QMSplit.Theta.IgusaPsi4` | `scratch/qm-split/ThetaSplit.lean` L42 @ main | H-2 | **LEAF**; `2⁻²Σθ⁸` is Siegel modular of weight 4 | qm-split; field `igusaPsi4` of leaf-fold8 | published form: Igusa 1962-1967 (leaf-fold7's form; qm-split §4 flags that Igusa prints it as an identity of Eisenstein series) |
| H-132 | `HDec.QMSplit.Theta.IgusaChi10` | `scratch/qm-split/ThetaSplit.lean` L52 @ main | H-2 | **LEAF**; `−2⁻¹⁴∏θ²` is Siegel modular of weight 10 | qm-split; field `igusaChi10` of leaf-fold8 | published form: Igusa 1962-1967, as for `IgusaPsi4` (leaf-fold7's form; flag of qm-split §4) |
| H-135 | `HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq` | `scratch/qm-split/Haupt.lean` L2244 @ main | H-87, H-88 | **LEAF**; the valence formula for cocompact Fuchsian groups | qm-split; field `valenceFormulaCocompactEq` of leaf-fold8 | published form: Shimura 1971 Prop. 2.16, Thm 2.20; Rankin Thm 4.1.4 (qm-split §1) |
| H-136 | `HDec.LeafQCheck.HM.QMSplit.ShimizuCovolumeO1` | `scratch/qm-split/Haupt.lean` L3205 @ main | H-87, H-88 | **LEAF**; `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` | qm-split; field `shimizuCovolumeO1` of leaf-fold8 | published form: Shimura 1971 Prop. 9.2; Shimizu 1965 (qm-split §1) |
| H-139 | `HDec.QMSplit.Moduli.ShimuraFamily` | `scratch/qm-split/ModuliSplit.lean` L125 @ main | H-20 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); Shimura's holomorphic family composed with every `π : Y₃ → P¹` | qm-split; field `shimuraFamily` of leaf-fold8 | consequence of one theorem: Shimura 1967 Main Thm I; Deligne 389 §4.15; leaf candidate with the Lemma QP caveat (qm-split §1, §4) |
| H-144 | `HDec.LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24` | `scratch/qm-glue/HauptGlue.lean` L4770 @ main | H-88 | **LEAF**; Lin–Yang's Igusa vector at Baba–Granath's CM value `j = −16/27`, in Igusa's theta normalization | qm-glue; field `igusaCMValue24` of leaf-fold8 | published form: Lin–Yang 2020 (2), (14) at Baba–Granath's CM value, in Lauter–Naehrig–Yang's theta conventions: one published number, equivalent to the old glue (qm-glue §0 (a); leaf-fold8 §2) |

### 4.7 Props open only in scenario F, introduced since r3 (20: 5 LEAF, 15 GLUE strict; 11 LEAF, 9 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4''''. Its form is the task
report's label, or my reading where the report's own text (docstring or review) names more than one source; the
pointer says which.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-89 | `MCRGlue.ProperCurveAF` | `scratch/mcr-glue/MCRGlue.lean` L4044 @ main | H-84 | GLUE (composite); L1: finite sets of points of a proper smooth curve over `ℤ_(p)` lie in an affine open | mcr-glue | composite: Lichtenbaum 1968 Thm 2.8 with EGA II 4.5.4 (mcr-glue §3: composite of two results) |
| H-90 | `MCRGlue.FiniteQuotientExists` | `scratch/mcr-glue/MCRGlue.lean` L4057 @ main | H-84 | **LEAF**; L2: the quotient by a finite group of `ℤ_(p)`-automorphisms exists and is finite | mcr-glue; being attempted (cloud) | published form: SGA 1 Exp. V Prop. 1.8 and 1.1, special case (mcr-glue §3) |
| H-91 | `MCRGlue.TameQuotientSmooth` | `scratch/mcr-glue/MCRGlue.lean` L4072 @ main | H-84 | GLUE (composite); L3: a tame quotient of a proper smooth relative curve is proper and smooth | mcr-glue | composite: SGA 1 Exp. V, Mumford AV §7 Thm 3, EGA IV 17.5.1 (mcr-glue §3: composite of three results) |
| H-92 | `MCRGlue.SmoothModelOfP1` | `scratch/mcr-glue/MCRGlue.lean` L4086 @ main | H-84 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); L4: a proper smooth `ℤ_(p)`-curve with generic fibre `P¹_ℚ` is `P¹_{ℤ_(p)}` | mcr-glue | consequence of one theorem: Liu, AGAC §8.3, §10.1 (mcr-glue §3: STANDARD; reading) |
| H-93 | `MCRGlue.TameFixedPointsDisjoint` | `scratch/mcr-glue/MCRGlue.lean` L4100 @ main | H-84 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); L5: fixed points of a tame automorphism with distinct underlying points have disjoint closures | mcr-glue | consequence of one theorem: Edixhoven 1992 Prop. 3.4 with finite étale over a DVR (mcr-glue §3: leaf consequence) |
| H-94 | `MCRGlue.TameInertiaCyclic` | `scratch/mcr-glue/MCRGlue.lean` L4119 @ main | H-84 | GLUE (composite); L6: a finite tame inertia group as in L5 is cyclic | mcr-glue | composite: Serre, Local Fields IV §2 Cor. 1 of Prop. 7, with L5's source (mcr-glue §3: composite of two results) |
| H-95 | `HDec.PropTSRed.CoverModelOfHeckeN` | `ZInQKernel/OneProof/H/TailG.lean` L743 @ main | H-84 | GLUE (project glue); the decomposition's own glue: a model of the Hecke cover of level `N` (gives `ModelYIrreducible` with T5) | mcr-quot | project glue: open here: the chain derives it only through `HeckeNoVertRam`, downstream of the coordinate that mcr-quot feeds (mcr-quot §1) |
| H-96 | `MCRQuot.P1SchemeQ` | `scratch/mcr-quot/MCRQuot.lean` L8549 @ main | H-84 | GLUE (project glue); `P¹_ℚ` exists, is proper and smooth, and represents maps to `P¹` by charts | mcr-quot | project glue: foundations: `Proj ℚ[X₀, X₁]` with its functor of points, not in Mathlib (mcr-quot §1) |
| H-97 | `MCRQuot.CMStabObj` | `scratch/mcr-quot/MCRQuot.lean` L7648 @ main | H-84 | GLUE (project glue); each CM class is fixed by a Hecke operation of order exactly 2 on classes (QM objects over `ℚ̄`) | mcr-quot | project glue: object-level glue on CM points, no schemes (mcr-quot §1) |
| H-114 | `ZInQ.HeightSplit.R5.EichlerOptimalEmbeddingCount` | `scratch/height-split/R5Count.lean` L70 @ main | H-3 | **LEAF**; optimal embeddings `R ↪ 𝒪` modulo `𝒪^×` are finite, with Eichler's count | height-split | published form: Eichler 1955; Vignéras III 5.11-5.12 (height-split §4; the `𝒪^×` versus `𝒪¹` count is UNVERIFIED) |
| H-115 | `ZInQ.HeightGlue.QM.CMDescent` | `scratch/height-glue/QMFull.lean` L1302 @ main | H-3 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); a QM pair over `ℂ` with `End_𝒪` an imaginary quadratic order is the base change of one over `ℚ̄` | height-glue | consequence of one theorem: Shimura–Taniyama 1961 §12.4 Prop. 26, with the classification of endomorphism algebras bundled (height-glue §3.2 and its review; reading) |
| H-116 | `ZInQ.HeightGlue.QM.QMUniformizationC` | `scratch/height-glue/QMFull.lean` L208 @ main | H-3 | GLUE (composite); QM pairs over `ℂ` up to isomorphism are the `𝒪^×`-orbits on `ℂ ∖ ℝ`, with `End_𝒪` the order of `τ` | height-glue | composite: Shimura 1963 §§2-4 with Hashimoto 1995, Rotger 2004, Voight Ch. 43: "not one printed statement" (height-glue §3, docstring) |
| H-133 | `HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.ThetaNullNonvanishing` | `scratch/qm-split/ThetaRatios.lean` L41 @ main | H-44 | **LEAF**; genus 2: at most one even theta-null vanishes | qm-split | published form: Mumford, Tata II IIIa §8; Igusa 1962 (qm-split §4) |
| H-134 | `HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.ThetaFourthRatiosAlgebraic` | `scratch/qm-split/ThetaRatios.lean` L58 @ main | H-44 | GLUE (composite); `θ⁴` ratios at period matrices of surfaces over number fields are algebraic | qm-split | composite: Appell–Humbert, GAGA, Thomae, Jacobi, Weil's dichotomy, or Shimura 1976 (qm-split §3) |
| H-137 | `HDec.QMSplit.Moduli.CanonicalModelY3` | `scratch/qm-split/ModuliSplit.lean` L40 @ main | H-1 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); the level-3 QM moduli problem has a fine witness | qm-split; being attempted (cloud) | consequence of one theorem: Shimura 1967; Deligne 389 Thm 4.21; the audit's qualified consequence (Lemma QP) (qm-split §4) |
| H-138 | `HDec.QMSplit.Moduli.ReciprocityOfFine` | `scratch/qm-split/ModuliSplit.lean` L77 @ main | H-1 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); per witness: Shimura reciprocity at CM points | qm-split | consequence of one theorem: Shimura reciprocity on the canonical model, transported (qm-split §3) |
| H-140 | `HDec.QMSplit.Moduli.CanonicalCoarseX6` | `scratch/qm-glue/ModuliCompare.lean` L581 @ main | H-1 | GLUE (composite); some fine witness carries a coarse witness onto `X₆(ℚ̄)`, `X₆` geometrically connected | qm-glue | composite: Shimura 1967 Main Thms I-II, Deligne 389 Thm 4.21 and §2 (π₀), SGA 1 V 1.8 (quotient), with the Lemma QP caveat; reading: qm-glue §4.2 labels it a published form |
| H-141 | `HDec.QMSplit.Moduli.BabaGranathX6` | `scratch/qm-glue/ModuliCompare.lean` L590 @ main | H-1 | **LEAF**; some coarse witness carries `π₆ : X₆ → P¹` with the fibre and CM clauses, onto `P¹(ℚ̄)` | qm-glue | published form: Baba–Granath 2008 Thm 2.1, §3.1, normalized by a Möbius map (qm-glue §4.2) |
| H-142 | `HDec.QMSplit.Moduli.GonzalezRotgerX6` | `scratch/qm-glue/ModuliCompare.lean` L600 @ main | H-1 | **LEAF**; some coarse witness has the residue fields of CM points (`R5ptProps`) | qm-glue | published form: González–Rotger 2006 Thm 5.12 (qm-glue §4.2) |
| H-143 | `HDec.QMSplit.Moduli.ConicCanonical` | `scratch/qm-glue/ModuliCompare.lean` L673 @ main | H-43 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); some witness of the full clause list has the conic model of `X₆` | qm-glue | consequence of one theorem: Kurihara 1979, Elkies 1998 §3; the stated form is derived as for H-43 (`X6Kummer.X6ConicModel`'s docstring); reading: qm-glue §4.2 labels it a published form |

### 4.8 Bundle fields never projected (not on the list)

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

### 4.9 Statement reviews of the leaves (leaf-review-a, leaf-review-b, leafq-check, the r4 tasks)

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

## 5. Completeness check

### 5.1 Scenario A (compiled composite)

`python3 scratch/frontier/chain.py A` (from the repository root): 0 signature mismatches; 72 open nodes = the
31 + 20 + 14 + 1 = 66 fields of C4''''s four bundles (each expanded from the structure as read at main) plus the 6
TYZ and GZ hypotheses of the top: the hypothesis list of the composite of C2, T0 with T0', and C4'''', 66 of them
projected (§4.8). With leaf-fold8's forms for the fields and this report's for the top, the projected 66 are 41 LEAF
and 25 GLUE strict, 52 and 14 lenient. `chain.py onep`: its hypotheses are scenario A's (the four bundles and the six top Props), and leaf-fold8's `fields8.tsv` lists the bundles' fields with the same names and types (the table abbreviates `bdRInvariants`'s binders).

### 5.2 Scenario F (frontier)

`python3 scratch/frontier/chain.py F`: 0 signature mismatches over 154 theorem edges in the file (26 followed on the
route); 86 open nodes = the 80 of §0 + the 6 never-projected fields. Where a followed edge's file is not the H base,
the check compares the Prop it proves with the one the route uses (`defcheck`):
- `CoordinateNormalization`: identical.
- `CoordinateFromSections`: identical (vs scratch/mcr-glue/MCRGlue.lean, which takes it).
- `TorsionStructure`: the kernel's own constant (ZInQKernel/HDecomp/Objects.lean), which OneProof/H imports.
- `FibreAutTame`: identical.
- `CurveBijIso`: identical.
- `CMSectionsDisjoint`: identical (vs scratch/mcr-glue/MCRGlue.lean, which takes it).
- `GenericQuotientP1`: identical.
- `T11b_Rigidity`: identical (vs ZInQKernel/HDecomp/LeafPush2/T.lean, imported by OneProof/H).
- `T11bExists`: identical.
The fields that cloud-w07 proves are kernel constants named with `_root_` in the bundles, and each proof imports the
module that defines its Prop (`rootcheck`): `NormalModelOfFunctionFieldQ`; `JacobianExists`.
For the files over leaf-fold4's chain (`import TailK`, qm-split's H-44 split here), the definitions of the chain
Props their followed edges use are identical in the H base and in leaf-fold4's sources (`chaincheck`): `ThetaRatiosAlgebraic` identical (OneProof/H vs leaf-fold4's chain).
The pairwise checks of r2 still pass. The eight kernel leaf copies that the flat files carried are gone: OneProof/H
imports `ZInQKernel/HDecomp/Objects.lean` itself. mcr-quot's T5 is the kernel's `ObjBridge.TorsionStructure`, which
`Objects.lean` proves `Iff.rfl` to `PkgI2.TorsionStructure.{0}` (`torsionStructure_iff`).

`python3 scratch/frontier/chain.py doc` compares the rows `Z-n`, `T-n`, `H-n` with the scenario-F open set minus the
never-projected fields: 80 rows with 80 distinct heads, equal to the F open set minus the never-projected fields.

What the script does not check: that the edges compose in one Lean environment; argument instantiation (for example
`heckeVertWitness_of_leaves5` takes `R1R2fp`, extracted from `r1r2` by `Classical.choice`); section variables that a
theorem takes through `include` (none on the route since qm-glue replaced qm-split's `qmHauptmodulBase3_of_O1`); and
the defs that a Prop's def mentions (only the top-level def text is compared).

## 6. Integration state

### 6.1 Composites that exist
- **`ZInQ.OneProof.frozenTarget`** (main; leaf-fold8's bundles and T0' since w59): scenario A as one library theorem (§1).
- **C4'''', leaf-fold8** (b0f2f6da, in w59): 31 + 20 + 14 + 1 fields inside OneProof (`TailY`-`TailZ4` over leaf-fold7's
  `TailP`-`TailX`); lake build and axioms REPORTED.
- **The top in the kernel**: C2 (atkin-li) and tyz-chain's T0, with T0' (tyz-split) in `OneProof/TYZSplit.lean`.
- Superseded: C4''' (leaf-fold6), C4'' (leaf-fold5), C4' (leaf-fold4), C4 (assemble-port) and the variants listed in r2.

### 6.2 What folding scenario F into C4'''' needs
leaf-fold7 and leaf-fold8 take a fold only if neither GLUE count rises and the fold lowers the strict GLUE count or
replaces a consequence or composite by published-form leaves (leaf-fold7 §5, leaf-fold8 §5). Under that rule:
- the cloud-w07 proofs would go in: they prove the fields' own constants (§5.2);
- H-3 stays out until `QMUniformizationC` is split (leaf-fold8 §5: strict and lenient GLUE +1 each);
- H-44 and the coordinate stay out: one field becomes a leaf plus smaller statements, and under the coordinate one
  glue field becomes three glue Props;
- H-1 and H-43: leaf-fold8 counted −2 + 3 strict GLUE with `CoarseFactor` open. coarse-factor has since proved it,
  over OneProof's own chain, so by leaf-fold8's forms the fold is now neutral in the strict count; with this report's
  readings of `CanonicalCoarseX6` and `ConicCanonical` it would rise by 2.
SPECULATIVE until compiled.

### 6.3 The library theorem
`ZInQ.OneProof.frozenTarget` has exactly the hypotheses of scenario A. Each F edge removes or replaces a field once
folded; B6 would change its TYZ hypothesis `hS` to `CMModuli` and `X0RatStructure`.

## 7. Findings

**Refresh r4 (2026-11-14).**

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

## 8. Tasks (snapshot 2026-11-14 12:40 PST; heads in `scratch/frontier/refs.txt`)

Finished, with results used in r4: leaf-fold8 (b0f2f6da), mcr-quot (9367131f), coarse-factor (961af262), cloud-w07
(44e8323f, fork PR #11), leaf-fold7 (53acb891), height-glue (48126d61), qm-glue (96c318b1), leaf-fold6 (733d8013),
mcr-glue (512c3a7e), av-glue (8d3c7a91), av-split (60d0da44), height-split (256f8e41), curve-split (34323233),
hodge-split (683f3372), qm-split (ead4b7dc), tyz-split (99e582b5), fork PRs #6-#10, and the integrator's one-proof
(OneProof on main). Used in r3 and compiled inside C4'''': leaf-fold5, leafq-check, tyz-chain and the r2 tasks. Read,
not folded: leaf-review-a, leaf-review-b. Being attempted: cloud workers W11-W15 (§0).

Running tasks are on the fork's tracker issue #3.

gz-statements (Contrib modules `ZInQKernel/Contrib/GZStatements/{Weak,Level,Compat,Hensel}.lean` on its branch) proves
that the narrower `ZInQ.GZStatements.FHNonvanishingCd` and `GrossZagierHeegnerCd` (restricted to `C_d`, `d ≡ 5 mod 8`,
`D < −4`) are implied by Z-1, Z-2 and still give `ZInQ.FrozenTarget`
(`frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`); they could replace Z-1, Z-2
(both remain GLUE). Not adopted here (not compiled together with `TYZChain.lean`).

This branch is integration w59 plus this refresh.
