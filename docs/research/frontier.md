# frontier: every open Prop on the path to `ZInQ.FrozenTarget`

Task frontier, 2026-11-13; refresh r2, 2026-11-14 (text checks only, no Lean run in r2). Base: integration w51
(71dc3f1b) with fork main 67c2daf9 (integration w52) merged, on wip/frontier-r2. Branch snapshot: the commits in
`scratch/frontier/refs.txt` (r2 section, read 00:05 PST). Lean: `scratch/frontier/TYZChain.lean`, `TopChain.lean`
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

## 0. Main result

**The list.** If every proof and reduction that the branches had compiled by 2026-11-14 00:05 PST is folded in
(scenario F, §5), the open Props on the path to `ZInQ.FrozenTarget` are **72: 23 LEAF and 49 GLUE**:

| premise | open Props | LEAF | GLUE | table |
|---|---|---|---|---|
| GZ, `Literature.GrossZagier` | 2 | 0 | 2 | §2.2 |
| TYZ, `Literature.TYZThm35ReadingA` | 5 | 2 | 3 | §3.2 |
| H, `SixContactMin`: research-level bundle fields | 21 | 7 | 14 | §4.2 |
| H: textbook bundle fields | 8 | 3 | 5 | §4.3 |
| H: fields that were glue in C4 | 12 | 0 | 12 | §4.4 |
| H: Props introduced by reductions | 24 | 11 | 13 | §4.5 |
| **total** | **72** | **23** | **49** | |

**Since 17:35 (70 → 72).** Five rows are proved outright: `TYZLcalOne` (T-2, tyz-lcal, from T-1 and T-3),
`Lemma321Five` (T-7, tyz-321, from the CM leaf T-5), `T09_WeilPairing` (H-29, av-b2, from H-53 and H-54),
`SerreRigidity3` (H-62, av-b2, from T35 and H-69) and `DivisiblePoints` (H-55, leaf-fold4: T5 gives the surjectivity
it was used for). Ten rows are replaced by seventeen smaller Props: `Thm35First` (T-6) by T-11; T3, T41, T6, T7 and
T11(b) by one weaker leaf each (H-76, H-77, H-70, H-71, H-75); T8 by H-72..H-74; T34 by H-78, H-79; T38 by
H-80..H-82 (its rational-point clause is proved); `HeckeVertWitness` (H-50) by H-83..H-85, with `R1R2fp` from H-1,
T5 (H-25) and the proved `SmoothFibreReduced`. Five LEAF and ten GLUE rows leave; seven LEAF and ten GLUE rows enter.

**The 72 names** (L = LEAF; all others GLUE; details in the tables):
- GZ: `ZInQ.GZDecomp.FHNonvanishing`; `ZInQ.GZDecomp.GrossZagierHeegner`.
- TYZ: `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` (L); `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2`; `ZInQ.Contrib.TYZGenus.Package.Lemma318Literal` (L); `ZInQ.Contrib.TYZGenus.Shimura.ShimuraReciprocityModFn`; `ZInQ.Contrib.TYZGenus.TYZ35.TYZThm33Pinned`.
- H: `LeafAdopt.R1R2fpRep`; `PkgI1.ThetaModularity`; `LeafQM.AV.R5fpCount` (L); `PkgI2.RaynaudCriterion`; `PkgI2.NeronOggShafarevich` (L); `PkgI3.FaltingsSemisimple` (L); `PkgI3.FaltingsTate` (L); `ZInQ.Contrib.R10.DeRhamComparisonHT`; `PkgI4.PanBerger`; `PkgI4.EigenformHT`; `DeligneSerreConseq`; `LeafModCurves.R16_EichlerShimuraJ1'`; `ZInQ.LeafPush2.R18_Javanpeykar`; `ZInQ.DefFaltings.R19_GaudronRemond` (L); `ZInQ.DefFaltings.R20_FaltingsLemma5` (L); `ZInQ.DefFaltings.R21_Bost`; `ZInQ.LeafPush2.R22_Pazuki`; `ZInQ.DefFaltings.StableHeightFinite`; `∀ h, G0Split.FibreQM.R1bFamily …`; `LadicCond.CarayolR17'` (L); `G0Galois.R14Det`; `PkgI2.ReductionTorsionBijective`; `PkgI2.TorsionStructure` (L); `∀ p, PkgI4.T23_FontaineClosure p`; `EigenformTwist`; `PkgI3.QMDichotomyYu`; `LeafModCurves.JacobianExists ℚ` (L); `ZInQ.LeafPush2.UniformizationExists` (L); `ZInQ.RLeaf.X0Transitive`; `FS5NoCM.CMOptimalEmbedding`; `X6Kummer.X6ConicModel`; `HSyn.G0Split.ThetaPt.ThetaRatiosAlgebraic`; `PkgI1.QMHauptmodul`; `HSyn.G0Split.FibreQM.QMClassNumberOne`; `HSyn.G0Split.FibreQM.PeriodMapH.CMDescends`; `HSyn.G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar`; `G0Galois.SenTwist`; `G0Galois.FiniteImageHT`; `WeilPairing.T09_SymmIsogenyExists`; `WeilPairing.IsogenyQuasiInverse`; `HomUnify.HomLatticeCorr`; `HSyn.G0Split.FibreQM.PeriodGlue.GammaStarGen`; `TSHecke.Y3Connected`; `QMAutCard`; `ALFixedPoints`; `ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii` (L); `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` (L); `ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii` (L); `ZariskiConn.ZariskiConnectedness` (L); `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` (L); `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` (L); `ZInQ.Contrib.AVB1.PoincareComplement` (L); `ZInQ.Contrib.AVB1.ImageFactorization`; `ZInQ.Contrib.AVB1.SimpleSurjIsogeny`; `AVB2.T11bExists` (L); `ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj` (L); `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` (L); `ZInQ.Contrib.CurvesG.DimJacobianEqGenus`; `ZInQ.Contrib.CurvesG.GenusX1Field`; `ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ` (L); `ZInQ.Contrib.CurvesG.NormalCurveSmoothQ`; `ZInQ.Contrib.CurvesG.GeomConnectedOfConstantFieldQ`; `VertWitness.ShimuraGoodReduction`; `ModelGlue.ModelCoordinateResidue`; `ModelGlue.CurveBijIso`.

Six more bundle fields (R1(d) reciprocity `r1rec`, R3, R5(ii), R7(b), R8, T10) are hypotheses of the compiled H
assembly but are never projected by its proof (§4.6); they are not on the list, and removing them needs only a
restated bundle (not done).

**How far this is checked.**
- **GZ and TYZ.** `ZInQ.Frontier.frozenTarget_of_open` (`scratch/frontier/TYZChain.lean`, compiled 11-13, standard
  axioms) derives `ZInQ.FrozenTarget` from H and the 9 GZ and TYZ Props of the 17:35 list. r2's three TYZ edges
  (tyz-lcal, tyz-321, tyz-35; §3.1) each compile on their branch (0 errors, standard axioms; REPORTED) and are checked
  textually here: signatures, and def texts identical to `TYZChain.lean`'s (the L-leaves are the kernel's own
  constants in both files). No one file compiles the three together with C0 yet.
- **H, scenario A ("compiled").** leaf-fold4's `HDec.HSyn.sixContactMin_of_open4` (C4', §1; flat file compiled in
  1048 s, 326 axiom reports all standard; REPORTED by its report) gives the kernel's `ZInQ.SixContactMin` from
  26 + 19 + 20 + 1 = 66 fields. With `frozenTarget_of_open` this is a composite of two compiled theorems that meet at
  the kernel Prop `ZInQ.SixContactMin`. Its open set is 75 Props, 69 of them projected (§5.1). **leaf-fold4 compiles
  the 17:35 scenario F**: its 60 projected fields are the 61 H rows of the 17:35 list minus `DivisiblePoints`.
- **H, scenario F ("frontier").** A plus the 14 H edges of §4.1, each a theorem that compiles on its branch per the
  branch's own log. `chain.py` checks each edge's hypotheses and conclusion (0 mismatches) and checks that every
  leaf-fold4 Prop an edge proves or reduces has the same `def` text in the proving file (or its kernel definition) as
  in leaf-fold4's flat file (11 of 11), plus the pairwise def checks of §5.2. The composite of scenario F is not
  compiled anywhere; leaf-fold5 (running) folds the H edges.

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

**Findings in brief** (§7): leaf-fold4 compiles the 17:35 list; fork main carried the 11:21 version of this report
until w51; the two statement reviews call five open rows CONSEQUENCE that this report calls LEAF (H-3, H-16, H-21,
H-25, H-38: a human decision); tyz-318's reduction of T-4 and shimura-modfn's split of T-5 are recorded but not folded;
chain.py's ts-kummer revision of 17:35 was not on the fork (repaired).

## 1. The chain to `ZInQ.FrozenTarget`

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| C0 | `ZInQ.Frontier.frozenTarget_of_open` | `scratch/frontier/TYZChain.lean` (this task, compiled) | `SixContactMin`, the 7 TYZ Props of §3.2 (via T0), `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (fork-main-only variant: `frozenTarget_of_open_main`, `TopChain.lean`, with A3's 7 TYZ Props) |
| C1 | `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` | `Contrib/GZDecomp/Decomp.lean` @ main | `SixContactMin`, `TYZThm35ReadingA`, `HeckeThetaNewform`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (via `GrossZagierCd`; `HeckeContinuation`, `FunctionalEquation5` discharged by the proved `ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) |
| C2 | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` | `Contrib/GZTheta/NewCMFinal.lean` @ wip/atkin-li 6f77abb1 | `SixContactMin`, `TYZThm35ReadingA`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` |
| C3 | TYZ: §3.1 | | → `TYZThm35ReadingA` |
| C4' | H: `HDec.HSyn.sixContactMin_of_open4 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4) (l : OpenAddedLeaves4) (g : OpenGlue4)` | `scratch/leaf-fold4/Leaves4.lean` L118447 @ wip/leaf-fold4 9dcf1ca8 (final; flat file, 118 478 lines, md5 6bbeb639: `lake env lean` exit 0 in 1048 s, 0 errors, no `sorry`, 326 axiom reports all standard; olean chain and `Check4.lean`, the kernel conclusion, compiled; REPORTED by its report and log); on fork main since w49 | → `ZInQ.SixContactMin`; 26 + 19 + 20 + 1 fields (§4) |
| C5 | assemble-port's `HDec.HSyn.sixContactMin_of_leaves5` (C4 of the 17:35 report; 26 + 17 + 27 fields) | `scratch/assemble-port/AssemblePort.lean` L116751 @ 92a27877 | C4' is its successor through leaf-fold2-4: the 17:35 scenario-F edges folded, `chartProper`, `chartQuasiFinite`, `hauptmodulUnique` proved, `periodMapGlue`, `abVarSpreadsOut` reduced to leaves, `DivisiblePoints` removed (leaf-fold4 §1.1); g0-assemble3's 46-glue-field `sixContactMin_of_leaves4` before it |
| C6 | H, per field: §4 | | each open field, or the Props it was reduced to |
| (C0 ∘ C4' in the library) | `ZInQ.OneProof.frozenTarget (r : HDec.HSyn.OpenResearchLeaves2) (t : HDec.HSyn.OpenTextbookLeaves4) (l : HDec.HSyn.OpenAddedLeaves4) (g : HDec.HSyn.OpenGlue4) (h11 …) (h1 …) (h29 …) (hcm …) (hs …) (h318 …) (hG …) (hL2 …) (hL3 …) : ZInQ.FrozenTarget` | `ZInQKernel/OneProof/Main.lean` @ wip/one-proof 3d527a1c (the integrator's; leaf-fold4's olean chain as library modules + `TopChain.lean`) | scenario A with `TopChain.lean`'s 7 TYZ hypotheses (A3 of §3.1); wip/one-proof-tyz (running) adds cm-bridge's chain |

The fork's registered headline (`ZInQKernel/MainLiterature.lean`) has five hypotheses; two are proved
(`ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) and C1 already uses them. C4' concludes the kernel's
`ZInQ.SixContactMin` (the flat file imports the kernel's definition; `Leaves.lean` is wrapped in `namespace HDec`), so
C0 and C4' compose by modus ponens. Earlier compiled H assemblies (cpts-transport's 44-field and linked-ram's 45-field
`GluePieces5` in the W0 world, lt-goodred's and linked-frob's variants, leaf-fold2's `sixContactMin_of_open2`) are
superseded by C4 and C4'. leaf-fold5 (running) is a further assembly.

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

| # | Lean name | defined in | class | nearest published sources (all numbers UNVERIFIED) | last task; newest commit | running now |
|---|---|---|---|---|---|---|
| Z-1 | `ZInQ.GZDecomp.FHNonvanishing` | `Contrib/GZDecomp/Decomp.lean:109` @ main | GLUE (lit-composite: Friedberg–Hoffstein's theorem with chosen local conditions, plus the root number of a twist `ε(f⊗χ_D) = ε(f)χ_D(−N)`; gz-decomp §2.4 argues it is not stronger than the source; **open**: whether FH's printed theorem allows the level `32d²`, even and not squarefree; a human must check) | Friedberg–Hoffstein, Ann. of Math. 142 (1995) 385–423, Thm B; Bump–Friedberg–Hoffstein, Invent. Math. 102 (1990) 543–618; Waldspurger, Compositio Math. 54 (1985); Atkin–Li, Invent. Math. 48 (1978) | gz-decomp; main | no |
| Z-2 | `ZInQ.GZDecomp.GrossZagierHeegner` | `Contrib/GZDecomp/Decomp.lean:131` @ main | GLUE (lit-composite: Gross–Zagier's formula, Gross's `ȳ_K = −ε y_K`, the modular parametrization (Eichler–Shimura, Faltings' isogeny theorem), nondegeneracy of `ĥ` (proved in Tau Ceti), folded into one existential because the Heegner point cannot be named in Lean today; gz-decomp §2.5) | Gross–Zagier, Invent. Math. 84 (1986) 225–320, Thm I.6.3, Ch. V; Gross, *Heegner points on X₀(N)* (Durham 1983), 1984, §5; Shimura 1971 Thm 7.14–7.15; Faltings, Invent. Math. 73 (1983), Kor. 2; Shimura, Nagoya Math. J. 43 (1971) | gz-decomp; main | no |

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

### 3.2 Open Props (5: 2 LEAF, 3 GLUE)

| # | Lean name | defined in | class | citation (UNVERIFIED unless marked) | last task; newest commit | running now |
|---|---|---|---|---|---|---|
| T-1 | `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` | `Contrib/TYZDecomp/Leaves.lean` @ main | **LEAF** (specialization: odd `m` only) | TYZ Thm 1.1, first assertion, L371–380 (read by nt-tyz) | tyz-decomp; main (tyz-lcal audit 11-13: faithful, not stronger) | no |
| T-3 | `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2` | same | GLUE (mod-2 composite of Lemma 2.9 and Prop. 2.3) | TYZ Lemma 2.9, L1062–1066 (journal Lemma 2.9 per the AI locator audit); Prop. 2.3, L580–586 | tyz-decomp; main (tyz-lcal audit 11-13: faithful, not stronger) | no |
| T-4 | `ZInQ.Contrib.TYZGenus.Package.Lemma318Literal` (at `HHprime`) | `Contrib/TYZGenus/Package.lean:808` @ main | **LEAF** (specialization: only `⊆ A[(1+i)³]`, `n ≡ 5`; the identification of `HHprime` and `y² = x³ + 4x` with TYZ's `ℍ'_n`, `2y² = x³ + x` is AI-reviewed) | TYZ Lemma 3.18, L2230–2232 (read by nt-tyz, cm-bridge) | cm-points; main (owner: cm-numeric). tyz-318 (94b05c87): from the GLUE `SqrtTwoNotInHHprime` (TYZ's Step 3, `∀ s ∈ ℍ'_n, s² ≠ 2`), proved outright when `n` is the only divisor `≡ 5 (mod 8)`; not folded (it trades a LEAF for GLUE) | sqrt2-glue (`SqrtTwoNotInHHprime`) |
| T-5 | `ZInQ.Contrib.TYZGenus.Shimura.ShimuraReciprocityModFn` | `ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean` @ tyz-cm 0ad48a7d | GLUE (Gross's form of Shimura reciprocity for values of `g ∈ ℚ(X₀(N))` at Heegner points, for all `N`, all regular `g`, all lattice pairs: stronger than any single printed statement) | Shimura 1971 Thm 5.4; Silverman, *Advanced topics* II.8.2; Gross 1984 §3; Cox Cor. 11.37 | tyz-cm (finished 11:42). shimura-modfn (6bc73469): correctly stated, a consequence of Shimura 1971 Thm 5.4 with the canonical model of `X₀(N)`, no stronger; its split `MainTheoremCMj` + `RatX0Rep` + the leaf at singular points is not folded (the report keeps the CM leaf) | no |
| T-11 | `ZInQ.Contrib.TYZGenus.TYZ35.TYZThm33Pinned` (for every `ℓ` with `IsTYZLcal ℓ`) | `scratch/tyz-35/Thm35.lean` L750 @ tyz-35 a8101726 | GLUE (lit-composite: TYZ Thm 3.3 with Lemma 3.14 for the pinned CM points; signs absorbed into `ε`, `z_n ∈ A(H'_n)` from Shimura reciprocity and Thm 3.6(1), `P_χ` independent of the lifts; HUMAN CHECK of `Φ`, `χ_{d₀,d₁}` and `h₂` against Period7.tex) | TYZ Thm 3.3 L1299–1311 (proof L1865–2023), Lemma 3.14 L1868, Lemma 3.15 L1919; its inputs Thm A.9 L3062–3077 (Yuan–Zhang–Zhang) and Gross–Zagier/Kolyvagin | tyz-35 (finished 23:19; replaces T-6 `Thm35First`) | no |

Retired rows: T-2 `TYZLcalOne` (proved, B2), T-6 `Thm35First` (reduced to T-11, B4), T-7 `Lemma321Five` (proved,
B3). `TopChain.lean` (fork main only, and the integrator's one-proof) has instead T-1 to T-4 with `TYZLcalOne` and three
GLUE Props: `CM.CMFieldOfDefinition ringClassFieldD`, `Package.TYZSigmaFixesZn` (TYZ Thm 3.6(1) / Cor. 3.9 via Shimura
reciprocity) and the bundled `∀ ℓ, IsTYZLcal ℓ → Package.GenusPointLeafCM ℓ`.

## 4. H: `ZInQ.SixContactMin`

Base (r2): leaf-fold4's compiled C4' (wip/leaf-fold4 9dcf1ca8). It folds everything the 17:35 scenario F applied on
top of assemble-port's C4 (`t40` through `X0Transitive`, `t26` from T5, `piTwistC`, `sphereFactorAffine`,
`properSmoothGenConnected` through Zariski's theorem), proves hecke-rest's `chartProper`, `chartQuasiFinite` and
period-glue's `hauptmodulUnique`, reduces `periodMapGlue` and `abVarSpreadsOut` to leaves, derives `QMDenZeroCM3`, and
drops `DivisiblePoints` (T5 gives the surjectivity it was used for). Bundles: `OpenResearchLeaves2` (26, unchanged since
leaf-fold2), `OpenTextbookLeaves4` (19), `OpenAddedLeaves4` (20) and `OpenGlue4` (1, `heckeVertWitness`). leaf-fold4
uses the kernel's own theorems for `AutOInnerFinite`, Skolem–Noether, Zariski, the spread-out theorem, T5/T26 and T40
by definitional unfolding (leaf-fold4 §1.1). Worlds: **W-HDec** = the chain in `namespace HDec` (assemble-port,
leaf-fold, leaf-fold2-4; av-b2 compiles on leaf-fold3's olean chain); **W-kern** = files that import
`ZInQKernel.HDecomp.*` (the Contrib textbook proofs, AVB1, CurvesG, NeronC, SmoothFibre, zariski-conn, t5-torsion);
**W-vw** = vert-witness's `VertWitness.lean` (hecke-rest's statements verbatim) and model-glue's files built on it. In
C4' every H name below carries the prefix `HDec.`; the tables omit it. Row numbers are those of the 17:35 report; rows
that left the list keep their numbers retired; new rows start at H-70. Def locations in the kept rows are the C4 copies
(the same text as leaf-fold4's flat file, by chain.py's def checks); "K" gives the kernel copy under
`ZInQKernel/HDecomp/`.

### 4.1 What scenario F applies on top of C4' (each VERIFIED by `chain.py`: signature, and def text identical to leaf-fold4's)

| field of C4' (row) | now | theorem · branch@commit · file | world |
|---|---|---|---|
| `t6 : PkgI3.HomFreeFinite` (H-26) | ⇐ H-70 | `ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed` · av-b1 (main) · `Contrib/AVB1/AlgClosed.lean` | W-kern |
| `t7 : PkgI3.CharPolyIndepOfEll` (H-27) | ⇐ H-71 | `ZInQ.Contrib.AVB1.charPolyIndepOfEll_of_algClosed` · same | W-kern |
| `t8 : PkgI3.PoincareReducibility` (H-28) | ⇐ H-72, H-73, H-74 | `ZInQ.Contrib.AVB1.poincareReducibility_of_pieces` · av-b1 · `Contrib/AVB1/Poincare.lean` (also `…_of_simpleImage` from H-72 and `SimpleImageIsogeny`, which follows from H-73, H-74) | W-kern |
| `t9 : LeafPush.T09_WeilPairing` (H-29) | proved from H-53, H-54 | `HDec.AVB2.t9_of_leaves3` · av-b2 (main) · `scratch/av-b2/olean/AVB2Main.lean` (weil-pairing's proof at the field's own type) | W-HDec |
| `serreRigidity3 : HeckeRest.SerreRigidity3` (H-62) | proved from H-38 (T35), H-69 | `HDec.AVB2.serreRigidity3_of_T35` · av-b2 · same (with g9-abvarbc's proved `MulIsogeny`) | W-HDec |
| `t11b : ZInQ.LeafPush2.T11b_Rigidity` (H-31) | ⇐ H-75 | `HDec.AVB2.t11b_of_exists` · av-b2 · same | W-HDec |
| `t3 : PkgI2.NeronMappingAbelianScheme` (H-23) | ⇐ H-76 | `ZInQ.Contrib.NeronC.neronMappingAbelianScheme_of_surj` · neron-c (main) · `Contrib/NeronC/NMPInjective.lean` | W-kern |
| `t41 : ZInQ.H5Neron.NeronModelExists` (H-39) | ⇐ H-77 | `ZInQ.Contrib.NeronC.neronModelExists_of_extension` · neron-c · `Contrib/NeronC/NeronGroup.lean` | W-kern |
| `t34 : LeafModCurves.DimJ1Genus` (H-37) | ⇐ H-78, H-79 | `ZInQ.Contrib.CurvesG.dimJ1Genus_of_split` · curves-g (main) · `Contrib/CurvesG/GenusSplit.lean` | W-kern |
| `t38 : X1Belyi.CurveOfFunctionFieldQ` (H-40) | ⇐ H-80, H-81, H-82 | `ZInQ.Contrib.CurvesG.curveOfFunctionFieldQ_of_split` · curves-g · `Contrib/CurvesG/CurveSplit.lean` (the rational-point clause is proved by the valuative criterion) | W-kern |
| `heckeVertWitness : HeckeRestNV.HeckeVertWitness` (H-50) | ⇐ H-83, `R1R2fp` (from H-1), `SmoothFibreReduced`, `ModelCoordinate`, `ModelComparison` | `VertWitness.heckeVertWitness_of_leaves` · vert-witness (main) · `scratch/vert-witness/VertWitness.lean` | W-vw |
| `SmoothFibreReduced` (vert-witness) | proved | `ZInQ.SmoothFibre.smoothFibreReduced` · smooth-fibre 82abd02c (main) · `Contrib/SmoothFibre/Basic.lean` (Mathlib only; same body as vert-witness's def) | W-kern |
| `ModelCoordinate` (vert-witness) | ⇐ H-84 | `ModelGlue.modelCoordinate_of_residue` · model-glue c6231df7 (main) · `scratch/model-glue/ModelGlue6.lean` | W-vw |
| `ModelComparison` (vert-witness) | ⇐ H-85, H-25 (T5) | `ModelGlue.modelComparison_of_curveBijIso` · model-glue · same | W-vw |

Retired rows: H-23, H-26, H-27, H-28, H-29, H-31, H-37, H-39, H-40, H-50, H-55 (`DivisiblePoints`, removed by leaf-fold4)
and H-62.

Not applied: homlattice's `HomLatticeCorr ⇐ StrongUniformizationExists + GAGAMorphism` (it would raise the count by one;
leaf-fold4 §6); t5-torsion's further options for T5 (a leaf for a leaf); av-b2's `divisiblePoints_of_posChar` (not
needed since leaf-fold4); neron-c's reduction of H-77 to local leaves (one published leaf for three leaves and two glue
Props); spread-out's `abVarSpreadsOut_of_ega_loc` (a leaf for glue).

### 4.2 Research-level bundle fields still open (21: 7 LEAF, 14 GLUE)
| # | field : Lean name | leaf | class | citation | flags | last task |
|---|---|---|---|---|---|---|
| H-1 | `r1r2 : LeafAdopt.R1R2fpRep` | R1(a,c,d), π₀, R2, R5 on X₆ | GLUE (assembled from several statements) | Shimura, Ann. of Math. 85 (1967), Main Thms I-II; Deligne, Sém. Bourbaki 389 (1971), Thm 4.21, Cor. 5.7, Ex. 5.8; Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1, Lemma 3.1; González–Rotger | Lemma P; pin clauses UNVERIFIED | pin-apply, leaf-adopt |
| H-2 | `r4 : PkgI1.ThetaModularity` | R4 | GLUE ("in the form stated"; signs checked numerically) | Igusa, Amer. J. Math. 84 (1962), 89 (1967) pp. 833-834, 848 | used on route F only (by `s8WeightExact_of`) | pkg-I1 |
| H-3 | `r5count : LeafQM.AV.R5fpCount` | R5(i) | **LEAF** (restated 2026-11-12 to the text the audit read: `2^b(R) h(R)`) | González–Rotger, J. Math. Soc. Japan 58 (2006), Prop. 5.6 | Lemma P | leaf-qm-fp, loc-fix |
| H-4 | `r6 : PkgI2.RaynaudCriterion` | R6 | GLUE (Galois-theoretic consequence) | SGA 7 I, Exp. IX, Prop. 4.7 with 3.5; Silverberg–Zarhin, AIF 45 (1995), Thm 3.5 | case `m = 3` UNVERIFIED | pkg-I2 |
| H-5 | `r7a : PkgI2.NeronOggShafarevich` | R7(a) | **LEAF** | Serre–Tate, Ann. of Math. 88 (1968), Thm 1 | UNVERIFIED | pkg-I2 |
| H-6 | `r9a : PkgI3.FaltingsSemisimple` | R9(a) | **LEAF** | Faltings, Invent. Math. 73 (1983), Satz 3 (erratum 75 (1984)) | UNVERIFIED | pkg-I3 |
| H-7 | `r9b : PkgI3.FaltingsTate` | R9(b) | **LEAF** | Faltings 1983, Satz 4, Kor. 1 | UNVERIFIED | pkg-I3 |
| H-8 | `r10 : ZInQ.Contrib.R10.DeRhamComparisonHT` (in C4 the copy `HDec.PkgI4.DeRhamComparisonHT`, same text) | R10 amended | GLUE (Tate-module form, a consequence with T10; plus the Hodge–Tate weight clause) | Scholze, Forum Math. Pi 1 (2013), Cor. 1.8, Thms 9.1, 9.3 + corrigendum; Tate 1967; Faltings 1988 | added clause UNVERIFIED | r10-amend |
| H-9 | `r11r12 : PkgI4.PanBerger` | R11 + R12 | GLUE (joint consequence of two theorems) | Berger, Invent. Math. 148 (2002), Thm 0.7; Pan, JAMS 35 (2022), Thm 1.0.4 | JAMS numbering UNVERIFIED | pkg-I4 |
| H-10 | `r13 : PkgI4.EigenformHT` | R13 | GLUE (consequence via Kato, after dualization) | Kato, Astérisque 295 (2004), §§9.2-9.4; Saito 1997 | | pkg-I4 |
| H-12 | `r15 : DeligneSerreConseq` | R15 | GLUE (consequence, with T25, T18, T19) | Deligne–Serre, Ann. Sci. ÉNS 7 (1974), Thm 4.1, Lemma 3.2 | | hdec-faithful |
| H-13 | `r16 : LeafModCurves.R16_EichlerShimuraJ1'` | R16 | GLUE (three suppliers) | Shimura 1971 Thm 7.9; Shimura 1973 Thm 1 | | leaf-modcurves |
| H-14 | `r18 : ZInQ.LeafPush2.R18_Javanpeykar` | R18 | GLUE (consequence) | Javanpeykar, ANT 8 (2014), Thm 1.1.1 | H5 | leaf-push2 |
| H-15 | `r19 : ZInQ.DefFaltings.R19_GaudronRemond` | R19 | **LEAF** | Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4 (read by the audit) | H5; normalization-sensitive | def-faltings |
| H-16 | `r20 : ZInQ.DefFaltings.R20_FaltingsLemma5` | R20 | **LEAF** | Faltings 1983, Lemma 5; Raynaud, Astérisque 127, VII Cor. 2.1.3 | H5; UNVERIFIED | def-faltings |
| H-17 | `r21 : ZInQ.DefFaltings.R21_Bost` | R21 | GLUE (taken through Gaudron–Rémond §9; Bost's display unread) | Bost, Sém. Bourbaki 795 (1996) | H5 | def-faltings |
| H-18 | `r22 : ZInQ.LeafPush2.R22_Pazuki` | R22 | GLUE (hardened, not the literal corollary) | Pazuki, Bull. SMF 140 (2012), Cor. 1.3(2) | H5; Def. 2.6 identification UNVERIFIED | leaf-push2 |
| H-19 | `h5fin : ZInQ.DefFaltings.StableHeightFinite` | H5 (finiteness) | GLUE (theorem plus correctness of the definition) | Faltings 1983 §1; Deligne, Sém. Bourbaki 616; BLR 1.2/1, 1.4/3 | | h5-glue, g0-assemble2 |
| H-20 | `r1b : ∀ h, G0Split.FibreQM.R1bFamily …` (research field in C4) | R1(b) | GLUE (family form for the triple `Classical.choice` picks from `R1R2fpRep`) | Shimura 1967 Main Thm I; Deligne 389 §4.15 | | fibre-qm-period |
| H-21 | `r17 : LadicCond.CarayolR17'` (research field in C4) | R17 | **LEAF** | Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A) (read by the audit) | | def-ladic-cond |
| H-22 | `r14 : G0Galois.R14Det` (in C4 the research field R14 is the form with the determinant clause; g0-assemble3 had the det-free `EigenformRepExists` plus a glue field `r14Det`) | R14 with det | GLUE (the reports call it LEAF, but its locators span three publications: Shimura 1971 Thm 7.14, Deligne 1971, Deligne–Serre 1974) | as H-11 | UNVERIFIED | g0-mod-galois |

### 4.3 Textbook bundle fields still open (8: 3 LEAF, 5 GLUE)

| # | field : Lean name | leaf | class | citation | tc-survey | last task; running |
|---|---|---|---|---|---|---|
| H-24 | `t4 : PkgI2.ReductionTorsionBijective` (leaf-fold4's field; `reductionTorsionBijective`, a glue-bundle field in C4; K Objects.lean:975) | T4 (I2-Red) | GLUE (consequence) | Serre–Tate 1968 §1 | NOT FOUND | pkg-I2; used by the frob chain (AlgFrobRed) |
| H-25 | `t5 : PkgI2.TorsionStructure` (K Objects.lean:993) | T5 (I2-Tors) | **LEAF** | Mumford, *Abelian varieties*, §4, §6 | WEAKER (g = 1) | pkg-I2 |
| H-32 | `t23 : ∀ p, PkgI4.T23_FontaineClosure p` | T23 | GLUE (the form on `V^∨` is a consequence, not exact) | Fontaine, Astérisque 223, Thm 3.8 | NOT FOUND | leaf-push |
| H-33 | `t24 : EigenformTwist` (K ModCurves/C9.lean:373) | T24 | GLUE (consequence; atkin-li's `AtkinLiTwistNew` is a different Prop) | Shimura 1971 Prop. 3.64; Atkin–Li 1978 | WEAKER | hdec-faithful |
| H-35 | `t27 : PkgI3.QMDichotomyYu` | T27 | GLUE (locator audit: consequence of the refereed Thm 1.1) | Chia-Fu Yu, J. Pure Appl. Algebra (2013), Thm 1.1 (journal p. 907; arXiv:1210.1125); volume UNVERIFIED | NOT FOUND | loc-fix |
| H-36 | `t33 : LeafModCurves.JacobianExists ℚ` | T33 | **LEAF** (specialized to `P₀ ∈ X(K)`) | Weil 1948; Milne, *Jacobian varieties*, Thm 1.1, Prop. 6.1 | NOT FOUND | leaf-modcurves |
| H-38 | `t35 : ZInQ.LeafPush2.UniformizationExists` | T35 | **LEAF** | Mumford §1 with GAGA (Serre 1956) | WEAKER | leaf-push2 |
| H-41 | `x0Transitive : ZInQ.RLeaf.X0Transitive` (`ZInQKernel/Contrib/RLeaf/IgusaX0.lean:69` @ t40-igusa e9b071d6; for T40) | T40 | GLUE (Galois transitivity on cyclic subgroups of order `N`, derived from the irreducibility of the modular equation through `C ↦ j(E_j/C)`) | Lang, *Elliptic functions*, Ch. 5 §2 Thm 3; Cox Thm 11.18; Shimura 1971 §6.1 | no row | t40-igusa, t40-tate (both finished): `x1RationalCusp_of_x0_tateMuN`, `tateMuN` proved |

T6, T7, T8, T9, T11(b), T3, T41, T34 and T38 are proved or reduced (§4.1); their replacements are rows of §4.5.

### 4.4 Fields that were glue in C4, still open (12, all GLUE; in C4' they are `OpenAddedLeaves4` fields, and `homLatticeCorr` is in `OpenTextbookLeaves4`)

| # | field : Lean name | def part | content; nearest published sources (UNVERIFIED) | report's label | last task; running |
|---|---|---|---|---|---|
| H-42 | `cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding` | a60_fs5 | CM points via optimal embeddings; "a consequence of the published statement" (Shimura 1967; Jordan 1981 §3; González–Rotger 2006 §5) | LEAF | fs5-nocm; no |
| H-43 | `x6ConicModel : X6Kummer.X6ConicModel` | f20_x6kummer | `X₆` is the conic `Y² + 3X² + 3Z² = 0`, `π₆ = −16(X²+Z²)/(27Z²)`; consequence of the published model (Kurihara 1979; Elkies 1998 §3) | LEAF | x6-kummer; no |
| H-44 | `thetaRatiosAlgebraic : HSyn.G0Split.ThetaPt.ThetaRatiosAlgebraic` | 80_theta | theta-constant ratios at a period matrix are algebraic; composite (Shimura, Duke 43 (1976); Mumford, Tata II) | LEAF? | g0-thetapoint; no |
| H-45 | `qmHauptmodul : PkgI1.QMHauptmodul` | Leaves.lean L304 | the theta-quotient Hauptmodul of `Γ*`; "composite, not printed as one theorem" (Baba–Granath 2008; Lin–Yang 2020 Ex. 29; Igusa 1967) | LEAF? | pkg-I1; no |
| H-46 | `qmClassNumberOne : HSyn.G0Split.FibreQM.QMClassNumberOne` | a80_fqm | Eichler class number one for `𝒪`, lattice form (Vignéras Cor. III.5.7; Voight 28.5.17) | LEAF | fibre-qm-period; no |
| H-47 | `cmDescends : HSyn.G0Split.FibreQM.PeriodMapH.CMDescends` | e20_periodmap | CM points descend (Shimura–Taniyama 1961; Shimura 1967) | LEAF? | period-map; period-glue lists it (no commit since 10:27) |
| H-48 | `valenceBoundGammaStar : HSyn.G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar` | e20 | the valence formula for `Γ*` with signature (0;2,4,6) (Shimura 1971 §2.4; Rankin Thm 4.1.4) | LEAF | period-map; period-glue lists it |
| H-51 | `senTwist : G0Galois.SenTwist` | a35_g12det | HT weights of a twist shift by a constant; consequence (Sen 1980 §2) | LEAF | g12-det; no |
| H-52 | `finiteImageHT : G0Galois.FiniteImageHT` | a35 | finite image ⇒ HT with weights 0; composite (Tate 1967 §3; Ax–Sen–Tate; Hilbert 90) | LEAF | g12-det; no |
| H-53 | `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` | a35 | symmetric isogeny to a dual; "existential in D, hence a consequence" (Mumford §§6, 8, 20, 23) | LEAF | weil-pairing; no |
| H-54 | `isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse` | a35 | `fg = [d]`, `gf = [d]` on `K̄`-points (Mumford §7-8) | LEAF | weil-pairing; no |
| H-69 | `homLatticeCorr : HomUnify.HomLatticeCorr` | z95b (hom-unify's `H20_bundle.lean` L184-224, verbatim) | `Hom(A_ℂ, B_ℂ) ≅ {M : MΛ_A ⊆ Λ_B}` through analytic uniformizations: lifting over any `K` with `σ : K → ℂ`, realization over `ℂ`; replaces T11(a), `homLinearLift`, `t11aRiemannHom`. homlattice: true and no stronger than the literature, but not printed in this form (uniformization, GAGA, algebraic ⇒ holomorphic, Birkenhake–Lange Prop. 1.2.1; Mumford §1, §3; Serre 1956) | LEAF (textbook) | hom-unify, folded by assemble-port 5f944406; no |

### 4.5 Props introduced by reductions (24: 11 LEAF, 13 GLUE; H-58..H-67 are `OpenAddedLeaves4` fields of C4')

| # | Lean name | def file @ commit | from field | class; content; sources (UNVERIFIED) | last task; running |
|---|---|---|---|---|---|
| H-58 | `HSyn.G0Split.FibreQM.PeriodGlue.GammaStarGen` | `W8.lean` L415 @ 7e1531df | 16 | GLUE (generators of `Γ*` as explicit `Sp₄(ℤ)` matrices; Takeuchi 1977; report: leaf candidate, "flagged") | period-glue |
| H-59 | `TSHecke.Y3Connected` | ts-hecke `scratch/ts-hecke/TSHecke.lean` L6101 @ ff8e6731 | 28 | GLUE (π₀ of the Shimura curve, Deligne 389 §§2-3, Milne, plus an orbit computation; report: "leaf R1conn") | ts-hecke |
| H-61 | `QMAutCard` | hecke-rest `scratch/hecke-rest/HeckeRestAll.lean` L7369 @ 6c2c1d76 | 31 | GLUE (`|Aut(A,ι)|` = 4, 6, 2 by CM type: consequences of Shimura's classification, Ann. of Math. 78 (1963); Rotger, Crelle 561 (2003) §2) | hecke-rest (finished) |
| H-63 | `ALFixedPoints` | same, L7395 | 31 | GLUE (fixed points of the Atkin–Lehner involutions on `X₆` are CM by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]`; Rotger, Trans. AMS 356 (2004) §§2-4; Ogg 1983; plus an embedding check) | hecke-rest |
| H-64 | `ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii` | spread-out `ZInQKernel/Contrib/SpreadOut/Spread.lean` L35 @ aa304ed7 | 44-46 (route T, via `AbVarSpreadsOut`) | **LEAF** (descent of schemes of finite presentation to a finite stage of a limit; EGA IV₃ 8.8.2(ii), Stacks 01ZM) | spread-out (finished 11:30) |
| H-65 | `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` | same, L49 | 44-46 | **LEAF** (descent of properness; EGA IV₃ 8.10.5(xii), Stacks 081F) | spread-out |
| H-66 | `ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii` | same, L61 | 44-46 | **LEAF** (descent of smoothness; EGA IV₄ 17.7.8(ii), Stacks 07RP) | spread-out |
| H-67 | `ZariskiConn.ZariskiConnectedness` | zariski-conn `ZInQKernel/Contrib/ZariskiConn/Basic.lean` L188 @ 3802f2bc | 44-46 (via `ProperSmoothGenConnected`) | **LEAF** (proper `f`, `Y` locally noetherian, `f_*𝒪_X = 𝒪_Y` ⇒ fibres geometrically connected; EGA III₁ 4.3.4, with non-emptiness from 4.3.1; flag: two numbered statements of one section) | zariski-conn (finished 12:06) |
| H-70 | `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` | `Contrib/AVB1/AlgClosed.lean` L38 @ main | t6 (H-26) | **LEAF** (T6 over algebraically closed fields only: Mumford, *Abelian varieties* §19 Thm 3 in Mumford's own setting; Milne 1986 Thm 12.5) | av-b1 |
| H-71 | `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` | same, L51 | t7 (H-27) | **LEAF** (specialization: T7 over algebraically closed fields, without `deg P = 2g` and `P(n) = deg(n − φ)`; Mumford §19 Thm 4) | av-b1 |
| H-72 | `ZInQ.Contrib.AVB1.PoincareComplement` | `Contrib/AVB1/Poincare.lean` L42 @ main | t8 (H-28) | **LEAF** (Poincaré's complete reducibility in its complement form, weakened; Milne 1986 Prop. 12.1; Mumford §19 Thm 1) | av-b1 |
| H-73 | `ZInQ.Contrib.AVB1.ImageFactorization` | same, L56 | t8 (H-28) | GLUE (lit-composite of textbook facts on images of homomorphisms of abelian varieties; av-b1 §3.3) | av-b1 |
| H-74 | `ZInQ.Contrib.AVB1.SimpleSurjIsogeny` | same, L71 | t8 (H-28) | GLUE (lit-composite: `(ker h)⁰_red` is an abelian subvariety, and simplicity; av-b1 §3.3) | av-b1 |
| H-75 | `AVB2.T11bExists` | `scratch/av-b2/olean/AVB2Main.lean` L215 @ main | t11b (H-31) | **LEAF** (T11(b) with `∃!` weakened to `∃`; Conrad, Enseign. Math. 52 (2006) §3; Milne 1986 §20; uniqueness proved, `baseChange_map_injective`) | av-b2 |
| H-76 | `ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj` | `Contrib/NeronC/NMPInjective.lean` L91 @ main | t3 (H-23) | **LEAF** (the surjective half of the Néron mapping property of abelian schemes over a DVR, BLR §1.2 Prop. 8; the injective half is proved from Mathlib) | neron-c |
| H-77 | `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` | `Contrib/NeronC/NeronGroup.lean` L82 @ main | t41 (H-39) | **LEAF** (a smooth separated quasi-compact model with the extension property and no group law: weaker than BLR §1.4 Thm 3; the group law, `gen` a homomorphism and uniqueness are proved) | neron-c |
| H-78 | `ZInQ.Contrib.CurvesG.DimJacobianEqGenus` | `Contrib/CurvesG/GenusSplit.lean` L46 @ main | t34 (H-37) | GLUE (lit-composite: `T₀J ≅ H¹(X, 𝒪_X)`, Milne, *Jacobian varieties* Prop. 2.1, with Serre duality; the genus is Mathlib-level `fieldGenus`) | curves-g |
| H-79 | `ZInQ.Contrib.CurvesG.GenusX1Field` | same, L59 | t34 (H-37) | GLUE (lit-composite: Shimura's canonical model of `X₁(N)`, Shimura 1971 Prop. 6.9, the genus formula Prop. 1.40, base change of `H⁰(Ω¹)`) | curves-g |
| H-80 | `ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ` | `Contrib/CurvesG/CurveSplit.lean` L27 @ main | t38 (H-40) | **LEAF** (the printed statement of the Stacks section on the normal model of a function field of one variable; curves-g §2) | curves-g |
| H-81 | `ZInQ.Contrib.CurvesG.NormalCurveSmoothQ` | same, L38 | t38 (H-40) | GLUE (lit-composite of two printed facts: normal of dimension 1 is regular; regular and locally of finite type over a perfect field is smooth; Stacks 00TV, 0B8X) | curves-g |
| H-82 | `ZInQ.Contrib.CurvesG.GeomConnectedOfConstantFieldQ` | same, L48 | t38 (H-40) | GLUE (lit-composite of two printed facts: `Γ(X, 𝒪_X) = ℚ` from `ConstantFieldIsQ`, then Stacks 0FD1) | curves-g |
| H-83 | `VertWitness.ShimuraGoodReduction` | `scratch/vert-witness/VertWitness.lean` L1477 @ main | heckeVertWitness (H-50) | GLUE (lit-composite: for each `p > 324` a smooth proper model over `ℤ_(p)` of the level-3 QM Shimura curve with the universal family, the moduli bijection on `ℚ̄`-points and the Hecke automorphisms; Morita 1981, Carayol 1986, Kottwitz 1992, Buzzard 1997; report: leaf; the level-3-at-`3 ∣ D` coverage needs a human check) | vert-witness |
| H-84 | `ModelGlue.ModelCoordinateResidue` | `scratch/model-glue/ModelGlue6.lean` L2232 @ c6231df7 | heckeVertWitness (H-50), through `ModelCoordinate` | GLUE (the coordinate of the tame quotient `𝒴/Γ' ≅ P¹_{ℤ_(p)}` with `CoordFibres` and transcendental reduction at the generic points of the special fibre) | model-glue (finished 23:03) |
| H-85 | `ModelGlue.CurveBijIso` | same, L2954 | heckeVertWitness (H-50), through `ModelComparison` | GLUE (a morphism of proper smooth curves over `ℚ` that is bijective on `ℚ̄`-points is an isomorphism: degree equals the points of a general fibre, by generic smoothness; report: textbook leaf; a composite, not found printed in this form) | model-glue |

Proved since the 17:35 snapshot and gone from the tables: `SerreRigidity3` (av-b2), `T09_WeilPairing` (av-b2), and in the
chain below `HeckeVertWitness`: `SmoothFibreReduced` (smooth-fibre), `SpecialFibreMaxIdeal`, `SpecialFibreUniformizer`,
`SpecialFibreDVR` (vert-witness), `ModelGenericFibre`, `GermOfQbarValues`, `ModelIntegral`, `ModelFunctionField`
(model-glue, the last two from H-85 and `TwistClassFinite`, which comes from T5). Proved before 17:35: see the 17:35
report (`git show d8c95123:docs/research/frontier.md`).

### 4.6 Bundle fields never projected (not on the list)

`r1rec : LeafQM.AV.R1rec`, `r3 : ZInQ.LeafPush2.R03_LinYang`, `r5 : LeafQM.AV.R5fp`, `r7b : PkgI2.SerreTatePotentialGood`,
`r8 : PkgI2.GrothendieckMonodromy`, `t10 : T10Etale.T10_TateDuality`. VERIFIED (agent-h-leaves and my grep) for
g0-assemble3's flat file: they occur only in the structure literals that convert the bundles (and `t10` only in the
unused `HSyn.TextbookLeaves.t10_groupIso`); C4 converts its bundles to g0-assemble3's and uses the same consumers
(REPORTED by assemble-port's report; not re-grepped, its flat file has more conversions). assemble-port already deleted
the unused textbook fields T1, T3, T4 (as textbook fields), T16(b), T20, T21, T28, T29.
r2: in leaf-fold4's flat file `r1rec`, `r7b`, `r8` occur only as `f := r.f` in three structure literals, and `t10` only
there and in `T10_groupIso_of_tateDuality` (VERIFIED, grep of `Leaves4.lean` @ 9dcf1ca8); `r3` and `r5` were not
re-grepped (their names collide with local variables).

### 4.7 Statement reviews of the leaves (leaf-review-a, leaf-review-b)

leaf-review-a (groups A, A′, F: 21 fields) and leaf-review-b (groups B, C, D, E, G: 41 fields) read every leaf-fold3
field with the definitions it uses. Verdicts: 8 PUBLISHED-FORM (`t11b`, `serreRigidity3`, `r7a`, `t41`, `r9a`, `r9b`,
`r19`, `t33`), 54 CONSEQUENCE, none STRONGER-THAN-SOURCE or NOT-A-PUBLISHED-STATEMENT, so no statement repair is
proposed. Their scale is not this report's: a CONSEQUENCE can be a specialization (LEAF here) or a derivation (GLUE
here). Open rows that are LEAF here and CONSEQUENCE there: H-3 (`r5count`), H-16 (`r20`), H-21 (`r17`), H-25 (`t5`),
H-38 (`t35`); a human should decide them, and this report keeps its classes. No open row is GLUE here and
PUBLISHED-FORM there (`serreRigidity3` was, and is now proved). Premises the reviews flag across rows: Lemma QP (its
existence half may be glue), the specialization of Deligne's PEL model to `R1fpProps` (an open human check, inherited by
`r1r2`, `r1b`, `y3Connected`, `x6ConicModel`), the definition of `stableFaltingsHeight` (group D), and a docstring error in
`QMDenZeroCM3` (order 10, not 30; corrected on main by e5e79f24).

## 5. Completeness check

### 5.1 Scenario A (compiled composite)

`python3 scratch/frontier/chain.py A` (from the repository root): 0 signature mismatches; 75 open nodes = the
26 + 19 + 20 + 1 = 66 fields of C4''s `OpenResearchLeaves2`, `OpenTextbookLeaves4`, `OpenAddedLeaves4`, `OpenGlue4`
(each expanded from the structure as read in `Leaves4.lean` @ 9dcf1ca8) plus the 9 TYZ and GZ hypotheses of C0: the
hypothesis list of the composite of two compiled theorems (C0, C4'). 69 of the 75 are projected (§4.6).

### 5.2 Scenario F (frontier)

`python3 scratch/frontier/chain.py F`: 0 signature mismatches over 72 theorem edges in the file (on the route:
C0, C4', the 14 H edges of §4.1 and the 3 TYZ edges B2-B4); 78 open nodes = the 72 of §0 + the 6 never-projected
fields of §4.6. Def texts: every C4' Prop that a route edge proves or reduces has the same def text in the proving file
(or, for W-kern files, the kernel definition) as in `Leaves4.lean` (11 of 11). Pairwise, all identical:
`SmoothFibreReduced` (smooth-fibre's kernel statement and vert-witness's); `ModelCoordinate`, `ModelComparison`,
`ShimuraGoodReduction` (model-glue's and vert-witness's); `Lemma321Five` (tyz-321) and `Thm35First` (tyz-35) against
`TYZChain.lean`; the CM leaf (the kernel's `ShimuraModFn.lean` and `TYZChain.lean`). The L-leaves are the kernel's
constants in both tyz-lcal and `TYZChain.lean`. The 17:35 route-T and kernel-copy checks pass against `Leaves4.lean`.

`python3 scratch/frontier/chain.py doc` compares the rows `Z-n`, `T-n`, `H-n` of this report with the scenario-F open
set minus the never-projected fields: VERIFIED equal (72 rows).

What the script does not check: that the edges compose in one Lean environment (the worlds differ; §6.2); argument
instantiation (for example `heckeVertWitness_of_leaves` takes `R1R2fp`, extracted from `r1r2` by `Classical.choice`);
and the defs that a Prop's def mentions (only the top-level def text is compared).

## 6. Integration state

### 6.1 Composites that exist
- **C4', leaf-fold4** (W-HDec, 9dcf1ca8, final): 26 + 19 + 20 + 1 fields; flat file, olean chain and the kernel
  conclusion compiled (REPORTED). On fork main since w49; the integrator's later edit e5e79f24 changes six docstring
  lines of `Leaves4.lean` (md5 b4c9f57e on main), no statement.
- **wip/one-proof** (3d527a1c, the integrator's): `ZInQ.OneProof.frozenTarget` states scenario A as one library theorem
  with C4''s four bundles and `TopChain.lean`'s 7 TYZ hypotheses (leaf-fold4's olean chain as `ZInQKernel/OneProof/H/`).
  wip/one-proof-tyz (1a7aa829, running) adds cm-bridge's chain as `OneProof/TYZBridge`; wip/op-dedupe (a2de2112)
  removes root-namespace duplicates.
- **leaf-fold5** (5121acdc, running): drafts parts for av-b2, the kernel transports and vert-witness/model-glue, that is,
  the H edges of §4.1.
- TYZ, each compiled on its own branch: cm-bridge's B1 (on main since w48); tyz-lcal's `tyzThm35ReadingA_of_three_leaves`
  (A1 without `TYZLcalOne`); tyz-321's `tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First` (B1 without
  `Lemma321Five`); tyz-35's `tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm33_lemma321Five` (B1 with T-11). No file
  combines B2-B4 yet.
- Superseded: C4 (assemble-port 92a27877), leaf-fold3 (68 Props), av-b2's `sixContactMin_of_openB2` and curves-g's
  `sixContactMin_of_openG` (single-file variants of leaf-fold3), g0-assemble3, cpts-transport, linked-ram, lt-goodred,
  linked-frob, hom-unify, leaf-fold2.

### 6.2 What folding scenario F into C4' needs
The 14 H edges of §4.1. The W-kern edges (AVB1, NeronC, CurvesG, SmoothFibre) are kernel modules on main whose defs
match leaf-fold4's text, so the definitional transport leaf-fold4 used for Zariski, spread-out and T40 should apply
(SPECULATIVE until compiled). av-b2's edges compile over leaf-fold3's olean chain, whose definitions C4' keeps.
vert-witness and model-glue are scratch files that restate hecke-rest's statements verbatim. leaf-fold5 is doing this
fold. On the TYZ side, one file needs B1 with B2, B3 and B4.

### 6.3 The library theorem
`ZInQ.OneProof.frozenTarget` is scenario A in the library, with `TopChain.lean`'s 7 TYZ hypotheses (A3 of §3.1). With
one-proof-tyz's TYZ bridge, C0's TYZ hypotheses can replace them, and with B2-B4 the five of §3.2; with leaf-fold5's
assembly the H bundles shrink to the rows of §4.

## 7. Findings

**Refresh r2 (2026-11-14).**

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

## 8. Tasks (snapshot 2026-11-14 00:05 PST; heads in `scratch/frontier/refs.txt`)

Finished, with results used in r2: leaf-fold4 (9dcf1ca8), vert-witness (9314d508), smooth-fibre (82abd02c), model-glue
(c6231df7), av-b1 (as merged; 02ae2421 is an unchecked snapshot), av-b2 (ffbd299a), curves-g (0fefa215), neron-c
(6bea04f0), tyz-lcal (61d0b14e), tyz-35 (a8101726), tyz-321 (521eacc0). Finished, read, not folded: leaf-review-a
(25f988f8) and leaf-review-b (3cc85b82) (§4.7), tyz-318 (94b05c87) and shimura-modfn (6bc73469) (§7 item 4),
stab-clash (78b9171f; duplicate Contrib declarations removed, `AllContrib.lean`; no Prop changes). cm-bridge is as at
17:35 (ed50dc33). Earlier finished tasks: the 17:35 report.

Running: leaf-fold5 (5121acdc; folds §4.1), sqrt2-glue (3f3b95c1; T-4's glue `SqrtTwoNotInHHprime`), ss-exponent
(37486c07; started from tyz-318), and the integrator's one-proof-tyz (1a7aa829) and op-dedupe (a2de2112).

gz-statements (Contrib modules `ZInQKernel/Contrib/GZStatements/{Weak,Level,Compat,Hensel}.lean` on its branch) proves
that the narrower `ZInQ.GZStatements.FHNonvanishingCd` and `GrossZagierHeegnerCd` (restricted to `C_d`, `d ≡ 5 mod 8`,
`D < −4`) are implied by Z-1, Z-2 and still give `ZInQ.FrozenTarget`
(`frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`); they could replace Z-1, Z-2
(both remain GLUE). Not adopted here (not compiled together with `TYZChain.lean`).

Fork main 67c2daf9 (integration w52) is merged into this branch; results used above that are on main are cited by their
task branches.
