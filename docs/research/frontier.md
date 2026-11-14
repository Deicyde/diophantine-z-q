# frontier: every open Prop on the path to `ZInQ.FrozenTarget`

Task frontier, 2026-11-13; refresh r2 and r3, 2026-11-14 (text checks only, no Lean run). Base of r3: integration
w54 (d5d43efc), on wip/frontier-r3. Branch snapshot: the commits in `scratch/frontier/refs.txt` (r3 section, read
02:30 PST). Lean: `scratch/frontier/TYZChain.lean`, `TopChain.lean`
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

**The list.** If every proof and reduction that the branches had compiled by 2026-11-14 02:30 PST is folded in
(scenario F, §5), the open Props on the path to `ZInQ.FrozenTarget` are **70: 17 LEAF and 53 GLUE** in the strict
count. If consequences of one theorem count as leaves, they are 41 LEAF and 29 GLUE.

| premise | open Props | strict LEAF | strict GLUE | lenient LEAF | lenient GLUE | table |
|---|---|---|---|---|---|---|
| GZ, `Literature.GrossZagier` | 2 | 0 | 2 | 0 | 2 | §2.2 |
| TYZ, `Literature.TYZThm35ReadingA` | 4 | 1 | 3 | 1 | 3 | §3.2 |
| H, `SixContactMin`: research-level bundle fields | 21 | 4 | 17 | 13 | 8 | §4.2 |
| H: textbook bundle fields | 8 | 1 | 7 | 8 | 0 | §4.3 |
| H: fields that were glue in C4 | 9 | 0 | 9 | 6 | 3 | §4.4 |
| H: Props introduced by reductions | 26 | 11 | 15 | 13 | 13 | §4.5 |
| **total** | **70** | **17** | **53** | **41** | **29** | |

By form: 17 published form, 24 consequences of one theorem, 27 composites, 2 project glue (`r1b`'s comparison for the
chosen triple, H-20, and the tame-quotient coordinate, H-84).

**Since r2 (72 rows; 23 LEAF and 49 GLUE under r2's classes).** Proved: `Lemma318Literal` (T-4; tyz-318 from
`SqrtTwoNotInHHprime`, which sqrt2-glue proves outright; ss-exponent proved the supersingular exponent it used) and
`GammaStarGen` (H-58, leafq-check, a finite descent). Replaced by smaller Props (leafq-check): `CMDescends` (H-47) by
Shimura–Taniyama `STQM` (H-86) with bundle fields already open; `ValenceBoundGammaStar` (H-48) by the valence formula
(H-87); `QMHauptmodul` (H-45) by `QMHauptmodulBase3` (H-88). Reclassified by the ruling above: H-3, H-16, H-21, H-25
and H-38, LEAF in r2, are consequences of one theorem (leaf-review-a/b), so GLUE in the strict count. The TYZ premise
now comes from the kernel's `TYZChain` (§3.1): four Props, everything else proved.

**The 70 names** (L = LEAF in both counts; c = consequence of one theorem, LEAF only in the lenient count; all others
GLUE; details in the tables):
- GZ: `ZInQ.GZDecomp.FHNonvanishing`; `ZInQ.GZDecomp.GrossZagierHeegner`.
- TYZ: `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` (L); `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2`; `ZInQ.Contrib.TYZGenus.Shimura.ShimuraReciprocityModFn`; `ZInQ.Contrib.TYZGenus.TYZ35.TYZThm33Pinned`.
- H: `LeafAdopt.R1R2fpRep`; `PkgI1.ThetaModularity` (c); `LeafQM.AV.R5fpCount` (c); `PkgI2.RaynaudCriterion` (c); `PkgI2.NeronOggShafarevich` (L); `PkgI3.FaltingsSemisimple` (L); `PkgI3.FaltingsTate` (L); `ZInQ.Contrib.R10.DeRhamComparisonHT`; `PkgI4.PanBerger`; `PkgI4.EigenformHT` (c); `DeligneSerreConseq`; `LeafModCurves.R16_EichlerShimuraJ1'`; `ZInQ.LeafPush2.R18_Javanpeykar` (c); `ZInQ.DefFaltings.R19_GaudronRemond` (L); `ZInQ.DefFaltings.R20_FaltingsLemma5` (c); `ZInQ.DefFaltings.R21_Bost` (c); `ZInQ.LeafPush2.R22_Pazuki` (c); `ZInQ.DefFaltings.StableHeightFinite`; `∀ h, G0Split.FibreQM.R1bFamily …`; `LadicCond.CarayolR17'` (c); `G0Galois.R14Det`; `PkgI2.ReductionTorsionBijective` (c); `PkgI2.TorsionStructure` (c); `∀ p, PkgI4.T23_FontaineClosure p` (c); `EigenformTwist` (c); `PkgI3.QMDichotomyYu` (c); `LeafModCurves.JacobianExists ℚ` (L); `ZInQ.LeafPush2.UniformizationExists` (c); `ZInQ.RLeaf.X0Transitive` (c); `FS5NoCM.CMOptimalEmbedding` (c); `X6Kummer.X6ConicModel` (c); `HSyn.G0Split.ThetaPt.ThetaRatiosAlgebraic`; `HSyn.G0Split.FibreQM.QMClassNumberOne` (c); `G0Galois.SenTwist` (c); `G0Galois.FiniteImageHT`; `WeilPairing.T09_SymmIsogenyExists` (c); `WeilPairing.IsogenyQuasiInverse` (c); `HomUnify.HomLatticeCorr`; `TSHecke.Y3Connected`; `QMAutCard`; `ALFixedPoints`; `ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii` (L); `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` (L); `ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii` (L); `ZariskiConn.ZariskiConnectedness` (L); `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` (L); `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` (L); `ZInQ.Contrib.AVB1.PoincareComplement` (L); `ZInQ.Contrib.AVB1.ImageFactorization`; `ZInQ.Contrib.AVB1.SimpleSurjIsogeny`; `AVB2.T11bExists` (L); `ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj` (L); `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` (L); `ZInQ.Contrib.CurvesG.DimJacobianEqGenus`; `ZInQ.Contrib.CurvesG.GenusX1Field`; `ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ` (L); `ZInQ.Contrib.CurvesG.NormalCurveSmoothQ`; `ZInQ.Contrib.CurvesG.GeomConnectedOfConstantFieldQ`; `VertWitness.ShimuraGoodReduction`; `ModelGlue.ModelCoordinateResidue`; `ModelGlue.CurveBijIso`; `STQM` (c); `ValenceFormulaGammaStar` (c); `QMHauptmodulBase3`.

Six more bundle fields (R1(d) reciprocity `r1rec`, R3, R5(ii), R7(b), R8, T10) are hypotheses of the compiled H
assembly but are never projected by its proof (§4.6); they are not on the list.

**How far this is checked.**
- **The top is compiled in the kernel.** atkin-li's `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner`
  (`Contrib/GZTheta/NewCMFinal.lean`, on main) derives `ZInQ.FrozenTarget` from H, reading A and the two GZ Props;
  tyz-chain's `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` (`Contrib/TYZChain/Main.lean`, w54) derives reading A
  from the four TYZ Props. Both are kernel modules built by the fork's CI chain (REPORTED by the integrator).
- **H, scenario A ("compiled").** leaf-fold5's `HDec.HSyn.sixContactMin_of_open5` (C4'', §1; flat file of the final
  text compiled in 1570 s, 349 axiom reports standard; REPORTED by its log) gives the kernel's `ZInQ.SixContactMin` from
  26 + 21 + 21 + 2 = 70 fields, 33 of them the kernel's own Props. With the top, scenario A has 76 open Props, 70
  projected (§5.1).
- **Scenario F ("frontier").** A plus the edges of §4.1: av-b1's split of the glue `SimpleImageIsogeny` and
  leafq-check's four results, each compiled on its branch per its log; `chain.py` checks signatures (0 mismatches). The
  leafq-check files import leaf-fold4's olean chain, so their Props are the chain's own constants. F is not compiled
  as one file; leaf-fold6 (running) is the next fold.

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

**Findings in brief** (§7): the classes now come with a form; five r2 LEAF rows are consequences of one theorem; the
TYZ side is four Props in the kernel; leaf-fold5 compiles r2's H list; leafq-check proves or shrinks four LEAF? fields.

## 1. The chain to `ZInQ.FrozenTarget`

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| C0 (r3) | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` with `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` | `Contrib/GZTheta/NewCMFinal.lean` @ main; `Contrib/TYZChain/Main.lean` @ w54 | `SixContactMin`, the 4 TYZ Props of §3.2, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (r1-r2: this task's `frozenTarget_of_open` in `scratch/frontier/TYZChain.lean`, with cm-bridge's 7 TYZ Props) |
| C1 | `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` | `Contrib/GZDecomp/Decomp.lean` @ main | `SixContactMin`, `TYZThm35ReadingA`, `HeckeThetaNewform`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (via `GrossZagierCd`; `HeckeContinuation`, `FunctionalEquation5` discharged by the proved `ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) |
| C2 | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` | `Contrib/GZTheta/NewCMFinal.lean` @ wip/atkin-li 6f77abb1 | `SixContactMin`, `TYZThm35ReadingA`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` |
| C3 | TYZ: §3.1 | | → `TYZThm35ReadingA` |
| C4'' | H: `HDec.HSyn.sixContactMin_of_open5 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves5) (l : OpenAddedLeaves5) (g : OpenGlue5)` | `scratch/leaf-fold5/Leaves5.lean` L121755 @ wip/leaf-fold5 5a7e03d1 (in w54; flat file of the final text, 121 783 lines, md5 5999e1db: `lake env lean` exit 0 in 1570 s, 0 errors, no `sorry`, 349 axiom reports all standard; olean chain and `Check5.lean` compiled; REPORTED by its log) | → `ZInQ.SixContactMin`; 26 + 21 + 21 + 2 fields (§4) |
| C4' (r2) | H: `HDec.HSyn.sixContactMin_of_open4 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4) (l : OpenAddedLeaves4) (g : OpenGlue4)` | `scratch/leaf-fold4/Leaves4.lean` L118447 @ wip/leaf-fold4 9dcf1ca8 (final; flat file, 118 478 lines, md5 6bbeb639: `lake env lean` exit 0 in 1048 s, 0 errors, no `sorry`, 326 axiom reports all standard; olean chain and `Check4.lean`, the kernel conclusion, compiled; REPORTED by its report and log); on fork main since w49 | → `ZInQ.SixContactMin`; 26 + 19 + 20 + 1 fields (§4) |
| C5 | assemble-port's `HDec.HSyn.sixContactMin_of_leaves5` (C4 of the 17:35 report; 26 + 17 + 27 fields) | `scratch/assemble-port/AssemblePort.lean` L116751 @ 92a27877 | C4' is its successor through leaf-fold2-4: the 17:35 scenario-F edges folded, `chartProper`, `chartQuasiFinite`, `hauptmodulUnique` proved, `periodMapGlue`, `abVarSpreadsOut` reduced to leaves, `DivisiblePoints` removed (leaf-fold4 §1.1); g0-assemble3's 46-glue-field `sixContactMin_of_leaves4` before it |
| C6 | H, per field: §4 | | each open field, or the Props it was reduced to |
| (C0 ∘ C4' in the library) | `ZInQ.OneProof.frozenTarget (r : HDec.HSyn.OpenResearchLeaves2) (t : HDec.HSyn.OpenTextbookLeaves4) (l : HDec.HSyn.OpenAddedLeaves4) (g : HDec.HSyn.OpenGlue4) (h11 …) (h1 …) (h29 …) (hcm …) (hs …) (h318 …) (hG …) (hL2 …) (hL3 …) : ZInQ.FrozenTarget` | `ZInQKernel/OneProof/Main.lean` @ wip/one-proof 3d527a1c (the integrator's; leaf-fold4's olean chain as library modules + `TopChain.lean`) | scenario A with `TopChain.lean`'s 7 TYZ hypotheses (A3 of §3.1); wip/one-proof-tyz (running) adds cm-bridge's chain |

The fork's registered headline (`ZInQKernel/MainLiterature.lean`) has five hypotheses; two are proved
(`ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) and C1 already uses them. C4' concludes the kernel's
`ZInQ.SixContactMin` (the flat file imports the kernel's definition; `Leaves.lean` is wrapped in `namespace HDec`), so
C0 and C4'' compose by modus ponens. Earlier compiled H assemblies (cpts-transport's 44-field and linked-ram's 45-field
`GluePieces5` in the W0 world, lt-goodred's and linked-frob's variants, leaf-fold2's `sixContactMin_of_open2`) are
superseded by C4, C4' and C4''. leaf-fold6 (running) is a further assembly.

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

### 3.2 Open Props (4: 1 LEAF, 3 GLUE in the strict count; 1 LEAF, 3 GLUE in the lenient count)


| # | Lean name | defined in | class | citation (UNVERIFIED unless marked) | last task; newest commit | running now | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| T-1 | `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` | `Contrib/TYZDecomp/Leaves.lean` @ main | **LEAF** (specialization: odd `m` only) | TYZ Thm 1.1, first assertion, L371–380 (read by nt-tyz) | tyz-decomp; main (tyz-lcal audit 11-13: faithful, not stronger) | no | published form: specialization of TYZ Thm 1.1 to odd `m` (tyz-lcal audit: faithful, not stronger) |
| T-3 | `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2` | same | GLUE (mod-2 composite of Lemma 2.9 and Prop. 2.3) | TYZ Lemma 2.9, L1062–1066 (journal Lemma 2.9 per the AI locator audit); Prop. 2.3, L580–586 | tyz-decomp; main (tyz-lcal audit 11-13: faithful, not stronger) | no | composite: TYZ Lemma 2.9 with Prop. 2.3, read mod 2 (tyz-lcal audit) |
| T-5 | `ZInQ.Contrib.TYZGenus.Shimura.ShimuraReciprocityModFn` | `ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean` @ tyz-cm 0ad48a7d | GLUE (Gross's form of Shimura reciprocity for values of `g ∈ ℚ(X₀(N))` at Heegner points, for all `N`, all regular `g`, all lattice pairs: stronger than any single printed statement) | Shimura 1971 Thm 5.4; Silverman, *Advanced topics* II.8.2; Gross 1984 §3; Cox Cor. 11.37 | tyz-cm (finished 11:42). shimura-modfn (6bc73469): correctly stated, a consequence of Shimura 1971 Thm 5.4 with the canonical model of `X₀(N)`, no stronger; its split `MainTheoremCMj` + `RatX0Rep` + the leaf at singular points is not folded (the report keeps the CM leaf) | no | composite: Shimura 1971 Thm 5.4 with the canonical model of `X₀(N)` (shimura-modfn) |
| T-11 | `ZInQ.Contrib.TYZGenus.TYZ35.TYZThm33Pinned` (for every `ℓ` with `IsTYZLcal ℓ`) | `scratch/tyz-35/Thm35.lean` L750 @ tyz-35 a8101726 | GLUE (lit-composite: TYZ Thm 3.3 with Lemma 3.14 for the pinned CM points; signs absorbed into `ε`, `z_n ∈ A(H'_n)` from Shimura reciprocity and Thm 3.6(1), `P_χ` independent of the lifts; HUMAN CHECK of `Φ`, `χ_{d₀,d₁}` and `h₂` against Period7.tex) | TYZ Thm 3.3 L1299–1311 (proof L1865–2023), Lemma 3.14 L1868, Lemma 3.15 L1919; its inputs Thm A.9 L3062–3077 (Yuan–Zhang–Zhang) and Gross–Zagier/Kolyvagin | tyz-35 (finished 23:19; replaces T-6 `Thm35First`) | no | composite: TYZ Thm 3.3 with Lemma 3.14 and the pinned conventions (tyz-35, docstring of `TYZThm33Pinned`) |


Retired rows: T-2 `TYZLcalOne` (proved, B2), T-4 `Lemma318Literal` (proved, B5), T-6 `Thm35First` (reduced to T-11, B4),
T-7 `Lemma321Five` (proved, B3).

## 4. H: `ZInQ.SixContactMin`

Base (r3): leaf-fold5's compiled C4'' (wip/leaf-fold5 5a7e03d1, in w54). It folds r2's H edges into one statement:
`HeckeVertWitness` from `ShimuraGoodReduction`, `CurveBijIso`, `r1r2`, `t5` and the glue `ModelCoordinateResidue`
(`SmoothFibreReduced` as the kernel's theorem), and the weaker group-B, C and G leaves of av-b1, av-b2, neron-c and
curves-g; T8 enters as Poincaré's complement theorem with av-b1's glue `SimpleImageIsogeny`. Bundles:
`OpenResearchLeaves5` (26), `OpenTextbookLeaves5` (21), `OpenAddedLeaves5` (21), `OpenGlue5` (2:
`modelCoordinateResidue`, `simpleImageIsogeny`). 33 fields are the kernel's own Props (leaf-fold5 §1.2). Worlds,
prefixes and def locations as in r2 (C4' and C4'' share leaf-fold4's chain); row numbers are kept, retired rows
listed, new rows from H-86.

### 4.1 What scenario F applies on top of C4'' (signatures VERIFIED by `chain.py`)

| field of C4'' (row) | now | theorem · branch@commit · file |
|---|---|---|
| `simpleImageIsogeny` (glue; not a row) | ⇐ H-73, H-74 | `ZInQ.Contrib.AVB1.simpleImageIsogeny_of_pieces` · av-b1 (main) · `Contrib/AVB1/Poincare.lean` |
| `gammaStarGen` (H-58) | proved | `gammaStarGen_proof` · leafq-check (w54) · `scratch/leafq-check/Fold.lean` (a finite descent on the `Γ*`-orbit of `i + j`) |
| `valenceBoundGammaStar` (H-48) | ⇐ H-87 | `valenceBound_of_formula` · same (the stabilizer bound `e_P ≤ 6` is proved) |
| `qmHauptmodul` (H-45) | ⇐ H-88, with H-2 (R4), `GammaStarGen` and `ValenceBoundGammaStar` | `qmHauptmodul_of_base2`, `base2_of_base3` · same |
| `cmDescends` (H-47) | ⇐ H-86, `T11b_Rigidity` (from H-75 by av-b2's edge), `TorsionDescends` (from T5, H-25), `r1r2` (H-1) | `cmDescends_of`, `torsionDescends_of_t5` · leafq-check · `scratch/leafq-check/CMDescendsGlue.lean` |

The r2 edges of the 17:35 and r2 reports are compiled inside C4'' and are off the route (they stay in `chain.py`).
Retired rows (r2 and r3): H-23, H-26, H-27, H-28, H-29, H-31, H-37, H-39, H-40, H-45, H-47, H-48, H-50, H-55, H-58, H-62.
Not applied: those listed in r2 (homlattice, t5-torsion's options, `divisiblePoints_of_posChar`, neron-c's local
reduction, `abVarSpreadsOut_of_ega_loc`).

### 4.2 Research-level bundle fields still open (21: 4 LEAF, 17 GLUE strict; 13 LEAF, 8 GLUE lenient)

| # | field : Lean name | leaf | class | citation | flags | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| H-1 | `r1r2 : LeafAdopt.R1R2fpRep` | R1(a,c,d), π₀, R2, R5 on X₆ | GLUE (assembled from several statements) | Shimura, Ann. of Math. 85 (1967), Main Thms I-II; Deligne, Sém. Bourbaki 389 (1971), Thm 4.21, Cor. 5.7, Ex. 5.8; Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1, Lemma 3.1; González–Rotger | Lemma P; pin clauses UNVERIFIED | pin-apply, leaf-adopt | composite: several statements on `X₆` (leaf-review-a §5.1) |
| H-2 | `r4 : PkgI1.ThetaModularity` | R4 | GLUE ("in the form stated"; signs checked numerically) | Igusa, Amer. J. Math. 84 (1962), 89 (1967) pp. 833-834, 848 | used on route F only (by `s8WeightExact_of`) | pkg-I1 | consequence of one theorem: Igusa's theta transformation formula (leaf-review-a §4.1) |
| H-3 | `r5count : LeafQM.AV.R5fpCount` | R5(i) | GLUE in the strict count (was LEAF; a consequence of one theorem, LEAF in the lenient count) (restated 2026-11-12 to the text the audit read: `2^b(R) h(R)`) | González–Rotger, J. Math. Soc. Japan 58 (2006), Prop. 5.6 | Lemma P | leaf-qm-fp, loc-fix | consequence of one theorem: González–Rotger Prop. 5.6 (leaf-review-a §5.6) |
| H-4 | `r6 : PkgI2.RaynaudCriterion` | R6 | GLUE (Galois-theoretic consequence) | SGA 7 I, Exp. IX, Prop. 4.7 with 3.5; Silverberg–Zarhin, AIF 45 (1995), Thm 3.5 | case `m = 3` UNVERIFIED | pkg-I2 | consequence of one theorem: SGA 7 IX 4.7 (leaf-review-b §2.2) |
| H-5 | `r7a : PkgI2.NeronOggShafarevich` | R7(a) | **LEAF** | Serre–Tate, Ann. of Math. 88 (1968), Thm 1 | UNVERIFIED | pkg-I2 | published form: Serre–Tate 1968 Thm 1 (leaf-review-b §2.2) |
| H-6 | `r9a : PkgI3.FaltingsSemisimple` | R9(a) | **LEAF** | Faltings, Invent. Math. 73 (1983), Satz 3 (erratum 75 (1984)) | UNVERIFIED | pkg-I3 | published form: Faltings 1983 (leaf-review-b §2.3) |
| H-7 | `r9b : PkgI3.FaltingsTate` | R9(b) | **LEAF** | Faltings 1983, Satz 4, Kor. 1 | UNVERIFIED | pkg-I3 | published form: Faltings 1983 (leaf-review-b §2.3) |
| H-8 | `r10 : ZInQ.Contrib.R10.DeRhamComparisonHT` (in C4 the copy `HDec.PkgI4.DeRhamComparisonHT`, same text) | R10 amended | GLUE (Tate-module form, a consequence with T10; plus the Hodge–Tate weight clause) | Scholze, Forum Math. Pi 1 (2013), Cor. 1.8, Thms 9.1, 9.3 + corrigendum; Tate 1967; Faltings 1988 | added clause UNVERIFIED | r10-amend | composite: Faltings 1988 and Tate 1967 with T10, plus the Hodge–Tate clause (leaf-review-b §2.4) |
| H-9 | `r11r12 : PkgI4.PanBerger` | R11 + R12 | GLUE (joint consequence of two theorems) | Berger, Invent. Math. 148 (2002), Thm 0.7; Pan, JAMS 35 (2022), Thm 1.0.4 | JAMS numbering UNVERIFIED | pkg-I4 | composite: Pan and Berger (leaf-review-b §2.4) |
| H-10 | `r13 : PkgI4.EigenformHT` | R13 | GLUE (consequence via Kato, after dualization) | Kato, Astérisque 295 (2004), §§9.2-9.4; Saito 1997 | | pkg-I4 | consequence of one theorem: Kato's theorem, after dualization (leaf-review-b §2.4) |
| H-12 | `r15 : DeligneSerreConseq` | R15 | GLUE (consequence, with T25, T18, T19) | Deligne–Serre, Ann. Sci. ÉNS 7 (1974), Thm 4.1, Lemma 3.2 | | hdec-faithful | composite: Deligne–Serre with T25, T18, T19, Chebotarev, Brauer–Nesbitt (leaf-review-a §3.2) |
| H-13 | `r16 : LeafModCurves.R16_EichlerShimuraJ1'` | R16 | GLUE (three suppliers) | Shimura 1971 Thm 7.9; Shimura 1973 Thm 1 | | leaf-modcurves | composite: Shimura 1973, Shimura 1971 §7.4, Diamond–Shurman (leaf-review-a §3.3) |
| H-14 | `r18 : ZInQ.LeafPush2.R18_Javanpeykar` | R18 | GLUE (consequence) | Javanpeykar, ANT 8 (2014), Thm 1.1.1 | H5 | leaf-push2 | consequence of one theorem: Javanpeykar (leaf-review-b §2.3) |
| H-15 | `r19 : ZInQ.DefFaltings.R19_GaudronRemond` | R19 | **LEAF** | Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4 (read by the audit) | H5; normalization-sensitive | def-faltings | published form: Gaudron–Rémond (leaf-review-b §2.3) |
| H-16 | `r20 : ZInQ.DefFaltings.R20_FaltingsLemma5` | R20 | GLUE in the strict count (was LEAF; a consequence of one theorem, LEAF in the lenient count) | Faltings 1983, Lemma 5; Raynaud, Astérisque 127, VII Cor. 2.1.3 | H5; UNVERIFIED | def-faltings | consequence of one theorem: Faltings 1983 Lemma 5 (leaf-review-b §2.3) |
| H-17 | `r21 : ZInQ.DefFaltings.R21_Bost` | R21 | GLUE (taken through Gaudron–Rémond §9; Bost's display unread) | Bost, Sém. Bourbaki 795 (1996) | H5 | def-faltings | consequence of one theorem: Bost's bound, taken through Gaudron–Rémond §9 (leaf-review-b §2.3) |
| H-18 | `r22 : ZInQ.LeafPush2.R22_Pazuki` | R22 | GLUE (hardened, not the literal corollary) | Pazuki, Bull. SMF 140 (2012), Cor. 1.3(2) | H5; Def. 2.6 identification UNVERIFIED | leaf-push2 | consequence of one theorem: Pazuki's corollary; the 17:35 note calls the Lean form hardened (leaf-review-b §2.3) |
| H-19 | `h5fin : ZInQ.DefFaltings.StableHeightFinite` | H5 (finiteness) | GLUE (theorem plus correctness of the definition) | Faltings 1983 §1; Deligne, Sém. Bourbaki 616; BLR 1.2/1, 1.4/3 | | h5-glue, g0-assemble2 | composite: the finiteness theorem plus the definition of the stable height (leaf-review-b §2.3, §3.1) |
| H-20 | `r1b : ∀ h, G0Split.FibreQM.R1bFamily …` (research field in C4) | R1(b) | GLUE (family form for the triple `Classical.choice` picks from `R1R2fpRep`) | Shimura 1967 Main Thm I; Deligne 389 §4.15 | | fibre-qm-period | project glue: the comparison for the triple chosen from `r1r2` is a project argument (leaf-review-a §5.2) |
| H-21 | `r17 : LadicCond.CarayolR17'` (research field in C4) | R17 | GLUE in the strict count (was LEAF; a consequence of one theorem, LEAF in the lenient count) | Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A) (read by the audit) | | def-ladic-cond | consequence of one theorem: Carayol 1986 Thm (A) (leaf-review-a §3.4) |
| H-22 | `r14 : G0Galois.R14Det` (in C4 the research field R14 is the form with the determinant clause; g0-assemble3 had the det-free `EigenformRepExists` plus a glue field `r14Det`) | R14 with det | GLUE (the reports call it LEAF, but its locators span three publications: Shimura 1971 Thm 7.14, Deligne 1971, Deligne–Serre 1974) | as H-11 | UNVERIFIED | g0-mod-galois | composite: Shimura 1971 Thm 7.14, Deligne 1971, Deligne–Serre 1974 (leaf-review-a §3.1) |

### 4.3 Textbook bundle fields still open (8: 1 LEAF, 7 GLUE strict; 8 LEAF, 0 GLUE lenient)

| # | field : Lean name | leaf | class | citation | tc-survey | last task; running | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| H-24 | `t4 : PkgI2.ReductionTorsionBijective` (leaf-fold4's field; `reductionTorsionBijective`, a glue-bundle field in C4; K Objects.lean:975) | T4 (I2-Red) | GLUE (consequence) | Serre–Tate 1968 §1 | NOT FOUND | pkg-I2; used by the frob chain (AlgFrobRed) | consequence of one theorem: Serre–Tate 1968 §1 (leaf-review-b §2.1) |
| H-25 | `t5 : PkgI2.TorsionStructure` (K Objects.lean:993) | T5 (I2-Tors) | GLUE in the strict count (was LEAF; a consequence of one theorem, LEAF in the lenient count) | Mumford, *Abelian varieties*, §4, §6 | WEAKER (g = 1) | pkg-I2 | consequence of one theorem: Mumford §4 Application 2 (leaf-review-b §2.1) |
| H-32 | `t23 : ∀ p, PkgI4.T23_FontaineClosure p` | T23 | GLUE (the form on `V^∨` is a consequence, not exact) | Fontaine, Astérisque 223, Thm 3.8 | NOT FOUND | leaf-push | consequence of one theorem: Fontaine, the form on `V^∨` (leaf-review-b §2.4) |
| H-33 | `t24 : EigenformTwist` (K ModCurves/C9.lean:373) | T24 | GLUE (consequence; atkin-li's `AtkinLiTwistNew` is a different Prop) | Shimura 1971 Prop. 3.64; Atkin–Li 1978 | WEAKER | hdec-faithful | consequence of one theorem: Shimura 1971 Prop. 3.64 (leaf-review-a §3.5) |
| H-35 | `t27 : PkgI3.QMDichotomyYu` | T27 | GLUE (locator audit: consequence of the refereed Thm 1.1) | Chia-Fu Yu, J. Pure Appl. Algebra (2013), Thm 1.1 (journal p. 907; arXiv:1210.1125); volume UNVERIFIED | NOT FOUND | loc-fix | consequence of one theorem: Yu 2013 Thm 1.1 (leaf-review-b §2.1) |
| H-36 | `t33 : LeafModCurves.JacobianExists ℚ` | T33 | **LEAF** (specialized to `P₀ ∈ X(K)`) | Weil 1948; Milne, *Jacobian varieties*, Thm 1.1, Prop. 6.1 | NOT FOUND | leaf-modcurves | published form: Weil; Milne, *Jacobian varieties* (leaf-review-b §2.5; curves-g §4) |
| H-38 | `t35 : ZInQ.LeafPush2.UniformizationExists` | T35 | GLUE in the strict count (was LEAF; a consequence of one theorem, LEAF in the lenient count) | Mumford §1 with GAGA (Serre 1956) | WEAKER | leaf-push2 | consequence of one theorem: Mumford §1 with GAGA (leaf-review-b §2.1) |
| H-41 | `x0Transitive : ZInQ.RLeaf.X0Transitive` (`ZInQKernel/Contrib/RLeaf/IgusaX0.lean:69` @ t40-igusa e9b071d6; for T40) | T40 | GLUE (Galois transitivity on cyclic subgroups of order `N`, derived from the irreducibility of the modular equation through `C ↦ j(E_j/C)`) | Lang, *Elliptic functions*, Ch. 5 §2 Thm 3; Cox Thm 11.18; Shimura 1971 §6.1 | no row | t40-igusa, t40-tate (both finished): `x1RationalCusp_of_x0_tateMuN`, `tateMuN` proved | consequence of one theorem: irreducibility of the modular equation (t40-igusa; not in the reviews) |


T6, T7, T8, T9, T11(b), T3, T41, T34 and T38 are proved or reduced (r2); their replacements are rows of §4.5.

### 4.4 Fields that were glue in C4, still open (in C4'' they are `OpenAddedLeaves5` fields, and `homLatticeCorr` is in `OpenTextbookLeaves5`) (9: 0 LEAF, 9 GLUE strict; 6 LEAF, 3 GLUE lenient)

| # | field : Lean name | def part | content; nearest published sources (UNVERIFIED) | report's label | last task; running | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-42 | `cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding` | a60_fs5 | CM points via optimal embeddings; "a consequence of the published statement" (Shimura 1967; Jordan 1981 §3; González–Rotger 2006 §5) | LEAF | fs5-nocm; no | consequence of one theorem: Shimura 1967, Jordan 1981 (leaf-review-a §5.7) |
| H-43 | `x6ConicModel : X6Kummer.X6ConicModel` | f20_x6kummer | `X₆` is the conic `Y² + 3X² + 3Z² = 0`, `π₆ = −16(X²+Z²)/(27Z²)`; consequence of the published model (Kurihara 1979; Elkies 1998 §3) | LEAF | x6-kummer; no | consequence of one theorem: Kurihara 1979, Elkies 1998 (leaf-review-a §5.11) |
| H-44 | `thetaRatiosAlgebraic : HSyn.G0Split.ThetaPt.ThetaRatiosAlgebraic` | 80_theta | theta-constant ratios at a period matrix are algebraic; composite (Shimura, Duke 43 (1976); Mumford, Tata II) | LEAF? | g0-thetapoint; no | composite: Shimura 1976, Mumford, Igusa (leaf-review-a §4.2) |
| H-46 | `qmClassNumberOne : HSyn.G0Split.FibreQM.QMClassNumberOne` | a80_fqm | Eichler class number one for `𝒪`, lattice form (Vignéras Cor. III.5.7; Voight 28.5.17) | LEAF | fibre-qm-period; no | consequence of one theorem: Eichler's class number one (leaf-review-a §5.9) |
| H-51 | `senTwist : G0Galois.SenTwist` | a35_g12det | HT weights of a twist shift by a constant; consequence (Sen 1980 §2) | LEAF | g12-det; no | consequence of one theorem: Sen 1980 §2 (leaf-review-b §2.4) |
| H-52 | `finiteImageHT : G0Galois.FiniteImageHT` | a35 | finite image ⇒ HT with weights 0; composite (Tate 1967 §3; Ax–Sen–Tate; Hilbert 90) | LEAF | g12-det; no | composite: Tate 1967, Ax–Sen–Tate, Hilbert 90 (leaf-review-b §2.4) |
| H-53 | `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` | a35 | symmetric isogeny to a dual; "existential in D, hence a consequence" (Mumford §§6, 8, 20, 23) | LEAF | weil-pairing; no | consequence of one theorem: Mumford §§6, 8, 20, 23 (leaf-review-b §2.1) |
| H-54 | `isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse` | a35 | `fg = [d]`, `gf = [d]` on `K̄`-points (Mumford §7-8) | LEAF | weil-pairing; no | consequence of one theorem: Mumford §7-8 (leaf-review-b §2.1) |
| H-69 | `homLatticeCorr : HomUnify.HomLatticeCorr` | z95b (hom-unify's `H20_bundle.lean` L184-224, verbatim) | `Hom(A_ℂ, B_ℂ) ≅ {M : MΛ_A ⊆ Λ_B}` through analytic uniformizations: lifting over any `K` with `σ : K → ℂ`, realization over `ℂ`; replaces T11(a), `homLinearLift`, `t11aRiemannHom`. homlattice: true and no stronger than the literature, but not printed in this form (uniformization, GAGA, algebraic ⇒ holomorphic, Birkenhake–Lange Prop. 1.2.1; Mumford §1, §3; Serre 1956) | LEAF (textbook) | hom-unify, folded by assemble-port 5f944406; no | composite: Birkenhake–Lange Prop. 1.2.1 with GAGA (leaf-review-b §2.1) |

### 4.5 Props introduced by reductions (H-59..H-67 and the r2 rows are fields of C4'') (26: 11 LEAF, 15 GLUE strict; 13 LEAF, 13 GLUE lenient)

| # | Lean name | def file @ commit | from field | class; content; sources (UNVERIFIED) | last task; running | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-59 | `TSHecke.Y3Connected` | ts-hecke `scratch/ts-hecke/TSHecke.lean` L6101 @ ff8e6731 | 28 | GLUE (π₀ of the Shimura curve, Deligne 389 §§2-3, Milne, plus an orbit computation; report: "leaf R1conn") | ts-hecke | composite: Deligne, Bourbaki 389, with an orbit computation (leaf-review-a §5.12) |
| H-61 | `QMAutCard` | hecke-rest `scratch/hecke-rest/HeckeRestAll.lean` L7369 @ 6c2c1d76 | 31 | GLUE (`|Aut(A,ι)|` = 4, 6, 2 by CM type: consequences of Shimura's classification, Ann. of Math. 78 (1963); Rotger, Crelle 561 (2003) §2) | hecke-rest (finished) | composite: Shimura 1963 with Rotger 2003 (leaf-review-a §5.13) |
| H-63 | `ALFixedPoints` | same, L7395 | 31 | GLUE (fixed points of the Atkin–Lehner involutions on `X₆` are CM by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]`; Rotger, Trans. AMS 356 (2004) §§2-4; Ogg 1983; plus an embedding check) | hecke-rest | composite: Ogg 1983, Rotger 2004 and an embedding check (leaf-review-a §5.14) |
| H-64 | `ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii` | spread-out `ZInQKernel/Contrib/SpreadOut/Spread.lean` L35 @ aa304ed7 | 44-46 (route T, via `AbVarSpreadsOut`) | **LEAF** (descent of schemes of finite presentation to a finite stage of a limit; EGA IV₃ 8.8.2(ii), Stacks 01ZM) | spread-out (finished 11:30) | published form: EGA IV₃ 8.8.2(ii) (spread-out) |
| H-65 | `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` | same, L49 | 44-46 | **LEAF** (descent of properness; EGA IV₃ 8.10.5(xii), Stacks 081F) | spread-out | published form: EGA IV₃ 8.10.5(xii) (spread-out) |
| H-66 | `ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii` | same, L61 | 44-46 | **LEAF** (descent of smoothness; EGA IV₄ 17.7.8(ii), Stacks 07RP) | spread-out | published form: EGA IV₄ 17.7.8(ii) (spread-out) |
| H-67 | `ZariskiConn.ZariskiConnectedness` | zariski-conn `ZInQKernel/Contrib/ZariskiConn/Basic.lean` L188 @ 3802f2bc | 44-46 (via `ProperSmoothGenConnected`) | **LEAF** (proper `f`, `Y` locally noetherian, `f_*𝒪_X = 𝒪_Y` ⇒ fibres geometrically connected; EGA III₁ 4.3.4, with non-emptiness from 4.3.1; flag: two numbered statements of one section) | zariski-conn (finished 12:06) | published form: EGA III₁ 4.3.1 and 4.3.4 (zariski-conn) |
| H-70 | `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` | `Contrib/AVB1/AlgClosed.lean` L38 @ main | t6 (H-26) | **LEAF** (T6 over algebraically closed fields only: Mumford, *Abelian varieties* §19 Thm 3 in Mumford's own setting; Milne 1986 Thm 12.5) | av-b1 | published form: Mumford §19 Thm 3 in its own setting (av-b1 §3.1) |
| H-71 | `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` | same, L51 | t7 (H-27) | **LEAF** (specialization: T7 over algebraically closed fields, without `deg P = 2g` and `P(n) = deg(n − φ)`; Mumford §19 Thm 4) | av-b1 | published form: specialization of Mumford §19 Thm 4 (av-b1 §3.2) |
| H-72 | `ZInQ.Contrib.AVB1.PoincareComplement` | `Contrib/AVB1/Poincare.lean` L42 @ main | t8 (H-28) | **LEAF** (Poincaré's complete reducibility in its complement form, weakened; Milne 1986 Prop. 12.1; Mumford §19 Thm 1) | av-b1 | published form: Milne 1986 Prop. 12.1, weakened (av-b1 §3.3) |
| H-73 | `ZInQ.Contrib.AVB1.ImageFactorization` | same, L56 | t8 (H-28) | GLUE (lit-composite of textbook facts on images of homomorphisms of abelian varieties; av-b1 §3.3) | av-b1 | composite: textbook facts on images of homomorphisms (av-b1 §3.3) |
| H-74 | `ZInQ.Contrib.AVB1.SimpleSurjIsogeny` | same, L71 | t8 (H-28) | GLUE (lit-composite: `(ker h)⁰_red` is an abelian subvariety, and simplicity; av-b1 §3.3) | av-b1 | composite: textbook facts on kernels and simplicity (av-b1 §3.3) |
| H-75 | `AVB2.T11bExists` | `scratch/av-b2/olean/AVB2Main.lean` L215 @ main | t11b (H-31) | **LEAF** (T11(b) with `∃!` weakened to `∃`; Conrad, Enseign. Math. 52 (2006) §3; Milne 1986 §20; uniqueness proved, `baseChange_map_injective`) | av-b2 | published form: T11(b) without uniqueness; T11(b) is in published form (av-b2 §1.1; leaf-review-b §2.1) |
| H-76 | `ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj` | `Contrib/NeronC/NMPInjective.lean` L91 @ main | t3 (H-23) | **LEAF** (the surjective half of the Néron mapping property of abelian schemes over a DVR, BLR §1.2 Prop. 8; the injective half is proved from Mathlib) | neron-c | published form: half of BLR §1.2 Prop. 8 (neron-c §1) |
| H-77 | `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` | `Contrib/NeronC/NeronGroup.lean` L82 @ main | t41 (H-39) | **LEAF** (a smooth separated quasi-compact model with the extension property and no group law: weaker than BLR §1.4 Thm 3; the group law, `gen` a homomorphism and uniqueness are proved) | neron-c | published form: BLR §1.4 Thm 3 without the group law (neron-c §1) |
| H-78 | `ZInQ.Contrib.CurvesG.DimJacobianEqGenus` | `Contrib/CurvesG/GenusSplit.lean` L46 @ main | t34 (H-37) | GLUE (lit-composite: `T₀J ≅ H¹(X, 𝒪_X)`, Milne, *Jacobian varieties* Prop. 2.1, with Serre duality; the genus is Mathlib-level `fieldGenus`) | curves-g | composite: Milne, *Jacobian varieties* Prop. 2.1 with Serre duality (curves-g §3) |
| H-79 | `ZInQ.Contrib.CurvesG.GenusX1Field` | same, L59 | t34 (H-37) | GLUE (lit-composite: Shimura's canonical model of `X₁(N)`, Shimura 1971 Prop. 6.9, the genus formula Prop. 1.40, base change of `H⁰(Ω¹)`) | curves-g | composite: Shimura 1971 Prop. 6.9 and Prop. 1.40 (curves-g §3) |
| H-80 | `ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ` | `Contrib/CurvesG/CurveSplit.lean` L27 @ main | t38 (H-40) | **LEAF** (the printed statement of the Stacks section on the normal model of a function field of one variable; curves-g §2) | curves-g | published form: the Stacks statement (curves-g §2) |
| H-81 | `ZInQ.Contrib.CurvesG.NormalCurveSmoothQ` | same, L38 | t38 (H-40) | GLUE (lit-composite of two printed facts: normal of dimension 1 is regular; regular and locally of finite type over a perfect field is smooth; Stacks 00TV, 0B8X) | curves-g | composite: two printed facts, Stacks 00TV and 0B8X (curves-g §2) |
| H-82 | `ZInQ.Contrib.CurvesG.GeomConnectedOfConstantFieldQ` | same, L48 | t38 (H-40) | GLUE (lit-composite of two printed facts: `Γ(X, 𝒪_X) = ℚ` from `ConstantFieldIsQ`, then Stacks 0FD1) | curves-g | composite: two printed facts, then Stacks 0FD1 (curves-g §2) |
| H-83 | `VertWitness.ShimuraGoodReduction` | `scratch/vert-witness/VertWitness.lean` L1477 @ main | heckeVertWitness (H-50) | GLUE (lit-composite: for each `p > 324` a smooth proper model over `ℤ_(p)` of the level-3 QM Shimura curve with the universal family, the moduli bijection on `ℚ̄`-points and the Hecke automorphisms; Morita 1981, Carayol 1986, Kottwitz 1992, Buzzard 1997; report: leaf; the level-3-at-`3 ∣ D` coverage needs a human check) | vert-witness | composite: Morita, Carayol, Kottwitz, Buzzard (vert-witness §3) |
| H-84 | `ModelGlue.ModelCoordinateResidue` | `scratch/model-glue/ModelGlue6.lean` L2232 @ c6231df7 | heckeVertWitness (H-50), through `ModelCoordinate` | GLUE (the coordinate of the tame quotient `𝒴/Γ' ≅ P¹_{ℤ_(p)}` with `CoordFibres` and transcendental reduction at the generic points of the special fibre) | model-glue (finished 23:03) | project glue: the coordinate of the tame quotient (model-glue) |
| H-85 | `ModelGlue.CurveBijIso` | same, L2954 | heckeVertWitness (H-50), through `ModelComparison` | GLUE (a morphism of proper smooth curves over `ℚ` that is bijective on `ℚ̄`-points is an isomorphism: degree equals the points of a general fibre, by generic smoothness; report: textbook leaf; a composite, not found printed in this form) | model-glue | composite: generic smoothness and a degree count (model-glue) |
| H-86 | `STQM` | `scratch/leafq-check/CMDescendsGlue.lean` L40 @ w54 | cmDescends (H-47) | GLUE in the strict count (Shimura–Taniyama in QM form: a QM abelian surface over `ℂ` with CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]` descends to a number field; docstring: a consequence of the published statement; LEAF in the lenient count) | leafq-check | consequence of one theorem: Shimura–Taniyama 1961 §12.4; Shimura 1998 §12.4 Prop. 26 (leafq-check, docstring of `STQM`) |
| H-87 | `ValenceFormulaGammaStar` | `scratch/leafq-check/Fold.lean` L487 @ w54 | valenceBoundGammaStar (H-48) | GLUE in the strict count (the valence formula for `Γ*` with signature `(0;2,4,6)`; docstring: a consequence of the published statements; LEAF in the lenient count) | leafq-check | consequence of one theorem: the valence formula, Shimura 1971 Prop. 2.16 and Thm 2.20; Rankin Thm 4.1.4 (leafq-check) |
| H-88 | `QMHauptmodulBase3` | `scratch/leafq-check/Fold.lean` L2441 @ w54 | qmHauptmodul (H-45) | GLUE (lit-composite: the Hauptmodul property of the theta quotient and its value `−16/27` at the order-2 point; the CM orbit clauses, `j_θ(√2 + i) = 0` and the pole at `i√3` are proved) | leafq-check | composite: what is left of `QMHauptmodul`: the Hauptmodul property and the value `−16/27` (leafq-check §1) |

Proved since the 17:35 snapshot and gone from the tables: `GammaStarGen` (leafq-check, r3), `SerreRigidity3` (av-b2), `T09_WeilPairing` (av-b2), and in the
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
r2 and r3: in leaf-fold4's and leaf-fold5's flat files `r1rec`, `r7b`, `r8` occur only as `f := r.f` in three structure literals, and `t10` only
there and in `T10_groupIso_of_tateDuality` (VERIFIED, grep of `Leaves4.lean` @ 9dcf1ca8 and `Leaves5.lean` @ 5a7e03d1); `r3` and `r5` were not
re-grepped (their names collide with local variables).

### 4.7 Statement reviews of the leaves (leaf-review-a, leaf-review-b, leafq-check)

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

## 5. Completeness check

### 5.1 Scenario A (compiled composite)

`python3 scratch/frontier/chain.py A` (from the repository root): 0 signature mismatches; 76 open nodes = the
26 + 21 + 21 + 2 = 70 fields of C4'''s four bundles (each expanded from the structure as read in `Leaves5.lean` @
5a7e03d1) plus the 4 TYZ and 2 GZ hypotheses of C0: the hypothesis list of the composite of three compiled theorems
(C2, T0 and C4''), 70 of them projected (§4.6).

### 5.2 Scenario F (frontier)

`python3 scratch/frontier/chain.py F`: 0 signature mismatches over 80 theorem edges in the file (on the route: C2,
T0, C4'', the split of `SimpleImageIsogeny` and leafq-check's six theorems); 76 open nodes = the 70 of §0 + the 6
never-projected fields. `T11b_Rigidity` (av-b2's edge, used by `cmDescends_of`) has the same def text as in
`Leaves5.lean`; leafq-check's Props are leaf-fold4's chain constants (its files `import TailK`), which C4'' keeps;
`SimpleImageIsogeny` is the kernel's constant in both. The pairwise and kernel-copy checks of r2 still pass.

`python3 scratch/frontier/chain.py doc` compares the rows `Z-n`, `T-n`, `H-n` with the scenario-F open set minus the
never-projected fields: VERIFIED equal (70 rows).

What the script does not check: that the edges compose in one Lean environment; argument instantiation (for example
`heckeVertWitness_of_leaves5` takes `R1R2fp`, extracted from `r1r2` by `Classical.choice`); and the defs that a Prop's def
mentions (only the top-level def text is compared).

## 6. Integration state

### 6.1 Composites that exist
- **C4'', leaf-fold5** (W-HDec, 5a7e03d1): 26 + 21 + 21 + 2 fields, 33 of them kernel constants; flat file of the final
  text, olean chain and kernel conclusion compiled (REPORTED). In w54.
- **The top in the kernel**: C2 (atkin-li, on main) and tyz-chain's T0 (w54). Scenario A is the composite of C2, T0
  and C4''.
- **wip/one-proof** (053cbad0, the integrator's): `ZInQ.OneProof.frozenTarget` with leaf-fold4's bundles and
  `TopChain.lean`'s 7 TYZ hypotheses as one library theorem; one-proof-tyz and op-dedupe continue it.
- **leaf-fold6** (3a628985, running) is the next H fold; mcr-glue (79463bbf) and av-glue are running glue tasks.
- Superseded: C4' (leaf-fold4), C4 (assemble-port), leaf-fold3, and the variants listed in r2; on the TYZ side, this
  task's `TYZChain.lean` (r1) and cm-bridge's B1 as the top.

### 6.2 What folding scenario F into C4'' needs
leafq-check's theorems are already over leaf-fold4's chain, which C4'' extends, so they should fold as they are
(SPECULATIVE until compiled); av-b1's split of `SimpleImageIsogeny` is a kernel theorem about the kernel's Prop.

### 6.3 The library theorem
`ZInQ.OneProof.frozenTarget` is scenario A of r2 in the library. With T0 (kernel) and C4'' it becomes scenario A of
this report.

## 7. Findings

**Refresh r3 (2026-11-14).**

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

## 8. Tasks (snapshot 2026-11-14 02:30 PST; heads in `scratch/frontier/refs.txt`)

Finished, with results used in r3: tyz-chain (377a2ec5), sqrt2-glue (84107b66), ss-exponent, tyz-318 (94b05c87),
tyz-321, shimura-modfn (6bc73469), leaf-fold5 (5a7e03d1), leafq-check. Used in r2 and compiled inside C4'': leaf-fold4,
vert-witness, smooth-fibre, model-glue, av-b1, av-b2, curves-g, neron-c, tyz-lcal, tyz-35. Read, not folded:
leaf-review-a, leaf-review-b, stab-clash.

Running: leaf-fold6 (3a628985), mcr-glue (79463bbf), av-glue, and the integrator's one-proof (053cbad0), one-proof-tyz
and op-dedupe.

gz-statements (Contrib modules `ZInQKernel/Contrib/GZStatements/{Weak,Level,Compat,Hensel}.lean` on its branch) proves
that the narrower `ZInQ.GZStatements.FHNonvanishingCd` and `GrossZagierHeegnerCd` (restricted to `C_d`, `d ≡ 5 mod 8`,
`D < −4`) are implied by Z-1, Z-2 and still give `ZInQ.FrozenTarget`
(`frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`); they could replace Z-1, Z-2
(both remain GLUE). Not adopted here (not compiled together with `TYZChain.lean`).

This branch is integration w54 (d5d43efc) plus this refresh.
