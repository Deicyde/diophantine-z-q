# frontier: every open Prop on the path to `ZInQ.FrozenTarget`

Task frontier, 2026-11-13. Base: fork main b7cdba8e (merged into wip/frontier). Branch snapshot: the commits in
`scratch/frontier/refs.txt` (refreshed 14:35 PST, §8). Lean: `scratch/frontier/TYZChain.lean`, `TopChain.lean` (compiled).
Mechanical check: `scratch/frontier/chain.py` (with `chainlib.py`), output `scratch/frontier/chain_out.txt`.
Results log: `scratch/frontier/log.md`. Working notes from three read-only survey agents:
`scratch/frontier/agent-{h-glue,h-leaves,tyz}.md`. No existing project file was edited. Model work; no human review.

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

**The list.** If every proof and reduction that today's branches compiled is folded in (scenario F, §5), the
open Props on the path to `ZInQ.FrozenTarget` are **72: 22 LEAF and 50 GLUE**:

| premise | open Props | LEAF | GLUE | table |
|---|---|---|---|---|
| GZ, `Literature.GrossZagier` | 2 | 0 | 2 | §2.2 |
| TYZ, `Literature.TYZThm35ReadingA` | 7 | 3 | 4 | §3.2 |
| H, `SixContactMin`: research-level bundle fields | 21 | 7 | 14 | §4.2 |
| H: textbook bundle fields | 18 | 8 | 10 | §4.3 |
| H: glue bundle fields still open | 13 | 0 | 13 | §4.4 |
| H: new Props from today's reductions | 11 | 4 | 7 | §4.5 |
| **total** | **72** | **22** | **50** | |

Six more bundle fields (R1(d) reciprocity `r1rec`, R3, R5(ii), R7(b), R8, T10) are hypotheses of the compiled H
assembly but are never projected by its proof (§4.6); they are not on the list, and removing them needs only a restated
bundle (not done).

**How far this is checked.**
- **GZ and TYZ: compiled.** `ZInQ.Frontier.frozenTarget_of_open` (this task, `scratch/frontier/TYZChain.lean`,
  compiled, standard axioms) derives `ZInQ.FrozenTarget` from H and exactly the 9 GZ and TYZ Props of the list.
- **H, scenario A ("compiled").** assemble-port's compiled `HDec.HSyn.sixContactMin_of_leaves5` (C4, flat file checked
  by its task) gives the kernel's `ZInQ.SixContactMin` from three bundles of 26 + 18 + 28 fields. With
  `frozenTarget_of_open` this is a composite of two compiled theorems that meet at the kernel Prop `ZInQ.SixContactMin`,
  so the composite is modus ponens. Its open set is 81 Props (§5.1). It differs from the list in 6 fields of C4
  (`piTwistC`, `sphereFactorAffine` proved; `homLinearLift`, `properSmoothGenConnected`, `t40`, `t26` reduced) and in
  the 3 Props those reductions add (`HoloHomLift`, `ZariskiConnectedness`, `X0Transitive`): 81 − 6 + 3 = 78 = the 72 of
  the list + the 6 never-projected fields.
- **H, scenario F ("frontier").** A plus 10 theorem edges on the route (55 edges are checked in all, including
  superseded ones), each a theorem that compiles on its branch per the branch's own log. The edges live in different
  Lean files ("worlds"), so **the composite of scenario F is not compiled anywhere**. `chain.py` checks every edge
  textually (each theorem's hypotheses and conclusion: 0 mismatches), checks that every proved or reduced H bundle Prop
  has the same `def` text in the proving file as in C4's file (6 of 6 identical, §5.2), and checks that the tables of
  this report list exactly the open set.

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

**Findings in brief** (§7): the brief's claim that every textbook leaf T1-T32 is proved is false (12 of the 35
textbook bundle fields are proved; T3-T11, T23, T24, T26, T27 are open); field `tateRamAtThree` of `GluePieces4`
is likely false as stated (linked-ram F1; route T below avoids it); STATUS.md and README still say
`HeckeThetaNewform` is only reduced; HEAD's h-decomposition §2.2 is stale (T14, T28, T36, T37 proved); g0-assemble3
§6 misses seven unused bundle fields.

## 1. The chain to `ZInQ.FrozenTarget`

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| C0 | `ZInQ.Frontier.frozenTarget_of_open` | `scratch/frontier/TYZChain.lean` (this task, compiled) | `SixContactMin`, the 7 TYZ Props of §3.2 (via T0), `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (fork-main-only variant: `frozenTarget_of_open_main`, `TopChain.lean`, with A3's 7 TYZ Props) |
| C1 | `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` | `Contrib/GZDecomp/Decomp.lean` @ main | `SixContactMin`, `TYZThm35ReadingA`, `HeckeThetaNewform`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (via `GrossZagierCd`; `HeckeContinuation`, `FunctionalEquation5` discharged by the proved `ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) |
| C2 | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` | `Contrib/GZTheta/NewCMFinal.lean` @ wip/atkin-li 6f77abb1 | `SixContactMin`, `TYZThm35ReadingA`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` |
| C3 | TYZ: §3.1 | | → `TYZThm35ReadingA` |
| C4 | H: `HDec.HSyn.sixContactMin_of_leaves5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (gp : GluePieces5)` | `scratch/assemble-port/AssemblePort.lean` L116639 @ wip/assemble-port cd031f5b (flat file, 116 699 lines: `lake env lean` exit 0 in 1123 s, 0 errors, no `sorry`, 290 axiom reports all standard; REPORTED by its log, `flat_summary.txt`) | → `ZInQ.SixContactMin`; 26 + 18 + 28 fields (§4) |
| C5 | g0-assemble3's `HSyn.sixContactMin_of_leaves4` (46 glue fields) | `scratch/g0-assemble3/G0Assemble3.lean` L90474 @ 357f5d9e | C4 is its port to the HDec world, with most glue fields proved or reduced, 3 moved to the research bundle, 1 bypassed by T35, and lt-local's route for the linked-Tate block (assemble-port's report) |
| C6 | H, per field: §4 | | each open field, or the Props it was reduced to |

The fork's registered headline (`ZInQKernel/MainLiterature.lean`) has five hypotheses; two are proved
(`ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) and C1 already uses them. C4 concludes the kernel's
`ZInQ.SixContactMin` (the flat file imports the kernel's definition; `Leaves.lean` is wrapped in `namespace HDec`), so
C0 and C4 compose by modus ponens. Earlier compiled H assemblies (cpts-transport's 44-field and linked-ram's 45-field
`GluePieces5` in the W0 world, lt-goodred's and linked-frob's variants, leaf-fold2's `sixContactMin_of_open2`) are
superseded by C4. leaf-fold3 (running) is a further assembly.

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
| **T0** (this task, compiled) | `ZInQ.Frontier.tyzThm35ReadingA_of_open` (= B1) | `scratch/frontier/TYZChain.lean` (B1 with the 11 tyz-cm modules, verbatim) | the 7 Props of §3.2 → `TYZThm35ReadingA` |

### 3.2 Open Props (7: 3 LEAF, 4 GLUE)

| # | Lean name | defined in | class | citation (UNVERIFIED unless marked) | last task; newest commit | running now |
|---|---|---|---|---|---|---|
| T-1 | `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` | `Contrib/TYZDecomp/Leaves.lean` @ main | **LEAF** (specialization: odd `m` only) | TYZ Thm 1.1, first assertion, L371–380 (read by nt-tyz) | tyz-decomp; main | no |
| T-2 | `ZInQ.Contrib.TYZDecomp.TYZLcalOne` | same | **LEAF** (a printed assertion, "Since 𝓛(1) = 1", L1082, not proved in TYZ; the value is Tunnell, Invent. Math. 72 (1983)) | TYZ L1082 (read by nt-tyz) | tyz-decomp; main | no |
| T-3 | `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2` | same | GLUE (mod-2 composite of Lemma 2.9 and Prop. 2.3) | TYZ Lemma 2.9, L1062–1066 (journal Lemma 2.9 per the AI locator audit); Prop. 2.3, L580–586 | tyz-decomp; main | no |
| T-4 | `ZInQ.Contrib.TYZGenus.Package.Lemma318Literal` (at `HHprime`) | `Contrib/TYZGenus/Package.lean:808` @ main | **LEAF** (specialization: only `⊆ A[(1+i)³]`, `n ≡ 5`; the identification of `HHprime` and `y² = x³ + 4x` with TYZ's `ℍ'_n`, `2y² = x³ + x` is AI-reviewed) | TYZ Lemma 3.18, L2230–2232 (read by nt-tyz, cm-bridge) | cm-points; main (owner: cm-numeric) | no |
| T-5 | `ZInQ.Contrib.TYZGenus.Shimura.ShimuraReciprocityModFn` | `ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean` @ tyz-cm 0ad48a7d | GLUE (Gross's form of Shimura reciprocity for values of `g ∈ ℚ(X₀(N))` at Heegner points, for all `N`, all regular `g`, all lattice pairs: stronger than any single printed statement) | Shimura 1971 Thm 5.4; Silverman, *Advanced topics* II.8.2; Gross 1984 §3; Cox Cor. 11.37 | tyz-cm (finished 11:42) | no |
| T-6 | `ZInQ.Contrib.TYZGenus.Package.Thm35First` (at `CMBridge.tyzZ`, for every `ℓ` with `IsTYZLcal ℓ`) | `Package.lean:289` @ main; `tyzZ` in `Bridge.lean` @ ed50dc33 | GLUE (composite: Thm 3.3 ε-part, recursion, Thm 3.5 first assertion; the `z_n` translation is AI-derived, tyz-t1 §3.1; Thm 3.3's constant rests on a computation TYZ do not print, L2014–2015) | TYZ Thm 3.3 L1299–1311, L1320–1330, Thm 3.5 L1353–1356, L1295 | cm-numeric, cm-bridge | no |
| T-7 | `ZInQ.Contrib.TYZGenus.CMBridge.Lemma321Five` | `Bridge.lean` @ ed50dc33 (copy of cm-numeric's) | GLUE (consequence of Lemma 3.21(1) through the `z_n` translation) | TYZ Lemma 3.21(1), L2496–2512, L2547–2554 | cm-bridge | no |

`TopChain.lean` (fork main only) has instead T-1 to T-4 and three GLUE Props: `CM.CMFieldOfDefinition ringClassFieldD`,
`Package.TYZSigmaFixesZn` (TYZ Thm 3.6(1) / Cor. 3.9 via Shimura reciprocity) and the bundled
`∀ ℓ, IsTYZLcal ℓ → Package.GenusPointLeafCM ℓ`.

## 4. H: `ZInQ.SixContactMin`

Base: assemble-port's compiled C4 (wip/assemble-port cd031f5b). It folds, from today's branches, cpts-transport,
ts-kummer and kummer-comp (all seven pieces), lt-local (route T, with lg-kerwild and frob-contrib's `UnramRoots`), hodge-bc2, twist-descent, period-glue (S8, W8, QMTwist), ts-hecke, hecke-rest, lt-goodred,
linked-ram, linked-frob (with frob-trace, alg-frob-red, afr-absfrob, frob-pieces), spread-out and leaf-fold2's T35
transport. Worlds: **W-HDec** = `scratch/h-decomposition/Leaves.lean` in `namespace HDec` (assemble-port, leaf-fold,
leaf-fold2, leaf-fold3); **W0** = g0-assemble3's root-namespace copy; **W-fqm** = period-map's files; **W-kern** = files
that import `ZInQKernel.HDecomp.*` (prop-ts-glue/ts-*, the frob chain, lt-local, conj-pieces, zariski-conn, t5-torsion,
the Contrib textbook proofs). Def locations below are the HDec copies in `AssemblePort.lean` @ cd031f5b (the same text
as W0's `scratch/g0-assemble3/Leaves.lean` and parts); "K" gives the kernel copy under `ZInQKernel/HDecomp/`.

### 4.1 What scenario F applies on top of C4 (each VERIFIED by `chain.py`: signature, and def text identical to assemble-port's)

| field(s) of C4 | now | theorem · branch@commit · file | world |
|---|---|---|---|
| `t40 : X1Belyi.X1RationalCusp` | ⇐ `X0Transitive` | `ZInQ.RLeaf.x1RationalCusp_of_x0_tateMuN (X0Transitive) (TateMuN)` · t40-igusa e9b071d6 · `Contrib/RLeaf/T40.lean`; `ZInQ.RLeaf.tateMuN` proved · t40-tate 7ed2ca99 · `Contrib/RLeaf/TateCuspMuN.lean` | W-kern |
| `t26 : PkgI3.TateModuleFree` | ⇐ T5 | `TateFree.tateModuleFree_of_torsionStructure (hT : PkgI2.TorsionStructure)` · t5-torsion 58ac8d0b · `scratch/t5-torsion/Tate.lean` | W-kern |
| `piTwistC` | proved from bundle fields | `PeriodGlue.piTwistC_of` at the triple from `r1r2`, with `twistOrbitFinite_of' (R1heckeProps) (T5) (AutOInnerFinite)` and `fibreTransferC_proof` · period-glue 7e1531df · PiTwist.lean; `AutOInnerFinite` proved (`autOInnerFinite`, scratch/aut-o-finite, main) | W-fqm |
| `sphereFactorAffine` | proved | `PeriodGlue.sphereFactorAffine_proof` · period-glue 7e1531df · SFA.lean | W-fqm |
| `homLinearLift` | ⇐ `HoloHomLift` | `G0Galois.homLinearLift_of_holoHomLift (hL : HoloHomLift)` · conj-pieces 110ae272 · Holo.lean (homlattice 89a1fc02 gives instead `StrongUniformizationExists → GAGAMorphism → HomLatticeCorr`, two leaves) | W-kern |
| `properSmoothGenConnected` | ⇐ `ZariskiConnectedness` | `ZariskiConn.properSmoothGenConnected_of_zariskiConnectedness` · zariski-conn 3802f2bc · `Contrib/ZariskiConn/Basic.lean` | W-kern |

Already in C4 at cd031f5b, so not edges here: `kummerCompositum` (kummer-comp's `kummerCompositum_final`) and route T
(`LTLocal.linkedTateLocal_of_tateBridge35`, replacing linked-ram's `upperBreakBound`, `betaSignAtTwo`; `TateBridge35` from
frob-pieces with the EGA IV fields and `properSmoothGenConnected`).

Not applied: t5-torsion's `tate_surj_numberField` replaces the only main-chain use of `divisiblePoints` (a rewiring,
not a proof of the field); its `torsionStructure_of_degree` reduces T5 to `KernelDegree` (+ `MulUnramifiedPosChar`), a
leaf for a leaf.

### 4.2 Research-level bundle fields still open (21: 7 LEAF, 14 GLUE)

Locators as in h-decomposition §2.1 and locators.md (the AI locator audit). "Lemma P" = the polarization-type lemma folded
into the Shimura-curve leaves (rv-qm-polar; locators UNVERIFIED); "H5" = these leaves have content only together with
the finiteness of the stable Faltings height. None of the 22 is proved anywhere and none is in Tau Ceti (tc-survey §0);
no running task targets one. Last task / newest form: as given; every one is a field of C4's `OpenResearchLeaves2`
@ assemble-port cd031f5b.

| # | field : Lean name | leaf | class | citation | flags | last task |
|---|---|---|---|---|---|---|
| H-1 | `r1r2 : LeafAdopt.R1R2fpRep` | R1(a,c,d), π₀, R2, R5 on X₆ | GLUE (assembled from several statements) | Shimura, Ann. of Math. 85 (1967), Main Thms I-II; Deligne, Sém. Bourbaki 389 (1971), Thm 4.21, Cor. 5.7, Ex. 5.8; Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1, Lemma 3.1; González–Rotger | Lemma P; pin clauses UNVERIFIED | pin-apply, leaf-adopt |
| H-2 | `r4 : PkgI1.ThetaModularity` | R4 | GLUE ("in the form stated"; signs checked numerically) | Igusa, Amer. J. Math. 84 (1962), 89 (1967) pp. 833-834, 848 | used on route F only (by `s8WeightExact_of`) | pkg-I1 |
| H-3 | `r5count : LeafQM.AV.R5fpCount` | R5(i) | **LEAF** (restated 2026-11-12 to the text the audit read: `2^b(R) h(R)`) | González–Rotger, J. Math. Soc. Japan 58 (2006), Prop. 5.6 | Lemma P | leaf-qm-fp, loc-fix |
| H-4 | `r6 : PkgI2.RaynaudCriterion` | R6 | GLUE (Galois-theoretic consequence) | SGA 7 I, Exp. IX, Prop. 4.7 with 3.5; Silverberg–Zarhin, AIF 45 (1995), Thm 3.5 | case `m = 3` UNVERIFIED | pkg-I2 |
| H-5 | `r7a : PkgI2.NeronOggShafarevich` | R7(a) | **LEAF** | Serre–Tate, Ann. of Math. 88 (1968), Thm 1 | UNVERIFIED | pkg-I2 |
| H-6 | `r9a : PkgI3.FaltingsSemisimple` | R9(a) | **LEAF** | Faltings, Invent. Math. 73 (1983), Satz 3 (erratum 75 (1984)) | UNVERIFIED | pkg-I3 |
| H-7 | `r9b : PkgI3.FaltingsTate` | R9(b) | **LEAF** | Faltings 1983, Satz 4, Kor. 1 | UNVERIFIED | pkg-I3 |
| H-8 | `r10 : ZInQ.Contrib.R10.DeRhamComparisonHT` | R10 amended | GLUE (Tate-module form, a consequence with T10; plus the Hodge–Tate weight clause) | Scholze, Forum Math. Pi 1 (2013), Cor. 1.8, Thms 9.1, 9.3 + corrigendum; Tate 1967; Faltings 1988 | added clause UNVERIFIED | r10-amend |
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

### 4.3 Textbook bundle fields still open (18: 8 LEAF, 10 GLUE)

References as in h-decomposition §2.2 (that table's heading marks all of them UNVERIFIED; only T27 was audited). K =
kernel copy. tc-survey (wip/tc-survey 489f46bc §1): WEAKER = Tau Ceti proves a weaker case only.

| # | field : Lean name | leaf | class | citation | tc-survey | last task; running |
|---|---|---|---|---|---|---|
| H-23 | `neronMappingAbelianScheme : PkgI2.NeronMappingAbelianScheme` (a glue-bundle field in C4; K Objects.lean:937) | T3 (I2-NMP) | GLUE (consequence) | BLR §1.2 Prop. 8 | NOT FOUND | pkg-I2; used by the frob chain (AlgFrobRed) |
| H-24 | `reductionTorsionBijective : PkgI2.ReductionTorsionBijective` (a glue-bundle field in C4; K Objects.lean:975) | T4 (I2-Red) | GLUE (consequence) | Serre–Tate 1968 §1 | NOT FOUND | pkg-I2; used by the frob chain (AlgFrobRed) |
| H-25 | `t5 : PkgI2.TorsionStructure` (K Objects.lean:993) | T5 (I2-Tors) | **LEAF** | Mumford, *Abelian varieties*, §4, §6 | WEAKER (g = 1) | pkg-I2 |
| H-26 | `t6 : PkgI3.HomFreeFinite` (K Objects.lean:445) | T6 (I3.M1) | **LEAF** | Mumford §19 Thm 3 | NOT FOUND | pkg-I3 |
| H-27 | `t7 : PkgI3.CharPolyIndepOfEll` | T7 (I3.M2) | **LEAF** | Mumford §19 Thm 4 | NOT FOUND | pkg-I3 |
| H-28 | `t8 : PkgI3.PoincareReducibility` | T8 (I3.M3) | GLUE (over any `k` of characteristic 0; consequence) | Milne, *Abelian varieties* (Cornell–Silverman 1986), Prop. 12.1 | NOT FOUND | pkg-I3 |
| H-29 | `t9 : LeafPush.T09_WeilPairing` | T9 | GLUE (consequence; polarization hidden). Also derivable from H-37 + H-38 by `oldT9_of_symmIsogeny` up to a universe (bridge not compiled) | Mumford §§20, 23 | WEAKER | leaf-push, weil-pairing |
| H-30 | `t11a : ZInQ.LeafPush2.T11a_RiemannEnd` (K LeafPush2/T.lean:45) | T11(a) | **LEAF** | Mumford §§1-3; Birkenhake–Lange Prop. 1.2.1; Serre 1956 | WEAKER | leaf-push2 |
| H-31 | `t11b : ZInQ.LeafPush2.T11b_Rigidity` | T11(b) | **LEAF** | Conrad 2006 §3; Milne 1986 §20 | NOT FOUND | leaf-push2 |
| H-32 | `t23 : ∀ p, PkgI4.T23_FontaineClosure p` | T23 | GLUE (the form on `V^∨` is a consequence, not exact) | Fontaine, Astérisque 223, Thm 3.8 | NOT FOUND | leaf-push |
| H-33 | `t24 : EigenformTwist` (K ModCurves/C9.lean:373) | T24 | GLUE (consequence; atkin-li's `AtkinLiTwistNew` is a different Prop) | Shimura 1971 Prop. 3.64; Atkin–Li 1978 | WEAKER | hdec-faithful |
| H-35 | `t27 : PkgI3.QMDichotomyYu` | T27 | GLUE (locator audit: consequence of the refereed Thm 1.1) | Chia-Fu Yu, J. Pure Appl. Algebra (2013), Thm 1.1 (journal p. 907; arXiv:1210.1125); volume UNVERIFIED | NOT FOUND | loc-fix |
| H-36 | `t33 : LeafModCurves.JacobianExists ℚ` | T33 | **LEAF** (specialized to `P₀ ∈ X(K)`) | Weil 1948; Milne, *Jacobian varieties*, Thm 1.1, Prop. 6.1 | NOT FOUND | leaf-modcurves |
| H-37 | `t34 : LeafModCurves.DimJ1Genus` | T34 | GLUE (citation chain) | Shimura 1971 Prop. 1.40, §6.7; Milne 1986 | DIFFERENT | leaf-modcurves |
| H-38 | `t35 : ZInQ.LeafPush2.UniformizationExists` | T35 | **LEAF** | Mumford §1 with GAGA (Serre 1956) | WEAKER | leaf-push2 |
| H-39 | `t41 : ZInQ.H5Neron.NeronModelExists` | T41 (N1) | **LEAF** | BLR 1.2/1, 1.4/3 | no row | h5-neron (reduced further by tau-n1n2, neron-lg; not used here) |
| H-40 | `t38 : X1Belyi.CurveOfFunctionFieldQ` | T38 | GLUE (consequence) | Hartshorne I.6, II.6.7; Stacks, *Curves and function fields* | no row | x1-belyi |
| H-41 | `ZInQ.RLeaf.X0Transitive` (`ZInQKernel/Contrib/RLeaf/IgusaX0.lean:69` @ t40-igusa e9b071d6; for T40) | T40 | GLUE (Galois transitivity on cyclic subgroups of order `N`, derived from the irreducibility of the modular equation through `C ↦ j(E_j/C)`) | Lang, *Elliptic functions*, Ch. 5 §2 Thm 3; Cox Thm 11.18; Shimura 1971 §6.1 | no row | t40-igusa, t40-tate (both finished): `x1RationalCusp_of_x0_tateMuN`, `tateMuN` proved |

### 4.4 Glue bundle fields still open (13, all GLUE; def files are g0-assemble3 parts)

| # | field : Lean name | def part | content; nearest published sources (UNVERIFIED) | report's label | last task; running |
|---|---|---|---|---|---|
| H-42 | `cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding` | a60_fs5 | CM points via optimal embeddings; "a consequence of the published statement" (Shimura 1967; Jordan 1981 §3; González–Rotger 2006 §5) | LEAF | fs5-nocm; no |
| H-43 | `x6ConicModel : X6Kummer.X6ConicModel` | f20_x6kummer | `X₆` is the conic `Y² + 3X² + 3Z² = 0`, `π₆ = −16(X²+Z²)/(27Z²)`; consequence of the published model (Kurihara 1979; Elkies 1998 §3) | LEAF | x6-kummer; no |
| H-44 | `thetaRatiosAlgebraic : HSyn.G0Split.ThetaPt.ThetaRatiosAlgebraic` | 80_theta | theta-constant ratios at a period matrix are algebraic; composite (Shimura, Duke 43 (1976); Mumford, Tata II) | LEAF? | g0-thetapoint; no |
| H-45 | `qmHauptmodul : PkgI1.QMHauptmodul` | Leaves.lean L304 | the theta-quotient Hauptmodul of `Γ*`; "composite, not printed as one theorem" (Baba–Granath 2008; Lin–Yang 2020 Ex. 29; Igusa 1967) | LEAF? | pkg-I1; no |
| H-46 | `qmClassNumberOne : HSyn.G0Split.FibreQM.QMClassNumberOne` | a80_fqm | Eichler class number one for `𝒪`, lattice form (Vignéras Cor. III.5.7; Voight 28.5.17) | LEAF | fibre-qm-period; no |
| H-47 | `cmDescends : HSyn.G0Split.FibreQM.PeriodMapH.CMDescends` | e20_periodmap | CM points descend (Shimura–Taniyama 1961; Shimura 1967) | LEAF? | period-map; period-glue lists it (no commit since 10:27) |
| H-48 | `valenceBoundGammaStar : HSyn.G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar` | e20 | the valence formula for `Γ*` with signature (0;2,4,6) (Shimura 1971 §2.4; Rankin Thm 4.1.4) | LEAF | period-map; period-glue lists it |
| H-50 | `heckeVertWitness : HeckeRestNV.HeckeVertWitness` | hecke-rest `NoVert.lean` @ 6c2c1d76 | one unramified vertical prime for the Hecke cover; equivalent to g0-assemble3's `HeckeNoVertRam` (`heckeNoVertRam_of_witness`, converse proved); its content is good reduction of `Y₃` (Morita 1981, Carayol 1986) or h-b1's Lemma NV | GLUE | ts-hecke, hecke-rest (finished 12:07) |
| H-51 | `senTwist : G0Galois.SenTwist` | a35_g12det | HT weights of a twist shift by a constant; consequence (Sen 1980 §2) | LEAF | g12-det; no |
| H-52 | `finiteImageHT : G0Galois.FiniteImageHT` | a35 | finite image ⇒ HT with weights 0; composite (Tate 1967 §3; Ax–Sen–Tate; Hilbert 90) | LEAF | g12-det; no |
| H-53 | `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` | a35 | symmetric isogeny to a dual; "existential in D, hence a consequence" (Mumford §§6, 8, 20, 23) | LEAF | weil-pairing; no |
| H-54 | `isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse` | a35 | `fg = [d]`, `gf = [d]` on `K̄`-points (Mumford §7-8) | LEAF | weil-pairing; no |
| H-55 | `divisiblePoints : WeilPairing.DivisiblePoints` | a35 | `A(K̄)` divisible (Mumford §4 Appl. 2) | LEAF | weil-pairing; no |

(13 = H-42..H-55 without H-49; g0-assemble3's field `analyticUniformizationOfDim` is gone in C4 (it follows from T35).
Field 33 `twistDescent` and H-49 `kummerCompositum` are proved and not counted.)

### 4.5 New Props from today's reductions (11: 4 LEAF, 7 GLUE)

| # | Lean name | def file @ commit | from field | class; content; sources (UNVERIFIED) | last task; running |
|---|---|---|---|---|---|
| H-57 | `HSyn.G0Split.FibreQM.PeriodGlue.T11aRiemannHom` | period-glue `scratch/period-glue/QMTwist.lean` L29 @ 7e1531df | 12 | GLUE (Riemann's theorem for homomorphisms over ℂ; Birkenhake–Lange 1.2.1 + GAGA; report: textbook leaf) | period-glue (finished 12:05); homlattice (running) reduces T11(a)-type statements to analytic leaves |
| H-58 | `HSyn.G0Split.FibreQM.PeriodGlue.GammaStarGen` | `W8.lean` L415 @ 7e1531df | 16 | GLUE (generators of `Γ*` as explicit `Sp₄(ℤ)` matrices; Takeuchi 1977; report: leaf candidate, "flagged") | period-glue |
| H-59 | `TSHecke.Y3Connected` | ts-hecke `scratch/ts-hecke/TSHecke.lean` L6101 @ ff8e6731 | 28 | GLUE (π₀ of the Shimura curve, Deligne 389 §§2-3, Milne, plus an orbit computation; report: "leaf R1conn") | ts-hecke |
| H-60 | `G0Galois.HoloHomLift` | conj-pieces `scratch/conj-pieces/Holo.lean` L52 @ 110ae272 | 35 | GLUE (holomorphic homomorphisms of complex tori lift linearly; report: textbook leaf) | conj-pieces; hom-unify (finished) proposes the stronger `HomLatticeCorr`; homlattice running |
| H-61 | `QMAutCard` | hecke-rest `scratch/hecke-rest/HeckeRestAll.lean` L7369 @ 6c2c1d76 | 31 | GLUE (`|Aut(A,ι)|` = 4, 6, 2 by CM type: consequences of Shimura's classification, Ann. of Math. 78 (1963); Rotger, Crelle 561 (2003) §2) | hecke-rest (finished) |
| H-62 | `SerreRigidity3` | same, L7382 | 31 | GLUE (Serre's lemma at level 3, finite-order form; Serre, Sém. Cartan 13 (1960/61) exp. 17 appendix; Silverberg–Zarhin, JPAA 111 (1996); Mumford §21 Thm 5) | hecke-rest |
| H-63 | `ALFixedPoints` | same, L7395 | 31 | GLUE (fixed points of the Atkin–Lehner involutions on `X₆` are CM by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]`; Rotger, Trans. AMS 356 (2004) §§2-4; Ogg 1983; plus an embedding check) | hecke-rest |
| H-64 | `ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii` | spread-out `ZInQKernel/Contrib/SpreadOut/Spread.lean` L35 @ aa304ed7 | 44-46 (route T, via `AbVarSpreadsOut`) | **LEAF** (descent of schemes of finite presentation to a finite stage of a limit; EGA IV₃ 8.8.2(ii), Stacks 01ZM) | spread-out (finished 11:30) |
| H-65 | `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` | same, L49 | 44-46 | **LEAF** (descent of properness; EGA IV₃ 8.10.5(xii), Stacks 081F) | spread-out |
| H-66 | `ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii` | same, L61 | 44-46 | **LEAF** (descent of smoothness; EGA IV₄ 17.7.8(ii), Stacks 07RP) | spread-out |
| H-67 | `ZariskiConn.ZariskiConnectedness` | zariski-conn `ZInQKernel/Contrib/ZariskiConn/Basic.lean` L188 @ 3802f2bc | 44-46 (via `ProperSmoothGenConnected`) | **LEAF** (proper `f`, `Y` locally noetherian, `f_*𝒪_X = 𝒪_Y` ⇒ fibres geometrically connected; EGA III₁ 4.3.4, with non-emptiness from 4.3.1; flag: two numbered statements of one section) | zariski-conn (finished 12:06) |

Proved since the first snapshot and therefore gone from this table: `TwistOrbitFinite` (`twistOrbitFinite_of'` from
`R1heckeProps` of `r1r2`, T5 and `AutOInnerFinite`, proved in aut-o-finite) and `FibreTransferC`
(`fibreTransferC_proof`), `QMLatticeTwistAlg` (`qmTwistLattice_of'` uses Skolem–Noether, proved in the kernel), all
period-glue 7e1531df; `CurveNormChart`, `CurveChartInf` (hecke-rest, Mathlib only); `HeckeFibreSizes` (hecke-rest:
from T5, H-61, H-62, H-63); `AbVarSpreadsOut` (spread-out: from H-64..H-66); `ProperSmoothGenConnected` (zariski-conn:
from H-67).

### 4.6 Bundle fields never projected (not on the list)

`r1rec : LeafQM.AV.R1rec`, `r3 : ZInQ.LeafPush2.R03_LinYang`, `r5 : LeafQM.AV.R5fp`, `r7b : PkgI2.SerreTatePotentialGood`,
`r8 : PkgI2.GrothendieckMonodromy`, `t10 : T10Etale.T10_TateDuality`. VERIFIED (agent-h-leaves and my grep) for
g0-assemble3's flat file: they occur only in the structure literals that convert the bundles (and `t10` only in the
unused `HSyn.TextbookLeaves.t10_groupIso`); C4 converts its bundles to g0-assemble3's and uses the same consumers
(REPORTED by assemble-port's report; not re-grepped, its flat file has more conversions). assemble-port already deleted
the unused textbook fields T1, T3, T4 (as textbook fields), T16(b), T20, T21, T28, T29.

## 5. Completeness check

### 5.1 Scenario A (compiled composite)

`python3 scratch/frontier/chain.py A`: 0 signature mismatches; 81 open nodes = the 26 + 18 + 28 = 72 fields of C4's
`OpenResearchLeaves2`, `OpenTextbookLeaves2`, `GluePieces5` (every field expanded from the structure as read in
`AssemblePort.lean` @ cd031f5b) plus the 9 TYZ and GZ hypotheses of C0. This is exactly the hypothesis list of the
composite of two compiled theorems (C0, C4).

### 5.2 Scenario F (frontier)

`python3 scratch/frontier/chain.py F`: 0 signature mismatches over the 55 theorem edges in the file (12 of them on the
route, counting C0 and C4); 78 open nodes = the 72 of §0 + the 6 never-projected fields of §4.6. The def text of every C4 Prop that a route
edge proves or reduces is identical in the proving file and in `AssemblePort.lean` (6 of 6). For route T, the defs of
`LinkedTateLocal`, `G7Data` (with `[L:ℚ] ≤ D`), `FibreSimple` and `QMEndRank` in lt-local's `LtLocal4.lean` are identical
to C4's; `FibreSimple` is derived inside the assembly (`G0FibreSimple.fibreSimple_of_leaves` from bundle fields), so it
is not an open Prop. `TateBridge35` has the same text in frob-pieces' and lt-local's files, `G15Ram.UnramRoots` in
unram-roots' and lt-local's; and C4's defs of the leaves that W-kern files take as hypotheses (`TateModuleFree`,
`ReductionTorsionBijective`, `NeronMappingAbelianScheme`, `RaynaudCriterion`, `TorsionStructure`, `HomFreeFinite`,
`QMDichotomyYu`, `CharPolyIndepOfEll`) are identical to the kernel's `ZInQKernel/HDecomp/Objects.lean` (VERIFIED).

`python3 scratch/frontier/chain.py doc` compares the rows `Z-n`, `T-n`, `H-n` of this report with the scenario-F open
set minus the never-projected fields: VERIFIED equal (72 rows).

What the script does not check: that the edges compose in one Lean environment (the worlds differ; §6.3); argument
instantiation (for example `piTwistC_of` is applied at the triple chosen from `r1r2`, and `G15Ram.UnramRoots` at
`(2,5)` and `(2,3)`); and the defs that a Prop's def mentions (only the top-level def text is compared).

## 6. Integration state

### 6.1 Composites that exist
- **C4, assemble-port** (W-HDec, cd031f5b): 26 + 18 + 28 fields, flat file compiled (1123 s). Its docstring and report
  label the 28 glue fields "18 LEAF, 7 LEAF?, 3 GLUE"; under the strict rule of this report only the three EGA IV fields
  are LEAF (and `properSmoothGenConnected` reduces to the LEAF `ZariskiConnectedness`), the rest GLUE. Its later state
  5f944406 (14:17; olean-chain check standard axioms, no flat check yet) folds hom-unify: `HomUnify.HomLatticeCorr`
  replaces T11(a), `homLinearLift` and `t11aRiemannHom` (17 textbook + 27 glue fields). homlattice found
  `HomLatticeCorr` true but not printed in that form (four pieces: uniformization, GAGA, algebraic ⇒ holomorphic,
  Birkenhake–Lange 1.2.1), so it is GLUE; adopting it would trade H-30 (LEAF), H-57 and H-60 (GLUE) for one GLUE Prop.
- leaf-fold3 (W-HDec, f7951690, flat file compiled 1042 s): `HDec.HSyn.sixContactMin_of_open3` with 68 Props
  (26 + 20 + 16 + 6 glue); period-map's reductions not folded, so coarser than C4.
- Earlier, superseded: g0-assemble3 (W0, 46 glue fields); cpts-transport (W0, 44); linked-ram (W0, 45); lt-goodred,
  linked-frob, hom-unify variants; leaf-fold2 (W-HDec, older base). leaf-fold3 (running) is a further W-HDec assembly.
- Area composites: `propTSAll_of_heckeRest` (Prop. TS from T2, `R1R2fp`, `MobiusGlue`, `SNSpecialize` (proved) and
  H-50, H-59, H-61..H-63); `LTLocal.linkedTateLocal_of_tateBridge35`; `FrobPiecesGood.tateBridge35_of_neron_nmp`;
  `ZariskiConnGlue.tateBridge35_of_neron_zariski_nmp`; `ZInQ.SpreadOutFull.tateBridge35_of_ega_nmp`.

### 6.2 What folding scenario F into C4 needs
Six fields (§4.1). `piTwistC`, `sphereFactorAffine` are W-fqm proofs (paste; assemble-port already pasted period-glue's
S8/W8/QMTwist parts); `homLinearLift`, `properSmoothGenConnected`, `t26`, `t40` are W-kern proofs whose def texts match
C4's (§5.2), to be re-copied as assemble-port did for the other W-kern files. leaf-fold3 reports that
`Contrib/RLeaf/T40.lean` cannot be imported next to the chain's Tau Ceti modules (a duplicate
`Units.val_mul_zpow_natCast_mul` from Tau Ceti's Backport copy), so `t40` needs a copy, not an import.

## 7. Findings

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

## 8. Tasks (snapshot 14:35 PST; heads in `scratch/frontier/refs.txt`)

Finished, with results used above: tyz-cm (0ad48a7d), cm-bridge (ed50dc33), t40-tate (7ed2ca99), t40-igusa (e9b071d6),
twist-descent, ts-kummer (1bbe3543), kummer-comp (423d6b7c), hecke-rest (6c2c1d76), period-glue (7e1531df), spread-out
(aa304ed7), zariski-conn (3802f2bc), t5-torsion (58ac8d0b), lt-local, assemble-port's flat check (cd031f5b), leaf-fold3
(f7951690). Finished, used through C4 or not on the route: linked-frob, linked-ram, hom-unify, homlattice (89a1fc02;
`HomLatticeCorr` ⇐ `StrongUniformizationExists` + `GAGAMorphism`), kerwild-fix (f596943a; an every-ℓ `LocalGlue` in
Glazer's normalization, still needing `EndRank4` and `AlgFrobRed`), frobchain-contrib, heightbc-contrib, mobius-contrib,
dim-contrib, infra-hodge, gz-statements (85d344bc; see below).

Running: assemble-port (5f944406, folding hom-unify; §6.1). No other task on this host has committed since 13:20.

gz-statements (Contrib modules `ZInQKernel/Contrib/GZStatements/{Weak,Level,Compat,Hensel}.lean` on its branch) proves
that the narrower `ZInQ.GZStatements.FHNonvanishingCd` and `GrossZagierHeegnerCd` (restricted to `C_d`, `d ≡ 5 mod 8`,
`D < −4`) are implied by Z-1, Z-2 and still give `ZInQ.FrozenTarget`
(`frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`); they could replace Z-1, Z-2
(both remain GLUE). Not adopted here (not compiled together with `TYZChain.lean`).

Fork main moved to 8ec80711 (integration w47, which includes this branch's early commits) after this task's one merge of
b7cdba8e; it was not merged again (the brief allows one merge). Results used above that are on main are cited by their
task branches.
