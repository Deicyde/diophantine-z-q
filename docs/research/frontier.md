# frontier: every open Prop on the path to `ZInQ.FrozenTarget`

Task frontier, 2026-11-13. Base: fork main b7cdba8e (merged into wip/frontier). Branch snapshot: the commits in
`scratch/frontier/refs.txt` (read 11:06 PST), refreshed in §8. Lean: `scratch/frontier/TYZChain.lean`, `TopChain.lean` (compiled).
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
open Props on the path to `ZInQ.FrozenTarget` are **79: 19 LEAF and 60 GLUE**:

| premise | open Props | LEAF | GLUE | table |
|---|---|---|---|---|
| GZ, `Literature.GrossZagier` | 2 | 0 | 2 | §2.2 |
| TYZ, `Literature.TYZThm35ReadingA` | 10 | 3 | 7 | §3.2 |
| H, `SixContactMin`: research-level bundle fields | 22 | 7 | 15 | §4.2 |
| H: textbook bundle fields | 19 | 9 | 10 | §4.3 |
| H: glue bundle fields still open | 14 | 0 | 14 | §4.4 |
| H: new Props from today's reductions | 12 | 0 | 12 | §4.5 |
| **total** | **79** | **19** | **60** | |

Ten more bundle fields (R1(d) reciprocity `r1rec`, R3, R5(ii), R7(b), R8, T1, T10, T16(b), T29(a), T29(b)) are
hypotheses of the compiled H assembly but are never projected by its proof (§4.6); they are not on the list, and
removing them needs only a restated bundle (not done).

**How far this is checked.**
- **GZ and TYZ: compiled.** `ZInQ.Frontier.frozenTarget_of_open` (this task, `scratch/frontier/TYZChain.lean`,
  compiled, standard axioms) derives `ZInQ.FrozenTarget` from H and exactly the 12 GZ and TYZ Props of the list.
- **H, scenario A ("compiled").** cpts-transport's compiled `HSyn.sixContactMin_of_leaves5` gives the kernel's
  `ZInQ.SixContactMin` from three bundles (24 + 35 + 44 fields). With `frozenTarget_of_open` this is a composite of
  two compiled theorems that meet at the kernel Prop `ZInQ.SixContactMin` (cpts-transport's file imports the kernel's
  definition), so the composite is modus ponens. Its open set is 115 Props (§5.1).
- **H, scenario F ("frontier").** A plus 55 theorem edges (and 8 textual ones: data extracted from a bundle field,
  the split of `x1`), each a theorem that compiles on its branch per the branch's own log. The edges live in different
  Lean files ("worlds"), so **the composite of scenario F is not compiled anywhere**. `chain.py` checks every edge
  textually (each theorem's hypotheses and conclusion: 0 mismatches) and checks that every proved or reduced H bundle
  Prop has the same `def` text in the proving file as in the assembly (all identical, §5.2), and that the tables of
  this report list exactly the open set. Folding the edges into one file is mechanical copying in most cases (§6.3),
  but it is not done.

**Declarations proved by this task.** All compile with `lake env lean` (exit 0, no `sorry`), and `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for each (VERIFIED; outputs `scratch/frontier/TYZChain_out.txt`,
`TopChain_out.txt`).

```lean
-- scratch/frontier/TYZChain.lean: tyz-cm's ShimuraRecip … ShimuraMain (66d92d11) and cm-bridge's Bridge.lean
-- (68d27814), verbatim minus imports (build_tyz.py), then:
theorem ZInQ.GZTheta.Frontier.newCM : ZInQ.GZTheta.NewCM     -- verbatim copy of atkin-li's proof
theorem ZInQ.GZTheta.Frontier.heckeThetaNewform : ZInQ.GZDecomp.HeckeThetaNewform
theorem ZInQ.Frontier.tyzThm35ReadingA_of_open (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hV : ZInQ.Contrib.TYZGenus.Shimura.CMValueRingClass)
    (hI : ZInQ.Contrib.TYZGenus.X0.EtaModelInvariant)
    (hsh : ZInQ.Contrib.TYZGenus.CMBridge.TYZSigmaShiftsF0) (h318 : Lemma318Literal HHprime)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ ZInQ.Contrib.TYZGenus.CMBridge.tyzZ)
    (h5 : ZInQ.Contrib.TYZGenus.CMBridge.Lemma321Five)
    (h36 : ZInQ.Contrib.TYZGenus.CMBridge.TYZThm36Seven) :
    ZInQ.Literature.TYZThm35ReadingA
theorem ZInQ.Frontier.frozenTarget_of_open (hH : ZInQ.SixContactMin) (h11 …) (h1 …) (h29 …) (hV …) (hI …)
    (hsh …) (h318 …) (h35 …) (h5 …) (h36 …)       -- the ten hypotheses above
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
| C0 | `ZInQ.Frontier.frozenTarget_of_open` | `scratch/frontier/TYZChain.lean` (this task, compiled) | `SixContactMin`, the 10 TYZ Props of §3.2 (via T0), `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (fork-main-only variant: `frozenTarget_of_open_main`, `TopChain.lean`, with A3's 7 TYZ Props) |
| C1 | `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` | `Contrib/GZDecomp/Decomp.lean` @ main | `SixContactMin`, `TYZThm35ReadingA`, `HeckeThetaNewform`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (via `GrossZagierCd`; `HeckeContinuation`, `FunctionalEquation5` discharged by the proved `ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) |
| C2 | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` | `Contrib/GZTheta/NewCMFinal.lean` @ wip/atkin-li 6f77abb1 | `SixContactMin`, `TYZThm35ReadingA`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` |
| C3 | TYZ: §3.1 | | → `TYZThm35ReadingA` |
| C4 | H: `HSyn.sixContactMin_of_leaves5 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces5)` | `scratch/cpts-transport/Bundle5.lean` L1351 @ wip/cpts-transport 93a1e33c (flat check standard axioms, REPORTED) | → `ZInQ.SixContactMin`; `GluePieces5` = g0-assemble3's `GluePieces4` minus `baseChangeClassUnique`, `cPtsTransport` (both proved there), 44 fields |
| C5 | `HSyn.sixContactMin_of_leaves4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4)` | `scratch/g0-assemble3/G0Assemble3.lean` L90474 @ wip/g0-assemble3 357f5d9e (flat file compiled, 220 standard axiom reports, REPORTED) | → `ZInQ.SixContactMin`; C4 goes through it (`gluePieces4_of_gluePieces5`) |
| C6 | H, per field: §4 | | each open field, or the Props it was reduced to |

The fork's registered headline (`ZInQKernel/MainLiterature.lean`) has five hypotheses; two are proved
(`ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) and C1 already uses them. Three newer H assemblies exist on
running branches, in other worlds, and are not used here (§6.2): assemble-port's `HDec.HSyn.sixContactMin_of_leaves5`
(41-field `GluePieces5`, HDec namespace), linked-ram's 45-field `GluePieces5` (lt-goodred folded), linked-frob's
`GluePieces4` variant.

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
| B1 (cm-bridge, scratch) | `ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_ringClassD_sigmaShiftsF0_lemma318_thm35First_lemma321Five_thm36Seven` | `scratch/cm-bridge/Bridge.lean` L2063 @ cm-bridge 68d27814 (built on cm-numeric's `tyzThm35ReadingA_of_pinnedLeaves`; proves `GenusFieldLeLni`, `IInHprime`, `CMFieldOfDefinition7` from the CM leaf, `BetaOnGenus7`, and `TYZSigmaFixesZn` from `TYZSigmaShiftsF0`) | h11, h1, h29, `CM.CMFieldOfDefinition ringClassFieldD`, `TYZSigmaShiftsF0`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → Thm35First ℓ tyzZ`, `Lemma321Five`, `TYZThm36Seven` |
| B2 (tyz-cm, kernel module) | `ZInQ.Contrib.TYZGenus.Shimura.cmFieldOfDefinition_of_cmValue` | `ZInQKernel/Contrib/TYZGenus/ShimuraMain.lean` @ tyz-cm 66d92d11 (`EtaCuspGrowth`, `XQExpRational`, `YQExpRational` proved there) | `Shimura.CMValueRingClass`, `X0.EtaModelInvariant` → `CM.CMFieldOfDefinition ringClassFieldD` |
| **T0** (this task, compiled) | `ZInQ.Frontier.tyzThm35ReadingA_of_open` = B1 ∘ B2 | `scratch/frontier/TYZChain.lean` (B1, B2 and the six modules B2 imports, verbatim) | the 10 Props of §3.2 → `TYZThm35ReadingA` |

Alternative route on tyz-cm (not used): `TYZSigmaFixesZn ⇐ ShimuraReciprocityPic ∧ X0.EtaModelFricke`
(`Shimura.tyzSigmaFixesZn_of`) and `ShimuraReciprocityPic ⇐ ShimuraReciprocityModFn ∧ X0.EtaModelInvariant`
(`shimuraReciprocityPic_of_modFn`); this replaces T-5 and T-7 below by `ShimuraReciprocityModFn` (stronger than any
single printed statement) and `X0.EtaModelFricke` (an eta identity, checked numerically).

### 3.2 Open Props (10: 3 LEAF, 7 GLUE)

| # | Lean name | defined in | class | citation (UNVERIFIED unless marked) | last task; newest commit | running now |
|---|---|---|---|---|---|---|
| T-1 | `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` | `Contrib/TYZDecomp/Leaves.lean` @ main | **LEAF** (specialization: odd `m` only) | TYZ Thm 1.1, first assertion, L371–380 (read by nt-tyz) | tyz-decomp; main | no |
| T-2 | `ZInQ.Contrib.TYZDecomp.TYZLcalOne` | same | **LEAF** (a printed assertion, "Since 𝓛(1) = 1", L1082, not proved in TYZ; the value is Tunnell, Invent. Math. 72 (1983)) | TYZ L1082 (read by nt-tyz) | tyz-decomp; main | no |
| T-3 | `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2` | same | GLUE (mod-2 composite of Lemma 2.9 and Prop. 2.3) | TYZ Lemma 2.9, L1062–1066 (journal Lemma 2.9 per the AI locator audit); Prop. 2.3, L580–586 | tyz-decomp; main | no |
| T-4 | `ZInQ.Contrib.TYZGenus.Package.Lemma318Literal` (at `HHprime`) | `Contrib/TYZGenus/Package.lean:808` @ main | **LEAF** (specialization: only `⊆ A[(1+i)³]`, `n ≡ 5`; the identification of `HHprime` and `y² = x³ + 4x` with TYZ's `ℍ'_n`, `2y² = x³ + x` is AI-reviewed) | TYZ Lemma 3.18, L2230–2232 (read by nt-tyz, cm-bridge) | cm-points; main (owner: cm-numeric) | no |
| T-5 | `ZInQ.Contrib.TYZGenus.Shimura.CMValueRingClass` | `ZInQKernel/Contrib/TYZGenus/ShimuraMain.lean` @ tyz-cm 66d92d11 | GLUE (lit-composite: for every `N`, every `g ∈ ℚ(X₀(N))` regular on `ℍ` and every Heegner form of discriminant `D`, `g(τ_Q) ∈ H_D`: the main theorem of CM with the rational structure of `ℚ(X₀(N))`; weaker than `ShimuraReciprocityModFn`) | Shimura 1971 Thm 5.7, Prop. 6.9 / Thm 6.23, §6.8; Gross 1984 §1–§3; Cox Thm 11.1 | tyz-cm | tyz-cm (report written 10:59) |
| T-6 | `ZInQ.Contrib.TYZGenus.X0.EtaModelInvariant` | `Contrib/TYZGenus/X0.lean:137` @ main | GLUE (`x`, `y` invariant under `Γ₀(32)`: an instance of the Ligozat/Newman/Gordon–Hughes criterion) | Ligozat, Bull. SMF Mém. 43 (1975); Ono, CBMS 102, Thm 1.64 | x0-32; main | no |
| T-7 | `ZInQ.Contrib.TYZGenus.CMBridge.TYZSigmaShiftsF0` | `scratch/cm-bridge/Bridge.lean` L393 @ 68d27814 | GLUE (consequence of TYZ's Hecke identity `Q^{1+2ϖ} = Q + τ(1)` and Shimura reciprocity at `P_n`; numerics for 5 values of `n`) | TYZ Prop. "heckeaction5"(1), L1488–1490 (number UNVERIFIED) | cm-numeric, cm-bridge | cm-bridge (report written 11:07) |
| T-8 | `ZInQ.Contrib.TYZGenus.Package.Thm35First` (at `CMBridge.tyzZ`, for every `ℓ` with `IsTYZLcal ℓ`) | `Package.lean:289` @ main; `tyzZ` in `Bridge.lean` @ 68d27814 | GLUE (composite: Thm 3.3 ε-part, recursion, Thm 3.5 first assertion; the `z_n` translation is AI-derived, tyz-t1 §3.1; Thm 3.3's constant rests on a computation TYZ do not print, L2014–2015) | TYZ Thm 3.3 L1299–1311, L1320–1330, Thm 3.5 L1353–1356, L1295 | cm-numeric, cm-bridge | no |
| T-9 | `ZInQ.Contrib.TYZGenus.CMBridge.Lemma321Five` | `Bridge.lean` L296 @ 68d27814 (copy of cm-numeric's) | GLUE (consequence of Lemma 3.21(1) through the `z_n` translation) | TYZ Lemma 3.21(1), L2496–2512, L2547–2554 | cm-bridge | no |
| T-10 | `ZInQ.Contrib.TYZGenus.CMBridge.TYZThm36Seven` | `Bridge.lean` L1072 @ 68d27814 | GLUE (a reading of Thm 3.6(3), Artin normalization converted; numerics 12/12) | TYZ Thm 3.6(3), L1424–1427; L1247–1250 | cm-bridge | no |

`TopChain.lean` (fork main only) has instead T-1 to T-4 and three GLUE Props: `CM.CMFieldOfDefinition ringClassFieldD`,
`Package.TYZSigmaFixesZn` (TYZ Thm 3.6(1) / Cor. 3.9 via Shimura reciprocity) and the bundled
`∀ ℓ, IsTYZLcal ℓ → Package.GenusPointLeafCM ℓ`.

## 4. H: `ZInQ.SixContactMin`

Worlds (agent-h-glue §0): **W0** = g0-assemble3's root-namespace copy of `Leaves.lean` (the same blob as g0-assemble2,
linked-tate, lt-goodred, cpts-transport, linked-ram, linked-frob); **W-fqm** = period-map's files (defs textually
identical to W0); **W-kern** = files that import `ZInQKernel.HDecomp.*` (hodge-bc2, prop-ts-glue/ts-*, the frob
chain, lt-local, conj-pieces, the Contrib textbook proofs); **W-HDec** = `scratch/h-decomposition/Leaves.lean` in
`namespace HDec` (leaf-fold, leaf-fold2, assemble-port). Def locations below are W0 (g0-assemble3 357f5d9e:
`scratch/g0-assemble3/Leaves.lean` for leaves, `parts/*.lean` for glue); "K" gives the kernel copy under
`ZInQKernel/HDecomp/`.

### 4.1 What scenario F applies to the H bundles (each VERIFIED by `chain.py`: signature, and def text identical to W0)

| field(s) | now | theorem · branch@commit · file | world |
|---|---|---|---|
| t2, t14a, t14b, t15, t16a, t17, t18, t20, t21, t25, t28, t31 | proved | `TBrauerPurityT2K.abhyankarDVR` (scratch/t-brauer-purity/T2Kernel.lean), `ZInQ.Contrib.T14.brauerHasse2C`, `brauerReciprocity2C`, `ZInQ.Contrib.BrauerT14T15.localH2CardC`, `ZInQ.Contrib.localKroneckerWeber`, `ZInQ.Contrib.KroneckerWeber.kroneckerWeberCyclic`, `ZInQ.Contrib.chebotarevExists`, `ZInQ.Contrib.Different.hilbertDifferentFormula`, `serreDifferentBound`, `T25.newformOfEigenform_leaf`, `T28.igusaClebschSeparation_proved`, `ZInQ.Contrib.T31.leafUnramified` · main | W-kern (W0 defs identical to the `HDecomp` defs) |
| x1 (T36-T40) | T36, T37 proved, T39 ⇐ T40 (all main); T40 ⇐ `IgusaTransitive` | `ZInQ.RLeaf.x1RationalCusp_of_igusaTransitive` · t40-tate c87d3b9b · `Contrib/RLeaf/TateCusp.lean` (with `tateCuspLaurent` proved); t40-igusa 5ee27509: `igusaTransitive_iff : IgusaTransitive ↔ X0Transitive ∧ TateMuN` | W-kern |
| 4 `hodgeBCInjective`, 5 `omegaBaseChange` | proved | `ZInQ.HeightBC.hodgeBCInjective`, `omegaBaseChange` · hodge-bc2 116dc2f2 | W-kern |
| 14 `s8Nonzero` | proved | `PeriodGlue.s8Nonzero_proof` · period-glue cbe9fe4c · S8.lean | W-fqm |
| 15 `sphereFactorAffine` | proved | `PeriodGlue.sphereFactorAffine_proof` · period-glue-b 80af6547 (a branch stopped at 10:12) · part_sphere.lean | W-fqm |
| 11 `piTwistC` | reduced | `PeriodGlue.piTwistC_of … (hT : TwistOrbitFinite Y Φ) (hF : FibreTransferC Y π)` at the triple from `r1r2` · period-glue cbe9fe4c · PiTwist.lean | W-fqm |
| 12 `qmTwistLattice` | reduced | `PeriodGlue.qmTwistLattice_of (hH : T11aRiemannHom) (hA : QMLatticeTwistAlg)` · cbe9fe4c · QMTwist.lean | W-fqm |
| 16 `s8WeightExact` | reduced | `PeriodGlue.s8WeightExact_of (hT : PkgI1.ThetaModularity) (hG : GammaStarGen)` · cbe9fe4c · W8.lean (uses the research leaf r4) | W-fqm |
| 19 `verticalResidueSeparable`, 20 `snSpecialize` | proved | `PropTSGlue.verticalResidueSeparable`, `PropTSGlue.snSpecialize` · ts-sn 1b8a3b3d (also prop-ts-glue 3d41b3d5) | W-kern |
| 22-27 (six Kummer pieces) | proved | `TsKummer.kummer{AbhyankarFinGlue, OtherBranchFin, VerticalFin, AbhyankarInfGlue, OtherBranchInf, VerticalInf}` · ts-kummer d9c06585 · KummerTS.lean | W-kern |
| 28 `heckeIrreducible` | reduced | `TSHecke.heckeIrreducible_of_connected (hC : Y3Connected)` · ts-hecke ff8e6731 | W-kern |
| 29 `heckeNormalizationIrr` | reduced | `TSHecke.heckeNormalizationIrr_of (CurveGaloisChart) (TorsionStructure)`, `curveGaloisChart_of (CurveNormChart)` · ff8e6731 | W-kern |
| 30 `heckeDegree` | proved from t5 | `TSHecke.heckeDegree_of_torsion` · ff8e6731 | W-kern |
| 31 `heckeBranch` | reduced | `TSHecke.heckeBranch_of' (R1R2fp) (CurveChartInf) (HeckeFibreSizes) (TorsionStructure)` · ff8e6731 | W-kern |
| 33 `twistDescent` | proved | `G0ModField.KernelField.twistDescent` · twist-descent fdd133f1 · Dev.lean (log: standard axioms) | W0 (KfGlue olean) |
| 35 `homLinearLift` | reduced | `G0Galois.homLinearLift_of_holoHomLift (hL : HoloHomLift)` · conj-pieces 110ae272 · Holo.lean | W-kern |
| 42 `goodRedTorsion` | proved | `LTGoodRed.goodRedTorsion` · lt-goodred 53ba766f · GoodRed.lean | W0 |
| 43 `qmEndRank` | proved from t6, t27 | `LTGoodRed.QM.qmEndRank_of_leaves` · 53ba766f | W0 |
| 44 `linkedFrob`, 45 `kernelFieldBreaks`, 46 `tateRamAtThree` | replaced (route T) | `LTLocal.linkedTateLocal_of_tateBridge35 (R6) (T5) (UnramRoots 2 5) (UnramRoots 2 3) (TateBridge35) (FibreSimple) (QMEndRank)` · lt-local 3d1b90b5 · LtLocal4.lean (over g0-assemble3's `G7Data`) gives g0-assemble2's `LinkedTateLocal`, from which g0-assemble3 needs none of 44-46; `UnramRoots` proved (`UnramRootsTask.unramRoots`, unram-roots b066d686); `TateBridge35` ⇐ `FrobPiecesGood.tateBridge35_of_neron_nmp (T26) (AbVarSpreadsOut) (ProperSmoothGenConnected) (T4) (T3)` · frob-pieces 60340bed | W-kern |
| 3 `analyticUniformizationOfDim` | bypassed | its only consumer `ProductMetrizationOfProductUnif` follows from T35 in W-HDec: `productMetrizationOfProductUnif_of_t35` · leaf-fold2 b38ee0c4 · parts/b20_fold.lean | W-HDec |
| 10 `baseChangeClassUnique`, 18 `cPtsTransport` | proved, folded | cpts-transport 93a1e33c (C4) | W0 |

### 4.2 Research-level bundle fields still open (22: 7 LEAF, 15 GLUE)

Locators as in h-decomposition §2.1 and locators.md (the AI locator audit). "Lemma P" = the polarization-type lemma folded
into the Shimura-curve leaves (rv-qm-polar; locators UNVERIFIED); "H5" = these leaves have content only together with
the finiteness of the stable Faltings height. None of the 22 is proved anywhere and none is in Tau Ceti (tc-survey §0);
no running task targets one. Last task / newest form: as given; every one is a field of `ResearchLeaves4` @ g0-assemble3
357f5d9e (or of `GluePieces5` for the last three).

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
| H-11 | `r14 : EigenformRepExists` | R14 | GLUE (consequence; chain partly UNVERIFIED) | Shimura 1971 Thm 7.14; Deligne, Sém. Bourbaki 355 (1971); Deligne–Serre 1974 | Eisenstein caveat | g0-mod-galois |
| H-12 | `r15 : DeligneSerreConseq` | R15 | GLUE (consequence, with T25, T18, T19) | Deligne–Serre, Ann. Sci. ÉNS 7 (1974), Thm 4.1, Lemma 3.2 | | hdec-faithful |
| H-13 | `r16 : LeafModCurves.R16_EichlerShimuraJ1'` | R16 | GLUE (three suppliers) | Shimura 1971 Thm 7.9; Shimura 1973 Thm 1 | | leaf-modcurves |
| H-14 | `r18 : ZInQ.LeafPush2.R18_Javanpeykar` | R18 | GLUE (consequence) | Javanpeykar, ANT 8 (2014), Thm 1.1.1 | H5 | leaf-push2 |
| H-15 | `r19 : ZInQ.DefFaltings.R19_GaudronRemond` | R19 | **LEAF** | Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4 (read by the audit) | H5; normalization-sensitive | def-faltings |
| H-16 | `r20 : ZInQ.DefFaltings.R20_FaltingsLemma5` | R20 | **LEAF** | Faltings 1983, Lemma 5; Raynaud, Astérisque 127, VII Cor. 2.1.3 | H5; UNVERIFIED | def-faltings |
| H-17 | `r21 : ZInQ.DefFaltings.R21_Bost` | R21 | GLUE (taken through Gaudron–Rémond §9; Bost's display unread) | Bost, Sém. Bourbaki 795 (1996) | H5 | def-faltings |
| H-18 | `r22 : ZInQ.LeafPush2.R22_Pazuki` | R22 | GLUE (hardened, not the literal corollary) | Pazuki, Bull. SMF 140 (2012), Cor. 1.3(2) | H5; Def. 2.6 identification UNVERIFIED | leaf-push2 |
| H-19 | `h5fin : ZInQ.DefFaltings.StableHeightFinite` | H5 (finiteness) | GLUE (theorem plus correctness of the definition) | Faltings 1983 §1; Deligne, Sém. Bourbaki 616; BLR 1.2/1, 1.4/3 | | h5-glue, g0-assemble2 |
| H-20 | `r1bFamily : ∀ h, HSyn.G0Split.FibreQM.R1bFamily …` (GluePieces5) | R1(b) | GLUE (family form for the triple `Classical.choice` picks from `R1R2fpRep`) | Shimura 1967 Main Thm I; Deligne 389 §4.15 | | fibre-qm-period; assemble-port moves it to the research bundle |
| H-21 | `carayolR17 : LadicCond.CarayolR17'` (GluePieces5) | R17 | **LEAF** | Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A) (read by the audit) | | def-ladic-cond |
| H-22 | `r14Det : G0Galois.R14Det` (GluePieces5) | R14 with det | GLUE (the reports call it LEAF, but its locators span three publications: Shimura 1971 Thm 7.14, Deligne 1971, Deligne–Serre 1974) | as H-11 | UNVERIFIED | g0-mod-galois |

### 4.3 Textbook bundle fields still open (19: 9 LEAF, 10 GLUE)

References as in h-decomposition §2.2 (that table's heading marks all of them UNVERIFIED; only T27 was audited). K =
kernel copy. tc-survey (wip/tc-survey 489f46bc §1): WEAKER = Tau Ceti proves a weaker case only.

| # | field : Lean name | leaf | class | citation | tc-survey | last task; running |
|---|---|---|---|---|---|---|
| H-23 | `t3 : PkgI2.NeronMappingAbelianScheme` (K Objects.lean:937) | T3 (I2-NMP) | GLUE (consequence) | BLR §1.2 Prop. 8 | NOT FOUND | pkg-I2; used on route T only |
| H-24 | `t4 : PkgI2.ReductionTorsionBijective` (K Objects.lean:975) | T4 (I2-Red) | GLUE (consequence) | Serre–Tate 1968 §1 | NOT FOUND | pkg-I2; route T only |
| H-25 | `t5 : PkgI2.TorsionStructure` (K Objects.lean:993) | T5 (I2-Tors) | **LEAF** | Mumford, *Abelian varieties*, §4, §6 | WEAKER (g = 1) | pkg-I2 |
| H-26 | `t6 : PkgI3.HomFreeFinite` (K Objects.lean:445) | T6 (I3.M1) | **LEAF** | Mumford §19 Thm 3 | NOT FOUND | pkg-I3 |
| H-27 | `t7 : PkgI3.CharPolyIndepOfEll` | T7 (I3.M2) | **LEAF** | Mumford §19 Thm 4 | NOT FOUND | pkg-I3 |
| H-28 | `t8 : PkgI3.PoincareReducibility` | T8 (I3.M3) | GLUE (over any `k` of characteristic 0; consequence) | Milne, *Abelian varieties* (Cornell–Silverman 1986), Prop. 12.1 | NOT FOUND | pkg-I3 |
| H-29 | `t9 : LeafPush.T09_WeilPairing` | T9 | GLUE (consequence; polarization hidden). Also derivable from H-37 + H-38 by `oldT9_of_symmIsogeny` up to a universe (bridge not compiled) | Mumford §§20, 23 | WEAKER | leaf-push, weil-pairing |
| H-30 | `t11a : ZInQ.LeafPush2.T11a_RiemannEnd` (K LeafPush2/T.lean:45) | T11(a) | **LEAF** | Mumford §§1-3; Birkenhake–Lange Prop. 1.2.1; Serre 1956 | WEAKER | leaf-push2 |
| H-31 | `t11b : ZInQ.LeafPush2.T11b_Rigidity` | T11(b) | **LEAF** | Conrad 2006 §3; Milne 1986 §20 | NOT FOUND | leaf-push2 |
| H-32 | `t23 : ∀ p, PkgI4.T23_FontaineClosure p` | T23 | GLUE (the form on `V^∨` is a consequence, not exact) | Fontaine, Astérisque 223, Thm 3.8 | NOT FOUND | leaf-push |
| H-33 | `t24 : EigenformTwist` (K ModCurves/C9.lean:373) | T24 | GLUE (consequence; atkin-li's `AtkinLiTwistNew` is a different Prop) | Shimura 1971 Prop. 3.64; Atkin–Li 1978 | WEAKER | hdec-faithful |
| H-34 | `t26 : PkgI3.TateModuleFree` | T26 (I3.M0) | **LEAF** | Mumford §§4, 18-19 | WEAKER | pkg-I3 |
| H-35 | `t27 : PkgI3.QMDichotomyYu` | T27 | GLUE (locator audit: consequence of the refereed Thm 1.1) | Chia-Fu Yu, J. Pure Appl. Algebra (2013), Thm 1.1 (journal p. 907; arXiv:1210.1125); volume UNVERIFIED | NOT FOUND | loc-fix |
| H-36 | `t33 : LeafModCurves.JacobianExists ℚ` | T33 | **LEAF** (specialized to `P₀ ∈ X(K)`) | Weil 1948; Milne, *Jacobian varieties*, Thm 1.1, Prop. 6.1 | NOT FOUND | leaf-modcurves |
| H-37 | `t34 : LeafModCurves.DimJ1Genus` | T34 | GLUE (citation chain) | Shimura 1971 Prop. 1.40, §6.7; Milne 1986 | DIFFERENT | leaf-modcurves |
| H-38 | `t35 : ZInQ.LeafPush2.UniformizationExists` | T35 | **LEAF** | Mumford §1 with GAGA (Serre 1956) | WEAKER | leaf-push2 |
| H-39 | `t41 : ZInQ.H5Neron.NeronModelExists` | T41 (N1) | **LEAF** | BLR 1.2/1, 1.4/3 | no row | h5-neron (reduced further by tau-n1n2, neron-lg; not used here) |
| H-40 | `X1Belyi.CurveOfFunctionFieldQ` (inside `x1`) | T38 | GLUE (consequence) | Hartshorne I.6, II.6.7; Stacks, *Curves and function fields* | no row | x1-belyi |
| H-41 | `ZInQ.RLeaf.IgusaTransitive` (`Contrib/RLeaf/X1RationalCusp.lean:123` @ main; for T40) | T40 | GLUE ("consequence of Igusa 1959") | Igusa 1959; Shimura 1971 §6.2 | no row | t40-igusa (`↔ X0Transitive ∧ TateMuN`); **t40-tate running on `TateMuN`** |

### 4.4 Glue bundle fields still open (14, all GLUE; def files are g0-assemble3 parts)

| # | field : Lean name | def part | content; nearest published sources (UNVERIFIED) | report's label | last task; running |
|---|---|---|---|---|---|
| H-42 | `cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding` | a60_fs5 | CM points via optimal embeddings; "a consequence of the published statement" (Shimura 1967; Jordan 1981 §3; González–Rotger 2006 §5) | LEAF | fs5-nocm; no |
| H-43 | `x6ConicModel : X6Kummer.X6ConicModel` | f20_x6kummer | `X₆` is the conic `Y² + 3X² + 3Z² = 0`, `π₆ = −16(X²+Z²)/(27Z²)`; consequence of the published model (Kurihara 1979; Elkies 1998 §3) | LEAF | x6-kummer; no |
| H-44 | `thetaRatiosAlgebraic : HSyn.G0Split.ThetaPt.ThetaRatiosAlgebraic` | 80_theta | theta-constant ratios at a period matrix are algebraic; composite (Shimura, Duke 43 (1976); Mumford, Tata II) | LEAF? | g0-thetapoint; no |
| H-45 | `qmHauptmodul : PkgI1.QMHauptmodul` | Leaves.lean L304 | the theta-quotient Hauptmodul of `Γ*`; "composite, not printed as one theorem" (Baba–Granath 2008; Lin–Yang 2020 Ex. 29; Igusa 1967) | LEAF? | pkg-I1; no |
| H-46 | `qmClassNumberOne : HSyn.G0Split.FibreQM.QMClassNumberOne` | a80_fqm | Eichler class number one for `𝒪`, lattice form (Vignéras Cor. III.5.7; Voight 28.5.17) | LEAF | fibre-qm-period; no |
| H-47 | `cmDescends : HSyn.G0Split.FibreQM.PeriodMapH.CMDescends` | e20_periodmap | CM points descend (Shimura–Taniyama 1961; Shimura 1967) | LEAF? | period-map; period-glue lists it (no commit since 10:27) |
| H-48 | `valenceBoundGammaStar : HSyn.G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar` | e20 | the valence formula for `Γ*` with signature (0;2,4,6) (Shimura 1971 §2.4; Rankin Thm 4.1.4) | LEAF | period-map; period-glue lists it |
| H-49 | `kummerCompositum : PropTSGlue.KummerCompositum` | e10_propts | Kummer step, compositum (project glue) | GLUE | ts-kummer; **ts-kummer running** (stage 4a at 11:01) |
| H-50 | `heckeNoVertRam : PropTSGlue.HeckeNoVertRam` | e10 | no vertical ramification of the Hecke cover (h-b1 Lemma NV) | GLUE | ts-hecke; **hecke-rest running** (reduced to one unramified vertical prime, 10:56) |
| H-51 | `senTwist : G0Galois.SenTwist` | a35_g12det | HT weights of a twist shift by a constant; consequence (Sen 1980 §2) | LEAF | g12-det; no |
| H-52 | `finiteImageHT : G0Galois.FiniteImageHT` | a35 | finite image ⇒ HT with weights 0; composite (Tate 1967 §3; Ax–Sen–Tate; Hilbert 90) | LEAF | g12-det; no |
| H-53 | `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` | a35 | symmetric isogeny to a dual; "existential in D, hence a consequence" (Mumford §§6, 8, 20, 23) | LEAF | weil-pairing; no |
| H-54 | `isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse` | a35 | `fg = [d]`, `gf = [d]` on `K̄`-points (Mumford §7-8) | LEAF | weil-pairing; no |
| H-55 | `divisiblePoints : WeilPairing.DivisiblePoints` | a35 | `A(K̄)` divisible (Mumford §4 Appl. 2) | LEAF | weil-pairing; no |
| H-56 | `analyticUniformizationOfDim : ZInQ.Metrization.AnalyticUniformizationOfDim` | e30_unifdims | uniformization with its dimension (Mumford §1, §4; GAGA); repeats T35 over def-faltings' `AbVar` | LEAF | unif-dims; bypassed by T35 in W-HDec (§4.1), so **not counted** in §0 |

(H-56 is listed for completeness: it stays a hypothesis in W0, where no bypass is written; the count of §0 uses the
W-HDec bypass. 14 = H-42..H-55. Field 33 `twistDescent` was proved at 11:04 and is not listed.)

### 4.5 New Props from today's reductions (12, all GLUE)

| # | Lean name | def file @ commit | from field | content; label in its report | running |
|---|---|---|---|---|---|
| H-57 | `HSyn.G0Split.FibreQM.PeriodGlue.TwistOrbitFinite` | period-glue `scratch/period-glue/PiTwist.lean` L36 @ cbe9fe4c | 11 | finiteness of the QM-twist orbit; glue | period-glue (idle since 10:27) |
| H-58 | `HSyn.G0Split.FibreQM.PeriodGlue.FibreTransferC` | PiTwist.lean L61 | 11 | fibre transfer over ℂ; glue (false without its built-in properness/smoothness hypotheses, which the def has) | same |
| H-59 | `HSyn.G0Split.FibreQM.PeriodGlue.T11aRiemannHom` | QMTwist.lean L29 | 12 | Riemann's theorem for homomorphisms (Birkenhake–Lange 1.2.1 + GAGA); "textbook leaf" | same |
| H-60 | `HSyn.G0Split.FibreQM.PeriodGlue.QMLatticeTwistAlg` | QMTwist.lean L59 | 12 | quaternion/lattice algebra; glue | same |
| H-61 | `HSyn.G0Split.FibreQM.PeriodGlue.GammaStarGen` | W8.lean L415 | 16 | generators of `Γ*` (Takeuchi 1977); "leaf candidate" | same; period-num (stopped) has the alternative `NormalizerDecomp` |
| H-62 | `TSHecke.Y3Connected` | ts-hecke `scratch/ts-hecke/TSHecke.lean` L6101 @ ff8e6731 | 28 | `Y₃` connected (π₀ of Shimura curves: Deligne 389 §§2-3; Milne) plus an orbit computation; "leaf R1conn" | hecke-rest (target unknown) |
| H-63 | `TSHecke.CurveNormChart` | L6469 | 29 | normalization charts (Hartshorne II.6) | hecke-rest |
| H-64 | `TSHecke.CurveChartInf` | L6565 | 31 | chart at ∞ | hecke-rest |
| H-65 | `TSHecke.HeckeFibreSizes` | L6591 | 31 | fibre sizes 144/36/24/72 (Baba–Granath §3.1) | hecke-rest |
| H-66 | `G0Galois.HoloHomLift` | conj-pieces `scratch/conj-pieces/Holo.lean` L52 @ 110ae272 | 35 | holomorphic homomorphisms of complex tori lift linearly; "textbook leaf" | hom-unify (replaces 35 by the stronger `ZInQ.HomUnify.HomLatticeCorr`) |
| H-67 | `FrobPiecesNeron.AbVarSpreadsOut` | frob-pieces `scratch/frob-pieces/FrobPiecesFull.lean` @ 60340bed (= neron-lg N1-g1) | 44-46 (route T) | an abelian variety over a number field spreads out to an abelian scheme over `𝓞_L[1/f]` (EGA IV₃ 8.8.2, 8.10.5, IV₄ 17.7.8); "glue / candidate leaf" | **spread-out running** (EGA IV descent, 11:06) |
| H-68 | `FrobPiecesNeron.ProperSmoothGenConnected` | same | 44-46 | Zariski's connectedness for the spread-out model (EGA III₁ 4.3; Hartshorne III 11.3); stated over `𝓞_L[1/f]`, not the printed form | no |

### 4.6 Bundle fields never projected (not on the list)

`r1rec : LeafQM.AV.R1rec`, `r3 : ZInQ.LeafPush2.R03_LinYang`, `r5 : LeafQM.AV.R5fp`, `r7b : PkgI2.SerreTatePotentialGood`,
`r8 : PkgI2.GrothendieckMonodromy`, `t1 : PkgI2.PurityBranchLocus`, `t10 : T10Etale.T10_TateDuality`,
`t16b : PkgI6.LocalReciprocityUpper`, `t29a`, `t29b` (`LeafPush.T29a_DivisionNormalizer`, `T29b_SplitNormalizer`).
VERIFIED by agent-h-leaves (grep of every projection in g0-assemble3's flat file): they occur only in structure literals
(and `t10` only in the unused `HSyn.TextbookLeaves.t10_groupIso`). g0-assemble3 §6 lists only the textbook ones minus
`t10`. On route F, `r4`, `t3`, `t4` become used (by `s8WeightExact_of` and route T).

## 5. Completeness check

### 5.1 Scenario A (compiled composite)

`python3 scratch/frontier/chain.py A`: 0 signature mismatches; 115 open nodes = the 24 + 35 + 44 = 103 fields of
`ResearchLeaves4`, `TextbookLeaves`, `GluePieces5` (every field expanded from the structure as read in the source) plus
the 12 TYZ and GZ hypotheses of C0. This is exactly the
hypothesis list of the composite of two compiled theorems (C0, C4).

### 5.2 Scenario F (frontier)

`python3 scratch/frontier/chain.py F`: 0 signature mismatches over 55 theorem edges; 89 open nodes = the 79 of §0 + the
10 never-projected fields of §4.6. The def text of every H bundle Prop that an edge proves or reduces is identical in
the proving file and in g0-assemble3's file (35 of 37 comparisons, including the 12 kernel textbook proofs against the
`ZInQKernel/HDecomp` defs); the other two have no def in the proving file (`TwistDescent` comes from kf-glue's `KfGlue`
olean; `analyticUniformizationOfDim` is bypassed, not proved). For route T, the defs of `LinkedTateLocal`, `G7Data` (with `[L:ℚ] ≤ D`), `FibreSimple` and
`QMEndRank` in lt-local's `LtLocal4.lean` are identical to g0-assemble3's; `FibreSimple` is derived inside g0-assemble3's
assembly (`G0FibreSimple.fibreSimple_of_leaves` from bundle fields), so it is not an open Prop. `TateBridge35` has the same text in frob-pieces' and lt-local's files, `G15Ram.UnramRoots` in
unram-roots' and lt-local's; and the W0 defs of the leaves that W-kern files take as hypotheses (`TateModuleFree`,
`ReductionTorsionBijective`, `NeronMappingAbelianScheme`, `RaynaudCriterion`, `TorsionStructure`, `HomFreeFinite`,
`QMDichotomyYu`, `CharPolyIndepOfEll`) are identical to the kernel's `ZInQKernel/HDecomp/Objects.lean` (VERIFIED).

`python3 scratch/frontier/chain.py doc` compares the rows `Z-n`, `T-n`, `H-n` of this report with the scenario-F open
set minus the never-projected fields: VERIFIED equal (79 rows), apart from H-56, which is listed for completeness and
bypassed.

What the script does not check: that the edges compose in one Lean environment (the worlds differ; §6.3); argument
instantiation (for example `piTwistC_of` is applied at the triple chosen from `r1r2`, and `G15Ram.UnramRoots` at
`(2,5)` and `(2,3)`); and the defs that a Prop's def mentions (only the top-level def text is compared).

## 6. Integration state

### 6.1 Composites that exist
- Compiled in W0: g0-assemble3 `sixContactMin_of_leaves4` (46 glue fields); cpts-transport `sixContactMin_of_leaves5` (44);
  lt-goodred `integ/` (a different 27-field `GluePieces4` over linked-tate's bundle); linked-ram `GluePieces5` (45
  fields, lt-goodred folded; REPORTED, 10:53).
- W-HDec: assemble-port `HDec.HSyn.sixContactMin_of_leaves5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2)
  (gp : GluePieces5)` (41 fields; TailD olean check standard axioms per its log; its docstring count "14 LEAF / 3 LEAF? /
  24 GLUE" is 11 / 3 / 27 by the field docstrings); leaf-fold2 `sixContactMin_of_open2` (older base).
- Area composites, not folded into any bundle: `PropTSGlue.propTSAll_final''`, `TsKummer.propTSAll_ts`,
  `TSHecke.propTSAll_of_tsHecke'` (combined, Prop. TS needs 6 open Props: H-49, H-50, H-62..H-65);
  `LTLocal.linkedTateLocal_of_tateBridge35`, `G8Tate.linkedTateDataD_of_frob`, `FrobPiecesGood.tateBridge35_of_neron_nmp`.

### 6.2 Newer assemblies on running branches
assemble-port (W-HDec, 41 fields), linked-ram (W0, 45 fields), linked-frob (W0, `GluePieces4` variant). None folds
hodge-bc2, ts-sn, ts-kummer, ts-hecke, period-glue, conj-pieces, lt-local, frob-pieces or twist-descent.

### 6.3 What folding scenario F needs
- W-fqm → W0: paste (defs textually identical; agent-h-glue Appendix A).
- W-kern → W0: re-copy the files (linked-frob's log: the two worlds cannot be imported together), as g0-assemble3 did
  for infra-stalks and prop-ts-glue. ts-hecke also carries copies of aut-o-finite, infra-smooth-dim and curve-glue
  that W0 already has (duplicate names).
- Kernel textbook proofs → W0: the def texts match (§5.2); leaf-fold did the same fold in W-HDec with `exact`.
- lt-goodred and linked-frob use g0-assemble2's `G7Data` (no `[L:ℚ] ≤ D`); 42 and 43 do not mention `G7Data`; lt-local's
  route is already over g0-assemble3's `G7Data`.

## 7. Findings

1. **The brief's "every textbook leaf T1-T32 is proved" is false** (VERIFIED: agent grep of the 150 newest refs, my grep
   of 80 refs for six of the Props). Proved: T2, T14(a′), T14(b′), T15, T16(a), T17, T18, T20, T21, T25, T28, T31 (and
   T36, T37 inside `x1`). Open: T1, T3, T4, T5, T6, T7, T8, T9, T10, T11(a), T11(b), T16(b), T23, T24, T26, T27, T29(a),
   T29(b); of these T1, T10, T16(b), T29 are never used, T3 and T4 only on route T.
2. **`GluePieces4.tateRamAtThree` is likely false as stated** (linked-ram finding F1, SPECULATIVE there): it is not
   quantified over `G7Data`, so g0-assemble3's `[L:ℚ] ≤ D` fix does not reach it. Proposed replacement
   `UnramTate.TateRamAtThreeD` (adds `Module.finrank ℚ L ≤ ZInQ.heightD`), `scratch/linked-ram/olean/Tail.lean` L618 @
   linked-ram 42677d89, with `linkedRam_of'`. Route T (§4.1) does not use the field.
3. **Stale status texts.** STATUS.md and README say `HeckeThetaNewform` is "reduced to Atkin–Li"; it is proved
   (atkin-li). h-decomposition §2.2 on main marks T14, T28, T36, T37 open (proved) and lists T39 as a leaf (it follows
   from T40). g0-assemble3's docstrings call `heckeIrreducible` "truth SPECULATIVE" (settled by ts-hecke) and its §6 misses
   the unused fields `r1rec, r3, r4, r5, r7b, r8, t10`. cm-numeric's report still lists `IInH4`, `HprimeNormal`,
   `GenusFieldLeLni` as leaves (all proved). assemble-port's docstring count is wrong (§6.1).
4. **TYZ.** `TYZSigmaFixesZn` has two reductions (tyz-cm's to `ShimuraReciprocityPic` + `X0.EtaModelFricke`;
   cm-bridge's to `TYZSigmaShiftsF0` + `IInHprime`, used here); `CMNumeric.tyzZ` and `CMBridge.tyzZ` are two constants
   with the same body (an integration must keep one; T-8 is stated at `CMBridge.tyzZ`); T-8 to T-10 and the CM leaves
   are stated through the eta model `X0.phiC`, so their faithfulness also rests on x0-32's analytic-model statements,
   which are not hypotheses of the chain; `CM.heegnerPt` is `0` off the algebraic case (not a hole: T-5 with T-6 gives
   algebraicity).
5. **Name collisions to resolve when folding**: three structures named `GluePieces5` (cpts-transport, linked-ram,
   assemble-port) and two named `HSyn.GluePieces4` (g0-assemble3, lt-goodred); `WeilPairing.IsogenyQuasiInverse` vs
   `HSyn.G0RevIsog.IsogenyQuasiInverse`; `PropTSGlue.propTSAll_final'` (prop-ts-glue vs ts-sn).
6. **Statement changes proposed here: none.** (Finding 2 is linked-ram's proposal; gz-decomp's `GrossZagierCd` proposal
   stands.)

## 8. Running tasks (snapshot 11:06 PST; refs in `scratch/frontier/refs.txt`)

| task | branch head | open Prop(s) of this list it works on |
|---|---|---|
| tyz-cm | 66d92d11 | T-5 `CMValueRingClass` (report written 10:59; `EtaCuspGrowth` proved) |
| cm-bridge (other host) | 68d27814 | T-7..T-10 (report written 11:07; `BetaOnGenus7` proved) |
| t40-tate | c87d3b9b | `TateMuN`, half of H-41 |
| t40-igusa | 5ee27509 | H-41 (report written) |
| twist-descent | fdd133f1 | field 33: proved at 11:04 (counted as proved) |
| linked-frob | 277bd914 | field 44 (superseded by route T) |
| linked-ram (other host) | 0a44b5a1 | fields 45, 46 (superseded by route T) |
| hom-unify | f605e6c9 | H-66's field 35 (to the stronger `HomLatticeCorr`) |
| spread-out | d1cf705c | H-67 `AbVarSpreadsOut` |
| ts-kummer | 55b966f4 | H-49 `KummerCompositum` |
| hecke-rest | 335f294f | H-50 `HeckeNoVertRam` (and possibly H-62..H-65) |
| heightbc-contrib, mobius-contrib, infra-hodge, frob-contrib, dim-contrib | | porting proved results to Contrib, or targets outside this list (`ProductHodgeLattice`) |
| assemble-port, leaf-fold2 | 52e2caf1, b5168f76 | assemblies (no new proofs) |
| period-glue | cbe9fe4c (idle since 10:27) | H-47, H-48, H-57..H-61 listed as targets |
