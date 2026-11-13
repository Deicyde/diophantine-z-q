## 2. GZ: `ZInQ.Literature.GrossZagier`

Snapshot: fork main b7cdba8e; wip/atkin-li 6f77abb1 (finished). Only `C_d`, `d ≡ 5 (mod 8)` squarefree, is used
(gz-decomp §0.3, VERIFIED there by grep): the chain goes through `ZInQ.GZDecomp.GrossZagierCd`, which
`Literature.GrossZagier` implies (`grossZagierCd_of_grossZagier`).

### 2.1 Chain (VERIFIED: signatures read; the last line compiled here)

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| Z1 | `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagierCd` | `Contrib/GZDecomp/Scope.lean` @ main | `SixContactMin`, `TYZThm35ReadingA`, `GrossZagierCd` → `FrozenTarget` (discharges `HeckeContinuation`, `FunctionalEquation5` by the proved `ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) |
| Z2 | `ZInQ.GZDecomp.grossZagierCd_of_leaves'` | `Contrib/GZDecomp/Decomp.lean` @ main | `HeckeThetaNewform`, `FHNonvanishing`, `GrossZagierHeegner` → `GrossZagierCd` (all glue G1–G6 proved) |
| Z3 | `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` | `Contrib/GZDecomp/Decomp.lean` @ main | `SixContactMin`, `TYZThm35ReadingA`, `HeckeThetaNewform`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` |
| Z4 | `ZInQ.GZTheta.heckeThetaNewform : HeckeThetaNewform` (no hypotheses) and `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` | `Contrib/GZTheta/NewCMFinal.lean` @ wip/atkin-li 6f77abb1 | `SixContactMin`, `TYZThm35ReadingA`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` |
| Z5 (this task) | `ZInQ.GZTheta.Frontier.heckeThetaNewform` (verbatim copy of Z4's proof) inside `ZInQ.Frontier.frozenTarget_of_open_main` | `scratch/frontier/TopChain.lean` | compiled over fork main's modules, standard axioms |

### 2.2 Open Props (2, both GLUE in the strict sense)

| # | Lean name | defined in | strict | sources (all theorem numbers UNVERIFIED: no copy on this host) | last task, newest commit | running now |
|---|---|---|---|---|---|---|
| Z-1 | `ZInQ.GZDecomp.FHNonvanishing` | `Contrib/GZDecomp/Decomp.lean:109` @ main | **GLUE** (literature composite: derived from Friedberg–Hoffstein's theorem by choosing local conditions, with the root number of a twist, `ε(f⊗χ_D) = ε(f)χ_D(−N)`, folded in; gz-decomp §2.4 argues it is not stronger than the source; **open question** (cr3-trust §2.4 item 3): whether FH's printed theorem allows the level `N = 32d²`, even and not squarefree; a human must check) | Friedberg–Hoffstein, Ann. of Math. 142 (1995) 385–423, Thm B; Bump–Friedberg–Hoffstein, Invent. Math. 102 (1990) 543–618; Waldspurger, Compositio Math. 54 (1985); root number of twists: Shimura; Atkin–Li, Invent. Math. 48 (1978) | gz-decomp (on main) | no |
| Z-2 | `ZInQ.GZDecomp.GrossZagierHeegner` | `Contrib/GZDecomp/Decomp.lean:131` @ main | **GLUE** (literature composite: Gross–Zagier's formula, Gross's conjugation relation `ȳ_K = −ε y_K`, the modular parametrization of `E` (Eichler–Shimura; Faltings' isogeny theorem) and nondegeneracy of `ĥ` (proved in Tau Ceti), folded into one existential statement because the Heegner point cannot be named in Lean today; gz-decomp §2.5) | Gross–Zagier, Invent. Math. 84 (1986) 225–320, Thm I.6.3 and Ch. V; Gross, *Heegner points on X₀(N)*, Modular forms (Durham 1983), 1984, §5; Shimura 1971, Thm 7.14–7.15; Faltings, Invent. Math. 73 (1983), Korollar 2; for CM curves Shimura, Nagoya Math. J. 43 (1971) | gz-decomp (on main) | no |

Proved since gz-decomp: `HeckeThetaNewform` (atkin-li, also `AtkinLiTwistNew` and `NewformUniqueAcrossLevels`;
the fork's README/STATUS still say "reduced to Atkin–Li"). No task on this host is working on Z-1 or Z-2.
Statement-change proposal already on record (gz-decomp §0.3, not applied): replace the premise
`Literature.GrossZagier` by `GZDecomp.GrossZagierCd`.
