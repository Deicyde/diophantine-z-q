# W13 source normalization — checkpoint report (2026-11-16)

Branch `cloud-b3/w13-normalize` (own source branch), base `9558056025e82261994a8cb95a3b39796df13303`.
Author: Cloud Batch 3 Worker 13 normalization subagent (Metamate/agentcloud). No PR, no merge, no outreach.

## 1. What is implemented (all offline, outside production: `scratch/w13-normalize/tools/`)

* `leanlex.py`, `cmdparse.py`: comment/string-aware Lean 4.35 lexer (identifier classes copied from
  `Init/Meta/Defs.lean`) and command-level parser (checkColGt rule for `open`, `… in` combinators, one-line
  command chains).
* `EnvDump.lean`: reads facts of the 424 *built* external modules the staged tree imports (14,395 modules in
  their closure: namespaces registered per module, 717,907 public constants, protected flags, 47,182
  instances, 109,323 simp entries, 5,900 aliases). Reads only; adds nothing.
* `index.py`: static declaration index of the 9,000 staged files (Lean 4.35 naming: `_root_`, `private`,
  `registerNamePrefixes`, structure/inductive auxiliaries, `@[reassoc]`, attribute-only lines).
* `sim.py`, `translate.py`: the translator. Two copies of Lean's command scope state are simulated per file
  (S = recovered source with the port commands' semantics read from `PortUtil.lean`/`PortUtilExt.lean`, never
  executed; T = translated file); after each port command the plain `open`/`open scoped`/`export`/
  `attribute [-…]` commands bringing T to S are emitted, and T is re-synchronised after every other command.
  Semantics table: `ZInQKernel/Contrib/CloudB3W13/NORMALIZATION.md`.
* `NotationUses.lean` + `notation_inline.py`: Lean's own parser locates every use of a file-local notation
  (only parser-changing commands are elaborated, declarations are only parsed); uses are inlined
  (arguments substituted, parenthesised), with a binder-capture hazard check.
* `pipeline.py` (translate → notations → per-file Apache §4(b) notice), `compile.py` (dependency-ordered plain
  `lean -j2` compiles, one job, RSS/time per module), `hygiene.py` (comment/string-aware scan),
  `validate_erase.py` / `learn_consts.py` (diagnostic cross-check against the old 17:47 receipts).

## 2. What is applied in this commit

The full import cone of `Dictionary.D8.Assembly`, `Dictionary.Interfaces`,
`R2NOS.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj` and
`Source.Theorems.Thm_CerednikDrinfeld_QM_trace_eq_intCast_of_charZero_of_smoothOfRelativeDimension_two`:
75 staged modules (list: `evidence/cone_core.modules.json`); it contains builder5's 46-file wave 1 (all 46).
60 files changed (the other 15 had no port commands). Translated: 86 `r2nos_namespace_dual`, 57
`r2nos_open_dual`, 31 `r2nos_open_scoped_dual`, 6 `w03_reactivate`, 1 `w03_open`, 60 `PortUtilExt` imports;
4 synchronising `open`s; 2 local notations inlined at 24 uses (no capture hazard); the unused global
`notation α "^+" M` (Def_Compat_Mathlib430) removed. FiniteQuotient files untouched (W12 lane). No D5 file.

## 3. Actual checks on this commit

* Compile: all 75 modules compiled with plain `lake env lean -j2` in dependency order, one job at a time,
  against the warm (reflinked) `.lake`: 75/75 succeeded (rc 0, 0 errors; 414 s total, peak RSS 8.1 GB) on the translated tree; a second full pass on the final text of this commit (module docs restored, end-chain open lines dropped) also succeeded 75/75 (`evidence/build_core_pass2.json`).
* Axioms printed by the cone's own `#print axioms` lines (Dictionary D8 BasePoint/FibreTransport/
  FieldClauses/ModelFields, OrderBridge): only `propext`, `Classical.choice`, `Quot.sound`.
* Hygiene (comment/string-aware, 75 files): no `sorry`/`admit`/`axiom`/`native_decide`/`#eval`/`run_cmd`/
  `initialize`/`syntax`/`notation`/`macro`/`elab`/`r2nos_*`/`p2m_*`/`w03_*` except the trusted tactic
  `w03_exact_reverting`; no `PortUtilExt` import. Remaining: 10 pre-existing `#print axioms` queries in the
  Dictionary D8 files and OrderBridge (not code execution; left for the D-lane owners).

## 4. Whole-tree dry run (translator over all 9,000 staged files, nothing written)

172 s, 0 exceptions. Port commands handled: 15,373 `r2nos_open_dual`, 12,810 `r2nos_namespace_dual`, 2,505
`r2nos_open_scoped_dual`, 709 `r2nos_open_scoped`, 25,474 `r2nos_erase_attr` (870,179 names; 68,322 name
occurrences skipped as unresolvable), 4,814 `w03_open`, 4,408 `w03_export` (163 names skipped as in source),
5,569 `w03_reactivate`, 4 `w03_export_all`, 56 `r2nos_alias` (all provably redundant: the prefix chain already
resolves them to the same constant), 15 `#r2nos_type_eq_warn`; 8,889 `PortUtilExt` imports.

Residuals (31 files): 33 plain `open` commands in the *recovered source* that cannot elaborate in the staged
world — none produced by the translation:
* 20 `open _root_.ModularCurve` (S_ModularCurve_UVCrossingModel_* family, S_MvPowerSeries_exists_rename_swap_…,
  Thm_ModularCurve_UVCrossingModel_two_le_ringKrullDim): no module in their import closure declares a root
  `ModularCurve` namespace.
* 12 `open MvPowerSeries (subst)` (S_CerednikDrinfeld_SpecialFormalODModule_* and one
  S_CerednikDrinfeld_QM_FakeEllipticCurve_*): `MvPowerSeries` resolves to the port namespace only, which has no
  `subst` (Mathlib's is `_root_.MvPowerSeries.subst`).
* 1 `open _root_.…FLT.AlgebraicGeometry hiding isIntegral_of_smooth_of_preconnectedSpace`
  (Thm_AlgebraicGeometry_Smooth_algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint): the hidden
  name comes from a missing R2NOS port.
All 33 files have no old compile receipt; they belong to the unbanked late-repair set, not to normalization.

## 5. Known gaps before the remaining ~8,850 files are production-ready

1. Erase-guard completeness. Cross-check against 1,900 old receipt files (rc 0, line-aligned):
   326,085 decisions agree; 19,583 (5.7%) are false negatives (the translator omits a name the old build
   erased); 0 false positives (no emitted name fails to resolve). Causes: the 28 absent R2NOS/W12 ports (their
   import edges and declarations are unknown to the model) and auto-named declarations (anonymous instances,
   `@[simps]` lemmas, instance-valued structure fields). Fix: add the authority's `direct_source_imports` for
   absent modules, index the public upstream originals of the absent ports, and use receipt-learned owners
   (`learn_consts.py`). A false negative leaves an instance/simp lemma active (may change elaboration, cannot
   change the fixed final statement).
2. Notations outside the core cone: 531 `local notation` + 9 `local infixl` + 3 `local infixr` + 2
   `scoped macro` (tactic) in ~200 files; tool-ready, needs a batch run and review of hazard flags; the two
   tactic macros need a manual check of the inlined `first | …` layout.
3. 15 files over 150 KB (largest 878 KB): splitting at declaration boundaries is not started.
4. Compilation: the whole tree was never compiled in the new world. Measured here: ~5.5 s and ~7–8 GB per
   module on this host (one job); the full world is builder work on dedicated15807.
5. Blocked regardless of normalization: dependents of the 7 D5, 22 R2NOS and 6 W12 absent ports, and the 96
   late repairs.

## 6. Feasibility

The mechanical normalization of the remaining files is close (hours): the translator already covers every
port command in the tree with no translation residual, and runs in ~3 minutes. Item 5.1 needs about an hour
to close properly, items 5.2–5.3 a few hours. A green full H119 build is not close: it additionally needs the
absent ports, the 96 late repairs, an unknown number of compile-driven fixes in files never compiled in this
world, and a multi-hour full-world build.
