# stab-clash: every Contrib module importable at once

## Result

`ZInQKernel/Contrib/AllContrib.lean` (new) imports all 2064 other modules of `ZInQKernel/Contrib/`
(the list is `git ls-files 'ZInQKernel/Contrib/*.lean'`, checked identical to the file's imports).
`lake build ZInQKernel.Contrib.AllContrib` **succeeds** (VERIFIED, 2026-11-13 22:47 PST:
"Build completed successfully (11974 jobs)", no error). Since AllContrib imports every Contrib
module, this build also built every Contrib module that imports a changed file, directly or
transitively.

No theorem or Prop is proved by this task; it is a consolidation task. No declaration name or
statement used by any Lean file of the repository changed (see section 3). No pinned project file
was edited: the edits are confined to nine vendored Tau Ceti files under `ZInQKernel/Contrib/TauCeti/`
(each with a `-- Modified for the Z-in-Q kernel: ...` line) and `ThirdParty/TauCeti/NOTICE`.
`python3 ~/dzq-runs/tc/diffcheck2.py ~/dzq-wt/stab-clash`: MOD-UNNOTED 0, NOTE-ONLY 0, MOD-NOTED 45
(VERIFIED on the first run's host, after all edits). The resumed run's host has no
`~/dzq-runs/tc/` and no Tau Ceti checkouts, so diffcheck2 could not be rerun there. A substitute
check confirmed that each of the nine files changed since 998b4f79 has exactly one
`-- Modified for the Z-in-Q kernel: ... stab-clash ...` line, directly under its provenance line,
and one `(task stab-clash ...)` entry in NOTICE's modified list (VERIFIED).

## 1. The clashes

A static scan (`scratch/stab-clash/dupscan.py`, adapted from t40-clash's; output
`scratch/stab-clash/dupscan-before.txt`) found 71 declaration names declared in two Contrib files,
in 8 file pairs. In each pair one file is Tau Ceti's later version of the other. Neither file of a
pair imported the other, so each pair made it impossible to import both.

| # | older file (commit 5a01f5fe) | superseding file | names |
|---|---|---|---|
| 1 | `GroupTheory/GroupAction/Stabilizer.lean` | `GroupTheory/GroupAction/Stabilizer/Basic.lean` (97a5b235) | 21, incl. `Subgroup.stabilizerInclusion` |
| 2 | `RepresentationTheory/FDRep.lean` | `RepresentationTheory/FDRep/Basic.lean` (97a5b235) | 26 |
| 3 | `NumberTheory/LocalField/UnitFiltration/Pow.lean` | `.../UnitFiltration/Pow/Basic.lean` (97a5b235) | 9 |
| 4 | `NumberTheory/NumberField/FinitePlace.lean` | `.../NumberField/FinitePlace/Basic.lean` (97a5b235) | 2 |
| 5 | `NumberTheory/ClassFieldTheory/Global/PrescribedInvariant.lean` | `Backport/` module of the same path (whole 97a5b235 module) | 6 |
| 6 | `NumberTheory/ClassFieldTheory/Global/Kummer/Norm.lean` | `Backport/` module of the same path | 5 |
| 7 | `NumberTheory/ClassFieldTheory/Global/Kummer/AuxiliaryPlaces.lean` | `Backport/` module of the same path | 1 |
| 8 | `GroupTheory/SpecificGroups/Cyclic/Basic.lean` | `GroupTheory/SpecificGroups/Cyclic/PowMonoidHom.lean` (97a5b235) | 1: `IsCyclic.mem_range_powMonoidHom_iff` |

(All paths relative to `ZInQKernel/Contrib/TauCeti/`.) A second scan including instances and
without the comment filter (`scratch/stab-clash/names.py`, `dupscan2-before.txt`) found no further
real duplicates. The build of AllContrib is the decisive check.

## 2. The fixes (same pattern as t40-clash: keep one declaration, remove the other)

* Pairs 1-4 (VERIFIED by diff, `scratch/stab-clash/cmpdecl.py`): the 97a5b235 file contains every
  declaration of the 5a01f5fe file with identical statement text (pair 3: one proof differs), plus
  more. The 5a01f5fe file now holds only its header, provenance and Modified lines, a docstring,
  and `public import` of the 97a5b235 file. So every importer of the old module still sees every
  name it used, with the same statement.
* Pairs 5-7 (VERIFIED by grep): no Lean file of the repository imported the 5a01f5fe module; the
  Backport/ replacement (task kw-new) declares every name it declares, some with generalized
  statements. The 5a01f5fe file now re-exports the Backport/ module; its old statements are
  dropped (they were unused).
* Pair 8: as Tau Ceti itself did at 97a5b235, `IsCyclic.mem_range_powMonoidHom_iff` (hypothesis
  `n ∣ Nat.card G`) is removed from `Cyclic/Basic.lean`; the 97a5b235 version in
  `Cyclic/PowMonoidHom.lean` (stated with `Nat.gcd`) is kept. Its one user,
  `FieldTheory/Finite/EulerCriterion.lean`, now imports `Cyclic.PowMonoidHom` and uses the two proof
  lines of the 97a5b235 version of EulerCriterion (statement unchanged).

Edited files (each carries a Modified line and a NOTICE entry): the seven older files of pairs 1-7,
`Cyclic/Basic.lean`, `FieldTheory/Finite/EulerCriterion.lean`.

## 3. Who is affected

Direct importers of the edited files (`scratch/stab-clash/direct-importers.txt`, 15 modules, all
under Contrib) build as part of AllContrib. Outside `ZInQKernel/Contrib/`, only the scratch files
`scratch/tc-port/AllKW.lean` and `scratch/t40-clash/AllContrib.lean` import edited modules (VERIFIED
by `git grep`); no `ZInQKernel/` module outside Contrib does.

Caveat for upstream: upstream CI hash-pins existing .lean files. The nine edited files are vendored
Tau Ceti files on the fork; if any of them is already pinned upstream, the fix there must instead
be submitted as the upstream maintainers allow (the task instructions authorize these edits).

## 4. Reproduce

    lake build ZInQKernel.Contrib.AllContrib
    python3 ~/dzq-runs/tc/diffcheck2.py ~/dzq-wt/stab-clash
