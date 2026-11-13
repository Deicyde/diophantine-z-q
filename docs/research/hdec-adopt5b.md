# hdec-adopt5b: t-different, t-skolem-kw, t30-adelic, t10-etale and t28-igusa in the built project

Status: task hdec-adopt5b, 2026-11-13. Results log: `scratch/hdec-adopt5b/log.md`. Generator:
`scratch/hdec-adopt5b/adopt5b.py`. It reuses `scratch/hdec-adopt/wrap.py` for long lines and
`scratch/hdec-adopt2/blocks.py`. Hand repair of one line break: `fixups.py`. Statement check:
`same.py`. Axiom section: `axsec.py`.

## Result

VERIFIED (02:0x PST, after the last Lean change to the imported modules):

- `lake build ZInQKernel` exits 0: "Build completed successfully (10006 jobs)", 7 min 58 s.
- `lake env lean scripts/print_axioms.lean` exits 0. It prints 454 axiom lists, each exactly
  `[propext, Classical.choice, Quot.sound]`. 58 of them are new here (396 before). The list is
  `scratch/hdec-adopt5b/axioms.txt`.

All five developments named by the task are adopted. Nothing was dropped except the second batch
of `ring` proofs of t28-igusa's identities M3; see "Not adopted" for its status. There are 15
new modules (about 7,670 lines) under `ZInQKernel/HDecomp/Textbook/`. All are imported from
`ZInQKernel/HDecomp.lean` in one block after the last import line. The 58 axiom lines are one
block at the end of `scripts/print_axioms.lean`.

| Module (`HDecomp/Textbook/`) | Draft | Main results (all proved, standard axioms) |
|---|---|---|
| `Different` | `t-different/All.lean` | `PkgI6.hilbertDifferentFormula` (T20 local), `PkgI6.differentBound` (T21 local), `PkgI6.herbrandQuotient` (T22a), `PkgI6.herbrandTransitivity` (T22b), `hilbertDifferentFormula_of_dvr`, `monogenicDVR` |
| `SkolemNoether` | `t-skolem-kw/SkolemNoether.lean` | `TSkolemKW.skolemNoether : PkgI6.SkolemNoether` (T13), `hsynSkolemNoether`, `leafSkolemNoether : GlueDescent.LeafSkolemNoether` |
| `BrauerNesbitt` | `t-skolem-kw/BrauerNesbitt.lean` | `TSkolemKW.brauerNesbittChar0 : PkgI6.BrauerNesbittChar0` (T19), `hsynBrauerNesbitt` (matrix form) |
| `C10Closed` | `t-skolem-kw/C10Closed.lean` (last part) | `TSkolemKW.C10.c10_of_chebotarev`: `GlueC10.c10` without its Brauer–Nesbitt hypothesis |
| `FrobeniusDense` | `t-skolem-kw/FrobeniusDense.lean` | `TSkolemKW.HS.frobeniusDense_of_chebotarev : ChebotarevExists → FrobeniusDense` (T18 from its finite form) |
| `KroneckerWeberUse` | `t-skolem-kw/KroneckerWeberUse.lean` | the C8 glue: `dirichletCharacter_of_kroneckerWeberCyclic`, `ker_ge_of_kroneckerWeber`, `kroneckerWeberCyclic_of_kroneckerWeber`, `cycChar_surjective`, `isOpen_ker_of_continuous` |
| `ChebotarevCyclotomic` | `t-skolem-kw/ChebotarevCyclotomic.lean` | `chebotarevAt_cyclotomic` (sanity check of the leaf `ChebotarevExists`) |
| `T30SqrtCrit` | `t30-adelic/SqrtCrit.lean` | `T30.leafSqrtCrit_of_localKroneckerWeber`, `T30.leafSqrtCrit_of_t16a` (T30 from T16) |
| `G1Adelic` | `t30-adelic/Adelic.lean` | `G1Adelic.relIndex_eq_four`, `mem_sup_iff_forall`, `normalizer_component`, `gamma_count`, `gamma_order`, `gamma_count_Zint` |
| `G1Count` | `t30-adelic/G1Count.lean` | `G1Count.index_count_of_central` |
| `T10Etale` | `t10-etale/T10Etale.lean` (branch `wip/t10-etale`) | the `ℤ_ℓ`-module structure on `EllAdicCohomology`, `H0Equiv`, transport (`transport_smul`, `transport_bijective`, `transport_H0`), `galIso`; leaves `T10_TateDuality`, `T10_linIso` with `T10_linIso_of_tateDuality`, `T10_groupIso_of_linIso`, `T10_linIso_zero` |
| `Igusa/Forward` | `t28-igusa/Igusa.lean`, part 1 | leaf `PkgI1.IgusaClebschSeparation` and its definitions; `PkgI1.igusa_forward` (the `⇒` half), `igusaClebschSeparation_iff` |
| `Igusa/SO3` | part 2 | `T28SO3.so3` (`SO(3) = PGL(2)` for binary quadratics) |
| `Igusa/Generic` | parts 3-4 and the spot checks | `PkgI1.mestre_abstract`, `separation_generic`, **`igusaClebschSeparation_of : M3Identities → SeparationSpecial → IgusaClebschSeparation`** (the reduction), `spot_J` |
| `Igusa/M3a` | first batch of `ring` proofs | `PkgI1.m3_G11`, `m3_G12`, `m3_G13`, `m3_G22`, `m3_a111` |

Rules checked:
- Leaves stay `def … : Prop`. The new Prop definitions are `MonogenicDVR`,
  `TraceContainsRamificationIdx`, `HSynSkolemNoether`, `HSynBrauerNesbitt`, `HS.FrobeniusDense`,
  `KW.KroneckerWeber`, `KW.KroneckerWeberCyclic`, `T10_linIso`, `T10_TateDuality`,
  `IgusaClebschSeparation`, `IgusaSeparationEq`, `M3Identities` and `SeparationSpecial`. All of
  them come verbatim from the drafts.
- grep finds no `sorry` or `axiom` in the new modules. The one hit for `admit` is the English
  word in a comment.
- awk finds no line longer than 100 characters (VERIFIED).
- No build log was saved.
- Outside `scratch/hdec-adopt5b/` and this note, only `ZInQKernel/HDecomp/Textbook/` (new),
  `ZInQKernel/HDecomp.lean` and `scripts/print_axioms.lean` changed (`git diff --stat`).

**Statements unchanged** (`same.py`, VERIFIED). For every declaration of each draft, the table
gives one of three outcomes:
- the adopted module has a declaration of the same full name whose whitespace-normalized block
  (statement and proof) is identical;
- or it is a verbatim copy of existing HDecomp code (`scratch/hdec-adopt3/dups.py`: SAME), which
  the module now imports;
- or it is an exception.

| Draft | Declarations | Identical | Copies now imported | Exceptions |
|---|---|---|---|---|
| t-different/All.lean | 76 | 66 | 10 | 0 |
| t-skolem-kw/SkolemNoether.lean | 11 | 9 | 2 | 0 |
| t-skolem-kw/BrauerNesbitt.lean | 15 | 14 | 1 | 0 |
| t-skolem-kw/C10Closed.lean | 52 | 16 | 36 | 0 |
| t-skolem-kw/FrobeniusDense.lean | 40 | 13 | 27 | 0 |
| t-skolem-kw/KroneckerWeberUse.lean | 19 | 17 | 2 | 0 |
| t-skolem-kw/ChebotarevCyclotomic.lean | 3 | 2 | 1 | 0 |
| t30-adelic/SqrtCrit.lean | 31 | 31 | 0 | 0 |
| t30-adelic/Adelic.lean | 103 | 103 | 0 | 0 |
| t30-adelic/G1Count.lean | 3 | 3 | 0 | 0 |
| t10-etale/T10Etale.lean | 59 | 58 | 1 | 0 |
| t28-igusa/Igusa.lean | 155 | 152 | 0 | 3 (`m3_G23`, `m3_G33`, `m3_a112`: see below) |

The comparison ignores whitespace only. So the line breaks added by `wrap.py`, and the one
repaired by hand in `fixups.py`, change no statement or proof.

## Verbatim copies replaced by imports (VERIFIED: compiled)

- **t-different.** The draft's `namespace PkgI6` preamble (`lowerRam`, `mem_lowerRam`,
  `lowerRamR`, `herbrandPhi`, `upperRam`, `lowerRam_tower`) and the four leaf statements
  `HilbertDifferentFormula`, `DifferentBound`, `HerbrandQuotient`, `HerbrandTransitivity` are
  imported from `Conductor/I6Base.lean`. That file has the same names in the same namespace, so
  no `open` is needed. The theorems now prove the built project's leaf constants
  `PkgI6.HilbertDifferentFormula` etc. directly. These are the fields `t22a`, `t22b` of
  h-decomposition's `TextbookLeaves`, and the local forms of `t20`, `t21`.
- **t-skolem-kw.**
  - `TSkolemKW.SkolemNoether` is `PkgI6.SkolemNoether` (`Conductor/I6Base`).
  - `LeafSkolemNoether` is `GlueDescent.LeafSkolemNoether` (`Descent/B1Quat`).
  - `BrauerNesbittChar0` is `PkgI6.BrauerNesbittChar0`.
  - The whole `TSkolemKW.C10` part of `FrobeniusDense.lean` (23 declarations) and of
    `C10Closed.lean` (35) is `GlueC10`'s (`C10/C10.lean`).
  - `HSyn`'s `Qbar`, `GQ`, `LiesOver`, `IsArithFrob` in `FrobeniusDense.lean`, and `Qbar`, `GQ`
    in `KroneckerWeberUse.lean`, are `PkgI4`'s (`Conductor/LadicCond`).
  - `ChebCyc.card_quot` is `GlueC10.card_quot`.

  Each replacement is a selective `open` (for example `open PkgI6 (SkolemNoether)`), so the
  remaining text is unchanged. `C10Closed.lean`'s first part is `BrauerNesbitt.lean` verbatim
  (`diff`, VERIFIED), so the module imports `Textbook.BrauerNesbitt` and keeps only the last part
  (`brauerNesbittChar0'`, `c10_of_chebotarev`).
- **t10-etale.** `T10_groupIso` is `ZInQ.LeafPush2.T10_groupIso` (`LeafPush2/T.lean`, adopted by
  hdec-adopt4). It is over the same `PkgI3.AbVar` of `Objects.lean`, so `T10_groupIso_of_linIso`
  now ends in the built leaf-push2 constant. The draft's four specific Mathlib imports are kept;
  their oleans are part of the installed Mathlib build.
- **t30-adelic, t28-igusa.** No copies. The t30 files already imported built modules
  (`Vigneras.Local`, `Repo.A1Quaternion`, `Sqrt.Disj`, `Descent.B2Glue`). t28's `PkgI1` Igusa
  definitions are not in the build elsewhere: `grep IgusaClebschSeparation`, `def J10` and
  `namespace PkgI1` over `ZInQKernel/` gave nothing.

Drafts not adopted because another file subsumes them:
- t-different's `HilbertLocal.lean`, `DifferentBound.lean`, `Herbrand.lean` and `Statements.lean`
  are subsumed by `All.lean`, the draft's own deduplicated integration file.
- t-skolem-kw's `AllCheck.lean` is a concatenation of the four proof files.
- t28-igusa's `Defs.lean`, `Forward.lean`, `SO3.lean` and its `part_*`/`gen_*` fragments are
  subsumed by `Igusa.lean`, the deliverable assembled from them.

## Not adopted (or pending)

- **`Igusa/M3b`: the second batch of `ring` proofs (`m3_G23`, `m3_G33`, `m3_a112`).** The draft
  log reports about 7 minutes for this batch, and a sibling identity (`a113`) reached 27 GB before
  it was killed. The module is generated (`adopt5b.py --m3b`) but is NOT imported from
  `HDecomp.lean`, so the build above does not include it. Build attempt: see the log (PENDING at
  the time of writing). None of the reduction theorems needs these identities:
  `igusaClebschSeparation_of` takes `M3Identities` as a hypothesis.
- **Downstream use of the new theorems.** The theorems are not used downstream yet. For example,
  the `HSyn.TextbookLeaves` fields `t13`, `t19`, `t22a`, `t22b` and the `BrauerNesbittChar0`
  hypothesis of `GlueC10.c10` could be discharged by them. That bundle lives in
  `scratch/h-decomposition/Leaves.lean`, which this task may not edit. In the build, the
  discharge is available as terms: `TSkolemKW.C10.c10_of_chebotarev`, `PkgI6.herbrandQuotient`,
  and the others listed above.
- **Merge notes.** t10-etale's scratch directory is not in this branch's base: the generator
  reads the file from `origin/wip/t10-etale` (commit 9610b943) through `git show`, as its usage
  line says. The parallel adoption task also appends to `HDecomp.lean`'s import list and to
  `scripts/print_axioms.lean`. Both of this task's insertions are single contiguous blocks, each
  headed by a `-- hdec-adopt5b` comment.
