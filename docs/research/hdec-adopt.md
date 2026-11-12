# hdec-adopt: the H-decomposition glue in the built project

Status: task hdec-adopt, 2026-11-12. Results log: `scratch/hdec-adopt/log.md`; generator
`scratch/hdec-adopt/adopt.py` (with `wrap.py`).

## Result

All seven clusters are adopted. The sorry-free glue of the H decomposition is in the built
project as 26 modules under `ZInQKernel/HDecomp/` (about 9,200 lines), imported from
`ZInQKernel.lean` through `ZInQKernel/HDecomp.lean`, so the fork's CI (`lake build ZInQKernel`)
now checks it. VERIFIED: `lake build ZInQKernel` exits 0 (2026-11-12, 00:48 PST), and
`lake env lean scripts/print_axioms.lean` prints 179 axiom lists, every one exactly
`[propext, Classical.choice, Quot.sound]`. 88 of those are the HDecomp theorems added here. No
line is longer than 100 characters, and there is no `sorry` or `axiom` (both checked by script).
The build prints about 150 warnings for these modules: deprecations, unused simp arguments,
"simp already closes the goal" and the module-system hint. None is an error, and they were left
alone to keep the proofs as the drafts wrote them.

Six verbatim copies became imports (list below). No theorem statement changed in substance (A6 now names `PkgI2.*`, the same definitions as its dropped copy). The
literature leaves are still `def … : Prop` hypotheses. After deduplication, each scratch
definition is in the project exactly once.

Not done: the leftover glue-assembly drafts (`C8`, `E1Lin`, `E2Index`, `F3Glue`, `Leaves`).
They are not part of `GlueAssembly.lean` and were not adopted. No cluster was dropped.

## Layout (`ZInQKernel/HDecomp/`, imported by `ZInQKernel/HDecomp.lean`, imported by `ZInQKernel.lean`)

| Cluster | Modules | From |
|---|---|---|
| Shared abelian-variety layer | `Objects` | `scratch/obj-bridge/Objects.lean` (§A pkg-I3, §B pkg-I2, §C bridge, §D restated leaves) |
| Arakelov end (F2, E4 transfer, F3 numerics, F4, assembly) | `Assembly` | `scratch/glue-assembly/GlueAssembly.lean` |
| Descent (B1-B3) | `Descent.{ProjRep,B1Quat,Cochain,Constants,Chi,B2Glue,B2Assembly,B3Assembly}` | `scratch/glue-descent/` |
| Conductor bound (D1-D4) | `Conductor.{Breaks,Dyadic,Level}`; `Conductor.{I6Base,ArtinUpper,Inflation,SqrtChar}`; `Conductor.D1Local` | `scratch/glue-conductor/`; `scratch/glue-I6-rest/`; `scratch/glue-d1-local/` |
| A6 | `A6.{A6,Extend}` | `scratch/glue-a6-alg/{A6,Extend}.lean` |
| C10 | `C10.{C10,Trace}` | `scratch/glue-c10/` |
| Repository glue (A1, A3, A5-A8, A10) | `Repo.{A1Quaternion,Numerics,PRArith,TorsionFree}` | `scratch/glue-repo/` |

Every module docstring says that it is glue of `docs/research/h-decomposition.md` with the
literature leaves as hypotheses (`def … : Prop`). No `sorry`, no `axiom` (grep, VERIFIED).
Theorem statements are those of the drafts; the leaves stay `def … : Prop` hypotheses.

## Verbatim copies replaced by imports (VERIFIED: compiled)

- `C10/Trace.lean`: pkg-I3 §1-2 and `PkgI3.CharPolyIndepOfEll` come from `Objects` (§A is pkg-I3
  verbatim); only `PkgI3.trace_indep_of_ell`, `PkgI3.trace_eq_trace_of_ell` remain.
- `Conductor/D1Local.lean`: the copy of glue-conductor's `Breaks.lean` (lines 1-402 of the draft)
  is replaced by `import ZInQKernel.HDecomp.Conductor.Breaks`.
- `Conductor/I6Base.lean`: `PkgI6.exists_sq_eq_one_add` is proved by
  `GlueConductor.exists_sq_eq_one_add` (import of `Conductor/Dyadic.lean`) instead of a copy.
- `Conductor/ArtinUpper.lean` (glue-I6-rest's `Conductor.lean`): the copied pkg-I6 Part II
  definitions (`lowerRam`, `lowerRamR`, `herbrandPhi`, `upperRam`, `codimInv`, `artinConductor`)
  come from `Conductor/I6Base.lean`.
- `Assembly.lean`: F4Copy's copy of `ZInQKernel/Hypotheses/JHeight.lean` is replaced by an import
  of that module (`open ZInQ.JHeight`); `GlueAssembly.SixContactMinAt` and
  `GlueAssembly.sixContactMinAt_of_jHeightBound` (general `S`) stay.
- `A6/A6.lean`: §1-§9 (the pkg-I2 copy) are identical to `Objects` §B up to the namespace name
  (diff, VERIFIED); they are dropped and `PkgI2` is opened. The theorems
  `GlueA6Alg.goodReduction_of_QM_rational3` etc. are now stated over `PkgI2`'s definitions,
  which are the same definitions as the dropped copy's.

Not adopted, as superseded: `scratch/glue-a6-alg/Quat.lean` (its algebra is `GlueA6Alg.Alg` in
`A6.lean`); `scratch/glue-assembly/{C8,E1Lin,E2Index,F3Glue,Leaves}.lean` (outside
`GlueAssembly.lean`, which the task named).

## Axioms

`scripts/print_axioms.lean` now ends with a section listing the HDecomp theorems. These are
every `#print axioms` target of the adopted drafts, plus
`GlueAssembly.jHeightBound_of_glueOutputs` and `GlueAssembly.sixContactMinAt_of_jHeightBound`. The
headline glue theorems are listed below.

- Arakelov end: `GlueAssembly.sixContactMinAt_of_glueOutputs` (GlueOutputs S → SixContactMinAt
  S), `GlueAssembly.jHeightBound_of_glueOutputs`, `GlueAssembly.logHeight_Phi_le`.
- Descent: `GlueDescent.B2Q.b2_of_leaves`, `GlueDescent.B3Q.b3_of_leaves`,
  `GlueDescent.B3Q.b3_degree_le_QM`, `GlueDescent.exists_chi`.
- Conductor: `GlueConductor.D1_genuine`, `GlueConductor.level_le`,
  `GlueConductor.upper_break_le`, `PkgI6.artinConductor_le_of_upper`,
  `GlueD1Local.D1_krasner'`, `GlueI6Rest.inflation_two_eq_coboundary`,
  `GlueI6Rest.exists_half_iff`.
- A6: `GlueA6Alg.goodReduction_of_QM_rational3` (from the I2 leaves NOS, Raynaud, torsion),
  `GlueA6Alg.quatUnipotentTrivial`.
- C10: `GlueC10.c10`, `GlueC10.frobLift`, `PkgI3.trace_indep_of_ell`.
- Shared layer: `ObjBridge.homEquiv`, `ObjBridge.i3Leaves_iff` and the other `*_iff`
  restatements.
- Repository glue: `GlueRepo.A1.*` (order of discriminant 6, positivity of the Rosati form),
  `GlueRepo.PR.*`, `GlueRepo.Numerics.*`, `GlueRepo.TorsionFree.*`.

How to reproduce: run `python3 -I scratch/hdec-adopt/adopt.py`, which regenerates
`ZInQKernel/HDecomp/` from the scratch drafts and wraps long lines. Then run
`lake build ZInQKernel` and `lake env lean scripts/print_axioms.lean`.
