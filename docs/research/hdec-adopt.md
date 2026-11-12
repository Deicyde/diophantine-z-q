# hdec-adopt: the H-decomposition glue in the built project

Status: task hdec-adopt, 2026-11-12. Results log: `scratch/hdec-adopt/log.md`; generator
`scratch/hdec-adopt/adopt.py` (with `wrap.py`).

## Result

RESULT_PLACEHOLDER

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
`GlueAssembly.lean`, which the task named). One small copy remains: `PkgI6.exists_sq_eq_one_add`
(I6Base) duplicates `GlueConductor.exists_sq_eq_one_add` (Dyadic) in another namespace.

## Axioms

AXIOMS_PLACEHOLDER
