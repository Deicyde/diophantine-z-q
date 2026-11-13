# assemble-port (fleet summary)

**Result.** `HDec.HSyn.sixContactMin_of_leaves5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (gp : GluePieces5) :
ZInQ.SixContactMin` compiles with no `sorry` and only `[propext, Classical.choice, Quot.sound]` (VERIFIED).

It is g0-assemble3's assembly ported from the root-namespace Leaves copy to leaf-fold2's base:
- `scratch/h-decomposition/Leaves.lean` (namespace `HDec`), with the unused textbook fields deleted;
- leaf-fold2's open bundles.

**Hypotheses.**
- `OpenResearchLeaves2`: 26 fields.
- `OpenTextbookLeaves2`: 18 fields.
- `GluePieces5`: 28 fields, **18 LEAF + 7 LEAF? + 3 GLUE**. g0-assemble3's `GluePieces4` had 46 fields, 14 + 3 + 29 GLUE.

**The 3 remaining GLUE Props**: `piTwistC`, `sphereFactorAffine`, `heckeVertWitness`. Everything else
is a literature statement (69 in all).

**Folded in, each with its report.**
- The assignment's `SpecNonMeeting` (prop-ts-glue) and the R14 merge.
- lt-local's proof of `LinkedTateLocal`, with lg-kerwild and local-glue: ported over this file's objects by mechanical
  de-duplication, with `UnramRoots` taken from frob-contrib's kernel proof. It now supplies all of `LinkedTateData`, so
  linked-tate's `linkedFrob`, `kernelFieldBreaks` and `tateRamAtThree` are not hypotheses.
- cpts-transport, ts-kummer, kummer-comp, hodge-bc2, twist-descent, period-glue (S8/W8/QMTwist), ts-hecke, hecke-rest, lt-goodred.
- frob-pieces (via linked-frob's block), spread-out (three EGA IV leaves) and leaf-fold2's T35 transport.
- linked-ram's route is compiled too, but not used by the main theorem.

**Findings.**
- linked-ram F1: g0-assemble3's `tateRamAtThree` is likely false as stated, which would make `sixContactMin_of_leaves4`
  vacuous. It is not a hypothesis here.
- hecke-rest proved an older, stronger text of ts-hecke's `HeckeFibreSizes`. It is kept verbatim as
  `HeckeFibreSizesHR`, with a bridge to the current Prop.

**Compiles (VERIFIED).**
- Olean chain `LPrefix → TailA-F → TailD`: 0 errors; 74 axiom reports, all standard.
- Flat file `scratch/assemble-port/AssemblePort.lean` (116 699 lines): `lake env lean` exit 0 in 1123 s, 0 errors, no
  `sorry`; 290 axiom reports, all standard.

**What remains.**
- The 3 glue Props. period-glue reduces two of them further; that is not folded.
- The 69 literature statements; 7 of them are LEAF? composites, which the frontier task's stricter rule would count as
  GLUE.
- hom-unify's single leaf `HomLatticeCorr` (would merge three leaves; not folded here, though leaf-fold3 uses it).
- leaf-fold3, a parallel assembly, has 6 glue Props; this one has 3.

Report: `docs/research/assemble-port.md`. Log: `scratch/assemble-port/log.md`.
