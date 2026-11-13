# assemble-port (fleet summary)

**Result.** `HDec.HSyn.sixContactMin_of_leaves5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (gp : GluePieces5) :
ZInQ.SixContactMin` compiles with no `sorry` and only `[propext, Classical.choice, Quot.sound]` (VERIFIED). It is
g0-assemble3's assembly ported from the root-namespace Leaves copy to leaf-fold2's base: `scratch/h-decomposition/Leaves.lean`
(`namespace HDec`) with the unused textbook fields deleted, plus leaf-fold2's open bundles.

**The hypotheses.**
- `OpenResearchLeaves2`: 26 fields.
- `OpenTextbookLeaves2`: 18 fields.
- `GluePieces5`: 31 fields, 18 LEAF + 8 LEAF? + **5 GLUE**. g0-assemble3's `GluePieces4` had 46 fields, 14 + 3 + **29 GLUE**.

**What changed against `GluePieces4`.**
- 18 GLUE fields are proved.
- 6 GLUE fields are reduced to leaves only, and 2 to smaller glue.
- 3 LEAF fields moved to the research bundle (R1(b), R14 with its determinant clause, R17).
- 1 LEAF field now follows from T35.
- The remaining glue is `piTwistC`, `sphereFactorAffine`, `kummerCompositum`, `betaSignAtTwo` and `heckeVertWitness`.

**Sources folded in.** The assignment's `SpecNonMeeting` from prop-ts-glue, then every finished result with a report:
- cpts-transport, ts-kummer, hodge-bc2, twist-descent, period-glue (S8/W8/QMTwist);
- ts-hecke, hecke-rest;
- lt-goodred, linked-ram (final), linked-frob (with frob-trace, alg-frob-red, afr-absfrob, frob-pieces), spread-out;
- leaf-fold2's T35 transport.

**Finding (linked-ram F1, adopted).** g0-assemble3's field `tateRamAtThree` is likely false as stated (SPECULATIVE): it is
not quantified over `G7Data`. If so, `sixContactMin_of_leaves4` is vacuous. Here it is replaced by the corrected
`TateRamAtThreeD`, which is proved.

**linkedTateLocal** (report §3).
- local-glue gives `LocalGlue` modulo `KerWild` and `DescentPts`; lg-kerwild discharges both on G7's data.
- lt-local proves `LinkedTateLocal` from R6, T5, `UnramRoots` (now proved in Contrib by frob-contrib), `TateBridge35`,
  `FibreSimple` and `QMEndRank`.
- lt-local's route is not folded here: it lives over the kernel's objects. It could remove `betaSignAtTwo` and
  `upperBreakBound`.

**Compiles (VERIFIED).**
- Olean chain `LPrefix → TailA-F → TailD`: 0 errors; 69 axiom reports, all standard.
- Flat file `scratch/assemble-port/AssemblePort.lean` (110 743 lines): `lake env lean` exit 0 in 1079 s, 0 errors, no
  `sorry`; 285 axiom reports, all standard.

**What remains.**
- The 5 glue Props above. period-glue reduces two of them further; that is not folded.
- The 70 literature statements.
- lt-local's and hom-unify's routes.

Report: `docs/research/assemble-port.md`. Log: `scratch/assemble-port/log.md`.
