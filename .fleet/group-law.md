# group-law (fleet summary)

**Verdict.** `mumfordGroupLaw` was **not** removed: no −1. The field is *GIT* Thm 6.14 over every locally noetherian
base, non-reduced ones included. It is not proved, and the tree has no route to it: Grothendieck's deformation argument
needs Artinian obstruction theory and Grothendieck existence, and the DVR case needs Néron models over the local
rings of curves. None of these is in Mathlib or the fork.

**Main result (VERIFIED, no `sorry`, standard axioms).** The field's only use in `frozenTarget`'s closure is
`QMFamilyGroupLaw`. It is proved from *GIT* 6.14 over a **DVR**:
`LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr : ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR → QMFamilyGroupLaw`.
The new leaf is printed form and strictly weaker than the field (`dvr_of_field`). Where the local ring is a field, the
group law is proved outright. The rest is Lean:
* local rings of a smooth curve are fields or DVRs (`ZInQ.Contrib.Dim`);
* local laws spread to open neighbourhoods (spread-out's `Stage` machinery and EGA IV 8.8.2 in Mathlib);
* local laws glue, because on field points they are the fibres' laws (field-level rigidity, `isGrpFibre_of_rigidity`).

Also proved: `mumfordGroupLawRed_of_local`, the field over every reduced base, from the leaf over reduced noetherian
local rings.

**What compiles.** Six new files under `ZInQKernel/Contrib/OneProof/` (1,546 lines):
* `GroupLawGlue`, `GroupLawStage`, `GroupLawLocDiagram`, `GroupLawSpread`, `GroupLawStalks`;
* the final file `MumfordGroupLawRed`.

Results:
* `lake build` of Main, Discharges and the final file: 13,704 jobs OK.
* `#discharges`: no discharge from the new file (expected), standard axioms (scratch/group-law/discharges.txt).
* The files' imports avoid TailZ23 and above, so a fold can use them from TailZ23.

**Narrowing fold, compiled in an overlay.** The fold changes field type `MumfordGroupLaw` to `MumfordGroupLawDVR` in
OpenResearchLeaves14 to 26, three sites in TailZ23 and one in TailZ34. It was patched into 13 modules
(scratch/group-law/fold/narrowing.patch). All 31 downstream modules were recompiled into an olean overlay outside the
repo. Result: `frozenTarget` has standard axioms, and `MumfordGroupLaw` is out of its closure (fold/foldcheck.txt).
Count 0, with a weaker leaf. Autofold cannot express it, since no proof of the old field type exists. So
scratch/group-law/autofold.json is a manual spec. The autofold-ready alternative is dict-models' `MumfordGroupLawConn`.

**Remains.** The DVR leaf itself, and the field over non-reduced bases (unused by the chain). The fold has not had an
integration build or OPEN.md regeneration. The re-typing prune (−1, no leaf; possible now that rigid-prune's sites
N1/N2 left the closure) conflicts with the fold contract.

Report: docs/research/group-law.md. Log: scratch/group-law/log.md.
