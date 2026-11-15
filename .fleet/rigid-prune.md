# rigid-prune: summary

**Verdict.** `mumfordRigidityCore` (OpenResearchLeaves19) **cannot be pruned** by rewiring consumers onto the
abelian-scheme moduli leaves. Two consumers need the universal clause `R1univProps` of a witness on families that
are given only as `QMFamily`. Supplying it from the abelian-scheme leaves takes rigidity, unless a field statement
changes, which this task may not do.
* **N1: the field `OpenGlue7.quotientP1Coordinate`** has `R1fpProps Y Φ` among its hypotheses. Its consumer is
  `MCRGlue.modelCoordinateResidue_of_quotient'` (TailX L275).
* **N2: `ModelGlue.exists_genFib_to_Y`** (TailL L1645) classifies the generic fibre of the Shimura model's family.
  The field `shimuraGoodReductionNoGuard` gives that family as a `QMFamily` only.

Both needs are instances of `QMFamilyGroupLaw`: a QM family over a proper smooth ℚ-curve whose field fibres are
all objects is a `QMAbScheme`. Every other use of the universal clause compares two witnesses (`phi_part`) or uses
twists of the universal family, and needs no rigidity. The strict count is unchanged: 58 fields; kinds.tsv 48 LEAF
/ 17 GLUE; OPEN.md strictest 44 / 14.

**What was done instead (compiles, standard axioms).** New module `ZInQKernel/OneProof/H/TailZ40.lean`, after
merging origin/wip/gt-rigidity:
* `qmFamilyGroupLaw_of_groupLaw : MumfordGroupLaw → QMFamilyGroupLaw`. This needs only *GIT* Thm 6.14; clause (a)
  (Cor. 6.4) is replaced by a field-point proof that each `ι(a)` is a homomorphism (`isMonHom_of_fibres`).
* `r1fpProps_iff_ab_gl` and the nine `*_iff_ab_gl`.

TailZ23's three conversions now go through `qmFamilyGroupLaw_of_core r.mumfordRigidityCore`, and
`mumfordRigidity_of14` is deleted. Results of the checks:
* No `mumfordRigidity_of_core` remains in `frozenTarget`'s closure (ClosureCheck).
* `lake build +ZInQKernel.OneProof.Main` OK; `frozenTarget` uses only the three standard axioms.
* PruneScan: 0 unused fields.
* DumpCompact: 1 constant removed, 20 new (all in TailZ40), 3 conversions changed in value only; `frozenTarget` and
  every bundle are unchanged.
* DischargesTest: the earlier discharges and controls are unchanged, plus gt-rigidity's two discharges.

scratch/rigid-prune/Sites.lean compiles and states the two sites precisely:
* `ShimuraModelGenericAb`, with `exists_genFib_to_Y_ab` and `shimuraModelGenericAb_of_gl`;
* `phi_part_ab`.

**What remains (owner's decision; docs/research/rigid-prune.md §1.1).** Each option changes a field statement:
1. Recommended: weaken the field to gt-rigidity's `MumfordGroupLaw` (Thm 6.14 alone). This is a one-line change in
   the conversions.
2. Weaken it to `QMFamilyGroupLaw`.
3. Remove rigidity altogether. This means restating `quotientP1Coordinate` on `R1fpPropsAb` and
   `shimuraGoodReductionNoGuard` with an abelian-scheme family, and writing abelian-scheme copies of the 245 chain
   constants typed with `R1fpProps`-based Props. Those copies were not written.
