# p1-quot2 (fleet summary)

**Result.** The glue field `quotientP1Coordinate` (`HDec.MCRGlue.QuotientP1Coordinate`, bundle `OpenGlue7`) is discharged
by `HDec.MCRQuot.quotientP1Coordinate_of_fields3` (`ZInQKernel/Contrib/OneProof/QuotientP1Printed.lean`, standard axioms,
`#discharges` checked) from: the new printed leaf `QuotientP1Proof.LichtenbaumProjective` (Lichtenbaum 1968 Thm 2.8 /
Liu Thm 8.3.16 for S = Spec of a DVR; locator UNVERIFIED, flag unread), mcr-glue's L2 (published), the smoothness half
of L3 `TameQuotientSmoothRelDim` (composite), L4 `SmoothModelOfP1` (consequence), p1-quot's Edixhoven leaf, and five
existing chain fields (mumfordTorsionAlgClosed, mumfordRigidityCore, deligneComponentsY3PrintedAb,
uniformizationLeafAll, gagaMorphism). Strict count of the fold: p1-quot's +3 GLUE is now +1 (autofold dry-run 46/10 ->
49/11); it does not pay yet.

**What was done (all compiled).** (1) `CMStabObjWeak` from cm-stab's `GapGlue.cmStabObj_of` (merged origin/wip/cm-stab;
the two `CMStabObj` are defeq). (2) L1 replaced by Lichtenbaum's theorem: EGA II 4.5.4 over an affine base (vendored
graded prime avoidance), `dim 𝒴 = 2` for integral proper smooth relative curves over a DVR (new proof: fibre
dimensions, DVR stalks at maximal points of the special fibre), regularity from the vendored FLT theorem.
(3) Properness of SGA 1 quotients with q finite (surjective by lying over, finite type by Artin–Tate, separated via
the image of the diagonal), so L3 shrinks to its smoothness half. Helpers `QuotientP1/Lichtenbaum.lean`,
`QuotientP1/QuotProper.lean`; autofold spec `scratch/p1-quot2/autofold.json` (dry-run fold module compiles).

**What remains.** `TameQuotientSmoothRelDim` (tame base change + normal⇒smooth over perfect fields via the existing
field regularSmoothPerfect + EGA IV 17.5.1; no new leaf needed, but ~1.5–2.5k lines of Lean) and L4 (no printed form
found; needs coherent cohomology over a DVR). Doing the first would make the fold count-neutral. Report:
docs/research/p1-quot2.md.
