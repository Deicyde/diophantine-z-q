# persists-dvr: fleet summary

**Proved (VERIFIED, compiled; all axioms [propext, Classical.choice, Quot.sound]).** In
`ZInQKernel/Contrib/OneProof/PersistsDVR.lean`:
- `GapPersists.semistablePersistsDVR_of_printed (h3 : CToPrinted.SGA3_VIB_3_10) (h7 : CToPrinted.SGA7_IX_3_3)
  (hG : AVGlue.GeomConnOfRationalPoint) : ReductSplit.SemistablePersistsDVR`. This is SGA 7 IX 3.3 (i) over every
  DVR and every field K, for K'/K finite.
- `semistablePersistsSHcp_of_printed`: the same hypotheses, concluding `ReductB.SemistablePersistsSHcp`.
- `semistablePersistsSHcp_of_SH (h3) (h7 : SGA7PersistsNF.SGA7_IX_3_3_SH)
  (hN : GapSHPair.NeronBaseChangeStrictHenselization) (hG) : ReductB.SemistablePersistsSHcp`. Its hypotheses are
  bundle fields at the base.
- `ss1_ss3_of_printedNF`: the consumer form, for a manual fold.

**#discharges (VERIFIED).** `OpenResearchLeaves21.semistablePersistsSHcp` is discharged by `semistablePersistsSHcp_of_SH`
and by `semistablePersistsSHcp_of_printed`, both with standard axioms and no new leaf.

**Fold.** Autofold spec: scratch/persists-dvr/autofold.json. Checks:
- The dry run exits 0 with strict counts 45/10 on 55 → 44/10 on 54, and strictest 44/11 → 43/11.
- The generated module compiles (scratch/persists-dvr/FoldCheck.lean), and `sixContactMin_of_open29` has standard
  axioms.
- It is an outright field discharge. No existing consumer is edited, so there is no overlap with sga7-cp's
  `raynaudSemistableSH` and `sga7_IX_3_5_ForwardGeom`.
- If the lead prefers a manual reroute, the only reader is TailZ26 `ss1_ss3_of14NF` (L200-205), and the replacement
  term is in docs/research/persists-dvr.md §2.

**Method.**
1. The residue extension is algebraic for finite K'/K, so `isSemistable_bcDVR_iff` moves semistability to 𝒩 ×_O O'.
2. The identity component W gives j : W ×_O O' → 𝒩' (the chain's `identityComponentBaseChangeDVRRange_of`).
3. The semi-abelian U lands in (W ×_O O')_{κ̄'}, so the same U, B, π and torus witness semistability of 𝒩'.

No transport along a field extension is needed.

**Remaining.** Nothing for this task. The folds stay with the integration lead. The full `frozenTarget` build after
the fold was not run, because the fold was not applied. The dry-run module was compiled instead.
