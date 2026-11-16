# gr14-narrow (done)

**Result.** The research field `gaudronRemondThm14` (OpenResearchLeaves22, R19) can be replaced by its first
conjunct, the new LEAF `GapGR.GaudronRemondThm14Fwd`: Gaudron–Rémond, Duke 163 (2014), Thm 1.4, forward direction
only (an isogeny `A → B` of degree `≤ κ(A)`), over the published stable height. No field is removed. The reverse
direction was used only for existence, which is now proved from `milneIsogenyQuasiInverse` plus the proved
`MulIsogeny`, so the κ(A)/κ(B) reading risk leaves the proof. Report: docs/research/gr14-narrow.md.

**Proved** (all `[propext, Classical.choice, Quot.sound]`; files ZInQKernel/Contrib/OneProof/GR14Narrow.lean,
GR14Narrow/Chain.lean, GR14Narrow/Leaf.lean):
- `gaudronRemondThm14Fwd_of_field : ZInQ.HeightSplit.GaudronRemondThm14 → GaudronRemondThm14Fwd` (and `_of_open`
  from OpenResearchLeaves22).
- `isogenyReverseExists_of_milne : AvSplit.MilneIsogenyQuasiInverse → HDec.HSyn.G0RevIsog.IsogenyReverseExists` (and
  `_of_open` from OpenAddedLeaves17). Method: `[d]` is finite and surjective, so the quasi-inverse `g` is finite
  (`IsFinite.of_comp`) and surjective (`Surjective.of_comp`).
- For the fold:
  - `isogenyReverseExists_of_weil (hMul) (hQ : HDec.WeilPairing.IsogenyQuasiInverse)`, via the K̄-point
    morphism-extensionality lemma copied from TailP;
  - `R19Fwd`, `r19Fwd_of_r19`, `r19Fwd_of_leaves`, `transfer_core_fwd`, `reverseIsogeny_of_weil`.

**#discharges** (scratch/gr14-narrow/discharges.txt): no GapGR theorem discharges a field. This is expected for a
narrowing: the field changes statement. Totals: 63 open, 7 discharged by earlier contributions.

**Fold (manual; VERIFIED).**
- What it is: 27 edits in 20 files, listed with file:line in the report §3, as a script (scratch/gr14-narrow/apply_fold.py)
  and as a unified diff (scratch/gr14-narrow/fold.patch, which passes `git apply --check` at 43513d87).
- How it was checked: I applied it to a private reflink copy `~/gr14-foldtest`, outside the repo. There
  `lake build +ZInQKernel.OneProof.Main` succeeded (12,995 jobs), and frozenTarget has only the standard axioms.
- Result: the post-fold probe shows that the old GR14 statement, R19 and `isogenyReverseExists_of_r19` have left the
  live closure.
- Main changes:
  - the field type becomes `GapGR.GaudronRemondThm14Fwd` in all 15 generations;
  - `r19` becomes `GapGR.R19Fwd` in OpenResearchLeaves7/5/2 and ResearchLeaves3;
  - TailD:251 uses `transfer_core_fwd`;
  - TailK:308 uses `reverseIsogeny_of_weil mulIsogeny_proved l.isogenyQuasiInverse`;
  - TailZ4:163 uses `r19Fwd_of_leaves`;
  - new imports: Chain in TailD, Leaf in TailZ4.

**Remains** for the integration lead:
- apply the fold;
- regenerate OPEN.md, kinds.tsv and locators for the changed statement;
- optionally delete `~/gr14-foldtest`, a reflink copy of about 21 GB apparent size (I was not allowed `rm -rf`).

The leaf's paper title and issue number are from memory (UNVERIFIED).
