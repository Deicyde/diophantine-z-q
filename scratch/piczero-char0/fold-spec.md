# piczero-char0: manual fold spec (autofold cannot express a reroute)

Base: wip/leaf-fold33b 0e3c31258 (top `sixContactMin_of_open41`, TailZ48). Checked by `FoldCheck.lean` (compiles,
`frozenTarget_pz` and `sixContactMin_of_open42_pz` on [propext, Classical.choice, Quot.sound]).

1. Add the two contributions (already in this branch):
   * `ZInQKernel/Contrib/OneProof/PicZeroAbVarCharZero.lean` (hand-assembled by `gen/build_char0.py`);
   * `ZInQKernel/Contrib/OneProof/PicZeroAbVarCharZeroReroute.lean` (generated: `python3 scratch/piczero-char0/gen/gen.py OUT`
     from `taint2_out.txt`, which `Taint2.lean` writes on the current tree).
2. New module `ZInQKernel/OneProof/H/TailZ49.lean` = the `namespace HDec.HSyn` part of `FoldCheck.lean`
   (`OpenAddedLeaves21`, `openAddedLeaves20PZ_of_OpenAddedLeaves21`, `sixContactMin_of_open42_pz`; the check map
   `openAddedLeaves20PZ_of_20` may be kept or dropped), importing `ZInQKernel.OneProof.H.TailZ48` and
   `ZInQKernel.Contrib.OneProof.PicZeroAbVarCharZeroReroute`.
3. `Main.lean`: import TailZ49; `frozenTarget`'s binder `l : HDec.HSyn.OpenAddedLeaves20` becomes
   `l : HDec.HSyn.OpenAddedLeaves21` and `sixContactMin_of_open41 r t l` becomes `sixContactMin_of_open42_pz r t l`
   (exactly `frozenTarget_pz` in FoldCheck.lean).
4. kinds.tsv: delete the row `added picZeroAbVar` (GLUE/GLUE); add the three rows of `kinds-rows.tsv` (LEAF/LEAF,
   flagged unread). Counts (autofold.py's `counts`, H rows): strict 13/20 on 33 -> 16/19 on 35; strictest 13/20 -> 16/19.
5. locators.md: rows for the three leaves (draft in `locators-rows.md`), verdict UNVERIFIED.

If the tree moves before integration (another fold changes a carrier), regenerate: run `Taint2.lean` (seeds
picZeroAbVar, t09SymmIsogenyExists, t9, mumfordKLFiniteSectionAC, phiAmpleIsogeny) and `FieldTaint.lean` (to confirm no
new reader), then `gen/gen.py`; the per-declaration edits in gen.py fail loudly if a target line changed.
