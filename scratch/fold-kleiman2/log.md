# fold-kleiman2 log

Base wip/leaf-fold33b 75d94fe7 (TailZ67, `sixContactMin_of_open60`; render_open on base: 39 open, H strictest 11/23 on 34).

1. Merged origin/wip/kleiman-section2 7591fc3b (with kleiman-section's history; adds only files: Contrib
   KleimanPicZero954.lean, KleimanPicZeroProperQuot.lean, docs, scratch). Hygiene: 5 scratch files redeclaring
   HDec.HSyn bundles renamed .lean.txt (kleiman-section/{TailZ56,FrozenCheck,AutofoldDry},
   kleiman-section2/{TailZ56,FoldCheck}); no host paths found; no vendored LICENSE/NOTICE involved.
2. Readers of the field on the current top (VERIFIED, grep of ZInQKernel/): `l.kleimanPicZeroProper` is read only
   (a) in the generation conversion OpenAddedLeaves25 -> 24 -> 23 -> 22PZ (`picZeroAbVar0_of_leaves`) and
   (b) in `openResearchLeaves35_of_OpenResearchLeaves36_eb` (EichlerBoundCopy) via
   `HodgeTateFromPairing.hodgeTateDecompAbVar_of_open`, which also uses it only through `picZeroAbVar0_of_leaves`.
   So the chain reads the field only as `PicZeroChar0.PicZeroAbVar0` = `KleimanSection2.picZeroAbVar0_of_954`.
3. Generator scratch/fold-kleiman2/gen/gen.py (copy reroute; walks the chain from Main's top call). Output
   ZInQKernel/OneProof/H/TailZ68.lean: `OpenAddedLeaves26 = {picRepresentableAbVar, kleimanPicZeroProper954}`,
   `openAddedLeaves22PZ_of_OpenAddedLeaves26`, `t09SymmIsogenyExists0_of_open_k954`,
   `hodgeTateDecompAbVar_of_open_k954`, 14 copies `X_k954` (sixContactMin_of_open60 ... 48_eb and
   openResearchLeaves35_of_OpenResearchLeaves36_eb), `sixContactMin_of_open48_eb_k954` entering
   `sixContactMin_of_open45_pz_eb`; top `sixContactMin_of_open61`. Main.lean patched (import TailZ68, l retyped,
   top call open61).
4. Base dump (VERIFIED): build tree copied from ~/dzq-wt/leaf-fold33b (75d94fe7, byte-identical Main.lean);
   DumpCompact on base: 17204 constants (hashes_0_base.txt), frozenTarget standard axioms.
5. Build (VERIFIED): `lake build ZInQKernel.Contrib.OneProof.KleimanPicZero954 ZInQKernel.OneProof.H.TailZ68
   +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` completed (16075 jobs, build_1.txt);
   `sixContactMin_of_open61` and `ZInQ.OneProof.frozenTarget` depend on [propext, Classical.choice, Quot.sound].
   After the Main docstring paragraph, checks.sh 1 (one Lean process at a time): build incl.
   KleimanPicZeroProperQuot (merged with kleiman-section2's history) completed (16076 jobs); frozenTarget standard axioms.
6. Hash guard (VERIFIED, hashdiff_1.txt): before 17204, after 17230, only before 0, only after 26 (all in
   ZInQKernel.OneProof.H.TailZ68), changed 1: ZInQ.OneProof.frozenTarget (type+value).
7. Closure (VERIFIED, closure_1.txt): closure 301921 constants; PicFix.KleimanPicZeroProper, picZeroAbVar0_of_leaves,
   hodgeTateDecompAbVar_of_open, OpenAddedLeaves23/24/25, sixContactMin_of_open60, 48_eb and sorryAx absent;
   KleimanPicZeroProper954, picZeroAbVar0_of_954, OpenAddedLeaves26, open61, OpenAddedLeaves22PZ present;
   OpenAddedLeaves26 has 2 fields.
8. OpenStatements: 39 open hypotheses (kleimanPicZeroProper -> kleimanPicZeroProper954). DischargesTest rerun, no
   error: 39 open, 13374 theorems checked, 25 discharge one (none for the new field: expected, nothing proves a
   leaf; the old field cannot appear since it is no longer a hypothesis).
9. kinds.tsv: row `added kleimanPicZeroProper` replaced by `added kleimanPicZeroProper954` (published, pending review
   (new printed leaf, GLUE until a reviewer rates it), GLUE/GLUE, pending-review,unverified-locator; copy in
   kinds-row.tsv); hodgeTateDecompExists row's source text names the new field. claims.tsv: row
   kleimanPicZeroProper dropped. render_open.py: 34 H hypotheses, strictest 11/23, 5 others (39 open; unchanged:
   one GLUE out, one GLUE in; -1 GLUE when the leaf is rated LEAF); --check ok. frontier_crosswalk.py: 232 IDs, 6
   matched; --check ok.
10. autoform check blueprint --lean-root . (taskset -c 0): OK: 772 articles, 2333 dependencies, 697 fully proved; rc 0.
11. Reproducibility: gen.py dry run on the folded head stops with "OpenAddedLeaves26 has no field kleimanPicZeroProper
    (already folded?)", as designed. build_1.txt trimmed to progress/axiom/summary lines (full output 8.9 MB).
