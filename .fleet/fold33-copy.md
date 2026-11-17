# fold33-copy — fleet summary

**Result:** both field removals are folded into wip/leaf-fold33b as copy reroutes, and no existing declaration
changes.
* sga3-nbhd removes `sga3_VIB_3_10_Nbhd`.
* goodmodel-iso's fold G replaces `mumfordGroupLawConn` and `neronSchemeExtensionExists` by
  `neronSchemeExtensionDedekind`.
* Counts (render_open): 33 H, strictest 13/20 → 32, 12/20 → **31, 11/20**.
* After merging leaf-fold33b's new tip `4da8d4f3` (hQ, hP23 proved): 37 open hypotheses (31 H, 6 others).
* wip/leaf-fold33b fast-forwards to wip/fold33-copy.

* **How:**
  * `scratch/fold33-copy/Taint.lean` lists the 65 declarations of `sixContactMin_of_open41`'s proof whose type or value
    mentions `OpenResearchLeaves14`–`29`: the research generations and conversions, and the homfree `_hf` chain.
  * `gen/gen.py` (homfree-noemb's copylib) copies them with each fold's edits:
    * `ZInQKernel/OneProof/H/NoSGA3Copy.lean` (step 1, suffix NS);
    * `ZInQKernel/OneProof/H/GoodModelIsoCopy.lean` (step 2, suffix GM, both folds, copied from the originals).
  * `gen/top.py` writes the new top modules:
    * `TailZ49`: `OpenResearchLeaves30`, `sixContactMin_of_open42`;
    * `TailZ50`: `OpenResearchLeaves31`, `OpenTextbookLeaves16`, `sixContactMin_of_open43`.
  * Main keeps the `import TailZ50` / `sixContactMin_of_open43 r t l` shape.
* **Compiles and checks** (VERIFIED, after each step and after the merge):
  * `lake build +Main +Discharges` plus the new modules: OK.
  * frozenTarget uses only the standard axioms.
  * Closure check: the SGA 3 VI_B 3.10 and GIT 6.14 names, HomFree, sorryAx and the original generations are all out of
    the closure.
  * DumpCompact hash guard: no existing constant changed except `ZInQ.OneProof.frozenTarget`; only additions.
  * OpenStatements; render_open and frontier_crosswalk, each followed by `--check`: all ok.
  * DischargesTest rerun.
  * `autoform check blueprint --lean-root .` runs here and reports OK. The blueprint's targets
    `OpenResearchLeaves28.mumfordGroupLawConn` and `.sga3_VIB_3_10_Nbhd` still resolve, which was fold33-combine's
    failure.
  * autofold dry run on the result: TailZ51 generated and compiled.
* **Findings:**
  * Copying out of the homfree reroute repeated 220 top-level `open` lines, and the conversions then timed out. Each
    context command is now emitted once.
  * Copies under Contrib/OneProof add hundreds of misleading `DISCHARGES` lines for the copied projections, so the copy
    modules live in OneProof/H.
* **Remains:**
  * NoSGA3Copy and TailZ49 are dead code (outside the closure) and can be dropped at a cleanup.
  * blueprint/ was not edited. The new leaf `OpenResearchLeaves31.neronSchemeExtensionDedekind` has no page.
* Report: docs/research/fold33-copy.md. Log: scratch/fold33-copy/log.md.
