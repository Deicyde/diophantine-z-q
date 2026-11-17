# fold33-combine (2026-11-16, base wip/leaf-fold33b 0e3c3125)

**Verdict.** Two of the three field removals are folded and verified; the third does not compose with this base.
Branch wip/fold33-combine is the base plus commits, so wip/leaf-fold33b can be fast-forwarded to it.
- **sga3-nbhd** removes `sga3_VIB_3_10_Nbhd` (commit d4fc9592): **33 → 32 H, strictest 13/20 → 12/20**.
- **goodmodel-iso** (fold G) replaces `mumfordGroupLawConn` and `neronSchemeExtensionExists` by the one leaf
  `neronSchemeExtensionDedekind` (commit fbe2ca8b): **32 → 31 H, strictest 12/20 → 11/20**.
- Open hypotheses: 43 → 41.
- **charpoly-charp is left out.** Its reroute needs Mumford §19 Thm 3 (`PkgI3.HomFreeFinite`) at a characteristic-p
  field. homfree-noemb's reroute on the base keeps only the case of fields that embed into ℂ. On this base it becomes
  a count-neutral swap (T7 → characteristic-p T6), not a removal.

**How the folds compose.**
- Both folds are applied **in place** to the original H files:
  - the field is pruned from, or narrowed in, `OpenResearchLeaves14`–`29`, and its readers are replaced;
  - one binder `hNBC` is threaded TailZ23 → TailZ25, because of an import cycle;
  - goodmodel-iso's textbook side is a new top module, `TailZ49`
    (`OpenTextbookLeaves16`, `sixContactMin_of_open42`).
- The homfree reroute is **regenerated** with a parametrized copy of homfree-noemb's Taint.lean and gen.py
  (scratch/fold33-combine/hf/). On the base it reproduces the current reroute byte for byte.
- Scripts: scratch/fold33-combine/sga3_prune.py, gm_fold.py.

**What compiles (VERIFIED, after each fold).**
- `lake build` of Main, Discharges, ZInQKernel and every Contrib/OneProof module: 0 errors.
- frozenTarget has the standard three axioms.
- The closure check passes: the removed types are absent and there is no sorryAx.
- The hash guard passed; every changed constant is listed and explained in docs/research/fold33-combine.md §4.
- OpenStatements, render_open (with `--check`), frontier_crosswalk (with `--check`) and DischargesTest were all rerun.
- An autofold dry run works on the new tree.
- kinds.tsv and claims.tsv are updated: three rows dropped, a `neronSchemeExtensionDedekind` row added.

**What remains.**
- Two blueprint pages name Lean targets that the in-place folds delete. I can't edit them here, and autoform is not
  installed on this host, so it was not run:
  - mumford-group-law.md names `OpenResearchLeaves28.mumfordGroupLawConn`;
  - identity-component-neighbourhood.md names `OpenResearchLeaves28.sga3_VIB_3_10_Nbhd`.
- Decide whether charpoly-charp's swap is wanted.

Report: docs/research/fold33-combine.md. Log: scratch/fold33-combine/log.md.
