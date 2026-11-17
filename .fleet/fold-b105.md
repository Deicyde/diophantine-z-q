# fold-b105 (2026-11-17)

**Verdict: all three folds are in, built and checked.** The branch is d67ea55f plus this task's commits, so
wip/leaf-fold33b can fast-forward to it.

| | top | open | H strict / strictest |
| --- | --- | --- | --- |
| base | `sixContactMin_of_open67` | 36 | 4/27 on 31 |
| 1. chevalleyPerfect removed outright | TailZ75, `sixContactMin_of_open68` | 35 | 4/26 on 30 |
| 2. semistab-assembly (`bostLowerBoundAn`, `gaudronRemondThm14An` → `*SS`) | TailZ76, `sixContactMin_of_open69` | 35 | 4/26 on 30 |
| 3. pb-p1 (`panPrintedP`, `bergerPrintedVT` → `panPrintedF`, `bergerSurveyF`; `r11r12 := panBerger_of_F`) | TailZ77, `sixContactMin_of_open70` | 35 | 4/26 on 30 |

**What was done in each fold:**
- **Fold 1** is fold-chev's bypass rewritten for the let-step copy chain. The generator is
  `scratch/fold-b105/gen_chev_bypass.py`; it stops at `OpenResearchLeaves36EBCF`. The three readers take
  `ZInQ.ChevFree.*`.
- **Fold 2** is an autofold (`autofold-semistab.json`). Both leaves are kind published, with flags beginning "pending
  review" (GLUE).
- **Fold 3** is a bypass (`gen_pbp1_bypass.py`). Kinds rows: panPrintedF "pending review; unread"; bergerSurveyF
  "pending review", cited. Both are GLUE. The audit's panPrintedP review row moved to reviews-retired.tsv.
- **R11 docstring** fixed: Inventiones Thm 0.6 = Thm 5.19 of arXiv v3; 0.7 is Sen's theorem.
- **Merge hygiene:** BypassFold and FontaineSt renamed `.lean.txt`; pb-p1's build logs dropped.

**Checked after each fold** (VERIFIED):
- Build of Main + Discharges + the new modules succeeds; `frozenTarget` uses only the standard axioms.
- Hash guard: 36 new constants per fold, only `frozenTarget` changed.
- Closure: no sorryAx and none of the removed Props.
- OpenStatements gives 35.
- render_open, crosswalk and their `--check` pass; DischargesTest was rerun; the autoform check passes.

**New statements:** all four are cited prints, and none is on-the-spot:
- Bost (Astérisque 237) and Gaudron–Rémond Thm 1.4, with semistability as printed;
- Pan arXiv v2 Thm 1.0.4, the manuscript's own bibitem;
- Berger's survey IV.5.1.

The B1 sketch is not folded.

**For the lead:**
- **Berger numbering:** the retired audit row of bergerPrintedV reads "Théorème 0.7 = Corollaire 5.22", which disagrees
  with the 0.6/5.19 correction (UNVERIFIED either way).
- **Reviewer question:** do the SS leaves stay `published` given R3', or are they consequences?

**Replay:** see `scratch/fold-b105/REPLAY.md`. Three commands; a text-only test ran them on a head with a fake extra
autofold. Report: `docs/research/fold-b105.md`; log: `scratch/fold-b105/log.md`.
