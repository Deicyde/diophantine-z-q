# fold-cm (2026-11-17)

**Verdict: the CM-branch package is folded at +4, as Jack ruled ("Fold now at +4 (Recommended)").** Both components
were regenerated on fold-c8's top and committed separately, each with the full checks. H count: 5/24 on 29 →
**5/28 on 33**, the integrator's expected count, measured with render_open.

* **Component 1** (cm-fold-rebase 664e00417): `sixContactMin_of_open81` on `OpenResearchLeaves62` (TailZ88).
  * Out: `gonzalezRotgerThm512X6RCF`.
  * In: `cmFibreSplit` (glue) and `fowlerProp27`, `cmjDegree`, `cmPotentialGood`, `cmHeight62` (pending review).
  * The NoCM base of fold-c8's chain is replaced by the manuscript's CM branch on the live bundles
    (`Contrib/OneProof/CMBranchUC8.lean`, proof file).
  * Generated chain modules: `OneProof/H/CMTopLive`, `CMR5_1/2/CMR5` (`R5ptProps` as `True`), `CMOpen`.
* **Component 2** (y3-x6b 9a2bbbe3f): `sixContactMin_of_open82` on `OpenResearchLeaves63` (TailZ89).
  * Out: `x6CoarseModuliIdeal`, `elkiesX6StarEveryIdeal`.
  * In: `y3ToP1j` (pending review) and `heckeSqrtBranchAny` (glue; its `Y₃`-only argument is labelled on-the-spot).
  * Generated modules: `OneProof/H/Y3Copy1-6`, `Y3Open`.
* **Compiles and is checked** (VERIFIED):
  * build of Main + Discharges succeeds;
  * `frozenTarget` uses only the standard axioms;
  * hash guard: only `frozenTarget` changed;
  * closure: no González–Rotger statement, no X₆ clause def, leaf or producer, no NoCM base, no `R5ptProps`, no `sorryAx`.
    The González–Rotger-named constants that remain are fields of type `GR56.R5fpCountLe`, which is proved.
  * OpenStatements gives 34; render_open and crosswalk `--check` pass; DischargesTest and autoform check pass; GATE=ok.
* **Manuscript check:** no error.
  * L581-631 OK (L598-600 correct as written).
  * L411-418 Gram matrix and L511-519 `G⁶ − 97200F² = H²` verified by exact computation.
  * L434-436 has an implicit step, filled by `y3ToP1j`.
  * L481-509 bypassed, unchecked.
* **Inbox 84.1 is not live:** the running autoland script has no claims/volatile exemption; only the uninstalled `.new`
  file has it.
* claims.tsv and volatile.tsv were not written. `ShimuraTotalToComponents` is not folded.
* **Remaining:** the reviews of the new leaves, and `cmFibreSplit` (A8 at a CM fibre). A replay on a later head is
  `scratch/fold-cm/REPLAY.md`.
