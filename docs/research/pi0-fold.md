# pi0-fold: `deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure` removed from the single proof, in place

Task pi0-fold, 2026-11-16. Base ec797e65 (origin/wip/leaf-fold30 without its docs-only tip). The base did not build
(§0). Source: pi0-prune (origin/wip/pi0-prune ecf45487, docs/research/pi0-prune.md), whose bypass was **not** pasted.
Results log: scratch/pi0-fold/log.md. Model work, no human review.

Marks: **VERIFIED** means compiled, or read in a named file on this host. **STANDARD** means textbook mathematics.
**SPECULATIVE** means judgement.

## 0. The base did not build (reported first)

`lake build +ZInQKernel.OneProof.Main` on ec797e65 reported a **build cycle**: TailZ23 → TailZ40 → TailZ39 → … →
TailZ24 → TailZ23 (VERIFIED).

**Cause.** Two folds used the same module name.
* rigid-prune's `TailZ40` (0bf41b17, `QMFamilyGroupLaw`) is imported by TailZ23, and by
  `Contrib/OneProof/DeligneComponentsY3Used`, which TailZ34 imports.
* leaf-fold30's autofold wrote its persists-dvr top module (56dcca02, `sixContactMin_of_open34`, which imports TailZ39)
  over it, under the same name.

**Fix** (commit 4a034cb1, separate from the rest so the integrator can see it):
* rigid-prune's module is restored verbatim as `TailZ40` (56dcca02^).
* leaf-fold30's module is moved verbatim to the new `TailZ60`, the first name of this task's reserved range.
* Main.lean imports `TailZ60`.
* No other file changed. DeligneComponentsY3Used is a Contrib file I may not edit, so `TailZ40` has to keep
  rigid-prune's content.

Every check below was run on the fixed base. The "before" hashes were taken after the fix, so the move does not
appear in the hash comparison.

## 1. Main result

**`frozenTarget` loses two hypotheses and gains none** (VERIFIED):
* The two are `OpenAddedLeaves17.deligneComponentsX6PrintedAb` and `OpenAddedLeaves17.geomConnOfAlgClosure`.
* `lake build +ZInQKernel.OneProof.Main` succeeds (13695 jobs).
* `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`.
* PruneScan finds 0 unused fields out of 46.
* No new leaf and no new GLUE statement.

| docs/one-proof/kinds.tsv | H fields | strict | strictest | all rows strict | all rows strictest |
|---|---|---|---|---|---|
| before (ec797e65 + fix) | 48 | 40 LEAF / 8 GLUE | 39 / 9 | 48 / 11 | 47 / 12 |
| after | **46** | **38 / 8** | **37 / 9** | 46 / 11 | 45 / 12 |

Both fields were LEAF under both readings, so only the LEAF count drops (fields −2, as expected).

**Why the fields were not needed** (pi0-prune's finding; VERIFIED again here by the compiled reroute and PruneScan):
* Both fields fed only the last clause `R1pi0Props X` (`X₆` geometrically connected) of the row
  `HDec.LeafAdopt.R1R2fpRep`.
* No consumer on the single proof reads that clause. Every destructuring pattern discards it, or ends with a
  catch-all `-`.
* The rest of the row's witness `(Y, Φ, X, Ψ, fY)` with `R1fpProps ∧ X6Props` is already given by González–Rotger's
  leaf `GonzalezRotgerX6`, which the chain already takes.

### 1.1 Step 1: thread the weak row (compiled before any deletion)

Rule followed:
* A consumer's binder changes only from `R1R2fpRep` to the weaker `R1R2fpRepW`, which `R1R2fpRepW_of_rep` derives
  from `R1R2fpRep`.
* Producers keep their strong conclusions; the new weak producers are separate helpers.
* No field of frozenTarget's four bundles changes its statement. The `used-fields` type lists before and after
  step 1 are identical (VERIFIED, diff).

Edits (scratch/pi0-fold/thread.py, plus one recorded fix-up):

* **LPrefix**, next to `R1R2fpRep`:
  * `def R1R2fpRepW` (`R1R2fpRep` without `∧ R1pi0Props X`) and `theorem R1R2fpRepW_of_rep : R1R2fpRep → R1R2fpRepW`.
  * `R1R2fp_of_rep` is now stated on `R1R2fpRepW`. Its proof is the same apart from a pattern one conjunct shorter.
* **Binders and internal bundle fields** switched to `R1R2fpRepW` (33 lines):
  * structure fields `r1r2` in `ResearchLeaves`, `OpenResearchLeaves` (LPrefix), `ResearchLeaves3` (TailD),
    `OpenResearchLeaves2` (TailE), `5` (TailN), `7` (TailX), `8` (TailZ4), `9` (TailZ9) and `10` (TailZ15);
  * `∀ h : …` fields `r1bFamily`, `periodMapGlue` (`GluePieces3`), `r1b` (`OpenResearchLeaves2`/`5`), `periodMapGlue`
    (`OpenGlue2`, `OpenGlue3`);
  * the consumers `fibreQMPeriod_main_rep`, `fibreQMPeriod_of_named_rep`, `propTSAll_of_pieces3`,
    `periodMapGlue_of_leaves4`, `heckeVertWitness_of_leaves5`, `descend_main`, `r1b_of`, `r1b_of'`, `x6ConicModel_of`,
    `x6ConicModel_of_canonical'`, `pairsLift_of_rep`, `coarseFactor_of_rep(')`, `x6ConicModel_of_elkies(_t5)`,
    `r1rec_of_rep` and `r5fp_of_rep`. Three of them (`r1rec_of_rep`, `r5fp_of_rep`, `pairsLift_of_rep`) have a
    destructuring pattern one conjunct shorter.

  These are bundles of older generations, not frozenTarget's bundles. The switch is the renaming pi0-prune's gen.py
  applies to its copies, done here in place. Note that `r1b`/`periodMapGlue` become `∀ h : R1R2fpRepW, …`, a
  stronger statement, but only on internal bundles that the chain fills with proofs.
* **TailO.**
  * The body of `LeafQCheck.cmDescends_of` is now `cmDescends_ofW`, on the weak row.
  * `cmDescends_of` (strong) keeps its type and delegates through `R1R2fpRepW_of_rep`. st-qbar's
    `GapST.cmDescends_of` (Contrib, not editable) calls it with the strong row.
  * `cmDescends_of6` uses `cmDescends_ofW`.
* **New contributor file `ZInQKernel/Contrib/OneProof/Pi0FoldSTQM.lean`**: `GapST.cm_pointW` and `GapST.stQM_ofW`.
  These are st-qbar's `cm_point` and `stQM_of` on the weak row, with the same proofs and one pattern one conjunct
  shorter; scratch/pi0-fold/gen_stqmw.py generates the file from STQM.lean. TailX imports it, and `stQM :=
  GapST.stQM_ofW r.r1r2 …`. **st-qbar's `GapST.stQM_of` still compiles unchanged** (STQM.lean is untouched). The
  chain's `stQM` now uses the W form, as pi0-prune's STQMW.lean anticipated.
* **TailZ21.**
  * The weak producers from pi0-prune's `tools/base_producers.lean` are pasted after `x6Rows_of_leaves`
    (scratch/pi0-fold/producers.lean, with `x6ConicModel_of_elkies_t5W` read as the switched
    `x6ConicModel_of_elkies_t5`).
  * The weakened statements are `CoarseX6OfFineW`, `CanonicalCoarseX6W` and `GeomConnX6W`, each with its
    implication from the original, plus `geomConnX6W_of_gr`.
  * The producer chain is `r1r2fpRep_ofW`, `r1r2fpRep_of'W`, `coarseX6OfFine_ofW`, `canonicalModelY3_of_coarseW`,
    `pairsLift_of_canonicalW`, `coarseCompare_of_canonicalW`, `r1r2fpRep_of_split{,5,6}W` and
    `r1r2fpRep_of_printed{,_t5}W`.
  * On top of it sit `r1r2_of_publishedW` (the hypotheses of `r1r2_of_published` minus `hD`/`hE`),
    `x6ConicModel_of_publishedW`, `structure X6LeavesW` (`X6Leaves` without `deligneX6P`, `geomConn`) and
    `x6Rows_of_leavesW`.
  * `x6ConicModel_of_published` (strong) now wraps `R1R2fpRepW_of_rep`.
* **TailZ23.** `x6Rows_of_open14 : … → LeafAdopt.R1R2fpRepW ∧ X6ConicModel` is built from `x6Rows_of_leavesW` and
  reads neither field.
  * sgr-fold's `SGRFold.heckeSqrtBranchAny_of_open29` (Contrib, not editable) uses
    `LeafAdopt.R1R2fp_of_rep (x6Rows_of_open14 …).1`. That is why `R1R2fp_of_rep` and `x6Rows_of_open14` switch
    together.
  * SGRFold compiles unchanged. Its constant's value hash changes because the elaborated term changes.
* **Fix-up found by the build** (off-chain): TailZ17 `researchLeaves10_of_open11` now reads `r1r2 :=
  R1R2fpRepW_of_rep ((r1R2fpRep_iff_ab …).mpr r.r1r2Ab)`.

PruneScan after step 1 (VERIFIED, prunescan-step1-out.txt):
* exactly `OpenAddedLeaves17.{deligneComponentsX6PrintedAb, geomConnOfAlgClosure}` are unused;
* the prune set is the two fields in `OpenAddedLeaves12`–`17` (12 entries).

### 1.2 Step 2: the prune (scratch/pi0-fold/prune_pi0.py; prune_out.txt lists the 130 deleted lines)

* The 12 fields, with their docstrings, in `OpenAddedLeaves12` (TailZ22), `13` (TailZ24), `14` (TailZ26), `15`
  (TailZ30), `16` (TailZ31) and `17` (TailZ34).
* Their 10 assignments, in `addedLeaves12_of_open13` and `openAddedLeaves1{3,4,5,6}_of_OpenAddedLeaves1{4,5,6,7}`.
* The dead readers of the generation-12 fields, all off-chain in TailZ22: `x6Rows_of_open13`,
  `researchLeaves12_of_open13`, `addedLeaves11_of_open12` and `sixContactMin_of_open16`, with their `#print` lines.
  leaf-fold14's maps go from generation 14 to generation 9 directly; nothing else names these four (VERIFIED, grep).
* Docstrings updated: TailZ22's module doc, Main.lean's module doc and `x6Rows_of_open14`.
* docs/one-proof/kinds.tsv: the two fields' rows are deleted. claims.tsv: their two rows are deleted, plus 4 stale
  rows (§4). The deleted rows are saved in scratch/pi0-fold/removed-rows.txt and stale-claims-rows-removed.txt.

## 2. Every hypothesis

The full statements are in docs/one-proof/OPEN.md, regenerated: 57 open hypotheses, of which 46 are H fields
(`OpenResearchLeaves26` 25, `OpenTextbookLeaves11` 11, `OpenAddedLeaves17` 9, `OpenGlue8` 1) and 11 are other
arguments of frozenTarget. `OpenAddedLeaves17` keeps:
* `thetaRatiosAlgebraic`, `tateTwistInvariants`, `axSenTate`, `milneIsogenyQuasiInverse`, `egaIV_8_10_5_xii`;
* `picRepresentableAbVar`, `picZeroAbVar`, `phiAmpleIsogeny`, `weilPairingMumford`.

None of these statements changed.

## 3. The remaining leaves by theory

The only change is in the moduli/Shimura group, which loses Deligne's `π₀` display for `X₆` (Sém. Bourbaki 389,
PSPM 33; locators UNVERIFIED) and the textbook criterion EGA IV 4.5 / Stacks 0389 in its weakened form. The `X₆`
rows now rest on:
* González–Rotger 2006 Thm 5.12 (`gonzalezRotgerX6Ab`, already a field);
* Baba–Granath, ray-class reciprocity and Elkies' equations (all already fields);
* T5.

## 4. Checks (all VERIFIED; one Lean process at a time)

**Base**, ec797e65 with the §0 fix:
* the build succeeds;
* DumpCompact (OneProof and Contrib.OneProof modules): 17254 constants, in hashes_before.txt, with frozenTarget's
  pp.all type in dumpcompact_before_out.txt;
* PruneScan: 0 unused of 48.

**After step 1:** the build succeeds (13695 jobs, after the TailZ17 fix-up), and PruneScan finds exactly the two
fields unused.

**After step 2:**
* The build succeeds (13695 jobs).
* frozenTarget's axioms are the three standard ones.
* PruneScan: 25 + 11 + 9 + 1 = 46 fields, 0 unused, prune set empty (prunescan-out.txt).

**DumpCompact + cmp_hashes.py** (cmp_hashes_out.txt): 17254 constants before, 17276 after.
* **Removed (16):**
  * the 12 projections `OpenAddedLeaves1{2..7}.{deligneComponentsX6PrintedAb, geomConnOfAlgClosure}`;
  * the 4 dead readers of §1.2.
* **New (38), all helpers:**
  * LPrefix: `R1R2fpRepW`, `R1R2fpRepW_of_rep`;
  * TailO: `cmDescends_ofW`;
  * TailZ21: the 22 weak producers and weak Props of §1.1, plus `X6LeavesW` with its 10 auxiliaries and projections
    (33 constants);
  * the contributor module Pi0FoldSTQM: `GapST.cm_pointW`, `GapST.stQM_ofW`.
* **Changed (157):**
  * 110 generated auxiliaries and projections (`mk`, `_flat_ctor`, `rec`, `recOn`, `casesOn`, field projections)
    of the 18 edited structures. These are the six `OpenAddedLeaves12`–`17`; `GluePieces3`, `OpenGlue2`,
    `OpenGlue3`, `OpenResearchLeaves`, `OpenResearchLeaves2/5/7/8/9/10`, `ResearchLeaves` and `ResearchLeaves3`.
  * The edited consumers, type changed (T): `R1R2fp_of_rep`, `descend_main`, `fibreQMPeriod_main_rep`,
    `fibreQMPeriod_of_named_rep`, `heckeVertWitness_of_leaves5`, `periodMapGlue_of_leaves4`, `propTSAll_of_pieces3`,
    `r1rec_of_rep`, `r5fp_of_rep`, `coarseFactor_of_rep`, `coarseFactor_of_rep'`, `pairsLift_of_rep`, `r1b_of`,
    `r1b_of'`, `x6ConicModel_of`, `x6ConicModel_of_canonical'`, `x6ConicModel_of_elkies`, `x6ConicModel_of_elkies_t5`
    and `x6Rows_of_open14`. Also the field projections `ResearchLeaves(3).r1r2`, `OpenResearchLeaves(2,5,7,8,9,10).r1r2`,
    `OpenResearchLeaves2/5.r1b`, `GluePieces3.{periodMapGlue, r1bFamily}` and `OpenGlue2/3.periodMapGlue`.
  * Value only (V):
    * conversions: `addedLeaves12_of_open13`, `openAddedLeaves1{3,4,5,6}_of_OpenAddedLeaves1{4,5,6,7}`, `addedLeaves6_of_open7`,
      `addedLeaves9_of_open14`, `researchLeaves9_of_open14`, `researchLeaves10_of_open11`;
    * consumers: `cmDescends_of` (delegates to `cmDescends_ofW`), `cmDescends_of6`, `x6ConicModel_of_published`;
    * a dependent: `SGRFold.heckeSqrtBranchAny_of_open29`. Its file is unchanged; its elaborated term passes through
      the switched `x6Rows_of_open14`.
  * `frozenTarget` and every `sixContactMin_of_open*` keep their hashes, and frozenTarget's pp.all type text is
    identical. No other constant changed.

**DischargesTest** (scratch/contrib-kit/DischargesTest-output.txt), controls as before:
* `t1` discharges `OpenGlue8.nvLocalInertia` and still assumes it;
* `t2` discharges nothing;
* `t3` discharges `cartierSmooth` and is flagged for `sorry`;
* the 7 real discharges are by existing contributions;
* 57 open hypotheses.

Pi0Prune's 116 spurious lines do not appear, because no bundle was copied.

**OpenStatements.lean:** 57 open hypotheses, written to open-statements.json.

**render_open.py:** it refused at first. claims.tsv had 4 rows for fields that earlier folds had already removed:
`igusaGL2`, `h29`, `elkiesX6StarPrinted` and `semistablePersistsSHcp`. The base fails the same way, which is why
leaf-fold30's tip ddbcfd61 regenerated only the json.
* I deleted those 4 rows. They are rows of removed fields; this is the one edit beyond my own two fields' rows.
* render_open.py then wrote OPEN.md, pages-wanted.md, CONTRIBUTING.md and STATUS.md.
* `--check` reports: "ok: 57 open hypotheses, all classified; 4 generated files up to date".

**FaithCheck:** not needed, since no HDec copy was replaced by a kernel declaration.

## 5. Not done, and why

* **Old producers left in place.** The strong producers (`r1r2_of_published`, `x6Rows_of_leaves`, `r1r2fpRep_of…`
  in TailU/TailZ20) and the iff `r1R2fpRep_iff_ab` (TailZ17, TailZ40) are now off the closure but kept. They are
  correct, and other modules may cite them. The same holds for `X6Leaves`.
* **No `R1pi0Props` consumer was searched for outside the closure.** By construction, PruneScan only sees the
  closure.
* **The base fix of §0** must reach the integration branch, or leaf-fold30's TailZ40 must be renamed there in some
  other way.

## 6. `frozenTarget`: removed and added hypotheses

* **Removed:**
  * `OpenAddedLeaves17.deligneComponentsX6PrintedAb : ShimuraGlue.DeligneComponentsX6PrintedAb`: Deligne's
    computation of `π₀` of the Shimura variety at level `𝒪̂^×` on the canonical coarse `X₆`, in printed form on
    abelian schemes (Sém. Bourbaki 389 Thm 2.4, §3; PSPM 33 2.1.3, 2.6.3; locators UNVERIFIED). LEAF.
  * `OpenAddedLeaves17.geomConnOfAlgClosure : HDec.QMSplit.Moduli.GeomConnOfAlgClosure`: a proper scheme over a
    field of characteristic 0 is geometrically connected once it is connected over `k̄` (EGA IV 4.5, Stacks 0389,
    weakened; locators UNVERIFIED). LEAF.
* **Added:** none. frozenTarget's binders are the same types; `OpenAddedLeaves17` has two fields fewer.

## 7. State of the branches

| branch | merged | used |
|---|---|---|
| origin/wip/pi0-prune ecf45487 | not merged | report, producers (tools/base_producers.lean), STQMW recipe; its bypass was not pasted |
| origin/wip/dcy3-fold | in the base | PruneScan, DeadCascade, DumpCompact, cmp_hashes, prune_lib copied to scratch/pi0-fold/ |
| origin/wip/leaf-fold30 ddbcfd61 | base is its parent ec797e65 | its tip only regenerated the json (redone here) |
