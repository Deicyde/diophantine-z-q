# fold33-combine: two of the three field removals compose with leaf-fold33b; charpoly-charp does not

Task fold33-combine, 2026-11-16. Base wip/leaf-fold33b `0e3c3125` (origin/main `c1e4ed1b` is already an ancestor of
the base, so main was not merged). Branch wip/fold33-combine: the folds are commits on top of the base, so
wip/leaf-fold33b can be fast-forwarded to it. Results log: `scratch/fold33-combine/log.md`. Model work, no human review.

Marks: **VERIFIED** = compiled, computed, or read in a named file on this host.

## 1. Result

| step | field(s) | outcome | H hypotheses, strictest (render_open) | open hypotheses |
|---|---|---|---|---|
| base | | | 33, 13/20 | 43 |
| charpoly-charp | `charPolyIndepOfEllAlgClosed` | **left out**: it does not compose (§2) | | |
| sga3-nbhd | `sga3_VIB_3_10_Nbhd` | removed, no new leaf (commit `d4fc9592`) | **32, 12/20** | 42 |
| goodmodel-iso | `mumfordGroupLawConn` and `neronSchemeExtensionExists` replaced by `neronSchemeExtensionDedekind` | net −1, no new glue (commit `fbe2ca8b`) | **31, 11/20** | 41 |

After each fold all of the following were run and passed (VERIFIED):
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`, plus `ZInQKernel` and every module
  `ZInQKernel/Contrib/OneProof/*.lean` (14269 jobs, 0 errors);
* `#print axioms ZInQ.OneProof.frozenTarget`: `[propext, Classical.choice, Quot.sound]`;
* a closure check (`scratch/fold33-combine/ClosureCheck.lean`, homfree-noemb's pattern) showing that the removed types
  are not in frozenTarget's closure;
* the DumpCompact hash guard, before and after, with every changed constant explained (§4);
* `lake env lean scripts/one_proof/OpenStatements.lean`;
* `render_open.py`, then `render_open.py --check`;
* `frontier_crosswalk.py`, then `frontier_crosswalk.py --check`;
* a rerun of `scratch/contrib-kit/DischargesTest.lean`;
* `autofold.py --dry-run` on the final tree, which generates the next generation correctly.

## 2. charpoly-charp does not compose with this base (VERIFIED by reading)

charpoly-charp removes T7 by rerouting `common_trace`. Its reroute is
`common_trace_of_homFree (hH : PkgI3.HomFreeFinite)`, used in TailK as
`linkedTateData_of_local_homFree t.t6 …`. It needs Mumford §19 Thm 3 at the reduction `Ā` of FrobTraceLink, which
lives over a field of characteristic `p`.

leaf-fold33b has already removed `homFreeFiniteAlgClosed` (leaf-fold33 step 8, homfree-noemb). It did so by giving
every T6 reader `HomFreeC.HomFreeFiniteC`. That is the theorem over fields with a ring homomorphism to `ℂ`, and it is
proved from `uniformizationLeafAll_proof` and `mumfordTorsionAlgClosed`. A field of characteristic `p` has no such
homomorphism, so charpoly-charp's reroute fails on this base in two ways:
* Regenerating the homfree reroute over the in-place edit fails by type: `gluePieces_of_open4_hf` would pass
  `t6 : HomFreeFiniteC` where `PkgI3.HomFreeFinite` is expected.
* Restoring T6 in characteristic `p` means adding a leaf. For example homfree-proof's `HomFreeFiniteAlgClosedNoEmb`
  (§19 Thm 3 over algebraically closed fields with no embedding into `ℂ`). That turns the fold into a count-neutral
  swap, Thm 4 → a restriction of Thm 3 (33 → 33).

Either way it is not a removal, so it is left out and wip/charpoly-charp is not merged. If the swap is still wanted,
it buys a more elementary leaf: Thm 3 in characteristic `p` does not need the polynomiality of the degree. It would
take a manual fold:
* add the characteristic-`p` T6 field;
* apply charpoly-charp's fold_edit.py, with `t6` supplied from both the ℂ case and the new field;
* regenerate the reroute.

The leaf-fold33 log already notes the same obstruction for deg-det's route.

## 3. How the two folds compose

The base has two kinds of fold on it:
* autofold generations: TailZ46 and TailZ47;
* homfree-noemb's copy reroute, `Contrib/OneProof/HomFreeFiniteAlgClosedReroute{,/Consumers}.lean`. It copies every
  declaration that depends on T6, including the copies of the research conversions 19←20 … 25←26 and of
  `sixContactMin_of_open17`–`40`. TailZ48 sits on top of it.

sga3-nbhd's own fold copied the research chain TailZ23–45 into `HDec.HSyn.NOL`. Combining that copy with the homfree
copy would need a copy of their product. So both folds were applied **in place to the original H files**, and the
homfree reroute was **regenerated** so that its copies inherit the edits:
* `scratch/fold33-combine/hf/Taint.lean` is homfree-noemb's taint analysis, rooted at `sixContactMin_of_open40`
  (TailZ47), so that it runs without the reroute.
* `scratch/fold33-combine/hf/gen/gen.py` is homfree-noemb's generator, with the taint file and the top module as
  arguments.
* On the unedited base, the regeneration reproduces both reroute files byte for byte (VERIFIED).

**sga3-nbhd** (`scratch/fold33-combine/sga3_prune.py`, 17 H files):
* The field `sga3_VIB_3_10` is deleted from `OpenResearchLeaves14`–`26`, and `sga3_VIB_3_10_Nbhd` from `27`–`29`.
* The five readers in sga3-nbhd's FOLD-SPEC table are replaced in place by its leaf-free variants:
  `SGA3Nbhd.NF.sga7_IX_3_3_of_SH'`, `SGA3Nbhd.Persists.semistablePersistsSHcp_of_SH'`,
  `SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre'`, the deletion of TailZ44's conversion line, and
  `SGA3Nbhd.semistableNeronBaseChange_noSGA3`.
* The last of these cannot be used in TailZ23, because the contribution's import closure contains TailZ23 and TailZ24.
  So `researchLeaves9_of_open14` gets a binder `hNBC : SemistableNeronBaseChange`. It is threaded through
  `sixContactMin_of_open17` and `_open18`, and `sixContactMin_of_open19` (TailZ25) supplies it. This is theta-fold2's
  pattern; the signatures from `_open19` up are unchanged.

**goodmodel-iso** (`scratch/fold33-combine/gm_fold.py`):
* Research side, G.patch's edits:
  * `mumfordGroupLaw` is narrowed to `MumfordGroupLawDVR` in generations 14–27, and the readers in TailZ23 and
    TailZ34 are changed to match;
  * the field swap `mumfordGroupLawConn` → `neronSchemeExtensionDedekind` is made in generation 28. On this base it is
    also needed in generation 29, which is leaf-fold33's autofold generation and did not exist when G was written;
  * `mumfordGroupLaw := GoodModelIso.mumfordGroupLawDVR_of_dedekind n.neronSchemeExtensionDedekind`.
* Textbook side, not in place: a new top module `OneProof/H/TailZ49.lean` in autofold's shape.
  * `OpenTextbookLeaves16` is `OpenTextbookLeaves15` without `neronSchemeExtensionExists`.
  * `neronSchemeExtensionExists_of_dedekind r.neronSchemeExtensionDedekind` supplies that field.
  * The top theorem is `sixContactMin_of_open42`. Main keeps the `import …TailZ49` / `sixContactMin_of_open42 r t l`
    shape.

Final frozenTarget bundles:
* `OpenResearchLeaves29` (24 fields, including `neronSchemeExtensionDedekind`);
* `OpenTextbookLeaves16` (`mumfordTorsionAlgClosed`, `charPolyIndepOfEllAlgClosed`, `gagaMorphism`);
* `OpenAddedLeaves20` (4 fields).

Bundles are still structures in `ZInQKernel.OneProof` modules, and autofold, OpenStatements and `#discharges` work
(VERIFIED).

## 4. Changed existing constants (DumpCompact over `ZInQKernel.OneProof`, VERIFIED)

The lists are in `scratch/fold33-combine/hashdiff_1_sga3.txt` and `hashdiff_2_gm.txt`; the dumps are `hashes_*.txt`.

**sga3-nbhd: 14107 → 14091 constants.**
* Only before (16): the deleted projections.
* Only after: none.
* Changed (239), and why:
  * the 16 structures `OpenResearchLeaves14`–`29` lose a field. That changes their constructor family (80:
    `mk`, `mk._flat_ctor`, `rec`, `casesOn`, …) and the values of the 140 projections after the deleted field (index
    shift);
  * the 15 conversions `openResearchLeaves(k)_of_(k+1)`, k = 14–28, change value (a field line is gone or a reader
    was replaced);
  * `researchLeaves9_of_open14`, `sixContactMin_of_open17` and `_open18` change type and value (the binder `hNBC`);
  * `sixContactMin_of_open19` changes value.
* `frozenTarget` is unchanged.

**goodmodel-iso: 14091 → 14102 constants.**
* Only before (2): `OpenResearchLeaves28/29.mumfordGroupLawConn`.
* Only after (13): the two `neronSchemeExtensionDedekind` projections and TailZ49's 11 constants.
* Changed (100), and why:
  * a field type changes in the 16 structures, which changes `mk`, `mk._flat_ctor`, `rec`, `casesOn` and `recOn`
    (80);
  * the projection `mumfordGroupLaw` of generations 14–27 changes type (14);
  * the conversions 27←28 and 28←29 change value;
  * the readers `x6Rows_of_open14`, `researchLeaves9_of_open14` and `sixContactMin_of_open28` change value;
  * `ZInQ.OneProof.frozenTarget` changes type and value (binder `OpenTextbookLeaves16`).

Outside the dump's scope, the regenerated copies in `HomFreeFiniteAlgClosedReroute.lean` change in the same way:
* `researchLeaves9_of_open14_hf` and `sixContactMin_of_open17_hf`–`19_hf`;
* the research-conversion copies;
* `x6Rows_of_open14_hf` and `sixContactMin_of_open28_hf`.

`Consumers.lean` is unchanged.

## 5. Closure and leaves

Closure (VERIFIED, `closure_2_gm.txt`, 270400 constants). It contains none of:
* the SGA 3 VI_B 3.10 names: `CToPrinted.SGA3_VIB_3_10`, `SGA3IdComp.SGA3_VIB_3_10_Nbhd`, `sga3_VIB_3_10_of_nbhd`,
  `idComp_baseChange`, `semistableNeronBaseChange_of_printed_full`;
* the GIT 6.14 names: `MumfordGroupLawConn`, `mumfordGroupLaw_of_conn`, `MumfordRigidity.MumfordGroupLaw`,
  `qmFamilyGroupLaw_of_groupLaw`;
* `HomFreeFiniteAlgClosed`, `PkgI3.HomFreeFinite`, `sorryAx`.

`NeronC.NeronSchemeExtensionExists` stays in the closure as a proved intermediate statement, supplied by
`neronSchemeExtensionExists_of_dedekind`, and no bundle field has it as its type.

Leaves:
* One new leaf row, `neronSchemeExtensionDedekind`: BLR *Néron models* 1.4 Thm 3 over an affine Dedekind scheme,
  existence half. It is published and LEAF, with the flag "locator UNVERIFIED", taken from goodmodel-iso's
  `fold/autofold-G.json`.
* kinds.tsv rows dropped: `sga3_VIB_3_10_Nbhd`, `mumfordGroupLawConn`, `neronSchemeExtensionExists`.
* claims.tsv rows dropped: the two held project rows.

## 6. Open items for the lead

* **Blueprint** (not editable here; autoform is not installed on this host, so it was not run). Two pages name Lean
  targets that the in-place folds delete:
  * `blueprint/roadmap/height-decomposition/abelian-varieties/mumford-group-law.md` names
    `HDec.HSyn.OpenResearchLeaves28.mumfordGroupLawConn`;
  * `group-schemes/identity-component-neighbourhood.md` names `HDec.HSyn.OpenResearchLeaves28.sga3_VIB_3_10_Nbhd`.

  `autoform render --require-declarations` will flag both until the pages are retargeted or dropped. The leaf is now
  `OpenResearchLeaves29.neronSchemeExtensionDedekind`, and the SGA 3 page no longer corresponds to a hypothesis.
* Merged scratch files that redeclare HDec.HSyn bundles were renamed `.lean.txt`:
  * `scratch/sga3-nbhd/fold/TailZ46.lean`;
  * `scratch/sga3-nbhd/fold/FoldCheck.lean`;
  * `scratch/neron-ext/AutofoldDry.lean`.
* Host paths were removed from the merged logs, patches and scripts.
