# fold33-copy: both field removals folded into leaf-fold33b as copy reroutes; every existing declaration unchanged

Task fold33-copy, 2026-11-16. Base wip/leaf-fold33b `30674d98`. origin/main `c1e4ed1b` was already an ancestor, so
main was not merged. During the task wip/leaf-fold33b moved to `4da8d4f3` (hQ and hP23 proved), and that tip is merged
in. wip/leaf-fold33b therefore fast-forwards to wip/fold33-copy (VERIFIED: `git merge-base --is-ancestor`).
Results log: `scratch/fold33-copy/log.md`. This is model work with no human review.

Marks: **VERIFIED** means compiled, computed, or read in a named file on this host.

## 1. Result

| step | field(s) | commit | H hypotheses, strictest (render_open) | open hypotheses |
|---|---|---|---|---|
| base `30674d98` | | | 33, 13/20 | 41 |
| 1 sga3-nbhd | `sga3_VIB_3_10_Nbhd` removed, no new leaf | `f9076458`, moved in `6e346f20` | **32, 12/20** | 40 |
| 2 goodmodel-iso (fold G) | `mumfordGroupLawConn` and `neronSchemeExtensionExists` replaced by `neronSchemeExtensionDedekind` | `ebb45463` | **31, 11/20** | 39 |
| 3 merge leaf-fold33b `4da8d4f3` | hQ and hP23 (proved upstream of this task) | `848c7402` | 31, 11/20, 6 others | 37 |

Unlike fold33-combine's in-place folds:
* no existing declaration changes;
* the original research generations `OpenResearchLeaves14`–`29`, their conversions, the homfree `_hf` chain and
  `sixContactMin_of_open41` all stay;
* the blueprint targets `HDec.HSyn.OpenResearchLeaves28.mumfordGroupLawConn` and
  `OpenResearchLeaves28.sga3_VIB_3_10_Nbhd` still resolve.

`autoform check blueprint --lean-root .` runs on this host. After each step it reports "OK: 781 articles, 2343
dependencies, 705 fully proved, 2531 declaration name(s) resolved" (VERIFIED).

## 2. How the copy works

**Taint list.** `scratch/fold33-copy/Taint.lean` imports TailZ48 and computes the declarations to copy:
* It starts from the closure of the old top `sixContactMin_of_open41` (241711 constants).
* The carriers are the structures `OpenResearchLeaves14`–`29`. Each of them has one of the two sga3 fields and one of
  `mumfordGroupLaw` / `mumfordGroupLawConn`, so **both folds have the same carriers**.
* Every constant whose type or value mentions a carrier is tainted, transitively.
* Result: 519 tainted constants, of which 66 are source declarations (`taint_0_base.txt`):
  * the 16 research generations;
  * 11 research conversions (TailZ25–46);
  * 39 declarations of homfree-noemb's reroute that thread the research bundle: the `_hf` chain
    `sixContactMin_of_open17_hf`–`40_hf`, `researchLeaves9_of_open14_hf`, `x6Rows_of_open14_hf`, the `_hf` research
    conversions, and SGRFold's two `_hf` theorems;
  * TailZ48's `sixContactMin_of_open41`, which is not copied: the new top module replaces it.

**Generator.** `scratch/fold33-copy/gen/gen.py` uses homfree-noemb's copylib, with the item list taken from the taint
file.
* It copies the 65 declarations verbatim up to a renaming: `XNS`/`x_ns` for field 1, `XGM`/`x_gm` for field 2. Helpers
  in a carrier's namespace are renamed through the carrier's name.
* It applies the fold's edits and asserts that none of the removed fields is left in the code.
* `gen/top.py` writes the top module in autofold's shape and patches Main.

**Field 1** (`ZInQKernel/OneProof/H/NoSGA3Copy.lean`, 2075 lines):
* the field `sga3_VIB_3_10` is deleted from generations 14–26 and `sga3_VIB_3_10_Nbhd` from 27–29;
* sga3-nbhd's five readers are replaced (its FOLD-SPEC table):
  * `SGA3Nbhd.semistableNeronBaseChange_noSGA3`;
  * `NF.sga7_IX_3_3_of_SH'`;
  * `Persists.semistablePersistsSHcp_of_SH'`;
  * TailZ44's conversion line, deleted;
  * `Pre.sga7_IX_3_3_SH_of_pre'`.
* fold33-combine needed an `hNBC` binder threaded through TailZ23–25. The copy module can import the contribution
  directly, so it does not.

The top module `OneProof/H/TailZ49.lean` contains:
* `OpenResearchLeaves30`, which is `OpenResearchLeaves29` without the field (24 fields);
* `openResearchLeaves29NS_of_OpenResearchLeaves30`;
* `sixContactMin_of_open42 (r : OpenResearchLeaves30) (t : OpenTextbookLeaves15) (l : OpenAddedLeaves20)`, which
  goes through `sixContactMin_of_open40_hf_ns`.

**Field 2** (`ZInQKernel/OneProof/H/GoodModelIsoCopy.lean`): the same 65 declarations, copied **from the originals**
with both folds. The edit counts are those of fold33-combine's gm_fold.py:
* `mumfordGroupLaw` is narrowed to `GroupLaw.MumfordGroupLawDVR` in generations 14–27;
* the readers become `qmFamilyGroupLaw_of_dvr` (×3) and `y3Connected_of_ab_gl ∘ qmFamilyGroupLaw_of_dvr`;
* `mumfordGroupLawConn` → `neronSchemeExtensionDedekind` in generations 28–29;
* `mumfordGroupLaw := GoodModelIso.mumfordGroupLawDVR_of_dedekind n.neronSchemeExtensionDedekind`.

The copy is taken from the originals, not from NoSGA3Copy, so that the names do not stack. NoSGA3Copy and TailZ49 stay
in the build, unchanged, outside frozenTarget's closure.

The top module `OneProof/H/TailZ50.lean` contains:
* `OpenResearchLeaves31`: `OpenResearchLeaves30` with the swap;
* `OpenTextbookLeaves16`: `OpenTextbookLeaves15` without `neronSchemeExtensionExists`, which
  `GroupLawNeron.neronSchemeExtensionExists_of_dedekind r.neronSchemeExtensionDedekind` supplies;
* `sixContactMin_of_open43`.

**Main** keeps the `import …TailZ50` / `sixContactMin_of_open43 r t l` shape, and its module docstring has two new
paragraphs. Bundles are structures in `ZInQKernel.OneProof` modules, so OpenStatements, `#discharges` and autofold see
them. autofold's dry run (discharging two fields by `sorry`) generates TailZ51 with `OpenResearchLeaves32`,
`OpenTextbookLeaves17` and `sixContactMin_of_open44`, and that file compiles (VERIFIED).

## 3. Two findings about copy reroutes (VERIFIED by compile and by the DischargesTest output)

* **Repeated `open` commands time out the elaborator.** copylib re-emits each source block's top-level context. A
  block copied out of the homfree reroute brings along every top-level `open` of that file, so the generated module
  had 220 copies of `open CategoryTheory … MonObj` and of two other `open` lines. The late field-by-field research
  conversions (19←20, 20←21, 21←22, 23←24, 25←26) then hit `isDefEq` timeouts, even at 1000000 heartbeats.
  The fix was to emit each top-level context command once. After that, the module compiles at default heartbeats in
  under a minute (8 s in the final build).
* **Copies under `Contrib/OneProof` flood `#discharges`.** `#discharges` scans every theorem of
  `ZInQKernel.Contrib.OneProof.*`, and the projections of the copied Prop structures are theorems that conclude an open
  field. With the copies there, the output grew from 48 to 301 `DISCHARGES` lines (542 after field 2), nearly all of
  them misleading entries in CONTRIBUTING.md's worked example. So the copy modules live under `ZInQKernel/OneProof/H/`,
  which the task allows for new modules. The worked example then changes only by the bundle names and the entries of
  the removed fields. homfree-noemb's reroute, which is in Contrib, is the source of the existing `…HF.<field>`
  entries: 68 lines of the base output mention an HF bundle.

## 4. Checks after each step (all VERIFIED; outputs in `scratch/fold33-copy/`)

Each step ran the following:
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` plus the new modules (`build_*-tail.txt`);
* `#print axioms` of frozenTarget and of the new top theorem, both `[propext, Classical.choice, Quot.sound]`;
* the closure check (`ClosureCheck.lean` → `closure_*.txt`);
* the DumpCompact hash guard (`DumpCompact.lean` → `hashes_*.txt`, `hashdiff.py` → `hashdiff_*.txt`);
* `lake env lean scripts/one_proof/OpenStatements.lean`;
* `render_open.py`, then `--check`;
* `frontier_crosswalk.py`, then `--check`;
* the DischargesTest rerun into its output file;
* the autoform check.

Hash guard (DumpCompact over the `ZInQKernel.OneProof` modules):

| comparison | before → after | only before | only after | changed |
|---|---|---|---|---|
| base → step 1 | 14107 → 14139 | 0 | 32 (TailZ49) | 1: `ZInQ.OneProof.frozenTarget` |
| base → step 1b (copy moved into OneProof/H) | 14107 → 14705 | 0 | 598 (566 NoSGA3Copy + 32 TailZ49) | 1: frozenTarget |
| 1b → step 2 | 14705 → 15313 | 0 | 608 (566 GoodModelIsoCopy + 42 TailZ50) | 1: frozenTarget |
| step 2 → merge | 15313 → 15313 | 0 | 0 | 1: frozenTarget |

Closure of frozenTarget after step 2 (270833 constants). It contains none of:
* the SGA 3 VI_B 3.10 names: `CToPrinted.SGA3_VIB_3_10`, `SGA3IdComp.SGA3_VIB_3_10_Nbhd`, `sga3_VIB_3_10_of_nbhd`,
  `idComp_baseChange`, `semistableNeronBaseChange_of_printed_full`;
* the GIT 6.14 names: `MumfordConn.MumfordGroupLawConn`, `mumfordGroupLaw_of_conn`, `MumfordRigidity.MumfordGroupLaw`,
  `qmFamilyGroupLaw_of_groupLaw`;
* HomFree, `sorryAx`;
* the originals `OpenResearchLeaves14`/`29` and `sixContactMin_of_open41`, or the NS copies.

`OpenResearchLeaves29GM`, `NeronSchemeExtensionDedekind`, `mumfordGroupLawDVR_of_dedekind` and
`neronSchemeExtensionExists_of_dedekind` are in it. `NeronC.NeronSchemeExtensionExists` stays in it as a proved
intermediate statement, and no bundle field has it as its type. The bundles are `OpenResearchLeaves31` (24 fields),
`OpenTextbookLeaves16` (3) and `OpenAddedLeaves20` (4).

Tables:
* kinds.tsv: rows `sga3_VIB_3_10_Nbhd`, `mumfordGroupLawConn` and `neronSchemeExtensionExists` dropped. Row
  `neronSchemeExtensionDedekind` added (BLR *Néron models* 1.4 Thm 3 with 1.2 Def 1, existence half, affine Dedekind
  base): published, LEAF/LEAF, "locator UNVERIFIED", packet R2, tier T4. The row is goodmodel-iso's spec as
  fold33-combine wrote it.
* claims.tsv: the two held project rows (neron-ext, group-law) dropped.

## 5. Open items for the lead

* The base moved once during the task. If wip/leaf-fold33b moves again, merge it in; the generated docs conflict and
  are regenerated by the scripts.
* NoSGA3Copy and TailZ49 (step 1's generation) are now dead code in the build: both are outside frozenTarget's
  closure. They can be dropped at the next cleanup, or kept as the record of step 1.
* The blueprint chapter still describes `sga3_VIB_3_10_Nbhd` and `mumfordGroupLawConn` as leaves of the old
  generation. They resolve, but they are no longer open hypotheses of frozenTarget. A page for the new leaf
  `OpenResearchLeaves31.neronSchemeExtensionDedekind` would be the blueprint's next step. blueprint/ was not edited.
* To fold the next field by copy on this tree:
  1. rerun `Taint.lean` with the new root and field names;
  2. run `gen.py` with a new suffix and an edit list;
  3. write the new top module with `top.py`.
