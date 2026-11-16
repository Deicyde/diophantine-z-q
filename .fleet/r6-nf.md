# r6-nf: final

**Result (VERIFIED, compiled).** `frozenTarget` loses `OpenResearchLeaves21.neronSchemeModelExistsDVR` (BLR 1.4/3 over
every DVR) and gains nothing. H fields 56 → 55; strict 46/10 → 45/10; strictest 45/11 → 44/11 (fields −1, LEAF −1).

What made the field unnecessary:
* **r8 was dead.** It is pruned from `ResearchLeaves3` and `OpenResearchLeaves2/5/7/8`, together with the three
  `OpenResearchLeaves9` fields that fed only r8.
* **r6 is applied only at number fields.** It is now `HDec.PkgI2.RaynaudCriterionNF` (LPrefix; the kernel's R6 with
  `[NumberField K]`) in the six old bundles. Its consumers are restated: `[NumberField K]` is added at the A6
  application sites and in `QML3.goodReduction`, `qmModelG3_of` builds the instance from `K ≤ L'`, and the rest only
  have the binder retyped.
* **r6 and SS1/SS3 are supplied in `sixContactMin_of_open20` (TailZ26).** They come from neron-dvr's
  `GapNeron.neronSchemeModelExistsNF` (N1 alone), through new helpers `raynaudCriterionNF_of14` and `ss1_ss3_of14NF`
  (the §3.2 reroute), threaded as binders of open17–19. TailZ26 now imports NeronDVR. The types of open20–open28 and
  `frozenTarget` are unchanged.
* **The prune.** PruneScan then found the top field unused. It was pruned from generations 14–21, with the dead reader
  `ss1_ss3_of14`.

**Checks:**
* `lake build +ZInQKernel.OneProof.Main` OK;
* `frozenTarget` axioms `[propext, Classical.choice, Quot.sound]`, and its type is identical to the base;
* PruneScan: 0 unused of 55;
* DumpCompact/cmp_hashes: removed 18 (16 projections, the dead reader, one auxiliary `_proof_3` shared by hash),
  new 40 (NeronDVR 35, helpers 5), changed 327 (bundles, conversions, stack open17–20, edited consumers);
* DischargesTest: same 7 discharges and controls, 62 open hypotheses;
* OpenStatements/render_open regenerated, `--check` ok.

**Remains / notes:**
* Two edits slightly beyond the letter of the rules, flagged in the report:
  * an import line in TailZ26;
  * an HDec definition equal to `GapNeron.RaynaudCriterionNF`. It could be deduped later by a one-line Contrib edit.
* The SGA 7 SH leaves that could now take cp forms (SPECULATIVE): `raynaudSemistableSH` (its r6 and SS1 uses are at
  number fields; `ss1_ss3_of_cp_fullNF` exists), and `sga7_IX_3_5_ForwardGeom` (its only live use is now r6, at number
  fields). They were not switched.
* frontier-crosswalk.tsv still lists H-148; that file was not editable here.

Report: docs/research/r6-nf.md. Log and tools: scratch/r6-nf/.
