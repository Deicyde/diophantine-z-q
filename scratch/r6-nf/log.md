# r6-nf results log

- 11-15 04:24 start. Base 9a100aa7 (wip/leaf-fold22b); merged origin/wip/neron-dvr (998fa5b5) -> 2a6b6c4b.
  lean/.lake/build was missing: copied (reflink) from ~/dzq-wt/theta-fold (lean/ identical).
- 04:26 base `lake build +ZInQKernel.OneProof.Main` OK (12984 jobs, only Main rebuilt); frozenTarget axioms standard.
- 04:27 base DumpCompact (scratch/r6-nf/DumpCompact.lean: OneProof + Contrib.OneProof modules in Main's env):
  15646 constants -> hashes_before.txt; frozenTarget type in frozenTarget_before.txt.
- 04:31 base PruneScan (Main root): OpenResearchLeaves21 29, OpenTextbookLeaves11 12, OpenAddedLeaves17 14,
  OpenGlue7 1 = 56 fields, 0 unused (prunescan-base-out.txt, used-fields-base.txt, unused-all-base.txt).
  unused-all-base already lists r8 in ResearchLeaves3, OpenResearchLeaves2/5/7/8 and OpenResearchLeaves9's
  semistableReductionDVR, semistableUnipotent, neronSchemeModelExistsDVR (they fed only r8); also
  ResearchLeaves3.r6 is unused (r6 is read only through OpenResearchLeaves2.r6 in gluePieces_of_open4).
- Design (no Lean): NeronDVR.lean imports BLRLocalizes -> TailZ24, so its theorems cannot be called in TailZ23
  where r6 and SS1/SS3 are produced. TailZ26 already imports BLRLocalizes. Plan: add `import
  ZInQKernel.Contrib.OneProof.NeronDVR` to TailZ26 (no new transitive imports besides NeronDVR itself), thread two
  binders `(h6 : PkgI2.RaynaudCriterionNF.{0}) (hSS : SemistableReductionThm ∧ SemistablePersists)` through
  sixContactMin_of_open17/18/19 (TailZ23-25), and supply them in sixContactMin_of_open20 (TailZ26) from its bundles;
  open20..open28 and frozenTarget keep their types (no conflict with concurrent folds building on open28).
  `PkgI2.RaynaudCriterionNF.{u}` is defined in LPrefix (HDec.PkgI2, universe-polymorphic; at .{0} it is
  syntactically GapNeron.RaynaudCriterionNF).
- step 1 (scratch/r6-nf/prune_r8.py, output prune_r8_out.txt): deleted r8 from ResearchLeaves3, OpenResearchLeaves2/5/7/8,
  the three r8-only fields of OpenResearchLeaves9, and their 12 assignments. Not compiled yet (compiled with step 2).
- 05:43 build after steps 1-2 (+ reroute/threading): `lake build +ZInQKernel.OneProof.Main` OK first try (12985 jobs); frozenTarget axioms standard.
- 05:50 PruneScan after step 2: exactly OpenResearchLeaves21.neronSchemeModelExistsDVR unused; prune set = the field in
  OpenResearchLeaves14-21 (8 FIELD lines, no constants; prune-set-step2.txt). unused-all: r8 rows and the
  OpenResearchLeaves9 r8-only fields gone. DeadCascade: ss1_ss3_of14 (+ generated casesOn/recOn).
- step 3b (scratch/r6-nf/prune_neron.py, prune_neron_out.txt): deleted the 8 fields, 7 assignments, ss1_ss3_of14.
- 06:3x build after step 3b: `lake build +ZInQKernel.OneProof.Main` OK (12985 jobs); frozenTarget axioms standard;
  frozenTarget's type prints identically (frozenTarget_before.txt vs frozenTarget_after.txt).
- PruneScan after: OpenResearchLeaves21 28, OpenTextbookLeaves11 12, OpenAddedLeaves17 14, OpenGlue7 1 = 55 fields,
  0 unused, prune set empty (prunescan-after-out.txt, used-fields.txt).
- DumpCompact after: 15668 constants (hashes_after.txt); cmp_hashes.py -> cmp_hashes_out.txt: removed 18, new 40,
  changed 327. Removed = 16 pruned projections + ss1_ss3_of14 +
  R08_GrothendieckMonodromy._proof_3 (aux-proof sharing: HDec.PkgI2.RaynaudCriterionNF._proof_1 has exactly its old
  type and value hashes; R08_GrothendieckMonodromy changes in value only). New = 35 NeronDVR (now in Main's closure via
  the TailZ26 import) + LPrefix 3 (RaynaudCriterionNF, its _proof_1, raynaudCriterionNF_of_general) + TailZ26 2
  (raynaudCriterionNF_of14, ss1_ss3_of14NF).
- DischargesTest: same 7 discharges and controls; 62 open hypotheses (was 63).
