# sgr-fold (fleet summary)

**Result: fold executed and compiled.** `ZInQ.OneProof.frozenTarget` no longer assumes
`shimuraIntegralModelRep` (the integral model of the Shimura curve, GLUE) or `quotientP1Coordinate` (GLUE). It
assumes one new glue field instead, `OpenGlue8.nvLocalInertia : SGRDirect.NVLocalInertia` (h-b1 Lemma NV step 3;
project glue, GLUE, not printed form).
- H fields: 56 → 55.
- strict: 45/11 → 45/10. strictest: 43/13 → 43/12.
- open hypotheses: 62 → 61.

**How:** sgr-direct's route NV, folded by hand in r6-nf's style. Details are in docs/research/sgr-fold.md.
- **Consumer rerouted.** TailO's `glue4_of_open6` now proves `HeckeVertWitness` with
  `SGRDirect.heckeVertWitness_of_nvSqrtAny`, from generation-6 fields.
- **Two Props carried down.** OpenGlue6 and OpenGlue7 carry `nvLocalInertia` and `heckeSqrtBranchAny`, so no
  stack-theorem type changed.
- **Prune.** PruneScan then flagged exactly the two fields, and the 12-field prune set was deleted. Off-chain, gens
  10 and 11 lost the field too and `addedLeaves5_of_open6` was deleted as a dead reader.
- **New top.** TailZ36 adds `OpenGlue8` and `sixContactMin_of_open30`. The contributor file
  `ZInQKernel/Contrib/OneProof/SGRFold.lean` proves `HeckeSqrtBranchAny` at the top from `elkiesX6StarPrinted`.

**Checks (VERIFIED):**
- `lake build +ZInQKernel.OneProof.Main` succeeds, and so does every module under ZInQKernel/OneProof and
  ZInQKernel/Contrib.
- The axioms are standard.
- `frozenTarget`'s type changed only in `g : OpenGlue7 → OpenGlue8`.
- PruneScan: 0 unused of 55.
- DumpCompact hash guard: only bundles, conversions (including the edited consumer) and `frozenTarget` changed; no
  stack theorem changed.
- `#discharges`: 61 / 7, the base's seven.
- `render_open.py --check` passes.

**Ledger edits:**
- kinds.tsv and claims.tsv: the two old rows were removed, and an nvLocalInertia row (claim: nv-local) was added.
- open-statements.json, OPEN.md, pages-wanted.md, CONTRIBUTING.md and STATUS.md were regenerated.
- The positive control `t1` in scratch/contrib-kit/DischargesTest.lean was moved to `NVLocalInertia` and rerun.

**What remains:**
- When nv-local proves `NVLocalInertia`, an autofold of `OpenGlue8.nvLocalInertia` gives another −1 GLUE.
- The host tasks p1-quot and sir-printed now target removed fields.
- kinds.tsv packet, label and tier, and the credits/fold-queue rows, are left for the integrator.
