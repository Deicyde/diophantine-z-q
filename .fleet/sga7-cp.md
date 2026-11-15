# sga7-cp (fleet summary)

**Verdict.** Neither `raynaudSemistableSH` (SGA 7 IX 4.7 over strictly henselian DVRs) nor
`sga7_IX_3_5_ForwardGeom` (SGA 7 IX 3.5 forward) can be removed through fields already in the bundles. 4.7 is the
chain's only source of semistability (SS1 via K1). The forward half of 3.5 is its only source of unipotent inertia
(r6, which A6 and G15Ram consume in Galois form). So both are **weakened to the instance actually used**: a strictly
henselian DVR of a characteristic-0 field with perfect residue field.
* `ReductB.RaynaudSemistableSHcp` (already in the tree) replaces the 4.7 field.
* The new `SGA7CP.SGA7_IX_3_5_ForwardGeomCP` replaces the 3.5 field.

Both are specializations of the print under every reading, so both are printed form (restricted). Each removes a
recorded reading risk:
* 4.7: the residue field need not be algebraically closed;
* 3.5: the k(s) reading. The CP form follows from the reading-robust `SGA7_IX_3_5_Forward` with no glue.

H fields stay 55, and strict/strictest stay 45/10 and 44/11. The hypotheses are strictly weaker (the old bundle
implies the new).

**What compiles (VERIFIED).**
* `ZInQKernel/Contrib/OneProof/SGA7CP.lean`: the leaf, r6 at number fields (`raynaudCriterionNF_of_cpLeaves`) and
  SS1/SS3 (`ss1_ss3_of_cpLeaves`) from the restricted leaves plus fields already in the bundles.
* `ZInQKernel/Contrib/OneProof/SGA7CPFold.lean`: the generation module, with `OpenResearchLeaves22` and
  `sixContactMin_of_open29`. It bypasses generations 14–21 to `sixContactMin_of_open11`, and is ready to move to
  `OneProof/H/TailZ35.lean`.
* `frozenTarget'` (Main's theorem switched to the new bundle and top theorem) has the standard axioms. Its type
  differs from `frozenTarget` only in the research bundle.
* Hash guard: 0 changed, 0 removed, 58 new.
* PruneScan: 0 unused of 55.
* `#discharges` output recorded: the new theorems discharge nothing, as expected for a weakening.

**What remains.**
* The integrator moves SGA7CPFold to `OneProof/H/TailZ35.lean`, switches Main (two tokens), applies the kinds.tsv
  rows (scratch/sga7-cp/kinds-rows-proposed.tsv) and regenerates OPEN.md.
* autofold.py cannot express a weaker replacement. scratch/sga7-cp/autofold.json documents the hand fold instead.
* Open reading items, unchanged: the `m = 3` boundary of 4.7 (locators.md R6) and the echelon clause of 3.5.

Report: docs/research/sga7-cp.md. Log: scratch/sga7-cp/log.md.
