# sga7-cp results log

Base: wip/r6-nf 0bc2446d (frozenTarget through sixContactMin_of_open28, 55 H fields).

## Reachability of the two fields (VERIFIED by reading TailZ23-TailZ34 and NeronDVR.lean)

* `raynaudSemistableSH` (OpenResearchLeaves14-21): one reader, `HSyn.raynaudSemistable_of14` (TailZ23 L724), via
  `ReductB.raynaudSemistable_of_SH_pair`; its consumers are
  * `HSyn.raynaudCriterionNF_of14` (TailZ26, r6 at number fields), and
  * `HSyn.semistableReductionDVR_of14` -> `HSyn.ss1_ss3_of14NF` (TailZ26, SS1/SS3).
* `sga7_IX_3_5_ForwardGeom` (OpenResearchLeaves20-21): one reader, the conversion
  `openResearchLeaves19_of_OpenResearchLeaves20` (TailZ33), filling `semistableUnipotent` by
  `UnipotentForward.semistableUnipotent_of_forwardGeom`; `semistableUnipotent` (gen 14-19) has one reader,
  `raynaudCriterionNF_of14` (r6 at number fields: `hU K O (AlgebraicClosure K) w ...`, `K` a number field).
* Composite conversions gen 21 -> gen 14: scratch/sga7-cp/compose.py (output in compose-out.txt).

## Can either field be removed through existing bundle fields? (SPECULATIVE judgement, mathematical)

* raynaudSemistableSH: no. SS1 (`SemistableReductionThm`) is derived from Raynaud's 4.7 (K1: A[m] rational after
  K(A[m])); no other bundle field gives semistability (3.3 = persistence presupposes it; 3.5 forward presupposes
  it; no 3.5 converse or Grothendieck 3.6 field).
* sga7_IX_3_5_ForwardGeom: no. The only source of unipotence of inertia for r6; the r6 consumers
  (`goodReduction_of_QM_rational3_of_alg`, `G15Ram.raynaudPlace_of_R6`) need the Galois form. An alternative route
  (semistable + potentially good => good, via the toric part) needs character groups of tori, not in the tree.
=> fallback: weaken both to the instance used (char 0, perfect residue field).

## Statements

* new leaf `SGA7CP.SGA7_IX_3_5_ForwardGeomCP` = `UnipotentForward.SGA7_IX_3_5_ForwardGeom` + `[CharZero K]`
  `[PerfectField (ResidueField O)]`.
* existing `ReductB.RaynaudSemistableSHcp` (TailZ23 L303) = `ReductGlue.RaynaudSemistableSH` + the same instances.
* new bundle `HDec.HSyn.OpenResearchLeaves22` (Contrib/OneProof/SGA7CPFold.lean) = OpenResearchLeaves21 with
  `raynaudSemistableSH` -> `raynaudSemistableSHcp`, `sga7_IX_3_5_ForwardGeom` -> `sga7_IX_3_5_ForwardGeomCP`.

## Compile log
* base build `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`: OK (12986 jobs; build-base.txt). VERIFIED
* DumpCompact base (Main): 15668 constants (hashes_before.txt). VERIFIED
* `lake build +ZInQKernel.Contrib.OneProof.SGA7CP`: OK first try (7.7 s). VERIFIED
* `lake build +ZInQKernel.Contrib.OneProof.SGA7CPFold`: OK first try (4.7 s). VERIFIED
* scratch/sga7-cp/Check.lean (Check-output.txt): `SGA7CPCheck.frozenTarget'` (Main's frozenTarget with
  `r : OpenResearchLeaves22` and `sixContactMin_of_open29`) standard axioms; type identical to frozenTarget except
  `OpenResearchLeaves21` -> `OpenResearchLeaves22`; frozenTarget recovered from frozenTarget' through
  `openResearchLeaves22_of_OpenResearchLeaves21` (example compiles). VERIFIED
* `#discharges` (same run): 62 open hypotheses, 1694 theorems checked, 31 discharge one. The 24 new lines are the
  projections `OpenResearchLeaves22.<f>` (assume the new bundle; artefact of the bundle living in a Contrib module);
  the SGA7CP theorems discharge nothing (weakening, not a proof of either field). VERIFIED
* DumpCompactAfter (Main + SGA7CP + SGA7CPFold) + cmp_hashes.py: base 15668, after 15726, removed 0, new 58
  (SGA7CP 15, SGA7CPFold 43), changed 0 (cmp_hashes_out.txt). VERIFIED
* PruneScan rooted at frozenTarget' (prunescan-out.txt): OpenResearchLeaves22 28, OpenTextbookLeaves11 12,
  OpenAddedLeaves17 14, OpenGlue7 1 = 55 fields, 0 unused, prune set empty. VERIFIED
