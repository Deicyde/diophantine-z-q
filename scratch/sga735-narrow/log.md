# sga735-narrow results log

Base: wip/leaf-fold33b 0e3c3125 (origin/main c1e4ed1b already merged: "Already up to date"). Build tree copied
from ~/dzq-wt/leaf-fold33b (same commit); `lake build ZInQKernel.OneProof.Main --no-build`: all up to date.

## Step 1: chain uses (VERIFIED, computed)

`scratch/sga735-narrow/Taint.lean` (homfree-noemb's Taint.lean with seeds = projections `sga7_IX_3_5_ForwardGeom`,
`semistableUnipotent`, closure of `HDec.HSyn.sixContactMin_of_open41`); output `taint_out.txt`:
closure 241701 constants, 58 tainted, carriers = OpenResearchLeaves14..29.
Field reads (projection uses other than pass-through `x := n.x`):
* `HDec.HSyn.openResearchLeaves19_of_OpenResearchLeaves20_hf` (HomFreeFiniteAlgClosedReroute.lean L1667):
  `semistableUnipotent := UnipotentForward.semistableUnipotent_of_forwardGeom n.sga7_IX_3_5_ForwardGeom ...`
  (the only read of `sga7_IX_3_5_ForwardGeom`).
* `HDec.HSyn.raynaudCriterionNF_of14_hf` (same file L1493): `GapNeron.raynaudCriterion_leavesNF ... r.semistableUnipotent`
  (the only read of `semistableUnipotent`). Proves `PkgI2.RaynaudCriterionNF` (r6 at NUMBER FIELDS).
  Inside, `raynaudCriterion_of_leavesNF` applies `hU` at `K` a number field, `O` any DVR of `K`
  (residue field finite, hence perfect), `Ω = AlgebraicClosure K`. Via `unipotentFromSH_of`, the field itself is
  applied at the inertia field `E` of `w` (char 0, residue field algebraic over the finite `k(O)` and separably closed,
  hence algebraically closed).

## Step 2a: k(s) reading -> restriction to algebraically closed residue fields

`ZInQKernel/Contrib/OneProof/SGA7IX35ForwardAC.lean` (namespace SGA735AC), compiled with `lake env lean`,
standard axioms (VERIFIED):
* `SGA7_IX_3_5_ForwardGeomAC` (field + `[IsAlgClosed (IsLocalRing.ResidueField O)]`);
* `forwardGeomAC_of_forwardGeom` (specialization), `forwardGeomAC_of_forwardRes` (from the k(s) reading),
  `forwardGeomAC_of_forward` (from gt-unip's reading-robust form);
* `SemistableUnipotentCP` (= ReductSplit.SemistableUnipotent + `[PerfectField k(O)]`),
  `semistableUnipotentCP_of_forwardGeomAC hP hE hN`;
* `raynaudCriterion_leavesNF_cp` (r6 at number fields from SemistableUnipotentCP),
  `raynaudCriterionNF_of_forwardGeomAC`.
