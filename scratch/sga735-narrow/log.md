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

## Step 2b: echelon clause (findings)

* The conclusion (sigma-1)^2 = 0 IS read: `HDec.PkgI2.quatUnipotentTrivial` (LPrefix.lean L702-773) needs the
  square-zero hypothesis on G[3^{2k}] (VERIFIED, read); it feeds goodReduction_of_QM_rational3 (A6 route) through r6.
  The D2 consumer `fixed_of_unipSq_of_iterate` (Objects.lean L1102) would accept any nilpotence index.
* So no narrowing; cannot prove (needs IX 2.4 + IX §2 ranks, sga7-35-proof); an IX 2.4 split leaf would be a
  consequence (GLUE). Reading (b) stays: new row flagged pending reading -> GLUE.

## Step 3: fold (VERIFIED)

* gen/gen.py (homfree-noemb copylib, taint-driven): FoldCheck.lean, 65 blocks (16 carriers, 41 tainted, 8 typed).
* Compile 1: missing olean (module not built) -> `lake build ZInQKernel.Contrib.OneProof.SGA7IX35ForwardAC` OK.
* Compile 2: heartbeat timeouts in 5 `_hf` maps; compile 3 (maxHeartbeats 1000000): 2 remain.
* Cause: top-level `open` from each block's context leaked into later blocks. Fix: wrap each block in section/end.
* Compile 4: no errors, 75 s; `sixContactMin_of_open42` axioms [propext, Classical.choice, Quot.sound].
* Statement.lean: rfl check OK. Discharges.lean: 48 lines, none from the new file (expected: weaker leaf).
* Counts: 33 fields, strict 13/20 -> 13/20 (proposed row, pending reading on (b)); 14/19 if the 3.5 display is
  read and contains the echelon clause.

## Use probe (VERIFIED, computed; UseProbe.lean, useprobe_out.txt)

* In the closure of sixContactMin_of_open41: HDec.PkgI2.quatUnipotentTrivial (used by
  HDec.PkgI2.goodReduction_of_QM_rational3), UnipSq, both RaynaudCriterionNF. NOT in closure:
  PkgI2.fixed_of_unipSq_of_iterate, PkgI2.D2_fixed_of_raynaud, PkgI2.RaynaudCriterion.
* 45 closure constants have UnipSq / RaynaudCriterionNF in their type (cost of narrowing r6 to a nilpotent form).
