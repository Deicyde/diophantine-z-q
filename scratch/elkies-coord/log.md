# elkies-coord results log

Task: discharge research field `elkiesX6StarPrinted` (ElkiesX6Star.ElkiesX6StarPrinted,
ZInQKernel/Contrib/OneProof/ElkiesX6Star.lean:67) from Elkies' printed form `ℚ(X₆)^W = ℚ(t)` + charts.

## Setup
- Build tree: copied .lake/build and lean/.lake/build from ~/dzq-wt/p1-quot (same commit 24f97774). VERIFIED
  `lake env lean` on a file importing ZInQKernel.Contrib.OneProof.ElkiesX6Star works without rebuild.

## Steps
- [x] ffPullback (comorphism of an automorphism on the function field), ffPullback_germ, res_eq_of_germ_eq:
  compile (scratch/elkies-coord/ElkiesCoord.lean). VERIFIED
- [x] Full chain compiles: scratch/elkies-coord/ElkiesCoord.lean, `elkiesX6StarPrinted_of_functionField :
  ElkiesX6StarFunctionField → ElkiesX6Star.ElkiesX6StarPrinted`; #print axioms: propext, Classical.choice,
  Quot.sound. VERIFIED
- [x] Contribution ZInQKernel/Contrib/OneProof/ElkiesX6StarPrinted.lean (copy of the scratch file);
  `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ElkiesX6StarPrinted`:
  12983 jobs, success. VERIFIED (a first build of #discharges against a stale copied Main.olean reported
  OpenResearchLeaves19; rerun after the proper build reports OpenResearchLeaves20.)
- [x] #discharges (scratch/elkies-coord/discharges.txt): DISCHARGES [OpenResearchLeaves20.elkiesX6StarPrinted] by
  ElkiesCoord.elkiesX6StarPrinted_of_functionField, still assumes [ElkiesCoord.ElkiesX6StarFunctionField], standard
  axioms. VERIFIED
- [x] autofold dry-run (autofold.json): strict 47/11 on 58 -> 48/10 on 58; strictest 46/12 -> 47/11.
  FoldDryRun.lean (dry-run output minus line 1) compiles; sixContactMin_of_open28 standard axioms. VERIFIED
- [x] Integrality from the charts (compiled; developed in scratch/elkies-coord/Integral.lean, commit "X6 integral
  and t regular...", then merged into ElkiesCoord.lean): `elkiesRing_isDomain` (ElkiesRing ↪ AdjoinRoot of
  r² + 3(s²+1) over ℚ[s], prime since monic quadratic without root: lc(b)² = −3 impossible), `isIntegral_of_charts`,
  `genericPoint_mem_of_charts`. The leaf's function-field clause is now `∀ (_ : IsIntegral X.left) (hη), ...`
  (conditional, weaker than the earlier `∃` form). VERIFIED
- [x] Rebuilt contribution (12123 jobs ok); #discharges rerun: same DISCHARGES line, 1344 theorems checked, standard
  axioms, no sorry; autofold dry-run unchanged (47/11 -> 48/10; strictest 46/12 -> 47/11); FoldDryRun.lean compiles,
  sixContactMin_of_open28 standard axioms. VERIFIED
