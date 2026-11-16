# raynaud-proof log

Base 0caafe66 (top module TailZ42, `sixContactMin_of_open35`; field `HDec.HSyn.OpenResearchLeaves26.raynaudSemistableSH`,
type `ReductGlue.RaynaudSemistableSH`, TailZ14 L1105).

## 2026-11-16 13:15 consumer scan (VERIFIED by grep over ZInQKernel/)
- `.raynaudSemistableSH` is read only at TailZ23 L722 (`raynaudSemistable_of14`); every other occurrence is a
  pass-through `raynaudSemistableSH := n.raynaudSemistableSH` in the generation maps.
- `raynaudSemistable_of14` is read by `raynaudCriterionNF_of14` (TailZ26 L171, r6 at number fields, via
  `GapNeron.raynaudCriterion_leavesNF`) and `semistableReductionDVR_of14` (TailZ23 L727, K1), whose only reader is
  `ss1_ss3_of14NF` (TailZ26 L179) through `GapNeron.ss1_ss3_of_cpNF`, which applies it only via
  `reductionNF_of_general` (number fields).
- Both feed `sixContactMin_of_open20` (TailZ26 L188). So the live chain applies 4.7 only at number-field DVRs
  (through `StrictHenselizationPair`, i.e. at strictly henselian DVRs of characteristic 0 with algebraically
  closed residue field).
- r6 (RaynaudCriterionNF) itself is read by A6 (`goodReduction_of_QM_rational3_of_alg`, LPrefix L814) only with
  m = 3, l = 3.

## Bundle fields checked as inputs (VERIFIED by reading OPEN.md / TailZ41)
- `sga7_IX_3_5_ForwardGeom`: semistable => (sigma-1)^2 = 0 (wrong direction for 4.7).
- `sga7_IX_3_3_SH`: N0 x S' = N'0 under semistable reduction (assumes semistability; wrong direction).
- `r7a` (NOS, Serre-Tate Thm 1): good reduction iff inertia trivial on all A[m] (needs all m, not one).
- `neronBaseChangeStrictHenselization`, `sga3_VIB_3_10`, `neronSchemeExtensionExists`, `mumfordTorsionAlgClosed`:
  structure inputs, no monodromy content.
- No field states Grothendieck's quasi-unipotence (SGA 7 IX 4.3 / Serre-Tate appendix), the semistable reduction
  theorem 3.6, or the converse of 3.5 (unipotent => semistable). r8 (GrothendieckMonodromy) is dead and was derived
  from 3.6 <- 4.7 anyway.
