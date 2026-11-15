# gt-sga7 — `sga7_IX_3_3` discharged from its strictly henselian form

**Verdict.** The open hypothesis `sga7_IX_3_3` (`CToPrinted.SGA7_IX_3_3`, SGA 7 IX 3.3 second assertion over any DVR
extension) is proved **with its exact type** in `ZInQKernel/Contrib/OneProof/SGA7PersistsNF.lean`:
`SGA7PersistsNF.sga7_IX_3_3_of_SH : SGA7_IX_3_3_SH → GapSHPair.NeronBaseChangeStrictHenselization →
CToPrinted.SGA3_VIB_3_10 → AVGlue.GeomConnOfRationalPoint → CToPrinted.SGA7_IX_3_3`. Only `SGA7_IX_3_3_SH` (the field
with both DVRs strictly henselian; a specialization of the field) is new; the other three are bundle fields. Proof:
gt-shpair's every-characteristic strict henselization pair, Néron base change, the SH statement at (P, P'), and fpqc
descent of the open immersion and its image along Spec P' → Spec O' (sh-printed2's argument, ported).

Correction to the task premise: the chain's `SemistablePersistsSHcp` is the *first* assertion of 3.3 and cannot give
the second; a strictly henselian form of the second assertion is the new leaf.

**Compiles (VERIFIED).** File: 10 s, 0 errors, standard axioms. `#discharges`: `DISCHARGES
[OpenResearchLeaves19.sga7_IX_3_3] by SGA7PersistsNF.sga7_IX_3_3_of_SH`. autofold dry run
(`scratch/gt-sga7/fold-spec.json`) compiles; strict 49/12 → 50/11, strictest 48/13 → 49/12.

**Also in the file.** The restricted leaf `SGA7_IX_3_3_SHcp` (+ char 0, perfect residue field: no reading risk) gives
`SGA7_IX_3_3cp`, and the one consumer rerouted (`semistableNeronBaseChange_of_SHcp`); that route needs a manual bypass
fold at TailZ23 L794 (report §4).

**Remains.** Read SGA 7 IX 3.3 (base trait; algebraically closed residue field?) to choose option A (reading-risk leaf,
auto-fold) or B (restricted leaf, bypass); locators.md row. Report: docs/research/gt-sga7.md.
