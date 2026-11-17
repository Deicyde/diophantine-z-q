# dict-models (fleet summary)

**Result.** All four rows asked about are proved exactly (statements unchanged), each from a new leaf in the print's
own form. The only other inputs are fields already in the bundles (`sga3_VIB_3_10`, `geomConnOfRationalPoint`).
The 11-16 dictionary pass had rated these rows consequence; each extra step it charged is now a Lean proof or no
longer needed.

1. `sga7_IX_3_3_SH`. New leaf `SGA7_IX_3_3_SHpre`, with `U := pullback.fst⁻¹(N⁰)`, which is the print's `N⁰ ×_S S'`.
   The field follows through the chain's `idComp_baseChange` (SGA 3 VI_B 3.3, already proved). Printed form.
2. `raynaudSemistableSH`. New leaf `RaynaudSemistableSHOr`: the conclusion is the `k(s)` form (with a general torus,
   one that splits over `k̄`) or the geometric form. Lean now proves the step from `k(s)` up to `k̄`
   (`hasSemiAbelian_pullback_bar`, every residue field, using 04KV). Printed form under either reading; the other
   reading risks (algebraically closed residue field, `m > 3`) are unchanged.
3. `mumfordGroupLaw`. New leaf `MumfordGroupLawConn` (adds `ConnectedSpace S`). The gluing over the open connected
   components is proved in general: `glue_ext`, `glue_exists`, and group objects glued by Yoneda through
   `GrpObj.ofRepresentableBy`. Printed form.
4. `neronBaseChangeStrictHenselization`. New leaf `BLR_7_2_1`, which is the chain's existing
   `ReductGlue.NeronBaseChangeUnramifiedDVR` (BLR 7.2 Thm 1 form). EGA IV 18.8.8 is no longer used. Printed form,
   with one reading risk: the print may cover only étale maps, strict henselization and completion.

**What compiles (VERIFIED).** Four files under `ZInQKernel/Contrib/OneProof/`: `SGA7IX33SHPre`,
`RaynaudSemistableOr`, `MumfordGroupLawConn`, `NeronBaseChangeBLR72`.
* `#discharges`: all four fields discharged, standard axioms (`scratch/dict-models/discharges.txt`).
* Verbatim statement copies check `rfl` against the originals (`Statements.lean`).
* The autofold spec `scratch/dict-models/autofold.json` dry-runs at 40/8 → 40/8. The rows are still LEAF on
  e22df37c; on a base with the dictionary re-rating applied, up to four rows return to LEAF.
* The dry-run fold compiles (`FoldCheck.lean`, `sixContactMin_of_open35` with standard axioms).

**What remains.** Reading checks with the prints, none done (no network):
* GIT 6.14 assumes `S` connected;
* the class of extensions in BLR 7.2/1;
* SGA 7 IX 3.3 and 4.7: the residue-field hypothesis and `m`.

Proposed locators rows: `scratch/dict-models/locators-rows-proposed.md`. The integrator runs autofold on the spec.

Report: docs/research/dict-models.md. Log: scratch/dict-models/log.md.
