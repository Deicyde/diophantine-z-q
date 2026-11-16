# raynaud-proof (2026-11-16)

**Verdict.** `raynaudSemistableSH` (SGA 7 IX 4.7 over a strictly henselian DVR) is **not** discharged; the target −1
is not reached. No bundle field or proved glue supplies the monodromy input 4.7 needs: quasi-unipotence (IX 4.3 /
Serre–Tate appendix), the semistable reduction theorem 3.6, or the converse of 3.5. The SGA 7 fields in the bundle
(3.5 forward, 3.3) point the wrong way, and NOS (r7a) needs every `m`. The smallest missing input is 4.7 itself.

**Main result (compiles, standard axioms).** The live proof uses 4.7 only in the restricted printed form
`ReductB.RaynaudSemistableSHcp` (characteristic 0, algebraically closed residue field). A closure probe over
frozenTarget (259,583 constants) shows that the field's only reader is `raynaudSemistable_of14`. Its two consumers,
r6 at number fields and SS1/SS3, are proved from the cp leaf plus the other top-bundle fields by
`RaynaudCP.consumers_of_cp` (and the bundle-free `consumers_of_cp_leaves`), in
`ZInQKernel/Contrib/OneProof/RaynaudSemistableCP.lean`. The cp leaf is a specialization of the field
(`raynaudSemistableSHcp_of_SH`). It removes the row's flagged risk (the print may assume an algebraically closed
residue field) and the k(s)-versus-k̄ reading. The `m = 3` boundary (locators R6) remains, and it cannot be
narrowed away: r6 is used at `m = 3` for all `ℓ`.

**Fold.** Not an autofold, because the leaf is weaker than the field. It needs a bypass:
1. thread `h6` and `hSS` through `sixContactMin_of_open20..35`;
2. prune the field;
3. add a new top field `raynaudSemistableSHcp`.

Counts are unchanged (one LEAF for one LEAF). The recipe is in docs/research/raynaud-proof.md §5;
scratch/raynaud-proof/autofold.json holds the row data.

**Checks.** `lake build` of the contribution (12,999 jobs) and of Main (13,697 jobs) both succeed. `#discharges`
runs, and no RaynaudCP theorem discharges a field (expected). The verbatim statement copies are `rfl`-equal.
Outputs are in scratch/raynaud-proof/.

**Remains.** The integrator's bypass fold. A reading of SGA 7 IX 4.7 at `m = 3`. Discharging 4.7 itself would
take at least two new published leaves (e.g. 3.6 and the converse of 3.5), which does not reduce the count.
