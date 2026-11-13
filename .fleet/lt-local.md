# lt-local (fleet summary)

**Result (VERIFIED, compiled, standard axioms only).** g0-assemble2's GLUE field 39
`HSyn.G0AssembleMod.LinkedTateLocal` is proved, with its statement unchanged, over g0-assemble3's
`G7Data`, which now carries `[L:ℚ] ≤ D`:

`LTLocal.linkedTateLocal_of_tateBridge35 : RaynaudCriterion (R6) → TorsionStructure (I2-Tors) →
UnramRoots 2 5 → UnramRoots 2 3 → G14Bridge.TateBridge35 → G0Split.FibreSimple →
LinkedTate.QMEndRank → LinkedTateLocal`

`linkedTateLocal_of_algFrobRed` is the same theorem with `TateBridge35` replaced by I3.M0 +
`FrobTrace.AlgFrobRed`.

Over g0-assemble2's `G7Data`, which lacks the bound, the same inputs prove the corrected statement
`LTLocal.LinkedTateLocalD`: `LinkedTateLocal` with the premise `finrank ℚ L ≤ heightD`.

**Finding.** This route needs `[L:ℚ] ≤ D`:
- for `G7Clauses`;
- for the tame closure of `L_v` at `p > D`.

The bound fails for arbitrary g0-assemble2 `G7Data`, as local-data F3, g8-object and linked-tate
also found. g0-assemble3's fix of `G7Data` is the right correction.

**What compiles.**
- `scratch/lt-local/LtLocal.lean` (9 576 lines, `build.sh`): exit 0, 64 s, 11 standard axiom
  reports.
- `scratch/lt-local/LtLocal4.lean` (9 626 lines, `build4.sh`, the G7Data fix ported by
  `mk_base4.py`): exit 0, 64 s, 14 standard axiom reports.

**New Lean, all proved.**
- `exists_equiv_extending`: `ℂ ≃+* ℚ̄_ℓ` compatible with given embeddings of `ℚ̄`.
- `g7Clauses_of_transport`: local-data's G7 clauses for `TateBridge35`'s transported cochain.
- `dim_bc_of_g7Data`: `dim A_{L'} = 2`.
- `modelEndRank4_of_qmEndRank`: `rank End(A_{L'}) = 4` from `FibreSimple` + `QMEndRank`.
- the main theorems.

`KerWild` and `DescentPts` come from lg-kerwild; `LocalData` comes from local-data's
`localData_of_g7`.

**What remains.**
- `TateBridge35`: g8-tate is working on it. frob-trace reduced it to I3.M0 + `AlgFrobRed`.
- `UnramRoots 2 5` and `UnramRoots 2 3`: local-glue's textbook statement, not yet in a bundle.

Recommendation: prove linked-tate's `LinkedRam` from local-glue on linked-tate's constructed data.
That would combine linked-tate's smaller Frobenius half with this route's leaf-only ramification
half. Not attempted.

Report: `docs/research/lt-local.md`. Log: `scratch/lt-local/log.md`.
