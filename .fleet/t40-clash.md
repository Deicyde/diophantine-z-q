# t40-clash: summary

**Verdict: fixed.** `ZInQKernel.Contrib.RLeaf.T40` (T40 and T39 from the single leaf
`X0Transitive`) now imports together with the Contrib Tau Ceti modules the H assembly uses.

**The clash.** Three names, not one, were declared twice. The copies are in the vendored
commit-5a01f5fe `TauCeti/Algebra/GroupWithZero/Units/Basic.lean` and in t40-tate's commit-4d91513e
`TauCeti/Backport/Algebra/Group/Units/Basic.lean`:
`Units.val_mul_zpow_natCast_mul`, `Units.val_mul_zpow_neg_natCast_succ_mul` and
`TauCeti.mem_range_iff_exists_units_map_eq`. Each Backport copy is Tau Ceti's later monoid
generalization of the same statement. `scratch/t40-clash/Clash2.lean` reproduced the error.

**The fix.** The Backport file drops the three copies and public-imports the vendored
GroupWithZero module, so downstream code still sees the names. Its only remaining declaration is
`Units.eq_of_mul_mul_inv_eq_of_commute`. Its "Modified for the Z-in-Q kernel" line and the
modified list in `ThirdParty/TauCeti/NOTICE` record the change. The only uses, in
`CoordinateEvaluation.lean`, are at a `NormedField`, and they build unchanged. No other file was
edited.

**What compiles** (each run one `lake` process, no errors):
- `lake build` of T40 and TateCuspTorsion rebuilt all 12 modules that import the changed file
  (3 min). T40's `#print axioms` lines report the standard axioms only.
- `scratch/t40-clash/Together.lean` compiles. It imports T40, Mobius.Main, FrobPieces
  (there is no `Contrib.FrobChain`), Chebotarev.FrobeniusDense, AbsFrob.Basic, GZTheta.ALFinal,
  RLeaf.T36Torsion and GroupWithZero.Units.Basic.
- `lake build` of all 74 top-level Contrib modules succeeds. T40 paired with each of the other
  73 compiles: 73/73 (`pairwise-result.txt`). Before the fix, 8 of them clashed with T40
  (KroneckerWeber.Leaves, LocalKW.T30, T14.WP3, TYZGenus.ShimuraFricke, and four Tau Ceti
  class-field modules).

**What remains (not T40, already there before this task).** Importing all of Contrib at once
(`AllContrib.lean`) fails because `Subgroup.stabilizerInclusion` is declared twice: once in the
vendored 5a01f5fe `GroupAction/Stabilizer.lean`, once in the vendored 97a5b235
`GroupAction/Stabilizer/Basic.lean`. That is outside this task's edit scope, and it can be fixed
the same way. Report: `docs/research/t40-clash.md`; log: `scratch/t40-clash/log.md`.
