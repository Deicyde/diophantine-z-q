# t25-newform — fleet report

**Main result: leaf T25 `PkgI4.NewformOfEigenform` is proved.**
`theorem T25.newformOfEigenform_leaf : PkgI4.NewformOfEigenform`
(ZInQKernel/Contrib/T25/NewformOfEigenform.lean), type exactly the leaf's Prop (C9.lean:384, verbatim
copy of Leaves.lean:4592), no extra hypotheses. `#print axioms`: [propext, Classical.choice,
Quot.sound]. `lake build ZInQKernel.Contrib.T25.NewformOfEigenform` succeeds.

**What compiles.**
- ZInQKernel/Contrib/T25/Bridge.lean (namespace `T25`): `newformOfEigenform` (unfolded leaf),
  `heckeTCuspNat_eq_coeff_smul` (coefficient identities ⇒ T_p-eigen for p ∤ M),
  `mem_cuspFormCharSpace_of_hasNebentypus` / `hasNebentypus_of_mem_cuspFormCharSpace` (slash
  nebentypus ↔ diamond character space), `newform_coeff_mul` (TC newform satisfies
  a_m a_n = Σ_{d|(m,n)} χ(d) d^{k-1} a_{mn/d²} for all m, n), `oldSpace_le_map_cuspFormsOld`,
  `not_mem_oldSpace`, plus small helpers (`slash_SL_eq_mapGL`, `coeff_zero`, `coeL`,
  `scaleGL_smul_eq_scaleH`). All standard axioms.
- 206 vendored oct16 Tau Ceti modules (~46.1k lines): closure of Newforms.Decomposition +
  Newforms.FullEigenform + HeckeSlash.Nebentypus.CoefficientFormula; one fix (explicit
  `IsSMulApply … UpperHalfPlane ℂ` args in ModularForms/Basic.lean). List in
  docs/research/t25-newform.md and scratch/t25-newform/vendor-new.txt.

**Key inputs.** TC `Newform.exists_newform_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul`,
`Newform.toEigenform` (bad-prime eigen), the divisor-sum formula for a_m(T_n F),
`mem_cuspFormCharSpace_iff_nebentypus`, `levelRaise_mem_cuspFormsOld`,
`disjoint_cuspFormsOld_cuspFormsNew`.

**Notion check.** Leaf `CF N k` is syntactically TC's cusp-form type; diamond label = lower-right
entry in both; TC newform ⇒ leaf newform. No statement difference.

**What remains.** Nothing for T25. No existing file edited.

Docs: docs/research/t25-newform.md; log: scratch/t25-newform/log.md.
